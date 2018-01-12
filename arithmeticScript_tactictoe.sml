(* ========================================================================== *)
(* This file was modifed by TacticToe.                                        *)
(* ========================================================================== *)
fun load_err s = load s handle _ => ();
List.app load_err ["BasicProvers", "Feedback", "Globals", "GrammarSpecials", "HOLgrammars", "HolKernel", "OpenTheoryMap", "PP", "Parse", "Prim_rec", "Q", "SatisfySimps", "UTF8", "Unicode", "UnicodeChars", "boolLib", "boolSimps", "markerLib", "mesonLib", "metisLib", "numTheory", "pairTheory", "prim_recTheory", "relationTheory", "simpLib"];
load "hhsRecord";
hhsSetup.set_irecord ();
hhsSetup.set_isearch ();

infix 0 hhs_infixl0_open hhs_infixl0_close;
infix 1 hhs_infixl1_open hhs_infixl1_close;
infix 2 hhs_infixl2_open hhs_infixl2_close;
infix 3 hhs_infixl3_open hhs_infixl3_close;
infix 4 hhs_infixl4_open hhs_infixl4_close;
infix 5 hhs_infixl5_open hhs_infixl5_close;
infix 6 hhs_infixl6_open hhs_infixl6_close;
infix 7 hhs_infixl7_open hhs_infixl7_close;
infix 8 hhs_infixl8_open hhs_infixl8_close;
infix 9 hhs_infixl9_open hhs_infixl9_close;
infixr 0 hhs_infixr0_open hhs_infixr0_close;
infixr 1 hhs_infixr1_open hhs_infixr1_close;
infixr 2 hhs_infixr2_open hhs_infixr2_close;
infixr 3 hhs_infixr3_open hhs_infixr3_close;
infixr 4 hhs_infixr4_open hhs_infixr4_close;
infixr 5 hhs_infixr5_open hhs_infixr5_close;
infixr 6 hhs_infixr6_open hhs_infixr6_close;
infixr 7 hhs_infixr7_open hhs_infixr7_close;
infixr 8 hhs_infixr8_open hhs_infixr8_close;
infixr 9 hhs_infixr9_open hhs_infixr9_close;
open hhsInfix;
open hhsRecord;
val _ = hhsRecord.start_thy "arithmetic"
open HolKernel boolLib Parse Prim_rec simpLib boolSimps metisLib BasicProvers
;
;
local
open OpenTheoryMap
;
val ns = [ "Number" , "Natural" ]
;
in
fun ot0 x y = OpenTheory_const_name { const = { Thy = "arithmetic" , Name = x } , name = ( ns , y ) }
;
fun ot x = ot0 x x
;
fun otunwanted x = OpenTheory_const_name { const = { Thy = "arithmetic" , Name = x } , name = ( [ "Unwanted" ] , "id" ) }
;
end
val _ = new_theory "arithmetic"
;
;
val _ = if ! Globals.interactive then ( ) else Feedback.emit_WARNING := false
;
;
val NOT_SUC = numTheory.NOT_SUC
;
val INV_SUC = numTheory.INV_SUC
;
val INDUCTION = numTheory.INDUCTION
;
;
val num_Axiom = prim_recTheory.num_Axiom
;
;
val INV_SUC_EQ = prim_recTheory.INV_SUC_EQ
;
val LESS_REFL = prim_recTheory.LESS_REFL
;
val SUC_LESS = prim_recTheory.SUC_LESS
;
val NOT_LESS_0 = prim_recTheory.NOT_LESS_0
;
val LESS_MONO = prim_recTheory.LESS_MONO
;
val LESS_SUC_REFL = prim_recTheory.LESS_SUC_REFL
;
val LESS_SUC = prim_recTheory.LESS_SUC
;
val LESS_THM = prim_recTheory.LESS_THM
;
val LESS_SUC_IMP = prim_recTheory.LESS_SUC_IMP
;
val LESS_0 = prim_recTheory.LESS_0
;
val EQ_LESS = prim_recTheory.EQ_LESS
;
val SUC_ID = prim_recTheory.SUC_ID
;
val NOT_LESS_EQ = prim_recTheory.NOT_LESS_EQ
;
val LESS_NOT_EQ = prim_recTheory.LESS_NOT_EQ
;
val LESS_SUC_SUC = prim_recTheory.LESS_SUC_SUC
;
val PRE = prim_recTheory.PRE
;
val RTC_IM_TC = prim_recTheory.RTC_IM_TC
;
val TC_IM_RTC_SUC = prim_recTheory.TC_IM_RTC_SUC
;
val LESS_ALT = prim_recTheory.LESS_ALT
;
;
val ADD = new_recursive_definition { name = "ADD" , rec_axiom = num_Axiom , def = ( Parse.Term [ QUOTE " (*#loc 1 1679*)($+ 0 n = n) /\\             ($+ (SUC m) n = SUC ($+ m n))" ] ) }
;
;
val _ = set_fixity "+" ( Infixl 500 )
;
;
val _ = ot "+"
;
val NUMERAL_DEF = new_definition ( "NUMERAL_DEF" , ( Parse.Term [ QUOTE " (*#loc 1 1846*)NUMERAL (x:num) = x" ] ) )
;
;
val ALT_ZERO = new_definition ( "ALT_ZERO" , ( Parse.Term [ QUOTE " (*#loc 1 1916*)ZERO = 0" ] ) )
;
;
local
open OpenTheoryMap
;
in
val _ = OpenTheory_const_name { const = { Thy = "arithmetic" , Name = "ZERO" } , name = ( [ "Number" , "Natural" ] , "zero" ) }
;
val _ = OpenTheory_const_name { const = { Thy = "num" , Name = "0" } , name = ( [ "Number" , "Natural" ] , "zero" ) }
;
end
val BIT1 = new_definition ( "BIT1" , ( Parse.Term [ QUOTE " (*#loc 1 2296*)BIT1 n = n + (n + SUC 0)" ] ) )
;
;
val BIT2 = new_definition ( "BIT2" , ( Parse.Term [ QUOTE " (*#loc 1 2363*)BIT2 n = n + (n + SUC (SUC 0))" ] ) )
;
;
val _ = new_definition ( GrammarSpecials.nat_elim_term , ( Parse.Term [ QUOTE " (*#loc 1 2460*)" , ANTIQUOTE ( ( mk_var ( GrammarSpecials.nat_elim_term , Type [ QUOTE " (*#loc 1 2505*):num->num" ] ) ) ) , QUOTE " (*#loc 1 2517*) n = n" ] ) )
;
;
val _ = otunwanted "NUMERAL"
;
val _ = ot0 "BIT1" "bit1"
;
val _ = ot0 "BIT2" "bit2"
;
val _ = add_numeral_form ( #"n" , NONE )
;
;
val _ = set_fixity "-" ( Infixl 500 )
;
;
val _ = Unicode.unicode_version { u = UTF8.chr 0x2212 , tmnm = "-" }
;
;
val _ = TeX_notation { hol = UTF8.chr 0x2212 , TeX = ( "\\ensuremath{-}" , 1 ) }
;
val SUB = new_recursive_definition { name = "SUB" , rec_axiom = num_Axiom , def = ( Parse.Term [ QUOTE " (*#loc 1 2921*)(0 - m = 0) /\\             (SUC m - n = if m < n then 0 else SUC(m - n))" ] ) }
;
;
val _ = ot "-"
;
val _ = add_rule { term_name = "numeric_negate" , fixity = Prefix 900 , pp_elements = [ TOK "-" ] , paren_style = OnlyIfNecessary , block_style = ( AroundEachPhrase , ( PP.CONSISTENT , 0 ) ) }
;
;
val _ = add_rule { term_name = GrammarSpecials.num_injection , fixity = Prefix 900 , pp_elements = [ TOK GrammarSpecials.num_injection ] , paren_style = OnlyIfNecessary , block_style = ( AroundEachPhrase , ( PP.CONSISTENT , 0 ) ) }
;
;
val _ = overload_on ( GrammarSpecials.num_injection , mk_const ( GrammarSpecials.nat_elim_term , ( Parse.Type [ QUOTE " (*#loc 1 3679*):num -> num" ] ) ) )
;
val _ = set_fixity "*" ( Infixl 600 )
;
;
val _ = TeX_notation { hol = "*" , TeX = ( "\\HOLTokenProd{}" , 1 ) }
;
val MULT = new_recursive_definition { name = "MULT" , rec_axiom = num_Axiom , def = ( Parse.Term [ QUOTE " (*#loc 1 3892*)(0 * n = 0) /\\              (SUC m * n = (m * n) + n)" ] ) }
;
;
val _ = ot "*"
;
val EXP = new_recursive_definition { name = "EXP" , rec_axiom = num_Axiom , def = ( Parse.Term [ QUOTE " (*#loc 1 4059*)($EXP m 0 = 1) /\\              ($EXP m (SUC n) = m * ($EXP m n))" ] ) }
;
;
val _ = ot0 "EXP" "^"
;
val _ = set_fixity "EXP" ( Infixr 700 )
;
;
val _ = add_infix ( "**" , 700 , HOLgrammars.RIGHT )
;
;
val _ = overload_on ( "**" , Term [ QUOTE " (*#loc 1 4271*)$EXP" ] )
;
;
val _ = TeX_notation { hol = "**" , TeX = ( "\\HOLTokenExp{}" , 2 ) }
;
val _ = add_rule { fixity = Suffix 2100 , term_name = UnicodeChars.sup_2 , block_style = ( AroundEachPhrase , ( PP.CONSISTENT , 0 ) ) , paren_style = OnlyIfNecessary , pp_elements = [ TOK UnicodeChars.sup_2 ] }
;
val _ = overload_on ( UnicodeChars.sup_2 , ( Parse.Term [ QUOTE " (*#loc 1 4656*)\\x. x ** 2" ] ) )
;
val _ = add_rule { fixity = Suffix 2100 , term_name = UnicodeChars.sup_3 , block_style = ( AroundEachPhrase , ( PP.CONSISTENT , 0 ) ) , paren_style = OnlyIfNecessary , pp_elements = [ TOK UnicodeChars.sup_3 ] }
;
val _ = overload_on ( UnicodeChars.sup_3 , ( Parse.Term [ QUOTE " (*#loc 1 4983*)\\x. x ** 3" ] ) )
;
val GREATER_DEF = new_definition ( "GREATER_DEF" , ( Parse.Term [ QUOTE " (*#loc 1 5049*)$> m n = n < m" ] ) )
;
val _ = set_fixity ">" ( Infix ( NONASSOC , 450 ) )
;
val _ = TeX_notation { hol = ">" , TeX = ( "\\HOLTokenGt{}" , 1 ) }
;
val _ = ot ">"
;
val LESS_OR_EQ = new_definition ( "LESS_OR_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 5241*)$<= m n = m < n \\/ (m = n)" ] ) )
;
val _ = set_fixity "<=" ( Infix ( NONASSOC , 450 ) )
;
val _ = Unicode.unicode_version { u = Unicode.UChar.leq , tmnm = "<=" }
;
val _ = TeX_notation { hol = Unicode.UChar.leq , TeX = ( "\\HOLTokenLeq{}" , 1 ) }
;
val _ = TeX_notation { hol = "<=" , TeX = ( "\\HOLTokenLeq{}" , 1 ) }
;
val _ = ot "<="
;
val GREATER_OR_EQ = new_definition ( "GREATER_OR_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 5605*)$>= m n = m > n \\/ (m = n)" ] ) )
;
val _ = set_fixity ">=" ( Infix ( NONASSOC , 450 ) )
;
val _ = Unicode.unicode_version { u = Unicode.UChar.geq , tmnm = ">=" }
;
;
val _ = TeX_notation { hol = ">=" , TeX = ( "\\HOLTokenGeq{}" , 1 ) }
;
val _ = TeX_notation { hol = Unicode.UChar.geq , TeX = ( "\\HOLTokenGeq{}" , 1 ) }
;
val _ = ot ">="
;
val EVEN = new_recursive_definition { name = "EVEN" , rec_axiom = num_Axiom , def = ( Parse.Term [ QUOTE " (*#loc 1 6006*)(EVEN 0 = T) /\\              (EVEN (SUC n) = ~EVEN n)" ] ) }
;
;
val _ = ot0 "EVEN" "even"
;
val ODD = new_recursive_definition { name = "ODD" , rec_axiom = num_Axiom , def = ( Parse.Term [ QUOTE " (*#loc 1 6184*)(ODD 0 = F) /\\              (ODD (SUC n) = ~ODD n)" ] ) }
;
;
val _ = ot0 "ODD" "odd"
;
val [ num_case_def ] = Prim_rec.define_case_constant num_Axiom
;
val _ = overload_on ( "case" , ( Parse.Term [ QUOTE " (*#loc 1 6356*)num_CASE" ] ) )
;
val FUNPOW = new_recursive_definition { name = "FUNPOW" , rec_axiom = num_Axiom , def = ( Parse.Term [ QUOTE " (*#loc 1 6468*)(FUNPOW f 0 x = x) /\\              (FUNPOW f (SUC n) x = FUNPOW f n (f x))" ] ) }
;
;
val NRC = new_recursive_definition { name = "NRC" , rec_axiom = num_Axiom , def = ( Parse.Term [ QUOTE " (*#loc 1 6637*)(NRC R 0 x y = (x = y)) /\\           (NRC R (SUC n) x y = ?z. R x z /\\ NRC R n z y)" ] ) }
;
;
val _ = overload_on ( "RELPOW" , ( Parse.Term [ QUOTE " (*#loc 1 6760*)NRC" ] ) )
;
val _ = overload_on ( "NRC" , ( Parse.Term [ QUOTE " (*#loc 1 6799*)NRC" ] ) )
;
val ONE = store_thm ( "ONE" , ( Parse.Term [ QUOTE " (*#loc 1 6839*)1 = SUC 0" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ NUMERAL_DEF , BIT1 , ALT_ZERO , ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ONE" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", hhsRecord.fetch "BIT1" "( ( DB.fetch \"arithmetic\" \"BIT1\" ) )", ",", 
hhsRecord.fetch "ALT_ZERO" "( ( DB.fetch \"arithmetic\" \"ALT_ZERO\" ) )", 
",", hhsRecord.fetch "ADD" "", "]" ] )
in hhsRecord.try_record_proof "ONE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val TWO = store_thm ( "TWO" , ( Parse.Term [ QUOTE " (*#loc 1 6935*)2 = SUC 1" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ NUMERAL_DEF , BIT2 , ONE , ADD , ALT_ZERO , BIT1 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "TWO" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", hhsRecord.fetch "BIT2" "( ( DB.fetch \"arithmetic\" \"BIT2\" ) )", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "ADD" "", ",", 
hhsRecord.fetch "ALT_ZERO" "( ( DB.fetch \"arithmetic\" \"ALT_ZERO\" ) )", 
",", hhsRecord.fetch "BIT1" "( ( DB.fetch \"arithmetic\" \"BIT1\" ) )", "]" ] )
in hhsRecord.try_record_proof "TWO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NORM_0 = store_thm ( "NORM_0" , ( Parse.Term [ QUOTE " (*#loc 1 7047*)NUMERAL ZERO = 0" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ NUMERAL_DEF , ALT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NORM_0" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", 
hhsRecord.fetch "ALT_ZERO" "( ( DB.fetch \"arithmetic\" \"ALT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "NORM_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
fun INDUCT_TAC g = INDUCT_THEN INDUCTION ASSUME_TAC g
;
;
val EQ_SYM_EQ' = INST_TYPE [ alpha |-> Type [ QUOTE " (*#loc 1 7206*):num" ] ] EQ_SYM_EQ
;
;
val num_case_compute = store_thm ( "num_case_compute" , ( Parse.Term [ QUOTE " (*#loc 1 7286*)!n. num_CASE n (f:'a) g = if n=0 then f else g (PRE n)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN REWRITE_TAC [ num_case_def , NOT_SUC , PRE ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "num_case_compute" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "num_case_def" "", ",", "numTheory.NOT_SUC", ",", 
"prim_recTheory.PRE", "]" ] )
in hhsRecord.try_record_proof "num_case_compute" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUC_NOT = save_thm ( "SUC_NOT" , GEN ( ( Parse.Term [ QUOTE " (*#loc 1 7454*)n:num" ] ) ) ( NOT_EQ_SYM ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 7486*)n:num" ] ) ) NOT_SUC ) ) )
;
;
val ADD_0 = store_thm ( "ADD_0" , ( Parse.Term [ QUOTE " (*#loc 1 7546*)!m. m + 0 = m" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_0" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "ADD" "", "]" ] )
in hhsRecord.try_record_proof "ADD_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_SUC = store_thm ( "ADD_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 7648*)!m n. SUC(m + n) = (m + SUC n)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_SUC" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "ADD" "", "]" ] )
in hhsRecord.try_record_proof "ADD_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_CLAUSES = store_thm ( "ADD_CLAUSES" , ( Parse.Term [ QUOTE " (*#loc 1 7775*)(0 + m = m)              /\\      (m + 0 = m)              /\\      (SUC m + n = SUC(m + n)) /\\      (m + SUC n = SUC(m + n))" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ ADD , ADD_0 , ADD_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_CLAUSES" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", hhsRecord.fetch "ADD" "", ",", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ",", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", "]" ] )
in hhsRecord.try_record_proof "ADD_CLAUSES" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_SYM = store_thm ( "ADD_SYM" , ( Parse.Term [ QUOTE " (*#loc 1 7982*)!m n. m + n = n + m" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_0 , ADD , ADD_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_SYM" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ",", 
hhsRecord.fetch "ADD" "", ",", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", "]" ] )
in hhsRecord.try_record_proof "ADD_SYM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_COMM = save_thm ( "ADD_COMM" , ADD_SYM )
;
;
val ADD_ASSOC = store_thm ( "ADD_ASSOC" , ( Parse.Term [ QUOTE " (*#loc 1 8156*)!m n p. m + (n + p) = (m + n) + p" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_ASSOC" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ADD_ASSOC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val num_CASES = store_thm ( "num_CASES" , ( Parse.Term [ QUOTE " (*#loc 1 8290*)!m. (m = 0) \\/ ?n. m = SUC n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN REWRITE_TAC [ NOT_SUC ] THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 8389*)(m:num)" ] ) ) THEN REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "num_CASES" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"numTheory.NOT_SUC", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 8389*)(m:num)\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"]" ] )
in hhsRecord.try_record_proof "num_CASES" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_ZERO_LT_ZERO = store_thm ( "NOT_ZERO_LT_ZERO" , ( Parse.Term [ QUOTE " (*#loc 1 8485*)!n. ~(n = 0) = 0 < n" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN STRUCT_CASES_TAC ( Q.SPEC [ QUOTE " (*#loc 1 8552*)n" ] num_CASES ) THEN REWRITE_TAC [ NOT_LESS_0 , LESS_0 , NOT_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_ZERO_LT_ZERO" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.STRUCT_CASES_TAC", "(", "Q.SPEC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 8552*)n\"", "]", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "prim_recTheory.NOT_LESS_0", ",", "prim_recTheory.LESS_0", ",", 
"numTheory.NOT_SUC", "]" ] )
in hhsRecord.try_record_proof "NOT_ZERO_LT_ZERO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_LT_ZERO_EQ_ZERO = store_thm ( "NOT_LT_ZERO_EQ_ZERO[simp]" , ( Parse.Term [ QUOTE " (*#loc 1 8691*)!n. ~(0 < n) <=> (n = 0)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ GSYM NOT_ZERO_LT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_LT_ZERO_EQ_ZERO" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "NOT_LT_ZERO_EQ_ZERO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_OR_EQ_ALT = store_thm ( "LESS_OR_EQ_ALT" , ( Parse.Term [ QUOTE " (*#loc 1 8815*)$<= = RTC (\\x y. y = SUC x)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ FUN_EQ_THM , LESS_OR_EQ , relationTheory.RTC_CASES_TC , LESS_ALT ] THEN REPEAT ( STRIP_TAC ORELSE EQ_TAC ) THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_OR_EQ_ALT" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "boolLib.FUN_EQ_THM", ",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", "relationTheory.RTC_CASES_TC", ",", "prim_recTheory.LESS_ALT", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", "(", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.ORELSE hhs_infixl0_close", 
"boolLib.EQ_TAC", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]" ] )
in hhsRecord.try_record_proof "LESS_OR_EQ_ALT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_ADD = store_thm ( "LESS_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 9045*)!m n. n<m ==> ?p. p+n = m" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC [ NOT_LESS_0 , LESS_THM ] THEN REPEAT STRIP_TAC THENL [ EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 9193*)SUC 0" ] ) ) THEN ASM_REWRITE_TAC [ ADD ] , RES_THEN ( STRIP_THM_THEN ( SUBST1_TAC o SYM ) ) THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 9303*)SUC p" ] ) ) THEN REWRITE_TAC [ ADD ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_ADD" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.NOT_LESS_0", ",", "prim_recTheory.LESS_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 9193*)SUC 0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "ADD" "", "]", ",", "boolLib.RES_THEN", "(", 
"boolLib.STRIP_THM_THEN", "(", "boolLib.SUBST1_TAC", "o", "HolKernel.SYM", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 9303*)SUC p\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD" "", "]", "]" ] )
in hhsRecord.try_record_proof "LESS_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val transitive_LESS = store_thm ( "transitive_LESS[simp]" , ( Parse.Term [ QUOTE " (*#loc 1 9404*)transitive $<" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ relationTheory.TC_TRANSITIVE , LESS_ALT ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "transitive_LESS" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "relationTheory.TC_TRANSITIVE", ",", 
"prim_recTheory.LESS_ALT", "]" ] )
in hhsRecord.try_record_proof "transitive_LESS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_TRANS = store_thm ( "LESS_TRANS" , ( Parse.Term [ QUOTE " (*#loc 1 9527*)!m n p. (m < n) /\\ (n < p) ==> (m < p)" ] ) ,
let
val tactictoe_tac1 = MATCH_ACCEPT_TAC ( REWRITE_RULE [ relationTheory.transitive_def ] transitive_LESS )
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_TRANS" 
 ( String.concatWith " " 
 [ "boolLib.MATCH_ACCEPT_TAC", "(", "boolLib.REWRITE_RULE", "[", 
"relationTheory.transitive_def", "]", 
hhsRecord.fetch "transitive_LESS" "( ( DB.fetch \"arithmetic\" \"transitive_LESS\" ) )", 
")" ] )
in hhsRecord.try_record_proof "LESS_TRANS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_ANTISYM = store_thm ( "LESS_ANTISYM" , ( Parse.Term [ QUOTE " (*#loc 1 9711*)!m n. ~((m < n) /\\ (n < m))" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_TRANS THEN IMP_RES_TAC LESS_REFL
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_ANTISYM" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
"prim_recTheory.LESS_REFL" ] )
in hhsRecord.try_record_proof "LESS_ANTISYM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_MONO_REV = save_thm ( "LESS_MONO_REV" , prim_recTheory.LESS_MONO_REV )
;
;
val LESS_MONO_EQ = save_thm ( "LESS_MONO_EQ" , prim_recTheory.LESS_MONO_EQ )
;
;
val LESS_EQ_MONO = store_thm ( "LESS_EQ_MONO" , ( Parse.Term [ QUOTE " (*#loc 1 10038*)!n m. (SUC n <= SUC m) = (n <= m)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_OR_EQ , LESS_MONO_EQ , INV_SUC_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_MONO" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", "]" ] )
in hhsRecord.try_record_proof "LESS_EQ_MONO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_LESS_SUC = store_thm ( "LESS_LESS_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 10186*)!m n. ~((m < n) /\\ (n < SUC m))" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ LESS_MONO_EQ , LESS_EQ_MONO , LESS_0 , NOT_LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_LESS_SUC" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", "prim_recTheory.LESS_0", ",", "prim_recTheory.NOT_LESS_0", "]" ] )
in hhsRecord.try_record_proof "LESS_LESS_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val transitive_measure = Q.store_thm ( "transitive_measure" , [ QUOTE " (*#loc 1 10391*)!f. transitive (measure f)" ] ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ relationTheory.transitive_def , prim_recTheory.measure_thm ] THEN MATCH_MP_TAC LESS_TRANS THEN SRW_TAC [ SatisfySimps.SATISFY_ss ] [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "transitive_measure" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", "relationTheory.transitive_def", ",", 
"prim_recTheory.measure_thm", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"SatisfySimps.SATISFY_ss", "]", "[", "]" ] )
in hhsRecord.try_record_proof "transitive_measure" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ = store_thm ( "LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 10613*)!m n. (m < n) = (SUC m <= n)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_OR_EQ_ALT , LESS_ALT , RTC_IM_TC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ_ALT" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ_ALT\" ) )", 
",", "prim_recTheory.LESS_ALT", ",", "prim_recTheory.RTC_IM_TC", "]" ] )
in hhsRecord.try_record_proof "LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_OR = store_thm ( "LESS_OR" , ( Parse.Term [ QUOTE " (*#loc 1 10742*)!m n. m < n ==> SUC m <= n" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_OR" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", "]" ] )
in hhsRecord.try_record_proof "LESS_OR" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_SUC_EQ = LESS_OR
;
;
val OR_LESS = store_thm ( "OR_LESS" , ( Parse.Term [ QUOTE " (*#loc 1 10869*)!m n. (SUC m <= n) ==> (m < n)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "OR_LESS" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", "]" ] )
in hhsRecord.try_record_proof "OR_LESS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_IFF_LESS_SUC = store_thm ( "LESS_EQ_IFF_LESS_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 10997*)!n m. (n <= m) = (n < (SUC m))" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_OR_EQ_ALT , LESS_ALT , TC_IM_RTC_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_IFF_LESS_SUC" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ_ALT" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ_ALT\" ) )", 
",", "prim_recTheory.LESS_ALT", ",", "prim_recTheory.TC_IM_RTC_SUC", "]" ] )
in hhsRecord.try_record_proof "LESS_EQ_IFF_LESS_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_IMP_LESS_SUC = store_thm ( "LESS_EQ_IMP_LESS_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 11156*)!n m. (n <= m) ==> (n < (SUC m))" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_EQ_IFF_LESS_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_IMP_LESS_SUC" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_EQ_IFF_LESS_SUC" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_IFF_LESS_SUC\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_EQ_IMP_LESS_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ZERO_LESS_EQ = store_thm ( "ZERO_LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 11286*)!n. 0 <= n" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_0 , LESS_EQ_IFF_LESS_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ZERO_LESS_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "LESS_EQ_IFF_LESS_SUC" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_IFF_LESS_SUC\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ZERO_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_SUC_EQ_COR = store_thm ( "LESS_SUC_EQ_COR" , ( Parse.Term [ QUOTE " (*#loc 1 11406*)!m n. ((m < n) /\\ (~(SUC m = n))) ==> (SUC m < n)" ] ) ,
let
val tactictoe_tac1 = CONV_TAC ( ONCE_DEPTH_CONV SYM_CONV ) THEN INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ LESS_MONO_EQ , INV_SUC_EQ , LESS_0 , NOT_LESS_0 , NOT_ZERO_LT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_SUC_EQ_COR" 
 ( String.concatWith " " 
 [ "boolLib.CONV_TAC", "(", "boolLib.ONCE_DEPTH_CONV", "boolLib.SYM_CONV", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", ",", "prim_recTheory.LESS_0", ",", 
"prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_SUC_EQ_COR" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_NOT_SUC = store_thm ( "LESS_NOT_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 11687*)!m n. (m < n) /\\ ~(n = SUC m) ==> SUC m < n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ LESS_MONO_EQ , INV_SUC_EQ , LESS_0 , NOT_LESS_0 , NOT_ZERO_LT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_NOT_SUC" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", ",", "prim_recTheory.LESS_0", ",", 
"prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_NOT_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_0_CASES = store_thm ( "LESS_0_CASES" , ( Parse.Term [ QUOTE " (*#loc 1 11918*)!m. (0 = m) \\/ 0<m" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN REWRITE_TAC [ LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_0_CASES" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "LESS_0_CASES" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_CASES_IMP = store_thm ( "LESS_CASES_IMP" , ( Parse.Term [ QUOTE " (*#loc 1 12042*)!m n. ~(m < n) /\\  ~(m = n) ==> (n < m)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ LESS_MONO_EQ , INV_SUC_EQ , LESS_0 , NOT_LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_CASES_IMP" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", ",", "prim_recTheory.LESS_0", ",", 
"prim_recTheory.NOT_LESS_0", "]" ] )
in hhsRecord.try_record_proof "LESS_CASES_IMP" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_CASES = store_thm ( "LESS_CASES" , ( Parse.Term [ QUOTE " (*#loc 1 12240*)!m n. (m < n) \\/ (n <= m)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ LESS_MONO_EQ , LESS_EQ_MONO , ZERO_LESS_EQ , LESS_0 , NOT_LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_CASES" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", "prim_recTheory.LESS_0", ",", "prim_recTheory.NOT_LESS_0", "]" ] )
in hhsRecord.try_record_proof "LESS_CASES" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_INV_0 = store_thm ( "ADD_INV_0" , ( Parse.Term [ QUOTE " (*#loc 1 12445*)!m n. (m + n = m) ==> (n = 0)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , INV_SUC_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_INV_0" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", "]" ] )
in hhsRecord.try_record_proof "ADD_INV_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_ADD = store_thm ( "LESS_EQ_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 12591*)!m n. m <= m + n" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN REWRITE_TAC [ LESS_OR_EQ ] THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES ] THEN MP_TAC ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 12741*)(m < (m + n)) \\/ (m = (m + n))" ] ) ) ) THEN STRIP_TAC THENL [ IMP_RES_TAC LESS_SUC THEN ASM_REWRITE_TAC [ ] , REWRITE_TAC [ SYM ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 12894*)m = m + n" ] ) ) ) , LESS_SUC_REFL ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_ADD" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MP_TAC", "(", 
"HolKernel.ASSUME", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 12741*)(m < (m + n)) \\\\/ (m = (m + n))\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.IMP_RES_TAC", 
"prim_recTheory.LESS_SUC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", ",", "boolLib.REWRITE_TAC", "[", "HolKernel.SYM", 
"(", "HolKernel.ASSUME", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 12894*)m = m + n\"", "]", ")", ")", ")", ",", 
"prim_recTheory.LESS_SUC_REFL", "]", "]" ] )
in hhsRecord.try_record_proof "LESS_EQ_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_ADD_EXISTS = store_thm ( "LESS_EQ_ADD_EXISTS" , ( Parse.Term [ QUOTE " (*#loc 1 12991*)!m n. n<=m ==> ?p. p+n = m" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ LESS_OR_EQ , DISJ_IMP_THM , FORALL_AND_THM , LESS_ADD ] THEN GEN_TAC THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 13134*)0" ] ) ) THEN REWRITE_TAC [ ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_ADD_EXISTS" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", "boolLib.DISJ_IMP_THM", ",", "boolLib.FORALL_AND_THM", ",", 
hhsRecord.fetch "LESS_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_ADD\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 13134*)0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD" "", "]" ] )
in hhsRecord.try_record_proof "LESS_EQ_ADD_EXISTS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_STRONG_ADD = store_thm ( "LESS_STRONG_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 13225*)!m n. n < m ==> ?p. (SUC p)+n = m" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_OR THEN IMP_RES_TAC LESS_EQ_ADD_EXISTS THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 13373*)p:num" ] ) ) THEN FULL_SIMP_TAC bool_ss [ ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_STRONG_ADD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_OR" "( ( DB.fetch \"arithmetic\" \"LESS_OR\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_EQ_ADD_EXISTS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD_EXISTS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 13373*)p:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_STRONG_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_SUC_REFL = store_thm ( "LESS_EQ_SUC_REFL" , ( Parse.Term [ QUOTE " (*#loc 1 13489*)!m. m <= SUC m" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN REWRITE_TAC [ LESS_OR_EQ , LESS_SUC_REFL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_SUC_REFL" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", "prim_recTheory.LESS_SUC_REFL", "]" ] )
in hhsRecord.try_record_proof "LESS_EQ_SUC_REFL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_ADD_NONZERO = store_thm ( "LESS_ADD_NONZERO" , ( Parse.Term [ QUOTE " (*#loc 1 13628*)!m n. ~(n = 0) ==> m < m + n" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ NOT_SUC , ADD_CLAUSES ] THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 13761*)n = 0" ] ) ) THEN ASSUME_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 13800*)m + n" ] ) ) LESS_SUC_REFL ) THEN RES_TAC THEN IMP_RES_TAC LESS_TRANS THEN ASM_REWRITE_TAC [ ADD_CLAUSES , LESS_SUC_REFL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_ADD_NONZERO" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"numTheory.NOT_SUC", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_CASES_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 13761*)n = 0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASSUME_TAC", "(", 
"HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 13800*)m + n\"", "]", ")", ")", "prim_recTheory.LESS_SUC_REFL", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.RES_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_SUC_REFL", "]" ] )
in hhsRecord.try_record_proof "LESS_ADD_NONZERO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_SUC_LESS_EQ_0 = store_thm ( "NOT_SUC_LESS_EQ_0" , ( Parse.Term [ QUOTE " (*#loc 1 13990*)!n. ~(SUC n <= 0)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ NOT_LESS_0 , GSYM LESS_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_SUC_LESS_EQ_0" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "prim_recTheory.NOT_LESS_0", ",", "boolLib.GSYM", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", "]" ] )
in hhsRecord.try_record_proof "NOT_SUC_LESS_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_LESS = store_thm ( "NOT_LESS" , ( Parse.Term [ QUOTE " (*#loc 1 14100*)!m n. ~(m < n) = (n <= m)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ LESS_MONO_EQ , LESS_EQ_MONO , ZERO_LESS_EQ , LESS_0 , NOT_LESS_0 , NOT_SUC_LESS_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_LESS" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", "prim_recTheory.LESS_0", ",", "prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "NOT_LESS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_LESS_EQUAL = store_thm ( "NOT_LESS_EQUAL" , ( Parse.Term [ QUOTE " (*#loc 1 14333*)!m n. ~(m <= n) = n < m" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ GSYM NOT_LESS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_LESS_EQUAL" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "NOT_LESS_EQUAL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_ANTISYM = store_thm ( "LESS_EQ_ANTISYM" , ( Parse.Term [ QUOTE " (*#loc 1 14450*)!m n. ~(m < n /\\ n <= m)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ LESS_MONO_EQ , LESS_EQ_MONO , ZERO_LESS_EQ , LESS_0 , NOT_LESS_0 , NOT_SUC_LESS_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_ANTISYM" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", "prim_recTheory.LESS_0", ",", "prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_EQ_ANTISYM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_0 = store_thm ( "LESS_EQ_0" , ( Parse.Term [ QUOTE " (*#loc 1 14672*)!n. (n <= 0) = (n = 0)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_OR_EQ , NOT_LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_0" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", "prim_recTheory.NOT_LESS_0", "]" ] )
in hhsRecord.try_record_proof "LESS_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = print "Now proving properties of subtraction\n"
;
val SUB_0 = store_thm ( "SUB_0" , ( Parse.Term [ QUOTE " (*#loc 1 14835*)!m. (0 - m = 0) /\\ (m - 0 = m)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ SUB , NOT_LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_0" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB" "", ",", "prim_recTheory.NOT_LESS_0", "]" ] )
in hhsRecord.try_record_proof "SUB_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_MONO_EQ = store_thm ( "SUB_MONO_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 14980*)!n m. (SUC n) - (SUC m) = (n - m)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THENL [ REWRITE_TAC [ SUB , LESS_0 ] , ONCE_REWRITE_TAC [ SUB ] THEN PURE_ONCE_REWRITE_TAC [ LESS_MONO_EQ ] THEN ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_MONO_EQ" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "SUB" "", ",", "prim_recTheory.LESS_0", "]", ",", 
"boolLib.ONCE_REWRITE_TAC", "[", hhsRecord.fetch "SUB" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", "]" ] )
in hhsRecord.try_record_proof "SUB_MONO_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_EQ_0 = store_thm ( "SUB_EQ_0" , ( Parse.Term [ QUOTE " (*#loc 1 15212*)!m n. (m - n = 0) = (m <= n)" ] ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ SUB_0 , LESS_EQ_MONO , SUB_MONO_EQ , LESS_EQ_0 , ZERO_LESS_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_EQ_0" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD1 = store_thm ( "ADD1" , ( Parse.Term [ QUOTE " (*#loc 1 15386*)!m. SUC m = m + 1" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THENL [ REWRITE_TAC [ ADD_CLAUSES , ONE ] , ASM_REWRITE_TAC [ ] THEN REWRITE_TAC [ ONE , ADD_CLAUSES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD1" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", ",", 
"boolLib.ASM_REWRITE_TAC", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "ADD1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUC_SUB1 = store_thm ( "SUC_SUB1" , ( Parse.Term [ QUOTE " (*#loc 1 15578*)!m. SUC m - 1 = m" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THENL [ REWRITE_TAC [ SUB , LESS_0 , ONE ] , PURE_ONCE_REWRITE_TAC [ SUB ] THEN ASM_REWRITE_TAC [ NOT_LESS_0 , LESS_MONO_EQ , ONE ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUC_SUB1" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "SUB" "", ",", "prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", ",", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", hhsRecord.fetch "SUB" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", "]" ] )
in hhsRecord.try_record_proof "SUC_SUB1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val PRE_SUB1 = store_thm ( "PRE_SUB1" , ( Parse.Term [ QUOTE " (*#loc 1 15799*)!m. (PRE m = (m - 1))" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN STRUCT_CASES_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 15871*)m:num" ] ) ) num_CASES ) THEN ASM_REWRITE_TAC [ PRE , CONJUNCT1 SUB , SUC_SUB1 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "PRE_SUB1" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.STRUCT_CASES_TAC", "(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 15871*)m:num\"", "]", ")", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "prim_recTheory.PRE", ",", "HolKernel.CONJUNCT1", 
hhsRecord.fetch "SUB" "", ",", 
hhsRecord.fetch "SUC_SUB1" "( ( DB.fetch \"arithmetic\" \"SUC_SUB1\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "PRE_SUB1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_0 = store_thm ( "MULT_0" , ( Parse.Term [ QUOTE " (*#loc 1 15989*)!m. m * 0 = 0" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ MULT , ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_0" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "MULT" "", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MULT_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_SUC = store_thm ( "MULT_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 16110*)!m n. m * (SUC n) = m + m*n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ MULT , ADD_CLAUSES , ADD_ASSOC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_SUC" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "MULT" "", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MULT_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_LEFT_1 = store_thm ( "MULT_LEFT_1" , ( Parse.Term [ QUOTE " (*#loc 1 16261*)!m. 1 * m = m" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN REWRITE_TAC [ ONE , MULT , ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_LEFT_1" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "MULT" "", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MULT_LEFT_1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_RIGHT_1 = store_thm ( "MULT_RIGHT_1" , ( Parse.Term [ QUOTE " (*#loc 1 16384*)!m. m * 1 = m" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ ONE ] THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ MULT , ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_RIGHT_1" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "MULT" "", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MULT_RIGHT_1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_CLAUSES = store_thm ( "MULT_CLAUSES" , ( Parse.Term [ QUOTE " (*#loc 1 16536*)!m n. (0 * m = 0)             /\\            (m * 0 = 0)             /\\            (1 * m = m)             /\\            (m * 1 = m)             /\\            (SUC m * n = m * n + n) /\\            (m * SUC n = m + m * n)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ MULT , MULT_0 , MULT_LEFT_1 , MULT_RIGHT_1 , MULT_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_CLAUSES" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", hhsRecord.fetch "MULT" "", ",", 
hhsRecord.fetch "MULT_0" "( ( DB.fetch \"arithmetic\" \"MULT_0\" ) )", ",", 
hhsRecord.fetch "MULT_LEFT_1" "( ( DB.fetch \"arithmetic\" \"MULT_LEFT_1\" ) )", 
",", 
hhsRecord.fetch "MULT_RIGHT_1" "( ( DB.fetch \"arithmetic\" \"MULT_RIGHT_1\" ) )", 
",", 
hhsRecord.fetch "MULT_SUC" "( ( DB.fetch \"arithmetic\" \"MULT_SUC\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MULT_CLAUSES" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_SYM = store_thm ( "MULT_SYM" , ( Parse.Term [ QUOTE " (*#loc 1 16868*)!m n. m * n = n * m" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC [ MULT_CLAUSES , SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 16967*)m*n" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 16977*)n:num" ] ) ] ADD_SYM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_SYM" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "boolLib.SPECL", "[", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 16967*)m*n\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 16977*)n:num\"", "]", ")", "]", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]" ] )
in hhsRecord.try_record_proof "MULT_SYM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_COMM = save_thm ( "MULT_COMM" , MULT_SYM )
;
;
val RIGHT_ADD_DISTRIB = store_thm ( "RIGHT_ADD_DISTRIB" , ( Parse.Term [ QUOTE " (*#loc 1 17109*)!m n p. (m + n) * p = (m * p) + (n * p)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , ADD_ASSOC ] THEN REWRITE_TAC [ SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 17292*)m+(m*p)" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 17306*)n:num" ] ) ] ADD_SYM , ADD_ASSOC ] THEN SUBST_TAC [ SPEC_ALL ADD_SYM ] THEN REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "RIGHT_ADD_DISTRIB" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "boolLib.SPECL", "[", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 17292*)m+(m*p)\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 17306*)n:num\"", "]", ")", "]", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", ",", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUBST_TAC", "[", 
"boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"]" ] )
in hhsRecord.try_record_proof "RIGHT_ADD_DISTRIB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LEFT_ADD_DISTRIB = store_thm ( "LEFT_ADD_DISTRIB" , ( Parse.Term [ QUOTE " (*#loc 1 17457*)!m n p. p * (m + n) = (p * m) + (p * n)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , SYM ( SPEC_ALL ADD_ASSOC ) ] THEN REWRITE_TAC [ SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 17654*)m:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 17666*)(p*n)+n" ] ) ] ADD_SYM , SYM ( SPEC_ALL ADD_ASSOC ) ] THEN SUBST_TAC [ SPEC_ALL ADD_SYM ] THEN REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LEFT_ADD_DISTRIB" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "boolLib.SPECL", "[", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 17654*)m:num\"", "]", ")", ",", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 17666*)(p*n)+n\"", "]", ")", "]", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", ",", 
"HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUBST_TAC", 
"[", "boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"]" ] )
in hhsRecord.try_record_proof "LEFT_ADD_DISTRIB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_ASSOC = store_thm ( "MULT_ASSOC" , ( Parse.Term [ QUOTE " (*#loc 1 17842*)!m n p. m * (n * p) = (m * n) * p" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ MULT_CLAUSES , RIGHT_ADD_DISTRIB ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_ASSOC" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MULT_ASSOC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_ADD = store_thm ( "SUB_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 17995*)!m n. (n <= m) ==> ((m - n) + n = m)" ] ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_0 , SUB_MONO_EQ , LESS_EQ_MONO , INV_SUC_EQ , LESS_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_ADD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", ",", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val PRE_SUB = store_thm ( "PRE_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 18202*)!m n. PRE(m - n) = (PRE m) - n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC [ SUB , PRE ] THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 18329*)m < n" ] ) ) THEN ASM_REWRITE_TAC [ PRE , LESS_OR_EQ , SUBS [ SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 18416*)m-n" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 18426*)0" ] ) ] EQ_SYM_EQ' ] ( SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 18469*)m:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 18481*)n:num" ] ) ] SUB_EQ_0 ) ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "PRE_SUB" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB" "", ",", "prim_recTheory.PRE", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_CASES_TAC", "(", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 18329*)m < n\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "prim_recTheory.PRE", ",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", "boolLib.SUBS", "[", "boolLib.SPECL", "[", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 18416*)m-n\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 18426*)0\"", "]", ")", "]", 
hhsRecord.fetch "EQ_SYM_EQ'" "( HolKernel.INST_TYPE [ HolKernel.alpha hhs_infixl0_open HolKernel.|-> hhs_infixl0_close Parse.Type [ HolKernel.QUOTE \" (*#loc 1 7206*):num\" ] ] boolLib.EQ_SYM_EQ )", 
"]", "(", "boolLib.SPECL", "[", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 18469*)m:num\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 18481*)n:num\"", "]", ")", "]", 
hhsRecord.fetch "SUB_EQ_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQ_0\" ) )", 
")", "]" ] )
in hhsRecord.try_record_proof "PRE_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
val ADD_EQ_0 = store_thm ( "ADD_EQ_0" , ( Parse.Term [ QUOTE " (*#loc 1 18547*)!m n. (m + n = 0) = (m = 0) /\\ (n = 0)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , NOT_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_EQ_0" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "numTheory.NOT_SUC", "]" ] )
in hhsRecord.try_record_proof "ADD_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_EQ_1 = store_thm ( "ADD_EQ_1" , ( Parse.Term [ QUOTE " (*#loc 1 18712*)!m n. (m + n = 1) = (m = 1) /\\ (n = 0) \\/ (m = 0) /\\ (n = 1)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THENL [ REWRITE_TAC [ ADD_CLAUSES , ONE , GSYM NOT_SUC ] , REWRITE_TAC [ NOT_SUC , ADD_CLAUSES , ONE , INV_SUC_EQ , ADD_EQ_0 ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_EQ_1" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"boolLib.GSYM", "numTheory.NOT_SUC", "]", ",", "boolLib.REWRITE_TAC", "[", 
"numTheory.NOT_SUC", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"prim_recTheory.INV_SUC_EQ", ",", 
hhsRecord.fetch "ADD_EQ_0" "( ( DB.fetch \"arithmetic\" \"ADD_EQ_0\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "ADD_EQ_1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_INV_0_EQ = store_thm ( "ADD_INV_0_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 18974*)!m n. (m + n = m) = (n = 0)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [ ADD_INV_0 ] THEN STRIP_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_INV_0_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_INV_0" "( ( DB.fetch \"arithmetic\" \"ADD_INV_0\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ADD_INV_0_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val PRE_SUC_EQ = store_thm ( "PRE_SUC_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 19179*)!m n. 0<n ==> ((m = PRE n) = (SUC m = n))" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ PRE , LESS_REFL , INV_SUC_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "PRE_SUC_EQ" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.PRE", ",", "prim_recTheory.LESS_REFL", ",", 
"prim_recTheory.INV_SUC_EQ", "]" ] )
in hhsRecord.try_record_proof "PRE_SUC_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val INV_PRE_EQ = store_thm ( "INV_PRE_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 19356*)!m n. 0<m /\\ 0<n ==> ((PRE m = (PRE n)) = (m = n))" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ PRE , LESS_REFL , INV_SUC_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "INV_PRE_EQ" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.PRE", ",", "prim_recTheory.LESS_REFL", ",", 
"prim_recTheory.INV_SUC_EQ", "]" ] )
in hhsRecord.try_record_proof "INV_PRE_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_SUC_NOT = store_thm ( "LESS_SUC_NOT" , ( Parse.Term [ QUOTE " (*#loc 1 19546*)!m n. (m < n)  ==> ~(n < SUC m)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN ASM_REWRITE_TAC [ NOT_LESS ] THEN REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_OR THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_SUC_NOT" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_OR" "( ( DB.fetch \"arithmetic\" \"LESS_OR\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "LESS_SUC_NOT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_EQ_SUB = store_thm ( "ADD_EQ_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 19767*)!m n p. (n <= p) ==> (((m + n) = p) = (m = (p - n)))" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_MONO_EQ , INV_SUC_EQ , LESS_EQ_MONO , SUB_0 , NOT_SUC_LESS_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_EQ_SUB" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", ",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ADD_EQ_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_MONO_ADD = store_thm ( "LESS_MONO_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 20020*)!m n p. (m < n) ==> (m + p) < (n + p)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , LESS_MONO_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_MONO_ADD" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.RES_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_MONO_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_MONO_ADD_INV = store_thm ( "LESS_MONO_ADD_INV" , ( Parse.Term [ QUOTE " (*#loc 1 20261*)!m n p. (m + p) < (n + p) ==> (m < n)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , LESS_MONO_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_MONO_ADD_INV" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_MONO_ADD_INV" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_MONO_ADD_EQ = store_thm ( "LESS_MONO_ADD_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 20464*)!m n p. ((m + p) < (n + p)) = (m < n)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [ LESS_MONO_ADD , LESS_MONO_ADD_INV ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_MONO_ADD_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_MONO_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD\" ) )", 
",", 
hhsRecord.fetch "LESS_MONO_ADD_INV" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD_INV\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_MONO_ADD_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LT_ADD_RCANCEL = save_thm ( "LT_ADD_RCANCEL" , LESS_MONO_ADD_EQ )
;
val LT_ADD_LCANCEL = save_thm ( "LT_ADD_LCANCEL" , ONCE_REWRITE_RULE [ ADD_COMM ] LT_ADD_RCANCEL )
;
val EQ_MONO_ADD_EQ = store_thm ( "EQ_MONO_ADD_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 20844*)!m n p. ((m + p) = (n + p)) = (m = n)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , INV_SUC_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EQ_MONO_ADD_EQ" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", "]" ] )
in hhsRecord.try_record_proof "EQ_MONO_ADD_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = print "Proving properties of <=\n"
;
val LESS_EQ_MONO_ADD_EQ = store_thm ( "LESS_EQ_MONO_ADD_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 21094*)!m n p. ((m + p) <= (n + p)) = (m <= n)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REWRITE_TAC [ LESS_OR_EQ ] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [ LESS_MONO_ADD_EQ , EQ_MONO_ADD_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_MONO_ADD_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD_EQ\" ) )", 
",", 
hhsRecord.fetch "EQ_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"EQ_MONO_ADD_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_EQ_MONO_ADD_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_TRANS = store_thm ( "LESS_EQ_TRANS" , ( Parse.Term [ QUOTE " (*#loc 1 21325*)!m n p. (m <= n) /\\ (n <= p) ==> (m <= p)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_OR_EQ_ALT , REWRITE_RULE [ relationTheory.transitive_def ] relationTheory.transitive_RTC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_TRANS" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ_ALT" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ_ALT\" ) )", 
",", "boolLib.REWRITE_RULE", "[", "relationTheory.transitive_def", "]", 
"relationTheory.transitive_RTC", "]" ] )
in hhsRecord.try_record_proof "LESS_EQ_TRANS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_LESS_TRANS = store_thm ( "LESS_EQ_LESS_TRANS" , ( Parse.Term [ QUOTE " (*#loc 1 21549*)!m n p. m <= n /\\ n < p ==> m < p" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REWRITE_TAC [ LESS_OR_EQ ] THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 21658*)m:num = n" ] ) ) THEN ASM_REWRITE_TAC [ LESS_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_LESS_TRANS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_CASES_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 21658*)m:num = n\"", "]", 
")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_EQ_LESS_TRANS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_LESS_EQ_TRANS = store_thm ( "LESS_LESS_EQ_TRANS" , ( Parse.Term [ QUOTE " (*#loc 1 21770*)!m n p. m < n /\\ n <= p ==> m < p" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REWRITE_TAC [ LESS_OR_EQ ] THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 21879*)n:num = p" ] ) ) THEN ASM_REWRITE_TAC [ LESS_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_LESS_EQ_TRANS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_CASES_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 21879*)n:num = p\"", "]", 
")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_LESS_EQ_TRANS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_LESS_EQ_MONO = store_thm ( "LESS_EQ_LESS_EQ_MONO" , ( Parse.Term [ QUOTE " (*#loc 1 21997*)!m n p q. (m <= p) /\\ (n <= q) ==> ((m + n) <= (p + q))" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN
let
val th1 = snd ( EQ_IMP_RULE ( SPEC_ALL LESS_EQ_MONO_ADD_EQ ) )
val th2 = PURE_ONCE_REWRITE_RULE [ ADD_SYM ] th1
in IMP_RES_THEN ( ASSUME_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 22247*)n:num" ] ) ) ) th1 THEN IMP_RES_THEN ( ASSUME_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 22306*)p:num" ] ) ) ) th2 THEN IMP_RES_TAC LESS_EQ_TRANS
end
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_LESS_EQ_MONO" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", "boolLib.IMP_RES_THEN", 
"(", "boolLib.ASSUME_TAC", "o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 22247*)n:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "th1" "( HolKernel.snd ( HolKernel.EQ_IMP_RULE ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO_ADD_EQ\" ) ) ) ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.ASSUME_TAC", "o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 22306*)p:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "th2" "( boolLib.PURE_ONCE_REWRITE_RULE [ ( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) ) ] ( HolKernel.snd ( HolKernel.EQ_IMP_RULE ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO_ADD_EQ\" ) ) ) ) ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
")" ] )
in hhsRecord.try_record_proof "LESS_EQ_LESS_EQ_MONO" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_REFL = store_thm ( "LESS_EQ_REFL" , ( Parse.Term [ QUOTE " (*#loc 1 22416*)!m. m <= m" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN REWRITE_TAC [ LESS_OR_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_REFL" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_EQ_REFL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_IMP_LESS_OR_EQ = store_thm ( "LESS_IMP_LESS_OR_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 22543*)!m n. (m < n) ==> (m <= n)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [ LESS_OR_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_IMP_LESS_OR_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_IMP_LESS_OR_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_MONO_MULT = store_thm ( "LESS_MONO_MULT" , ( Parse.Term [ QUOTE " (*#loc 1 22689*)!m n p. (m <= n) ==> ((m * p) <= (n * p))" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , MULT_CLAUSES , LESS_EQ_MONO_ADD_EQ , LESS_EQ_REFL ] THEN RES_TAC THEN IMP_RES_TAC ( SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 22944*)m:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 22956*)m*p" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 22966*)n:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 22978*)n*p" ] ) ] LESS_EQ_LESS_EQ_MONO ) THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_MONO_MULT" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO_ADD_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.RES_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", "(", 
"boolLib.SPECL", "[", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 22944*)m:num\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 22956*)m*p\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 22966*)n:num\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 22978*)n*p\"", "]", ")", "]", 
hhsRecord.fetch "LESS_EQ_LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_LESS_EQ_MONO\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]" ] )
in hhsRecord.try_record_proof "LESS_MONO_MULT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_MONO_MULT2 = store_thm ( "LESS_MONO_MULT2" , ( Parse.Term [ QUOTE " (*#loc 1 23120*)!m n i j. m <= i /\\ n <= j ==> m * n <= i * j" ] ) ,
let
val tactictoe_tac1 = mesonLib.MESON_TAC [ LESS_EQ_TRANS , LESS_MONO_MULT , MULT_COMM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_MONO_MULT2" 
 ( String.concatWith " " 
 [ "mesonLib.MESON_TAC", "[", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
",", 
hhsRecord.fetch "LESS_MONO_MULT" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_MULT\" ) )", 
",", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_MONO_MULT2" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val RIGHT_SUB_DISTRIB = store_thm ( "RIGHT_SUB_DISTRIB" , ( Parse.Term [ QUOTE " (*#loc 1 23299*)!m n p. (m - n) * p = (m * p) - (n * p)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 23387*)n <= m" ] ) ) THENL [
let
val imp = SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 23432*)(m-n)*p" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 23472*)n*p" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 23508*)m*p" ] ) ] ADD_EQ_SUB
in IMP_RES_THEN ( SUBST1_TAC o SYM o MP imp o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 23589*)p:num" ] ) ) ) LESS_MONO_MULT THEN REWRITE_TAC [ SYM ( SPEC_ALL RIGHT_ADD_DISTRIB ) ] THEN IMP_RES_THEN SUBST1_TAC SUB_ADD THEN REFL_TAC
end , IMP_RES_TAC ( REWRITE_RULE [ ] ( AP_TERM ( ( Parse.Term [ QUOTE " (*#loc 1 23794*)$~" ] ) ) ( SPEC_ALL NOT_LESS ) ) ) THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN IMP_RES_THEN ( ASSUME_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 23949*)p:num" ] ) ) ) LESS_MONO_MULT THEN IMP_RES_TAC SUB_EQ_0 THEN ASM_REWRITE_TAC [ MULT_CLAUSES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "RIGHT_SUB_DISTRIB" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_CASES_TAC", "(", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 23387*)n <= m\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "(", 
"boolLib.IMP_RES_THEN", "(", "boolLib.SUBST1_TAC", "o", "HolKernel.SYM", "o", 
"HolKernel.MP", 
hhsRecord.fetch "imp" "( boolLib.SPECL [ ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 23432*)(m-n)*p\" ] ) , ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 23472*)n*p\" ] ) , ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 23508*)m*p\" ] ) ] ( ( DB.fetch \"arithmetic\" \"ADD_EQ_SUB\" ) ) )", 
"o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 23589*)p:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "LESS_MONO_MULT" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_MULT\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.IMP_RES_THEN", "boolLib.SUBST1_TAC", 
hhsRecord.fetch "SUB_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_ADD\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REFL_TAC", ")", ",", 
"boolLib.IMP_RES_TAC", "(", "boolLib.REWRITE_RULE", "[", "]", "(", "HolKernel.AP_TERM", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 23794*)$~\"", "]", ")", ")", "(", 
"boolLib.SPEC_ALL", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_IMP_LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_IMP_LESS_OR_EQ\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.ASSUME_TAC", "o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 23949*)p:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "LESS_MONO_MULT" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_MULT\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "SUB_EQ_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQ_0\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "RIGHT_SUB_DISTRIB" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val LEFT_SUB_DISTRIB = store_thm ( "LEFT_SUB_DISTRIB" , ( Parse.Term [ QUOTE " (*#loc 1 24107*)!m n p. p * (m - n) = (p * m) - (p * n)" ] ) ,
let
val tactictoe_tac1 = PURE_ONCE_REWRITE_TAC [ MULT_SYM ] THEN REWRITE_TAC [ RIGHT_SUB_DISTRIB ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LEFT_SUB_DISTRIB" 
 ( String.concatWith " " 
 [ "boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_SYM" "( ( DB.fetch \"arithmetic\" \"MULT_SYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "RIGHT_SUB_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_SUB_DISTRIB\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LEFT_SUB_DISTRIB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_ADD_1 = store_thm ( "LESS_ADD_1" , ( Parse.Term [ QUOTE " (*#loc 1 24277*)!m n. (n<m) ==> ?p. m = n + (p + 1)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ ONE ] THEN INDUCT_TAC THEN REWRITE_TAC [ NOT_LESS_0 , LESS_THM ] THEN REPEAT STRIP_TAC THENL [ EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 24443*)0" ] ) ) THEN ASM_REWRITE_TAC [ ADD_CLAUSES ] , RES_THEN ( STRIP_THM_THEN SUBST1_TAC ) THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 24548*)SUC p" ] ) ) THEN REWRITE_TAC [ ADD_CLAUSES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_ADD_1" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.NOT_LESS_0", ",", "prim_recTheory.LESS_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 24443*)0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.RES_THEN", "(", "boolLib.STRIP_THM_THEN", "boolLib.SUBST1_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 24548*)SUC p\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "LESS_ADD_1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_ADD = store_thm ( "EXP_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 24639*)!p q n. n EXP (p+q) = (n EXP p) * (n EXP q)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ EXP , ADD_CLAUSES , MULT_CLAUSES , MULT_ASSOC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_ADD" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EXP_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_ODD_EQ_EVEN = store_thm ( "NOT_ODD_EQ_EVEN" , ( Parse.Term [ QUOTE " (*#loc 1 24824*)!n m. ~(SUC(n + n) = (m + m))" ] ) ,
let
val tactictoe_tac1 = REPEAT ( INDUCT_TAC THEN REWRITE_TAC [ ADD_CLAUSES ] ) THENL [ MATCH_ACCEPT_TAC NOT_SUC , REWRITE_TAC [ INV_SUC_EQ , NOT_EQ_SYM ( SPEC_ALL NOT_SUC ) ] , REWRITE_TAC [ INV_SUC_EQ , NOT_SUC ] , ASM_REWRITE_TAC [ INV_SUC_EQ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_ODD_EQ_EVEN" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "(", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.MATCH_ACCEPT_TAC", "numTheory.NOT_SUC", ",", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.INV_SUC_EQ", ",", "boolLib.NOT_EQ_SYM", "(", "boolLib.SPEC_ALL", 
"numTheory.NOT_SUC", ")", "]", ",", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.INV_SUC_EQ", ",", "numTheory.NOT_SUC", "]", ",", 
"boolLib.ASM_REWRITE_TAC", "[", "prim_recTheory.INV_SUC_EQ", "]", "]" ] )
in hhsRecord.try_record_proof "NOT_ODD_EQ_EVEN" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQUAL_ANTISYM = store_thm ( "LESS_EQUAL_ANTISYM" , ( Parse.Term [ QUOTE " (*#loc 1 25155*)!n m. n <= m /\\ m <= n ==> (n = m)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_OR_EQ ] THEN REPEAT STRIP_TAC THENL [ IMP_RES_TAC LESS_ANTISYM , ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQUAL_ANTISYM" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_ANTISYM\" ) )", 
",", "boolLib.ASM_REWRITE_TAC", "[", "]", "]" ] )
in hhsRecord.try_record_proof "LESS_EQUAL_ANTISYM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_ADD_SUC = store_thm ( "LESS_ADD_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 25370*)!m n. m < m + SUC n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THENL [ REWRITE_TAC [ LESS_0 , ADD_CLAUSES ] , POP_ASSUM ( ASSUME_TAC o REWRITE_RULE [ ADD_CLAUSES ] ) THEN ASM_REWRITE_TAC [ LESS_MONO_EQ , ADD_CLAUSES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_ADD_SUC" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", "prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.POP_ASSUM", "(", "boolLib.ASSUME_TAC", "o", "boolLib.REWRITE_RULE", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "LESS_ADD_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_OR_EQ_ADD = store_thm ( "LESS_OR_EQ_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 25627*)!n m. n < m \\/ ?p. n = p+m" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 25701*)n<m" ] ) ) THENL [ DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC , DISJ2_TAC THEN IMP_RES_TAC NOT_LESS THEN IMP_RES_TAC LESS_OR_EQ THENL [ CONV_TAC ( ONCE_DEPTH_CONV SYM_CONV ) THEN IMP_RES_THEN MATCH_ACCEPT_TAC LESS_ADD , EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 25953*)0" ] ) ) THEN ASM_REWRITE_TAC [ ADD ] ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_OR_EQ_ADD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_CASES_TAC", "(", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 25701*)n<m\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.DISJ1_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ",", "boolLib.DISJ2_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.CONV_TAC", "(", 
"boolLib.ONCE_DEPTH_CONV", "boolLib.SYM_CONV", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", 
"boolLib.MATCH_ACCEPT_TAC", 
hhsRecord.fetch "LESS_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_ADD\" ) )", 
",", "boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 25953*)0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "ADD" "", "]", "]", "]" ] )
in hhsRecord.try_record_proof "LESS_OR_EQ_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val lemma = TAC_PROOF ( ( [ ] , ( Parse.Term [ QUOTE " (*#loc 1 26037*)(~?n. P n /\\ !m. (m<n) ==> ~P m) ==> (!n m. (m<n) ==> ~P m)" ] ) ) ,
let
val tactictoe_tac1 = CONV_TAC ( DEPTH_CONV NOT_EXISTS_CONV ) THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ NOT_LESS_0 , LESS_THM ] THEN REPEAT ( FILTER_STRIP_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 26259*)P:num->bool" ] ) ) ) THENL [ POP_ASSUM SUBST1_TAC THEN DISCH_TAC , ALL_TAC ] THEN RES_TAC
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_87" 
 ( String.concatWith " " 
 [ "boolLib.CONV_TAC", "(", "boolLib.DEPTH_CONV", "boolLib.NOT_EXISTS_CONV", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.NOT_LESS_0", ",", "prim_recTheory.LESS_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", "(", 
"boolLib.FILTER_STRIP_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 26259*)P:num->bool\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.POP_ASSUM", 
"boolLib.SUBST1_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.DISCH_TAC", ",", "boolLib.ALL_TAC", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.RES_TAC" ] )
in hhsRecord.try_record_proof "tactictoe_prove_87" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val WOP = store_thm ( "WOP" , ( Parse.Term [ QUOTE " (*#loc 1 26385*)!P. (?n.P n) ==> (?n. P n /\\ (!m. (m<n) ==> ~P m))" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN ( ASSUME_TAC o MP lemma ) THEN CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC THEN POP_ASSUM ( MATCH_MP_TAC o SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 26625*)SUC n" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 26637*)n:num" ] ) ] ) THEN MATCH_ACCEPT_TAC LESS_SUC_REFL
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "WOP" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.CONV_TAC", "boolLib.CONTRAPOS_CONV", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.ASSUME_TAC", "o", "HolKernel.MP", hhsRecord.fetch "lemma" "", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", 
"boolLib.NOT_EXISTS_CONV", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.POP_ASSUM", "(", "boolLib.MATCH_MP_TAC", "o", "boolLib.SPECL", "[", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 26625*)SUC n\"", "]", ")", ",", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 26637*)n:num\"", "]", ")", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_ACCEPT_TAC", 
"prim_recTheory.LESS_SUC_REFL" ] )
in hhsRecord.try_record_proof "WOP" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val COMPLETE_INDUCTION = store_thm ( "COMPLETE_INDUCTION" , ( Parse.Term [ QUOTE " (*#loc 1 26753*)!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n" ] ) ,
let
val tactictoe_tac1 =
let
val wopeta = CONV_RULE ( ONCE_DEPTH_CONV ETA_CONV ) WOP
in GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN CONV_TAC ( ONCE_DEPTH_CONV NOT_FORALL_CONV ) THEN DISCH_THEN ( MP_TAC o MATCH_MP wopeta ) THEN BETA_TAC THEN REWRITE_TAC [ NOT_IMP ] THEN DISCH_THEN ( X_CHOOSE_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 27078*)n:num" ] ) ) ) THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 27111*)n:num" ] ) ) THEN ASM_REWRITE_TAC [ ]
end
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "COMPLETE_INDUCTION" 
 ( String.concatWith " " 
 [ "(", "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.CONV_TAC", "boolLib.CONTRAPOS_CONV", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", "(", 
"boolLib.ONCE_DEPTH_CONV", "boolLib.NOT_FORALL_CONV", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.MP_TAC", "o", "boolLib.MATCH_MP", 
hhsRecord.fetch "wopeta" "( boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV boolLib.ETA_CONV ) ( ( DB.fetch \"arithmetic\" \"WOP\" ) ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.BETA_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.NOT_IMP", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.DISCH_THEN", "(", "boolLib.X_CHOOSE_TAC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 27078*)n:num\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 27111*)n:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", ")" ] )
in hhsRecord.try_record_proof "COMPLETE_INDUCTION" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val FORALL_NUM_THM = Q.store_thm ( "FORALL_NUM_THM" , [ QUOTE " (*#loc 1 27207*)(!n. P n) = P 0 /\\ !n. P n ==> P (SUC n)" ] ,
let
val tactictoe_tac1 = METIS_TAC [ INDUCTION ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "FORALL_NUM_THM" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", "numTheory.INDUCTION", "]" ] )
in hhsRecord.try_record_proof "FORALL_NUM_THM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUC_SUB = store_thm ( "SUC_SUB[simp]" , ( Parse.Term [ QUOTE " (*#loc 1 27328*)!a. SUC a - a = 1" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THENL [ REWRITE_TAC [ SUB , LESS_REFL , ONE ] , ASM_REWRITE_TAC [ SUB_MONO_EQ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUC_SUB" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "SUB" "", ",", "prim_recTheory.LESS_REFL", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", ",", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "SUC_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_PLUS = store_thm ( "SUB_PLUS" , ( Parse.Term [ QUOTE " (*#loc 1 27494*)!a b c. a - (b + c) = (a - b) - c" ] ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN REWRITE_TAC [ SUB_0 , ADD_CLAUSES , SUB_MONO_EQ ] THEN PURE_ONCE_REWRITE_TAC [ SYM ( el 4 ( CONJUNCTS ADD_CLAUSES ) ) ] THEN PURE_ONCE_ASM_REWRITE_TAC [ ] THEN REFL_TAC
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_PLUS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", "HolKernel.SYM", "(", "HolKernel.el", "4", "(", 
"boolLib.CONJUNCTS", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
")", ")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_ASM_REWRITE_TAC", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REFL_TAC" ] )
in hhsRecord.try_record_proof "SUB_PLUS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val INV_PRE_LESS = store_thm ( "INV_PRE_LESS" , ( Parse.Term [ QUOTE " (*#loc 1 27778*)!m. 0 < m  ==> !n. PRE m < PRE n = m < n" ] ) ,
let
val tactictoe_tac1 = REPEAT ( INDUCT_TAC THEN TRY DISCH_TAC ) THEN REWRITE_TAC [ LESS_REFL , SUB , LESS_0 , PRE , NOT_LESS_0 ] THEN IMP_RES_TAC LESS_REFL THEN MATCH_ACCEPT_TAC ( SYM ( SPEC_ALL LESS_MONO_EQ ) )
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "INV_PRE_LESS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "(", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.TRY", 
"boolLib.DISCH_TAC", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "prim_recTheory.LESS_REFL", ",", 
hhsRecord.fetch "SUB" "", ",", "prim_recTheory.LESS_0", ",", "prim_recTheory.PRE", 
",", "prim_recTheory.NOT_LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
"prim_recTheory.LESS_REFL", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_ACCEPT_TAC", "(", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
")", ")" ] )
in hhsRecord.try_record_proof "INV_PRE_LESS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val INV_PRE_LESS_EQ = store_thm ( "INV_PRE_LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 28068*)!n. 0 < n ==> !m. ((PRE m <= PRE n) = (m <= n))" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN REWRITE_TAC [ LESS_REFL , LESS_0 , PRE ] THEN INDUCT_TAC THEN REWRITE_TAC [ PRE , ZERO_LESS_EQ ] THEN REWRITE_TAC [ ADD1 , LESS_EQ_MONO_ADD_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "INV_PRE_LESS_EQ" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.LESS_REFL", ",", "prim_recTheory.LESS_0", ",", "prim_recTheory.PRE", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.PRE", ",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", ",", 
hhsRecord.fetch "LESS_EQ_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO_ADD_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "INV_PRE_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val PRE_LESS_EQ = Q.store_thm ( "PRE_LESS_EQ" , [ QUOTE " (*#loc 1 28333*)!n. m <= n ==> PRE m <= PRE n" ] ,
let
val tactictoe_tac1 = INDUCT_TAC >>- 1 ?? ( REWRITE_TAC [ LESS_EQ_0 ] THEN DISCH_TAC THEN ASM_REWRITE_TAC [ LESS_EQ_REFL ] ) THEN VALIDATE ( CONV_TAC ( DEPTH_CONV ( REWR_CONV_A ( SPEC_ALL ( UNDISCH ( SPEC_ALL INV_PRE_LESS_EQ ) ) ) ) ) ) THEN REWRITE_TAC [ LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "PRE_LESS_EQ" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.VALIDATE", 
"(", "boolLib.CONV_TAC", "(", "boolLib.DEPTH_CONV", "(", "boolLib.REWR_CONV_A", "(", 
"boolLib.SPEC_ALL", "(", "boolLib.UNDISCH", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "INV_PRE_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"INV_PRE_LESS_EQ\" ) )", 
")", ")", ")", ")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "PRE_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LESS_EQ = store_thm ( "SUB_LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 28656*)!n m. (n - m) <= n" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ SYM ( SPEC_ALL SUB_EQ_0 ) , SYM ( SPEC_ALL SUB_PLUS ) ] THEN CONV_TAC ( ONCE_DEPTH_CONV ( REWR_CONV ADD_SYM ) ) THEN REWRITE_TAC [ SUB_EQ_0 , LESS_EQ_ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LESS_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "SUB_EQ_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQ_0\" ) )", 
")", ",", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "SUB_PLUS" "( ( DB.fetch \"arithmetic\" \"SUB_PLUS\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", 
"(", "boolLib.ONCE_DEPTH_CONV", "(", "boolLib.REWR_CONV", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", ")", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "SUB_EQ_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_EQ_EQ_0 = store_thm ( "SUB_EQ_EQ_0" , ( Parse.Term [ QUOTE " (*#loc 1 28890*)!m n. (m - n = m) = ((m = 0) \\/ (n = 0))" ] ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN REWRITE_TAC [ SUB_0 , NOT_SUC ] THEN REWRITE_TAC [ SUB ] THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 29044*)m<SUC n" ] ) ) THENL [ CONV_TAC ( ONCE_DEPTH_CONV SYM_CONV ) THEN ASM_REWRITE_TAC [ NOT_SUC ] , ASM_REWRITE_TAC [ INV_SUC_EQ , NOT_SUC ] THEN IMP_RES_THEN ( ASSUME_TAC o MATCH_MP OR_LESS ) NOT_LESS THEN IMP_RES_THEN ( STRIP_THM_THEN SUBST1_TAC ) LESS_ADD_1 THEN REWRITE_TAC [ ONE , ADD_CLAUSES , NOT_SUC ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_EQ_EQ_0" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
"numTheory.NOT_SUC", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", hhsRecord.fetch "SUB" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_CASES_TAC", "(", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 29044*)m<SUC n\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.CONV_TAC", "(", 
"boolLib.ONCE_DEPTH_CONV", "boolLib.SYM_CONV", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "numTheory.NOT_SUC", "]", ",", "boolLib.ASM_REWRITE_TAC", "[", 
"prim_recTheory.INV_SUC_EQ", ",", "numTheory.NOT_SUC", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.ASSUME_TAC", "o", "boolLib.MATCH_MP", 
hhsRecord.fetch "OR_LESS" "( ( DB.fetch \"arithmetic\" \"OR_LESS\" ) )", ")", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.STRIP_THM_THEN", "boolLib.SUBST1_TAC", ")", 
hhsRecord.fetch "LESS_ADD_1" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_1\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "numTheory.NOT_SUC", "]", "]" ] )
in hhsRecord.try_record_proof "SUB_EQ_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LESS_0 = store_thm ( "SUB_LESS_0" , ( Parse.Term [ QUOTE " (*#loc 1 29397*)!n m. (m < n) = 0 < (n - m)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN EQ_TAC THENL [ DISCH_THEN ( STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1 ) THEN REWRITE_TAC [ ONE , ADD_CLAUSES , SUB ] THEN REWRITE_TAC [ REWRITE_RULE [ SYM ( SPEC_ALL NOT_LESS ) ] LESS_EQ_ADD , LESS_0 ] , CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [ NOT_LESS , LESS_OR_EQ , NOT_LESS_0 , SUB_EQ_0 ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LESS_0" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.DISCH_THEN", 
"(", "boolLib.STRIP_THM_THEN", "boolLib.SUBST1_TAC", "o", "boolLib.MATCH_MP", 
hhsRecord.fetch "LESS_ADD_1" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_1\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.REWRITE_RULE", "[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
")", "]", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
",", "prim_recTheory.LESS_0", "]", ",", "boolLib.CONV_TAC", "boolLib.CONTRAPOS_CONV", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", "prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "SUB_EQ_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQ_0\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "SUB_LESS_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LESS_OR = store_thm ( "SUB_LESS_OR" , ( Parse.Term [ QUOTE " (*#loc 1 29798*)!m n. n < m ==> n <= (m - 1)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN DISCH_THEN ( STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1 ) THEN REWRITE_TAC [ SYM ( SPEC_ALL PRE_SUB1 ) ] THEN REWRITE_TAC [ PRE , ONE , ADD_CLAUSES , LESS_EQ_ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LESS_OR" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.STRIP_THM_THEN", "boolLib.SUBST1_TAC", "o", "boolLib.MATCH_MP", 
hhsRecord.fetch "LESS_ADD_1" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_1\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "PRE_SUB1" "( ( DB.fetch \"arithmetic\" \"PRE_SUB1\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "prim_recTheory.PRE", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_LESS_OR" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_SUB_ADD_LESS = store_thm ( "LESS_SUB_ADD_LESS" , ( Parse.Term [ QUOTE " (*#loc 1 30080*)!n m i. (i < (n - m)) ==> ((i + m) < n)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THENL [ REWRITE_TAC [ SUB_0 , NOT_LESS_0 ] , REWRITE_TAC [ SUB ] THEN REPEAT GEN_TAC THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 30249*)n < m" ] ) ) THEN ASM_REWRITE_TAC [ NOT_LESS_0 , LESS_THM ] THEN
let
fun tac th g = SUBST1_TAC th g handle _ => ASSUME_TAC th g
in DISCH_THEN ( STRIP_THM_THEN tac )
end THENL [ DISJ1_TAC THEN MATCH_MP_TAC SUB_ADD THEN ASM_REWRITE_TAC [ SYM ( SPEC_ALL NOT_LESS ) ] , RES_TAC THEN ASM_REWRITE_TAC [ ] ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_SUB_ADD_LESS" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
"prim_recTheory.NOT_LESS_0", "]", ",", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "SUB" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_CASES_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 30249*)n < m\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "prim_recTheory.NOT_LESS_0", ",", "prim_recTheory.LESS_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", "boolLib.DISCH_THEN", "(", 
"boolLib.STRIP_THM_THEN", 
hhsRecord.fetch "tac" "let fun tac th g = boolLib.SUBST1_TAC th g handle _ => boolLib.ASSUME_TAC th g in tac end", 
")", ")", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.DISJ1_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "SUB_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_ADD\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
")", "]", ",", "boolLib.RES_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", "]", "]" ] )
in hhsRecord.try_record_proof "LESS_SUB_ADD_LESS" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val TIMES2 = store_thm ( "TIMES2" , ( Parse.Term [ QUOTE " (*#loc 1 30631*)!n. 2 * n = n + n" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ MULT_CLAUSES , NUMERAL_DEF , BIT2 , ADD_CLAUSES , ALT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "TIMES2" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", hhsRecord.fetch "BIT2" "( ( DB.fetch \"arithmetic\" \"BIT2\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ALT_ZERO" "( ( DB.fetch \"arithmetic\" \"ALT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "TIMES2" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_MULT_MONO = store_thm ( "LESS_MULT_MONO" , ( Parse.Term [ QUOTE " (*#loc 1 30780*)!m i n. ((SUC n) * m) < ((SUC n) * i) = (m < i)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ MULT_CLAUSES ] THEN INDUCT_TAC THENL [ INDUCT_TAC THEN REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , LESS_0 ] , INDUCT_TAC THENL [ REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , NOT_LESS_0 ] , INDUCT_TAC THENL [ REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES ] , REWRITE_TAC [ LESS_MONO_EQ , ADD_CLAUSES , MULT_CLAUSES ] THEN REWRITE_TAC [ SYM ( SPEC_ALL ADD_ASSOC ) ] THEN PURE_ONCE_REWRITE_TAC [ ADD_SYM ] THEN REWRITE_TAC [ LESS_MONO_ADD_EQ ] THEN REWRITE_TAC [ ADD_ASSOC ] THEN
let
val th = SYM ( el 5 ( CONJUNCTS ( SPEC_ALL MULT_CLAUSES ) ) )
in PURE_ONCE_REWRITE_TAC [ th ]
end THEN ASM_REWRITE_TAC [ ] ] ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_MULT_MONO" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_0", "]", ",", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.NOT_LESS_0", "]", ",", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "th" "( HolKernel.SYM ( HolKernel.el 5 ( boolLib.CONJUNCTS ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) ) ) ) ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", "]", "]", "]" ] )
in hhsRecord.try_record_proof "LESS_MULT_MONO" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_MONO_EQ = store_thm ( "MULT_MONO_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 31531*)!m i n. (((SUC n) * m) = ((SUC n) * i)) = (m = i)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ MULT_CLAUSES ] THEN INDUCT_TAC THENL [ INDUCT_TAC THEN REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , NOT_EQ_SYM ( SPEC_ALL NOT_SUC ) ] , INDUCT_TAC THENL [ REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , NOT_SUC ] , INDUCT_TAC THENL [ REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES ] , REWRITE_TAC [ INV_SUC_EQ , ADD_CLAUSES , MULT_CLAUSES ] THEN REWRITE_TAC [ SYM ( SPEC_ALL ADD_ASSOC ) ] THEN PURE_ONCE_REWRITE_TAC [ ADD_SYM ] THEN REWRITE_TAC [ EQ_MONO_ADD_EQ ] THEN REWRITE_TAC [ ADD_ASSOC ] THEN
let
val th = SYM ( el 5 ( CONJUNCTS ( SPEC_ALL MULT_CLAUSES ) ) )
in PURE_ONCE_REWRITE_TAC [ th ]
end THEN ASM_REWRITE_TAC [ ] ] ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_MONO_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "boolLib.NOT_EQ_SYM", "(", "boolLib.SPEC_ALL", "numTheory.NOT_SUC", ")", "]", ",", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "numTheory.NOT_SUC", "]", ",", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.REWRITE_TAC", "[", "prim_recTheory.INV_SUC_EQ", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EQ_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"EQ_MONO_ADD_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "th" "( HolKernel.SYM ( HolKernel.el 5 ( boolLib.CONJUNCTS ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) ) ) ) ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", "]", "]", "]" ] )
in hhsRecord.try_record_proof "MULT_MONO_EQ" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_SUC_EQ = store_thm ( "MULT_SUC_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 32303*)!p m n. ((n * (SUC p)) = (m * (SUC p))) = (n = m)" ] ) ,
let
val tactictoe_tac1 = ONCE_REWRITE_TAC [ MULT_COMM ] THEN REWRITE_TAC [ MULT_MONO_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_SUC_EQ" 
 ( String.concatWith " " 
 [ "boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"MULT_MONO_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MULT_SUC_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_EXP_MONO = store_thm ( "MULT_EXP_MONO" , ( Parse.Term [ QUOTE " (*#loc 1 32476*)!p q n m.((n * ((SUC q) EXP p)) = (m * ((SUC q) EXP p))) = (n = m)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THENL [ REWRITE_TAC [ EXP , MULT_CLAUSES , ADD_CLAUSES ] , ASM_REWRITE_TAC [ EXP , MULT_ASSOC , MULT_SUC_EQ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_EXP_MONO" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.ASM_REWRITE_TAC", "[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
",", 
hhsRecord.fetch "MULT_SUC_EQ" "( ( DB.fetch \"arithmetic\" \"MULT_SUC_EQ\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "MULT_EXP_MONO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EQ_ADD_LCANCEL = store_thm ( "EQ_ADD_LCANCEL" , ( Parse.Term [ QUOTE " (*#loc 1 32728*)!m n p. (m + n = m + p) = (n = p)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , INV_SUC_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EQ_ADD_LCANCEL" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", "]" ] )
in hhsRecord.try_record_proof "EQ_ADD_LCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EQ_ADD_RCANCEL = store_thm ( "EQ_ADD_RCANCEL" , ( Parse.Term [ QUOTE " (*#loc 1 32883*)!m n p. (m + p = n + p) = (m = n)" ] ) ,
let
val tactictoe_tac1 = ONCE_REWRITE_TAC [ ADD_COMM ] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EQ_ADD_RCANCEL" 
 ( String.concatWith " " 
 [ "boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_ACCEPT_TAC", 
hhsRecord.fetch "EQ_ADD_LCANCEL" "( ( DB.fetch \"arithmetic\" \"EQ_ADD_LCANCEL\" ) )" ] )
in hhsRecord.try_record_proof "EQ_ADD_RCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EQ_MULT_LCANCEL = store_thm ( "EQ_MULT_LCANCEL[simp]" , ( Parse.Term [ QUOTE " (*#loc 1 33052*)!m n p. (m * n = m * p) = (m = 0) \\/ (n = p)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN REWRITE_TAC [ MULT_CLAUSES , NOT_SUC ] THEN REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , GSYM NOT_SUC , NOT_SUC ] THEN ASM_REWRITE_TAC [ INV_SUC_EQ , GSYM ADD_ASSOC , EQ_ADD_LCANCEL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EQ_MULT_LCANCEL" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "numTheory.NOT_SUC", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "boolLib.GSYM", "numTheory.NOT_SUC", ",", "numTheory.NOT_SUC", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "prim_recTheory.INV_SUC_EQ", ",", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", 
hhsRecord.fetch "EQ_ADD_LCANCEL" "( ( DB.fetch \"arithmetic\" \"EQ_ADD_LCANCEL\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EQ_MULT_LCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EQ_MULT_RCANCEL = store_thm ( "EQ_MULT_RCANCEL[simp]" , ( Parse.Term [ QUOTE " (*#loc 1 33386*)!m n p. (n * m = p * m) <=> (m = 0) \\/ (n = p)" ] ) ,
let
val tactictoe_tac1 = ONCE_REWRITE_TAC [ MULT_COMM ] THEN REWRITE_TAC [ EQ_MULT_LCANCEL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EQ_MULT_RCANCEL" 
 ( String.concatWith " " 
 [ "boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "EQ_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"EQ_MULT_LCANCEL\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EQ_MULT_RCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_SUB = store_thm ( "ADD_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 33545*)!a c. (a + c) - c = a" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_0 , SUB_MONO_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_SUB" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ADD_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_ADD_SUB = store_thm ( "LESS_EQ_ADD_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 33715*)!c b. (c <= b) ==> !a. (((a + b) - c) = (a + (b - c)))" ] ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_0 , SUB_MONO_EQ , NOT_SUC_LESS_EQ_0 , LESS_EQ_MONO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_ADD_SUB" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_EQ_ADD_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = print "More properties of subtraction...\n"
;
val SUB_EQUAL_0 = save_thm ( "SUB_EQUAL_0" , REWRITE_RULE [ ADD_CLAUSES ] ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 34032*)0" ] ) ) ADD_SUB ) )
;
;
val LESS_EQ_SUB_LESS = store_thm ( "LESS_EQ_SUB_LESS" , ( Parse.Term [ QUOTE " (*#loc 1 34107*)!a b. (b <= a) ==> !c. ((a - b) < c) = (a < (b + c))" ] ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_0 , SUB_MONO_EQ , NOT_SUC_LESS_EQ_0 , LESS_EQ_MONO , LESS_MONO_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_SUB_LESS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_EQ_SUB_LESS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_SUC_LESS_EQ = store_thm ( "NOT_SUC_LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 34354*)!n m.~(SUC n <= m) = (m <= n)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ SYM ( SPEC_ALL LESS_EQ ) , NOT_LESS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_SUC_LESS_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", ")", 
",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "NOT_SUC_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_SUB = store_thm ( "SUB_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 34480*)!b c. (c <= b) ==> !a. ((a - (b - c)) = ((a + c) - b))" ] ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_0 , SUB_MONO_EQ , NOT_SUC_LESS_EQ_0 , LESS_EQ_MONO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_SUB" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_IMP_LESS_ADD = store_thm ( "LESS_IMP_LESS_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 34719*)!n m. n < m ==> !p. n < (m + p)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN DISCH_THEN ( STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1 ) THEN REWRITE_TAC [ SYM ( SPEC_ALL ADD_ASSOC ) , ONE ] THEN PURE_ONCE_REWRITE_TAC [ ADD_CLAUSES ] THEN PURE_ONCE_REWRITE_TAC [ ADD_CLAUSES ] THEN GEN_TAC THEN MATCH_ACCEPT_TAC LESS_ADD_SUC
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_IMP_LESS_ADD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.STRIP_THM_THEN", "boolLib.SUBST1_TAC", "o", "boolLib.MATCH_MP", 
hhsRecord.fetch "LESS_ADD_1" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_1\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
")", ",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_ACCEPT_TAC", 
hhsRecord.fetch "LESS_ADD_SUC" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_SUC\" ) )" ] )
in hhsRecord.try_record_proof "LESS_IMP_LESS_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LESS_EQ_ADD = store_thm ( "SUB_LESS_EQ_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 35090*)!m p. (m <= p) ==> !n. (((p - m) <= n) = (p <= (m + n)))" ] ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_0 , SUB_MONO_EQ , NOT_SUC_LESS_EQ_0 , LESS_EQ_MONO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LESS_EQ_ADD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_LESS_EQ_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LESS_SUC = store_thm ( "SUB_LESS_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 35322*)!p m. p - m < SUC p" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 35423*)p" ] THEN CONJ_TAC THENL [ MATCH_ACCEPT_TAC SUB_LESS_EQ , MATCH_ACCEPT_TAC LESS_SUC_REFL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LESS_SUC" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQ_LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 35423*)p\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.MATCH_ACCEPT_TAC", 
hhsRecord.fetch "SUB_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_LESS_EQ\" ) )", 
",", "boolLib.MATCH_ACCEPT_TAC", "prim_recTheory.LESS_SUC_REFL", "]" ] )
in hhsRecord.try_record_proof "SUB_LESS_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_NE_SUC = MATCH_MP LESS_NOT_EQ ( SPEC_ALL SUB_LESS_SUC )
;
;
val SUB_LE_SUC = MATCH_MP LESS_IMP_LESS_OR_EQ ( SPEC_ALL SUB_LESS_SUC )
;
;
val SUB_CANCEL = store_thm ( "SUB_CANCEL" , ( Parse.Term [ QUOTE " (*#loc 1 35701*)!p n m. ((n <= p) /\\ (m <= p)) ==> (((p - n) = (p - m)) = (n = m))" ] ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ SUB_0 , ZERO_LESS_EQ , SUB_MONO_EQ , LESS_EQ_MONO , INV_SUC_EQ , NOT_SUC_LESS_EQ_0 , NOT_SUC , GSYM NOT_SUC , SUB_NE_SUC , GSYM SUB_NE_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_CANCEL" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", ",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", "numTheory.NOT_SUC", ",", "boolLib.GSYM", "numTheory.NOT_SUC", ",", 
hhsRecord.fetch "SUB_NE_SUC" "( boolLib.MATCH_MP prim_recTheory.LESS_NOT_EQ ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"SUB_LESS_SUC\" ) ) ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "SUB_NE_SUC" "( boolLib.MATCH_MP prim_recTheory.LESS_NOT_EQ ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"SUB_LESS_SUC\" ) ) ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_CANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val CANCEL_SUB = store_thm ( "CANCEL_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 36000*)!p n m.((p <= n) /\\ (p <= m)) ==> (((n - p) = (m - p)) = (n = m))" ] ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ SUB_0 , ZERO_LESS_EQ , SUB_MONO_EQ , LESS_EQ_MONO , INV_SUC_EQ , NOT_SUC_LESS_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "CANCEL_SUB" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", ",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "CANCEL_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_EXP_0 = store_thm ( "NOT_EXP_0" , ( Parse.Term [ QUOTE " (*#loc 1 36244*)!m n. ~(((SUC n) EXP m) = 0)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN REWRITE_TAC [ EXP ] THENL [ REWRITE_TAC [ NOT_SUC , ONE ] , STRIP_TAC THEN
let
val th = ( SYM ( el 2 ( CONJUNCTS ( SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 36420*)SUC n" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 36432*)1" ] ) ] MULT_CLAUSES ) ) ) )
in SUBST1_TAC th
end THEN REWRITE_TAC [ MULT_MONO_EQ ] THEN FIRST_ASSUM MATCH_ACCEPT_TAC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_EXP_0" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EXP" "", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", "numTheory.NOT_SUC", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", ",", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", 
"boolLib.SUBST1_TAC", 
hhsRecord.fetch "th" "( ( HolKernel.SYM ( HolKernel.el 2 ( boolLib.CONJUNCTS ( boolLib.SPECL [ ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 36420*)SUC n\" ] ) , ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 36432*)1\" ] ) ] ( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) ) ) ) ) ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"MULT_MONO_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.MATCH_ACCEPT_TAC", "]" ] )
in hhsRecord.try_record_proof "NOT_EXP_0" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val ZERO_LESS_EXP = store_thm ( "ZERO_LESS_EXP" , ( Parse.Term [ QUOTE " (*#loc 1 36658*)!m n. 0 < ((SUC n) EXP m)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN
let
val th = SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 36738*)(SUC n) EXP m" ] ) ) LESS_0_CASES
fun tac th g = ASSUME_TAC ( SYM th ) g handle _ => ACCEPT_TAC th g
in STRIP_THM_THEN tac th THEN IMP_RES_TAC NOT_EXP_0
end
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ZERO_LESS_EXP" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", 
"boolLib.STRIP_THM_THEN", 
hhsRecord.fetch "tac" "let fun tac th g = boolLib.ASSUME_TAC ( HolKernel.SYM th ) g handle _ => boolLib.ACCEPT_TAC th g in tac end", 
hhsRecord.fetch "th" "( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 36738*)(SUC n) EXP m\" ] ) ) ( ( DB.fetch \"arithmetic\" \"LESS_0_CASES\" ) ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "NOT_EXP_0" "( ( DB.fetch \"arithmetic\" \"NOT_EXP_0\" ) )", 
")" ] )
in hhsRecord.try_record_proof "ZERO_LESS_EXP" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val ODD_OR_EVEN = store_thm ( "ODD_OR_EVEN" , ( Parse.Term [ QUOTE " (*#loc 1 36981*)!n. ?m. (n = (SUC(SUC 0) * m)) \\/ (n = ((SUC(SUC 0) * m) + 1))" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ ONE ] THEN INDUCT_THEN INDUCTION STRIP_ASSUME_TAC THENL [ EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 37141*)0" ] ) ) THEN REWRITE_TAC [ ADD_CLAUSES , MULT_CLAUSES ] , EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 37211*)m:num" ] ) ) THEN ASM_REWRITE_TAC [ ADD_CLAUSES ] , EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 37275*)SUC m" ] ) ) THEN ASM_REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ODD_OR_EVEN" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Prim_rec.INDUCT_THEN", 
"numTheory.INDUCTION", "boolLib.STRIP_ASSUME_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.EXISTS_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 37141*)0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", ",", "boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 37211*)m:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 37275*)SUC m\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "ODD_OR_EVEN" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EXP_SUC_MONO = store_thm ( "LESS_EXP_SUC_MONO" , ( Parse.Term [ QUOTE " (*#loc 1 37395*)!n m.((SUC(SUC m)) EXP n) < ((SUC(SUC m)) EXP (SUC n))" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC [ EXP ] THENL [ REWRITE_TAC [ EXP , ADD_CLAUSES , MULT_CLAUSES , ONE , LESS_0 , LESS_MONO_EQ ] , ASM_REWRITE_TAC [ LESS_MULT_MONO ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EXP_SUC_MONO" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", hhsRecord.fetch "EXP" "", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
"]", ",", "boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_MULT_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_MULT_MONO\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "LESS_EXP_SUC_MONO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_LESS_CASES = store_thm ( "LESS_LESS_CASES" , ( Parse.Term [ QUOTE " (*#loc 1 37681*)!m n. (m = n) \\/ (m < n) \\/ (n < m)" ] ) ,
let
val tactictoe_tac1 =
let
val th = REWRITE_RULE [ LESS_OR_EQ ] ( SPECL [ ( ( Parse.Term [ QUOTE " (*#loc 1 37801*)m:num" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 37816*)n:num" ] ) ) ] LESS_CASES )
in REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ( fn t => REWRITE_TAC [ t ] ) th
end
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_LESS_CASES" 
 ( String.concatWith " " 
 [ "(", "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT_TCL", 
"boolLib.DISJ_CASES_THEN", "(", "fn", "t", "=>", "boolLib.REWRITE_TAC", "[", "t", "]", ")", 
hhsRecord.fetch "th" "( boolLib.REWRITE_RULE [ ( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) ) ] ( boolLib.SPECL [ ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 37801*)m:num\" ] ) ) , ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 37816*)n:num\" ] ) ) ] ( ( DB.fetch \"arithmetic\" \"LESS_CASES\" ) ) ) )", 
")" ] )
in hhsRecord.try_record_proof "LESS_LESS_CASES" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val GREATER_EQ = store_thm ( "GREATER_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 37982*)!n m. n >= m = m <= n" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REWRITE_TAC [ GREATER_OR_EQ , GREATER_DEF , LESS_OR_EQ ] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "GREATER_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "GREATER_OR_EQ" "( ( DB.fetch \"arithmetic\" \"GREATER_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "GREATER_DEF" "( ( DB.fetch \"arithmetic\" \"GREATER_DEF\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.AP_TERM_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_ACCEPT_TAC", 
"boolLib.EQ_SYM_EQ" ] )
in hhsRecord.try_record_proof "GREATER_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_CASES = store_thm ( "LESS_EQ_CASES" , ( Parse.Term [ QUOTE " (*#loc 1 38188*)!m n. m <= n \\/ n <= m" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN DISJ_CASES_THEN2 ( ASSUME_TAC o MATCH_MP LESS_IMP_LESS_OR_EQ ) ASSUME_TAC ( SPECL [ ( ( Parse.Term [ QUOTE " (*#loc 1 38327*)m:num" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 38342*)n:num" ] ) ) ] LESS_CASES ) THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_CASES" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISJ_CASES_THEN2", 
"(", "boolLib.ASSUME_TAC", "o", "boolLib.MATCH_MP", 
hhsRecord.fetch "LESS_IMP_LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_IMP_LESS_OR_EQ\" ) )", 
")", "boolLib.ASSUME_TAC", "(", "boolLib.SPECL", "[", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 38327*)m:num\"", "]", ")", ")", ",", "(", "(", "Parse.Term", 
"[", "HolKernel.QUOTE", "\" (*#loc 1 38342*)n:num\"", "]", ")", ")", "]", 
hhsRecord.fetch "LESS_CASES" "( ( DB.fetch \"arithmetic\" \"LESS_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]" ] )
in hhsRecord.try_record_proof "LESS_EQ_CASES" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQUAL_ADD = store_thm ( "LESS_EQUAL_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 38445*)!m n. m <= n ==> ?p. n = m + p" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REWRITE_TAC [ LESS_OR_EQ ] THEN DISCH_THEN ( DISJ_CASES_THEN2 MP_TAC SUBST1_TAC ) THENL [ MATCH_ACCEPT_TAC ( GSYM ( ONCE_REWRITE_RULE [ ADD_SYM ] LESS_ADD ) ) , EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 38671*)0" ] ) ) THEN REWRITE_TAC [ ADD_CLAUSES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQUAL_ADD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.DISJ_CASES_THEN2", "boolLib.MP_TAC", "boolLib.SUBST1_TAC", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.MATCH_ACCEPT_TAC", "(", "boolLib.GSYM", "(", "boolLib.ONCE_REWRITE_RULE", 
"[", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
"]", 
hhsRecord.fetch "LESS_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_ADD\" ) )", 
")", ")", ",", "boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 38671*)0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "LESS_EQUAL_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQ_EXISTS = store_thm ( "LESS_EQ_EXISTS" , ( Parse.Term [ QUOTE " (*#loc 1 38765*)!m n. m <= n = ?p. n = m + p" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN EQ_TAC THENL [ MATCH_ACCEPT_TAC LESS_EQUAL_ADD , DISCH_THEN ( CHOOSE_THEN SUBST1_TAC ) THEN MATCH_ACCEPT_TAC LESS_EQ_ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQ_EXISTS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.MATCH_ACCEPT_TAC", 
hhsRecord.fetch "LESS_EQUAL_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ADD\" ) )", 
",", "boolLib.DISCH_THEN", "(", "boolLib.CHOOSE_THEN", "boolLib.SUBST1_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_ACCEPT_TAC", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_EQ_EXISTS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_EQ_0 = store_thm ( "MULT_EQ_0" , ( Parse.Term [ QUOTE " (*#loc 1 38991*)!m n. (m * n = 0) = (m = 0) \\/ (n = 0)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN MAP_EVERY ( STRUCT_CASES_TAC o C SPEC num_CASES ) [ ( ( Parse.Term [ QUOTE " (*#loc 1 39111*)m:num" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 39125*)n:num" ] ) ) ] THEN REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , NOT_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_EQ_0" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MAP_EVERY", "(", 
"boolLib.STRUCT_CASES_TAC", "o", "HolKernel.C", "HolKernel.SPEC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "[", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 39111*)m:num\"", "]", 
")", ")", ",", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 39125*)n:num\"", 
"]", ")", ")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "numTheory.NOT_SUC", "]" ] )
in hhsRecord.try_record_proof "MULT_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_EQ_1 = store_thm ( "MULT_EQ_1" , ( Parse.Term [ QUOTE " (*#loc 1 39237*)!x y. (x * y = 1) = (x = 1) /\\ (y = 1)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN MAP_EVERY ( STRUCT_CASES_TAC o C SPEC num_CASES ) [ ( ( Parse.Term [ QUOTE " (*#loc 1 39369*)x:num" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 39383*)y:num" ] ) ) ] THEN REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , ONE , GSYM SUC_ID , INV_SUC_EQ , ADD_EQ_0 , MULT_EQ_0 ] THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_EQ_1" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MAP_EVERY", "(", 
"boolLib.STRUCT_CASES_TAC", "o", "HolKernel.C", "HolKernel.SPEC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "[", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 39369*)x:num\"", "]", 
")", ")", ",", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 39383*)y:num\"", 
"]", ")", ")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"boolLib.GSYM", "prim_recTheory.SUC_ID", ",", "prim_recTheory.INV_SUC_EQ", ",", 
hhsRecord.fetch "ADD_EQ_0" "( ( DB.fetch \"arithmetic\" \"ADD_EQ_0\" ) )", 
",", 
hhsRecord.fetch "MULT_EQ_0" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_0\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "MULT_EQ_1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_EQ_ID = store_thm ( "MULT_EQ_ID" , ( Parse.Term [ QUOTE " (*#loc 1 39604*)!m n. (m * n = n) = (m=1) \\/ (n=0)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN STRUCT_CASES_TAC ( SPEC ( Parse.Term [ QUOTE " (*#loc 1 39691*)m:num" ] ) num_CASES ) THEN REWRITE_TAC [ MULT_CLAUSES , ONE , GSYM NOT_SUC , INV_SUC_EQ ] THENL [ METIS_TAC [ ] , METIS_TAC [ ADD_INV_0_EQ , MULT_EQ_0 , ADD_SYM ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_EQ_ID" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRUCT_CASES_TAC", 
"(", "HolKernel.SPEC", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 39691*)m:num\"", "]", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"boolLib.GSYM", "numTheory.NOT_SUC", ",", "prim_recTheory.INV_SUC_EQ", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "metisLib.METIS_TAC", 
"[", "]", ",", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "ADD_INV_0_EQ" "( ( DB.fetch \"arithmetic\" \"ADD_INV_0_EQ\" ) )", 
",", 
hhsRecord.fetch "MULT_EQ_0" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_0\" ) )", 
",", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "MULT_EQ_ID" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_MULT2 = store_thm ( "LESS_MULT2" , ( Parse.Term [ QUOTE " (*#loc 1 39886*)!m n. 0 < m /\\ 0 < n ==> 0 < (m * n)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [ NOT_LESS , LESS_EQ_0 , DE_MORGAN_THM , MULT_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_MULT2" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", 
"boolLib.CONTRAPOS_CONV", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
",", "boolLib.DE_MORGAN_THM", ",", 
hhsRecord.fetch "MULT_EQ_0" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_MULT2" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ZERO_LESS_MULT = store_thm ( "ZERO_LESS_MULT" , ( Parse.Term [ QUOTE " (*#loc 1 40096*)!m n. 0 < m * n = 0 < m /\\ 0 < n" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 40170*)m" ] STRUCT_CASES_TAC num_CASES THEN REWRITE_TAC [ MULT_CLAUSES , LESS_REFL , LESS_0 ] THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 40273*)n" ] STRUCT_CASES_TAC num_CASES THEN REWRITE_TAC [ MULT_CLAUSES , LESS_REFL , LESS_0 , ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ZERO_LESS_MULT" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 40170*)m\"", "]", "boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_REFL", ",", "prim_recTheory.LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 40273*)n\"", "]", "boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_REFL", ",", "prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ZERO_LESS_MULT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ZERO_LESS_ADD = store_thm ( "ZERO_LESS_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 40424*)!m n. 0 < m + n = 0 < m \\/ 0 < n" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 40498*)m" ] STRUCT_CASES_TAC num_CASES THEN REWRITE_TAC [ ADD_CLAUSES , LESS_REFL , LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ZERO_LESS_ADD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 40498*)m\"", "]", "boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_REFL", ",", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "ZERO_LESS_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val FACT = new_recursive_definition { name = "FACT" , rec_axiom = num_Axiom , def = ( Parse.Term [ QUOTE " (*#loc 1 40680*)(FACT 0 = 1) /\\              (FACT (SUC n) = (SUC n) * FACT(n))" ] ) }
;
;
val FACT_LESS = store_thm ( "FACT_LESS" , ( Parse.Term [ QUOTE " (*#loc 1 40794*)!n. 0 < FACT n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN REWRITE_TAC [ FACT , ONE , LESS_SUC_REFL ] THEN MATCH_MP_TAC LESS_MULT2 THEN ASM_REWRITE_TAC [ LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "FACT_LESS" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "FACT" "", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"prim_recTheory.LESS_SUC_REFL", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_MULT2" "( ( DB.fetch \"arithmetic\" \"LESS_MULT2\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "FACT_LESS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = print "Theorems about evenness and oddity\n"
;
val EVEN_ODD = store_thm ( "EVEN_ODD" , ( Parse.Term [ QUOTE " (*#loc 1 41030*)!n. EVEN n = ~ODD n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ EVEN , ODD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_ODD" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "EVEN" "", ",", hhsRecord.fetch "ODD" "", "]" ] )
in hhsRecord.try_record_proof "EVEN_ODD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ODD_EVEN = store_thm ( "ODD_EVEN" , ( Parse.Term [ QUOTE " (*#loc 1 41144*)!n. ODD n = ~(EVEN n)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ EVEN_ODD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ODD_EVEN" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EVEN_ODD" "( ( DB.fetch \"arithmetic\" \"EVEN_ODD\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ODD_EVEN" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EVEN_OR_ODD = store_thm ( "EVEN_OR_ODD" , ( Parse.Term [ QUOTE " (*#loc 1 41245*)!n. EVEN n \\/ ODD n" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ EVEN_ODD , REWRITE_RULE [ DE_MORGAN_THM ] NOT_AND ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_OR_ODD" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EVEN_ODD" "( ( DB.fetch \"arithmetic\" \"EVEN_ODD\" ) )", 
",", "boolLib.REWRITE_RULE", "[", "boolLib.DE_MORGAN_THM", "]", "boolLib.NOT_AND", "]" ] )
in hhsRecord.try_record_proof "EVEN_OR_ODD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EVEN_AND_ODD = store_thm ( "EVEN_AND_ODD" , ( Parse.Term [ QUOTE " (*#loc 1 41383*)!n. ~(EVEN n /\\ ODD n)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ ODD_EVEN , NOT_AND ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_AND_ODD" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ODD_EVEN" "( ( DB.fetch \"arithmetic\" \"ODD_EVEN\" ) )", 
",", "boolLib.NOT_AND", "]" ] )
in hhsRecord.try_record_proof "EVEN_AND_ODD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EVEN_ADD = store_thm ( "EVEN_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 41488*)!m n. EVEN(m + n) = (EVEN m = EVEN n)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , EVEN ] THEN BOOL_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 41609*)EVEN m" ] ) ) THEN REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_ADD" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "EVEN" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.BOOL_CASES_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 41609*)EVEN m\"", "]", ")", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "EVEN_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EVEN_MULT = store_thm ( "EVEN_MULT" , ( Parse.Term [ QUOTE " (*#loc 1 41686*)!m n. EVEN(m * n) = EVEN m \\/ EVEN n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ MULT_CLAUSES , EVEN_ADD , EVEN ] THEN BOOL_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 41817*)EVEN m" ] ) ) THEN REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_MULT" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "EVEN_ADD" "( ( DB.fetch \"arithmetic\" \"EVEN_ADD\" ) )", 
",", hhsRecord.fetch "EVEN" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.BOOL_CASES_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 41817*)EVEN m\"", "]", ")", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "EVEN_MULT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ODD_ADD = store_thm ( "ODD_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 41890*)!m n. ODD(m + n) = ~(ODD m = ODD n)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REWRITE_TAC [ ODD_EVEN , EVEN_ADD ] THEN BOOL_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 42010*)EVEN m" ] ) ) THEN REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ODD_ADD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ODD_EVEN" "( ( DB.fetch \"arithmetic\" \"ODD_EVEN\" ) )", 
",", 
hhsRecord.fetch "EVEN_ADD" "( ( DB.fetch \"arithmetic\" \"EVEN_ADD\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.BOOL_CASES_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 42010*)EVEN m\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"]" ] )
in hhsRecord.try_record_proof "ODD_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ODD_MULT = store_thm ( "ODD_MULT" , ( Parse.Term [ QUOTE " (*#loc 1 42085*)!m n. ODD(m * n) = ODD(m) /\\ ODD(n)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REWRITE_TAC [ ODD_EVEN , EVEN_MULT , DE_MORGAN_THM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ODD_MULT" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ODD_EVEN" "( ( DB.fetch \"arithmetic\" \"ODD_EVEN\" ) )", 
",", 
hhsRecord.fetch "EVEN_MULT" "( ( DB.fetch \"arithmetic\" \"EVEN_MULT\" ) )", 
",", "boolLib.DE_MORGAN_THM", "]" ] )
in hhsRecord.try_record_proof "ODD_MULT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val two = prove ( ( Parse.Term [ QUOTE " (*#loc 1 42219*)2 = SUC 1" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ NUMERAL_DEF , BIT1 , BIT2 ] THEN ONCE_REWRITE_TAC [ SYM ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 42312*)0" ] ) ) NUMERAL_DEF ) ] THEN REWRITE_TAC [ ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_144" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", hhsRecord.fetch "BIT1" "( ( DB.fetch \"arithmetic\" \"BIT1\" ) )", ",", 
hhsRecord.fetch "BIT2" "( ( DB.fetch \"arithmetic\" \"BIT2\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ONCE_REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 42312*)0\"", "]", ")", ")", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_144" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EVEN_DOUBLE = store_thm ( "EVEN_DOUBLE" , ( Parse.Term [ QUOTE " (*#loc 1 42416*)!n. EVEN(2 * n)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN REWRITE_TAC [ EVEN_MULT ] THEN DISJ1_TAC THEN REWRITE_TAC [ EVEN , ONE , two ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_DOUBLE" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EVEN_MULT" "( ( DB.fetch \"arithmetic\" \"EVEN_MULT\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISJ1_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EVEN" "", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "two" "", "]" ] )
in hhsRecord.try_record_proof "EVEN_DOUBLE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ODD_DOUBLE = store_thm ( "ODD_DOUBLE" , ( Parse.Term [ QUOTE " (*#loc 1 42573*)!n. ODD(SUC(2 * n))" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ ODD ] THEN REWRITE_TAC [ GSYM EVEN_ODD , EVEN_DOUBLE ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ODD_DOUBLE" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", hhsRecord.fetch "ODD" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.GSYM", 
hhsRecord.fetch "EVEN_ODD" "( ( DB.fetch \"arithmetic\" \"EVEN_ODD\" ) )", 
",", 
hhsRecord.fetch "EVEN_DOUBLE" "( ( DB.fetch \"arithmetic\" \"EVEN_DOUBLE\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ODD_DOUBLE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EVEN_ODD_EXISTS = store_thm ( "EVEN_ODD_EXISTS" , ( Parse.Term [ QUOTE " (*#loc 1 42720*)!n. (EVEN n ==> ?m. n = 2 * m) /\\ (ODD n ==> ?m. n = SUC(2 * m))" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ ODD_EVEN ] THEN INDUCT_TAC THEN REWRITE_TAC [ EVEN ] THENL [ EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 42877*)0" ] ) ) THEN REWRITE_TAC [ MULT_CLAUSES ] , POP_ASSUM STRIP_ASSUME_TAC THEN CONJ_TAC THEN DISCH_THEN ( fn th => FIRST_ASSUM ( X_CHOOSE_THEN ( ( Parse.Term [ QUOTE " (*#loc 1 43019*)m:num" ] ) ) SUBST1_TAC o C MATCH_MP th ) ) THENL [ EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 43105*)SUC m" ] ) ) THEN REWRITE_TAC [ ONE , two , MULT_CLAUSES , ADD_CLAUSES ] , EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 43197*)m:num" ] ) ) THEN REFL_TAC ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_ODD_EXISTS" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ODD_EVEN" "( ( DB.fetch \"arithmetic\" \"ODD_EVEN\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EVEN" "", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.EXISTS_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 42877*)0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", ",", "boolLib.POP_ASSUM", "boolLib.STRIP_ASSUME_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"fn", "th", "=>", "boolLib.FIRST_ASSUM", "(", "boolLib.X_CHOOSE_THEN", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 43019*)m:num\"", "]", ")", ")", 
"boolLib.SUBST1_TAC", "o", "HolKernel.C", "boolLib.MATCH_MP", "th", ")", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.EXISTS_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 43105*)SUC m\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "two" "", ",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 43197*)m:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REFL_TAC", "]", "]" ] )
in hhsRecord.try_record_proof "EVEN_ODD_EXISTS" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val EVEN_EXISTS = store_thm ( "EVEN_EXISTS" , ( Parse.Term [ QUOTE " (*#loc 1 43274*)!n. EVEN n = ?m. n = 2 * m" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN EQ_TAC THENL [ REWRITE_TAC [ EVEN_ODD_EXISTS ] , DISCH_THEN ( CHOOSE_THEN SUBST1_TAC ) THEN MATCH_ACCEPT_TAC EVEN_DOUBLE ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_EXISTS" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.EQ_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EVEN_ODD_EXISTS" "( ( DB.fetch \"arithmetic\" \"EVEN_ODD_EXISTS\" ) )", 
"]", ",", "boolLib.DISCH_THEN", "(", "boolLib.CHOOSE_THEN", "boolLib.SUBST1_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_ACCEPT_TAC", 
hhsRecord.fetch "EVEN_DOUBLE" "( ( DB.fetch \"arithmetic\" \"EVEN_DOUBLE\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EVEN_EXISTS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ODD_EXISTS = store_thm ( "ODD_EXISTS" , ( Parse.Term [ QUOTE " (*#loc 1 43490*)!n. ODD n = ?m. n = SUC(2 * m)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN EQ_TAC THENL [ REWRITE_TAC [ EVEN_ODD_EXISTS ] , DISCH_THEN ( CHOOSE_THEN SUBST1_TAC ) THEN MATCH_ACCEPT_TAC ODD_DOUBLE ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ODD_EXISTS" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.EQ_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EVEN_ODD_EXISTS" "( ( DB.fetch \"arithmetic\" \"EVEN_ODD_EXISTS\" ) )", 
"]", ",", "boolLib.DISCH_THEN", "(", "boolLib.CHOOSE_THEN", "boolLib.SUBST1_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_ACCEPT_TAC", 
hhsRecord.fetch "ODD_DOUBLE" "( ( DB.fetch \"arithmetic\" \"ODD_DOUBLE\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ODD_EXISTS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EVEN_EXP_IFF = Q.store_thm ( "EVEN_EXP_IFF" , [ QUOTE " (*#loc 1 43715*)!n m. EVEN (m ** n) <=> 0 < n /\\ EVEN m" ] ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ EXP , ONE , EVEN , EVEN_MULT , LESS_0 , LESS_REFL ] THEN GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_EXP_IFF" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "EVEN" "", ",", 
hhsRecord.fetch "EVEN_MULT" "( ( DB.fetch \"arithmetic\" \"EVEN_MULT\" ) )", 
",", "prim_recTheory.LESS_0", ",", "prim_recTheory.LESS_REFL", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "EVEN_EXP_IFF" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EVEN_EXP = Q.store_thm ( "EVEN_EXP" , [ QUOTE " (*#loc 1 43952*)!m n. 0 < n /\\ EVEN m ==> EVEN (m ** n)" ] ,
let
val tactictoe_tac1 = METIS_TAC [ EVEN_EXP_IFF ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_EXP" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "EVEN_EXP_IFF" "( ( DB.fetch \"arithmetic\" \"EVEN_EXP_IFF\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EVEN_EXP" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ODD_EXP_IFF = Q.store_thm ( "ODD_EXP_IFF" , [ QUOTE " (*#loc 1 44074*)!n m. ODD (m ** n) <=> (n = 0) \\/ ODD m" ] ,
let
val tactictoe_tac1 = REWRITE_TAC [ ODD_EVEN , EVEN_EXP_IFF , DE_MORGAN_THM , NOT_LT_ZERO_EQ_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ODD_EXP_IFF" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ODD_EVEN" "( ( DB.fetch \"arithmetic\" \"ODD_EVEN\" ) )", 
",", 
hhsRecord.fetch "EVEN_EXP_IFF" "( ( DB.fetch \"arithmetic\" \"EVEN_EXP_IFF\" ) )", 
",", "boolLib.DE_MORGAN_THM", ",", 
hhsRecord.fetch "NOT_LT_ZERO_EQ_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_LT_ZERO_EQ_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ODD_EXP_IFF" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ODD_EXP = Q.store_thm ( "ODD_EXP" , [ QUOTE " (*#loc 1 44236*)!m n. 0 < n /\\ ODD m ==> ODD (m ** n)" ] ,
let
val tactictoe_tac1 = METIS_TAC [ ODD_EXP_IFF , NOT_LT_ZERO_EQ_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ODD_EXP" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "ODD_EXP_IFF" "( ( DB.fetch \"arithmetic\" \"ODD_EXP_IFF\" ) )", 
",", 
hhsRecord.fetch "NOT_LT_ZERO_EQ_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_LT_ZERO_EQ_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ODD_EXP" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EQ_LESS_EQ = store_thm ( "EQ_LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 44375*)!m n. (m = n) = ((m <= n) /\\ (n <= m))" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN EQ_TAC THENL [ STRIP_TAC THEN ASM_REWRITE_TAC [ LESS_EQ_REFL ] , REWRITE_TAC [ LESS_EQUAL_ANTISYM ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EQ_LESS_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
"]", ",", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "EQ_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_MONO_LESS_EQ = store_thm ( "ADD_MONO_LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 44613*)!m n p. (m + n) <= (m + p) = (n <= p)" ] ) ,
let
val tactictoe_tac1 = ONCE_REWRITE_TAC [ ADD_SYM ] THEN REWRITE_TAC [ LESS_EQ_MONO_ADD_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_MONO_LESS_EQ" 
 ( String.concatWith " " 
 [ "boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_EQ_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO_ADD_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ADD_MONO_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LE_ADD_LCANCEL = save_thm ( "LE_ADD_LCANCEL" , ADD_MONO_LESS_EQ )
;
val LE_ADD_RCANCEL = save_thm ( "LE_ADD_RCANCEL" , ONCE_REWRITE_RULE [ ADD_COMM ] LE_ADD_LCANCEL )
;
val _ = print "Theorems to support the arithmetic proof procedure\n"
;
val NOT_LEQ = store_thm ( "NOT_LEQ" , ( Parse.Term [ QUOTE " (*#loc 1 45035*)!m n. ~(m <= n) = (SUC n) <= m" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ SYM ( SPEC_ALL LESS_EQ ) ] THEN REWRITE_TAC [ SYM ( SPEC_ALL NOT_LESS ) ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_LEQ" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", ")", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
")", "]" ] )
in hhsRecord.try_record_proof "NOT_LEQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_NUM_EQ = store_thm ( "NOT_NUM_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 45206*)!m n. ~(m = n) = (((SUC m) <= n) \\/ ((SUC n) <= m))" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ EQ_LESS_EQ , DE_MORGAN_THM , NOT_LEQ ] THEN MATCH_ACCEPT_TAC DISJ_SYM
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_NUM_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EQ_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"EQ_LESS_EQ\" ) )", 
",", "boolLib.DE_MORGAN_THM", ",", 
hhsRecord.fetch "NOT_LEQ" "( ( DB.fetch \"arithmetic\" \"NOT_LEQ\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_ACCEPT_TAC", 
"boolLib.DISJ_SYM" ] )
in hhsRecord.try_record_proof "NOT_NUM_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_GREATER = store_thm ( "NOT_GREATER" , ( Parse.Term [ QUOTE " (*#loc 1 45398*)!m n. ~(m > n) = (m <= n)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ GREATER_DEF , NOT_LESS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_GREATER" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "GREATER_DEF" "( ( DB.fetch \"arithmetic\" \"GREATER_DEF\" ) )", 
",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "NOT_GREATER" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_GREATER_EQ = store_thm ( "NOT_GREATER_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 45524*)!m n. ~(m >= n) = (SUC m) <= n" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ GREATER_EQ , NOT_LEQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_GREATER_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "GREATER_EQ" "( ( DB.fetch \"arithmetic\" \"GREATER_EQ\" ) )", 
",", hhsRecord.fetch "NOT_LEQ" "( ( DB.fetch \"arithmetic\" \"NOT_LEQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "NOT_GREATER_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUC_ONE_ADD = store_thm ( "SUC_ONE_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 45647*)!n. SUC n = 1 + n" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN ONCE_REWRITE_TAC [ ADD1 , ADD_SYM ] THEN REFL_TAC
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUC_ONE_ADD" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", ",", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REFL_TAC" ] )
in hhsRecord.try_record_proof "SUC_ONE_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUC_ADD_SYM = store_thm ( "SUC_ADD_SYM" , ( Parse.Term [ QUOTE " (*#loc 1 45789*)!m n. SUC (m + n) = (SUC n) + m" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REWRITE_TAC [ ADD_CLAUSES ] THEN AP_TERM_TAC THEN ACCEPT_TAC ( SPEC_ALL ADD_SYM )
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUC_ADD_SYM" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.AP_TERM_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ACCEPT_TAC", "(", 
"boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", ")" ] )
in hhsRecord.try_record_proof "SUC_ADD_SYM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_SUC_ADD_LESS_EQ = store_thm ( "NOT_SUC_ADD_LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 46002*)!m n. ~(SUC (m + n) <= m)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REWRITE_TAC [ SYM ( SPEC_ALL LESS_EQ ) ] THEN REWRITE_TAC [ NOT_LESS , LESS_EQ_ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_SUC_ADD_LESS_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", ")", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "NOT_SUC_ADD_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_LESS_EQ_SUC =
let
val th1 = SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 46189*)b:num" ] ) ) ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 46209*)c:num" ] ) ) ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 46229*)a:num" ] ) ) LESS_MONO_ADD ) )
;
val th2 = SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 46303*)c:num" ] ) ) ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 46323*)d:num" ] ) ) ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 46343*)b:num" ] ) ) LESS_MONO_ADD ) )
;
val th3 = ONCE_REWRITE_RULE [ ADD_SYM ] th2
;
val th4 = CONJ ( UNDISCH_ALL th1 ) ( UNDISCH_ALL th3 )
;
val th5 = MATCH_MP LESS_TRANS th4
;
val th6 = DISCH_ALL th5
;
in store_thm ( "MULT_LESS_EQ_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 46616*)!m n p. m <= n = ((SUC p) * m) <= ((SUC p) * n)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN EQ_TAC THENL [ ONCE_REWRITE_TAC [ MULT_SYM ] THEN REWRITE_TAC [ LESS_MONO_MULT ] , CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [ SYM ( SPEC_ALL NOT_LESS ) ] THEN SPEC_TAC ( ( ( Parse.Term [ QUOTE " (*#loc 1 46876*)p:num" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 46890*)p:num" ] ) ) ) THEN INDUCT_TAC THENL [ REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES ] , STRIP_TAC THEN RES_TAC THEN ONCE_REWRITE_TAC [ MULT_CLAUSES ] THEN IMP_RES_TAC th6 ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_LESS_EQ_SUC" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_SYM" "( ( DB.fetch \"arithmetic\" \"MULT_SYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_MONO_MULT" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_MULT\" ) )", 
"]", ",", "boolLib.CONV_TAC", "boolLib.CONTRAPOS_CONV", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SPEC_TAC", 
"(", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 46876*)p:num\"", "]", ")", 
")", ",", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 46890*)p:num\"", "]", 
")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.RES_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "th6" "( boolLib.DISCH_ALL ( boolLib.MATCH_MP ( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) ) ( HolKernel.CONJ ( boolLib.UNDISCH_ALL ( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 46189*)b:num\" ] ) ) ( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 46209*)c:num\" ] ) ) ( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 46229*)a:num\" ] ) ) ( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD\" ) ) ) ) ) ) ( boolLib.UNDISCH_ALL ( boolLib.ONCE_REWRITE_RULE [ ( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) ) ] ( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 46303*)c:num\" ] ) ) ( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 46323*)d:num\" ] ) ) ( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 46343*)b:num\" ] ) ) ( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD\" ) ) ) ) ) ) ) ) ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "MULT_LESS_EQ_SUC" false tactictoe_tac2 tactictoe_tac1
end )
end
;
;
val LE_MULT_LCANCEL = store_thm ( "LE_MULT_LCANCEL" , ( Parse.Term [ QUOTE " (*#loc 1 47141*)!m n p. m * n <= m * p = (m = 0) \\/ n <= p" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 47225*)m" ] STRUCT_CASES_TAC num_CASES THENL [ REWRITE_TAC [ LESS_EQ_REFL , MULT_CLAUSES ] , REWRITE_TAC [ NOT_SUC , GSYM MULT_LESS_EQ_SUC ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LE_MULT_LCANCEL" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 47225*)m\"", "]", "boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", ",", "boolLib.REWRITE_TAC", "[", "numTheory.NOT_SUC", ",", "boolLib.GSYM", 
hhsRecord.fetch "MULT_LESS_EQ_SUC" "( ( ( DB.fetch \"arithmetic\" \"MULT_LESS_EQ_SUC\" ) ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "LE_MULT_LCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LE_MULT_RCANCEL = store_thm ( "LE_MULT_RCANCEL" , ( Parse.Term [ QUOTE " (*#loc 1 47422*)!m n p. m * n <= p * n = (n = 0) \\/ m <= p" ] ) ,
let
val tactictoe_tac1 = ONCE_REWRITE_TAC [ MULT_COMM ] THEN REWRITE_TAC [ LE_MULT_LCANCEL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LE_MULT_RCANCEL" 
 ( String.concatWith " " 
 [ "boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "LE_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_LCANCEL\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LE_MULT_RCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LT_MULT_LCANCEL = store_thm ( "LT_MULT_LCANCEL" , ( Parse.Term [ QUOTE " (*#loc 1 47594*)!m n p. m * n < m * p = 0 < m /\\ n < p" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 47674*)m" ] STRUCT_CASES_TAC num_CASES THENL [ REWRITE_TAC [ MULT_CLAUSES , LESS_REFL ] , REWRITE_TAC [ LESS_MULT_MONO , LESS_0 ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LT_MULT_LCANCEL" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 47674*)m\"", "]", "boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_REFL", "]", ",", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_MULT_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_MULT_MONO\" ) )", 
",", "prim_recTheory.LESS_0", "]", "]" ] )
in hhsRecord.try_record_proof "LT_MULT_LCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LT_MULT_RCANCEL = store_thm ( "LT_MULT_RCANCEL" , ( Parse.Term [ QUOTE " (*#loc 1 47859*)!m n p. m * n < p * n = 0 < n /\\ m < p" ] ) ,
let
val tactictoe_tac1 = ONCE_REWRITE_TAC [ MULT_COMM ] THEN REWRITE_TAC [ LT_MULT_LCANCEL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LT_MULT_RCANCEL" 
 ( String.concatWith " " 
 [ "boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "LT_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_MULT_LCANCEL\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LT_MULT_RCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LT_MULT_CANCEL_LBARE = save_thm ( "LT_MULT_CANCEL_LBARE" , CONJ ( REWRITE_RULE [ MULT_CLAUSES ] ( Q.SPECL [ [ QUOTE " (*#loc 1 48086*)m" ] , [ QUOTE " (*#loc 1 48091*)1" ] , [ QUOTE " (*#loc 1 48096*)n" ] ] LT_MULT_LCANCEL ) ) ( REWRITE_RULE [ MULT_CLAUSES ] ( Q.SPECL [ [ QUOTE " (*#loc 1 48162*)1" ] , [ QUOTE " (*#loc 1 48166*)m" ] , [ QUOTE " (*#loc 1 48171*)n" ] ] LT_MULT_RCANCEL ) ) )
;
val lt1_eq0 = prove ( ( Parse.Term [ QUOTE " (*#loc 1 48220*)x < 1 = (x = 0)" ] ) ,
let
val tactictoe_tac1 = Q.SPEC_THEN [ QUOTE " (*#loc 1 48255*)x" ] STRUCT_CASES_TAC num_CASES THEN REWRITE_TAC [ ONE , LESS_0 , NOT_LESS_0 , LESS_MONO_EQ , NOT_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_168" 
 ( String.concatWith " " 
 [ "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 48255*)x\"", "]", 
"boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"prim_recTheory.LESS_0", ",", "prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", "numTheory.NOT_SUC", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_168" false tactictoe_tac2 tactictoe_tac1
end )
;
val LT_MULT_CANCEL_RBARE = save_thm ( "LT_MULT_CANCEL_RBARE" , CONJ ( REWRITE_RULE [ MULT_CLAUSES , lt1_eq0 ] ( Q.SPECL [ [ QUOTE " (*#loc 1 48498*)m" ] , [ QUOTE " (*#loc 1 48502*)n" ] , [ QUOTE " (*#loc 1 48506*)1" ] ] LT_MULT_LCANCEL ) ) ( REWRITE_RULE [ MULT_CLAUSES , lt1_eq0 ] ( Q.SPECL [ [ QUOTE " (*#loc 1 48599*)m" ] , [ QUOTE " (*#loc 1 48603*)n" ] , [ QUOTE " (*#loc 1 48607*)1" ] ] LT_MULT_RCANCEL ) ) )
;
val le1_lt0 = prove ( ( Parse.Term [ QUOTE " (*#loc 1 48653*)1 <= n = 0 < n" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_EQ , ONE ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_169" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_169" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LE_MULT_CANCEL_LBARE = save_thm ( "LE_MULT_CANCEL_LBARE" , CONJ ( REWRITE_RULE [ MULT_CLAUSES , le1_lt0 ] ( Q.SPECL [ [ QUOTE " (*#loc 1 48844*)m" ] , [ QUOTE " (*#loc 1 48848*)1" ] , [ QUOTE " (*#loc 1 48852*)n" ] ] LE_MULT_LCANCEL ) ) ( REWRITE_RULE [ MULT_CLAUSES , le1_lt0 ] ( Q.SPECL [ [ QUOTE " (*#loc 1 48945*)1" ] , [ QUOTE " (*#loc 1 48949*)m" ] , [ QUOTE " (*#loc 1 48953*)n" ] ] LE_MULT_RCANCEL ) ) )
;
val LE_MULT_CANCEL_RBARE = save_thm ( "LE_MULT_CANCEL_RBARE" , CONJ ( REWRITE_RULE [ MULT_CLAUSES ] ( Q.SPECL [ [ QUOTE " (*#loc 1 49092*)m" ] , [ QUOTE " (*#loc 1 49096*)n" ] , [ QUOTE " (*#loc 1 49100*)1" ] ] LE_MULT_LCANCEL ) ) ( REWRITE_RULE [ MULT_CLAUSES ] ( Q.SPECL [ [ QUOTE " (*#loc 1 49166*)m" ] , [ QUOTE " (*#loc 1 49170*)n" ] , [ QUOTE " (*#loc 1 49174*)1" ] ] LE_MULT_RCANCEL ) ) )
;
val SUB_LEFT_ADD = store_thm ( "SUB_LEFT_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 49249*)!m n p. m + (n - p) = (if (n <= p) then m else (m + n) - p)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_0 , SUB_MONO_EQ , ZERO_LESS_EQ , NOT_SUC_LESS_EQ_0 , LESS_EQ_MONO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LEFT_ADD" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_LEFT_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_RIGHT_ADD = store_thm ( "SUB_RIGHT_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 49514*)!m n p. (m - n) + p = (if (m <= n) then p else (m + p) - n)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_0 , SUB_MONO_EQ , ZERO_LESS_EQ , NOT_SUC_LESS_EQ_0 , LESS_EQ_MONO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_RIGHT_ADD" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_RIGHT_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LEFT_SUB = store_thm ( "SUB_LEFT_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 49773*)!m n p. m - (n - p) = (if (n <= p) then m else (m + p) - n)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_0 , SUB_MONO_EQ , ZERO_LESS_EQ , NOT_SUC_LESS_EQ_0 , LESS_EQ_MONO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LEFT_SUB" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_LEFT_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_RIGHT_SUB = store_thm ( "SUB_RIGHT_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 50038*)!m n p. (m - n) - p = m - (n + p)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ SUB_0 , ADD_CLAUSES , SUB_MONO_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_RIGHT_SUB" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_RIGHT_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LEFT_SUC = store_thm ( "SUB_LEFT_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 50217*)!m n. SUC (m - n) = (if (m <= n) then (SUC 0) else (SUC m) - n)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 50329*)m <= n" ] ) ) THENL [ IMP_RES_THEN ( fn th => ASM_REWRITE_TAC [ th ] ) ( SYM ( SPEC_ALL SUB_EQ_0 ) ) , ASM_REWRITE_TAC [ SUB ] THEN ASSUM_LIST ( MAP_EVERY ( REWRITE_TAC o CONJUNCTS o ( PURE_REWRITE_RULE [ LESS_OR_EQ , DE_MORGAN_THM ] ) ) ) ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LEFT_SUC" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_CASES_TAC", "(", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 50329*)m <= n\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.IMP_RES_THEN", 
"(", "fn", "th", "=>", "boolLib.ASM_REWRITE_TAC", "[", "th", "]", ")", "(", "HolKernel.SYM", "(", 
"boolLib.SPEC_ALL", 
hhsRecord.fetch "SUB_EQ_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQ_0\" ) )", 
")", ")", ",", "boolLib.ASM_REWRITE_TAC", "[", hhsRecord.fetch "SUB" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASSUM_LIST", "(", 
"boolLib.MAP_EVERY", "(", "boolLib.REWRITE_TAC", "o", "boolLib.CONJUNCTS", "o", "(", 
"boolLib.PURE_REWRITE_RULE", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", "boolLib.DE_MORGAN_THM", "]", ")", ")", ")", "]" ] )
in hhsRecord.try_record_proof "SUB_LEFT_SUC" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val pls = prove ( ( Parse.Term [ QUOTE " (*#loc 1 50605*)p <= m \\/ p <= 0 = p <= m" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_EQ_0 ] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [ ZERO_LESS_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_175" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_175" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LEFT_LESS_EQ = store_thm ( "SUB_LEFT_LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 50801*)!m n p. (m <= (n - p)) = ((m + p) <= n) \\/ (m <= 0)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , SUB_0 , SUB_MONO_EQ , pls , ZERO_LESS_EQ , NOT_SUC_LESS_EQ_0 , LESS_EQ_MONO , NOT_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LEFT_LESS_EQ" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", hhsRecord.fetch "pls" "", ",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", "numTheory.NOT_SUC", "]" ] )
in hhsRecord.try_record_proof "SUB_LEFT_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_RIGHT_LESS_EQ = store_thm ( "SUB_RIGHT_LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 51080*)!m n p. ((m - n) <= p) = (m <= (n + p))" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ SUB_0 , ADD_CLAUSES , SUB_MONO_EQ , LESS_EQ_MONO , ZERO_LESS_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_RIGHT_LESS_EQ" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_RIGHT_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LEFT_LESS = store_thm ( "SUB_LEFT_LESS" , ( Parse.Term [ QUOTE " (*#loc 1 51301*)!m n p. (m < (n - p)) = ((m + p) < n)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN PURE_REWRITE_TAC [ LESS_EQ , SYM ( SPEC_ALL ( CONJUNCT2 ADD ) ) ] THEN PURE_ONCE_REWRITE_TAC [ SUB_LEFT_LESS_EQ ] THEN REWRITE_TAC [ SYM ( SPEC_ALL LESS_EQ ) , NOT_LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LEFT_LESS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.PURE_REWRITE_TAC", 
"[", hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", 
",", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", "(", "HolKernel.CONJUNCT2", 
hhsRecord.fetch "ADD" "", ")", ")", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "SUB_LEFT_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_LESS_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", ")", 
",", "prim_recTheory.NOT_LESS_0", "]" ] )
in hhsRecord.try_record_proof "SUB_LEFT_LESS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_RIGHT_LESS =
let
val BOOL_EQ_NOT_BOOL_EQ = prove ( ( Parse.Term [ QUOTE " (*#loc 1 51606*)!x y. (x = y) = (~x = ~y)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN BOOL_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 51691*)x:bool" ] ) ) THEN REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_179" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.BOOL_CASES_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 51691*)x:bool\"", "]", ")", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_179" false tactictoe_tac2 tactictoe_tac1
end )
;
in store_thm ( "SUB_RIGHT_LESS" , ( Parse.Term [ QUOTE " (*#loc 1 51775*)!m n p. ((m - n) < p) = ((m < (n + p)) /\\ (0 < p))" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [ BOOL_EQ_NOT_BOOL_EQ ] THEN PURE_REWRITE_TAC [ DE_MORGAN_THM , NOT_LESS ] THEN SUBST1_TAC ( SPECL [ ( ( Parse.Term [ QUOTE " (*#loc 1 51981*)n:num" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 51995*)p:num" ] ) ) ] ADD_SYM ) THEN REWRITE_TAC [ SUB_LEFT_LESS_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_RIGHT_LESS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", hhsRecord.fetch "BOOL_EQ_NOT_BOOL_EQ" "", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_REWRITE_TAC", "[", "boolLib.DE_MORGAN_THM", ",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUBST1_TAC", "(", 
"boolLib.SPECL", "[", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 51981*)n:num\"", "]", ")", ")", ",", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 51995*)p:num\"", "]", ")", ")", "]", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "SUB_LEFT_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_LESS_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_RIGHT_LESS" false tactictoe_tac2 tactictoe_tac1
end )
end
;
;
val SUB_LEFT_GREATER_EQ = store_thm ( "SUB_LEFT_GREATER_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 52129*)!m n p. (m >= (n - p)) = ((m + p) >= n)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ GREATER_EQ ] THEN GEN_TAC THEN REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ SUB_0 , ADD_CLAUSES , SUB_MONO_EQ , LESS_EQ_MONO , ZERO_LESS_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LEFT_GREATER_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "GREATER_EQ" "( ( DB.fetch \"arithmetic\" \"GREATER_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_LEFT_GREATER_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_RIGHT_GREATER_EQ = store_thm ( "SUB_RIGHT_GREATER_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 52401*)!m n p. ((m - n) >= p) = ((m >= (n + p)) \\/ (0 >= p))" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ GREATER_EQ ] THEN INDUCT_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ SUB_0 , ADD_CLAUSES , SUB_MONO_EQ , LESS_EQ_MONO , ZERO_LESS_EQ , NOT_SUC_LESS_EQ_0 , pls ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_RIGHT_GREATER_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "GREATER_EQ" "( ( DB.fetch \"arithmetic\" \"GREATER_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", hhsRecord.fetch "pls" "", "]" ] )
in hhsRecord.try_record_proof "SUB_RIGHT_GREATER_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LEFT_GREATER = store_thm ( "SUB_LEFT_GREATER" , ( Parse.Term [ QUOTE " (*#loc 1 52699*)!m n p. (m > (n - p)) = (((m + p) > n) /\\ (m > 0))" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [ GREATER_DEF ] THEN SUBST1_TAC ( SPECL [ ( ( Parse.Term [ QUOTE " (*#loc 1 52847*)m:num" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 52861*)p:num" ] ) ) ] ADD_SYM ) THEN REWRITE_TAC [ SUB_RIGHT_LESS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LEFT_GREATER" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "GREATER_DEF" "( ( DB.fetch \"arithmetic\" \"GREATER_DEF\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUBST1_TAC", "(", 
"boolLib.SPECL", "[", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 52847*)m:num\"", "]", ")", ")", ",", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 52861*)p:num\"", "]", ")", ")", "]", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "SUB_RIGHT_LESS" "( ( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_LESS\" ) ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_LEFT_GREATER" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_RIGHT_GREATER = store_thm ( "SUB_RIGHT_GREATER" , ( Parse.Term [ QUOTE " (*#loc 1 52982*)!m n p. ((m - n) > p) = (m > (n + p))" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [ GREATER_DEF ] THEN SUBST1_TAC ( SPECL [ ( ( Parse.Term [ QUOTE " (*#loc 1 53117*)n:num" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 53131*)p:num" ] ) ) ] ADD_SYM ) THEN REWRITE_TAC [ SUB_LEFT_LESS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_RIGHT_GREATER" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "GREATER_DEF" "( ( DB.fetch \"arithmetic\" \"GREATER_DEF\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUBST1_TAC", "(", 
"boolLib.SPECL", "[", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 53117*)n:num\"", "]", ")", ")", ",", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 53131*)p:num\"", "]", ")", ")", "]", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "SUB_LEFT_LESS" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_LESS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_RIGHT_GREATER" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LEFT_EQ = store_thm ( "SUB_LEFT_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 53239*)!m n p. (m = (n - p)) = ((m + p) = n) \\/ ((m <= 0) /\\ (n <= p))" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ SUB_0 , ADD_CLAUSES , INV_SUC_EQ , SUB_MONO_EQ , LESS_EQ_MONO , ZERO_LESS_EQ , LESS_EQ_0 , NOT_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LEFT_EQ" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
",", "numTheory.NOT_SUC", "]" ] )
in hhsRecord.try_record_proof "SUB_LEFT_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_RIGHT_EQ = store_thm ( "SUB_RIGHT_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 53518*)!m n p. ((m - n) = p) = (m = (n + p)) \\/ ((m <= n) /\\ (p <= 0))" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN INDUCT_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC [ SUB_0 , ADD_CLAUSES , INV_SUC_EQ , SUB_EQ_0 , SUB_MONO_EQ , LESS_EQ_MONO , ZERO_LESS_EQ , LESS_EQ_0 , NOT_SUC , GSYM NOT_SUC ] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_RIGHT_EQ" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", ",", 
hhsRecord.fetch "SUB_EQ_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQ_0\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
",", "numTheory.NOT_SUC", ",", "boolLib.GSYM", "numTheory.NOT_SUC", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]" ] )
in hhsRecord.try_record_proof "SUB_RIGHT_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LE = save_thm ( "LE" , CONJ LESS_EQ_0 ( prove ( ( Parse.Term [ QUOTE " (*#loc 1 53898*)(!m n. m <= SUC n = (m = SUC n) \\/ m <= n)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN CONV_TAC ( DEPTH_CONV ( LHS_CONV ( REWR_CONV LESS_OR_EQ ) ) ) THEN REWRITE_TAC [ GSYM LESS_EQ_IFF_LESS_SUC ] THEN MATCH_ACCEPT_TAC DISJ_COMM
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_187" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", "(", 
"boolLib.DEPTH_CONV", "(", "boolLib.LHS_CONV", "(", "boolLib.REWR_CONV", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "LESS_EQ_IFF_LESS_SUC" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_IFF_LESS_SUC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_ACCEPT_TAC", "boolLib.DISJ_COMM" ] )
in hhsRecord.try_record_proof "tactictoe_prove_187" false tactictoe_tac2 tactictoe_tac1
end ) ) )
;
;
val _ = print "Proving division\n"
;
val exists_lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 54186*)?r q. (k=(q*n)+r)" ] ) ,
let
val tactictoe_tac1 = MAP_EVERY EXISTS_TAC [ ( Parse.Term [ QUOTE " (*#loc 1 54236*)k:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 54248*)0" ] ) ] THEN REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_188" 
 ( String.concatWith " " 
 [ "boolLib.MAP_EVERY", "boolLib.EXISTS_TAC", "[", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 54236*)k:num\"", "]", ")", ",", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 54248*)0\"", "]", ")", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_188" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val smallest_lemma = CONV_RULE ( DEPTH_CONV NOT_EXISTS_CONV ) ( MATCH_MP ( CONV_RULE ( DEPTH_CONV BETA_CONV ) ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 54477*)\\r.?q.k=(q*n)+r" ] ) ) WOP ) ) exists_lemma )
;
;
val leq_add_lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 54577*)!m n. (n<=m) ==> ?p.m=n+p" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_OR_EQ ] THEN REPEAT STRIP_TAC THENL [ FIRST_ASSUM ( STRIP_ASSUME_TAC o MATCH_MP LESS_ADD_1 ) THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 54751*)p+1" ] ) ) THEN FIRST_ASSUM ACCEPT_TAC , EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 54813*)0" ] ) ) THEN ASM_REWRITE_TAC [ ADD_CLAUSES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_189" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.FIRST_ASSUM", "(", "boolLib.STRIP_ASSUME_TAC", "o", "boolLib.MATCH_MP", 
hhsRecord.fetch "LESS_ADD_1" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_1\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 54751*)p+1\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ",", "boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 54813*)0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_189" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val k_expr_lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 54895*)(k=(q*n)+(n+p)) ==> (k=((q+1)*n)+p)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ RIGHT_ADD_DISTRIB , MULT_CLAUSES , ADD_ASSOC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_190" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_190" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val less_add = TAC_PROOF ( ( [ ( Parse.Term [ QUOTE " (*#loc 1 55026*)0<n" ] ) ] , ( Parse.Term [ QUOTE " (*#loc 1 55038*)p < (n + p)" ] ) ) ,
let
val tactictoe_tac1 = PURE_ONCE_REWRITE_TAC [ ADD_SYM ] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN IMP_RES_THEN ( STRIP_THM_THEN SUBST1_TAC ) LESS_ADD_1 THEN REWRITE_TAC [ ADD_CLAUSES , ONE , NOT_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_191" 
 ( String.concatWith " " 
 [ "boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_ADD_NONZERO" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_NONZERO\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.STRIP_THM_THEN", "boolLib.SUBST1_TAC", ")", 
hhsRecord.fetch "LESS_ADD_1" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_1\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"numTheory.NOT_SUC", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_191" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DA = store_thm ( "DA" , ( Parse.Term [ QUOTE " (*#loc 1 55268*)!k n. 0<n ==> ?r q. (k=(q*n)+r) /\\ r<n" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC smallest_lemma THEN MAP_EVERY EXISTS_TAC [ ( Parse.Term [ QUOTE " (*#loc 1 55404*)n':num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 55417*)q:num" ] ) ] THEN ASM_REWRITE_TAC [ ] THEN DISJ_CASES_THEN CHECK_ASSUME_TAC ( SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 55525*)n':num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 55538*)n:num" ] ) ] LESS_CASES ) THEN IMP_RES_THEN ( STRIP_THM_THEN SUBST_ALL_TAC ) leq_add_lemma THEN IMP_RES_TAC k_expr_lemma THEN ANTE_RES_THEN IMP_RES_TAC less_add
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DA" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_ASSUME_TAC", 
hhsRecord.fetch "smallest_lemma" "", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MAP_EVERY", 
"boolLib.EXISTS_TAC", "[", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 55404*)n':num\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 55417*)q:num\"", "]", ")", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.DISJ_CASES_THEN", "boolLib.CHECK_ASSUME_TAC", "(", "boolLib.SPECL", "[", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 55525*)n':num\"", "]", ")", ",", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 55538*)n:num\"", "]", ")", "]", 
hhsRecord.fetch "LESS_CASES" "( ( DB.fetch \"arithmetic\" \"LESS_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", 
"(", "boolLib.STRIP_THM_THEN", "boolLib.SUBST_ALL_TAC", ")", 
hhsRecord.fetch "leq_add_lemma" "", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "k_expr_lemma" "", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ANTE_RES_THEN", 
"boolLib.IMP_RES_TAC", hhsRecord.fetch "less_add" "" ] )
in hhsRecord.try_record_proof "DA" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_exists = prove ( ( Parse.Term [ QUOTE " (*#loc 1 55740*)?MOD. !n. (0<n) ==>                !k.?q.(k=((q * n)+(MOD k n))) /\\ ((MOD k n) < n)" ] ) ,
let
val tactictoe_tac1 = EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 55846*)\\k n. @r. ?q. (k = (q * n) + r) /\\ r < n" ] ) ) THEN REPEAT STRIP_TAC THEN IMP_RES_THEN ( STRIP_ASSUME_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 55966*)k:num" ] ) ) ) DA THEN CONV_TAC ( TOP_DEPTH_CONV BETA_CONV ) THEN CONV_TAC SELECT_CONV THEN MAP_EVERY EXISTS_TAC [ ( Parse.Term [ QUOTE " (*#loc 1 56086*)r:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 56098*)q:num" ] ) ] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_193" 
 ( String.concatWith " " 
 [ "boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 55846*)\\\\k n. @r. ?q. (k = (q * n) + r) /\\\\ r < n\"", "]", ")", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.IMP_RES_THEN", "(", "boolLib.STRIP_ASSUME_TAC", "o", "HolKernel.SPEC", "(", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 55966*)k:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "DA" "( ( DB.fetch \"arithmetic\" \"DA\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", "(", 
"boolLib.TOP_DEPTH_CONV", "HolKernel.BETA_CONV", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", 
"boolLib.SELECT_CONV", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MAP_EVERY", "boolLib.EXISTS_TAC", "[", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 56086*)r:num\"", "]", ")", ",", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 56098*)q:num\"", "]", ")", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC" ] )
in hhsRecord.try_record_proof "tactictoe_prove_193" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_DIV_exist = prove ( ( Parse.Term [ QUOTE " (*#loc 1 56189*)?MOD DIV.       !n. 0<n ==>           !k. (k = ((DIV k n * n) + MOD k n)) /\\ (MOD k n < n)" ] ) ,
let
val tactictoe_tac1 = STRIP_ASSUME_TAC MOD_exists THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 56338*)MOD:num->num->num" ] ) ) THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 56383*)\\k n.  @q. (k = (q * n) + (MOD k n))" ] ) ) THEN REPEAT STRIP_TAC THENL [ CONV_TAC ( TOP_DEPTH_CONV BETA_CONV ) THEN CONV_TAC SELECT_CONV THEN RES_THEN ( STRIP_ASSUME_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 56571*)k:num" ] ) ) ) THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 56605*)q:num" ] ) ) THEN FIRST_ASSUM ACCEPT_TAC , RES_THEN ( STRIP_ASSUME_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 56688*)k:num" ] ) ) ) ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_194" 
 ( String.concatWith " " 
 [ "boolLib.STRIP_ASSUME_TAC", hhsRecord.fetch "MOD_exists" "", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 56338*)MOD:num->num->num\"", "]", 
")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 56383*)\\\\k n.  @q. (k = (q * n) + (MOD k n))\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.CONV_TAC", "(", "boolLib.TOP_DEPTH_CONV", "HolKernel.BETA_CONV", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", 
"boolLib.SELECT_CONV", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.RES_THEN", "(", "boolLib.STRIP_ASSUME_TAC", "o", "HolKernel.SPEC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 56571*)k:num\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 56605*)q:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ",", "boolLib.RES_THEN", "(", "boolLib.STRIP_ASSUME_TAC", "o", 
"HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 56688*)k:num\"", "]", ")", ")", ")", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_194" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIVISION = new_specification ( "DIVISION" , [ "MOD" , "DIV" ] , MOD_DIV_exist )
;
;
val _ = set_fixity "MOD" ( Infixl 650 )
;
;
val _ = set_fixity "DIV" ( Infixl 600 )
;
;
val DIV2_def = new_definition ( "DIV2_def" , ( Parse.Term [ QUOTE " (*#loc 1 56904*)DIV2 n = n DIV 2" ] ) )
;
;
local
open OpenTheoryMap
;
in
val _ = OpenTheory_const_name { const = { Thy = "arithmetic" , Name = "DIV2" } , name = ( [ "HOL4" , "arithmetic" ] , "DIV2" ) }
;
end
val MOD_ONE = store_thm ( "MOD_ONE" , ( Parse.Term [ QUOTE " (*#loc 1 57152*)!k. k MOD (SUC 0) = 0" ] ) ,
let
val tactictoe_tac1 = STRIP_TAC THEN MP_TAC ( CONJUNCT2 ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 57227*)k:num" ] ) ) ( REWRITE_RULE [ LESS_SUC_REFL ] ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 57289*)SUC 0" ] ) ) DIVISION ) ) ) ) THEN REWRITE_TAC [ LESS_THM , NOT_LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_ONE" 
 ( String.concatWith " " 
 [ "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MP_TAC", "(", "HolKernel.CONJUNCT2", "(", "HolKernel.SPEC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 57227*)k:num\"", "]", ")", ")", "(", 
"boolLib.REWRITE_RULE", "[", "prim_recTheory.LESS_SUC_REFL", "]", "(", 
"HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 57289*)SUC 0\"", "]", ")", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
")", ")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "prim_recTheory.LESS_THM", ",", 
"prim_recTheory.NOT_LESS_0", "]" ] )
in hhsRecord.try_record_proof "MOD_ONE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_1 = save_thm ( "MOD_1" , REWRITE_RULE [ SYM ONE ] MOD_ONE )
;
;
val DIV_LESS_EQ = store_thm ( "DIV_LESS_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 57469*)!n. 0<n ==> !k. (k DIV n) <= k" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN IMP_RES_THEN ( STRIP_ASSUME_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 57574*)k:num" ] ) ) ) DIVISION THEN FIRST_ASSUM ( fn th => fn g => SUBST_OCCS_TAC [ ( [ 2 ] , th ) ] g ) THEN REPEAT_TCL STRIP_THM_THEN MP_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 57712*)n:num" ] ) ) num_CASES ) THENL [ IMP_RES_TAC LESS_NOT_EQ THEN DISCH_THEN ( ASSUME_TAC o SYM ) THEN RES_TAC , DISCH_THEN ( fn th => SUBST_OCCS_TAC [ ( [ 3 ] , th ) ] ) THEN REWRITE_TAC [ MULT_CLAUSES ] THEN REWRITE_TAC [ SYM ( SPEC_ALL ADD_ASSOC ) ] THEN MATCH_ACCEPT_TAC LESS_EQ_ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_LESS_EQ" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.STRIP_ASSUME_TAC", "o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 57574*)k:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", "(", 
"fn", "th", "=>", "fn", "g", "=>", "boolLib.SUBST_OCCS_TAC", "[", "(", "[", "2", "]", ",", "th", ")", "]", 
"g", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT_TCL", 
"boolLib.STRIP_THM_THEN", "boolLib.MP_TAC", "(", "HolKernel.SPEC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 57712*)n:num\"", "]", ")", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.IMP_RES_TAC", "prim_recTheory.LESS_NOT_EQ", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.ASSUME_TAC", "o", "HolKernel.SYM", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.RES_TAC", ",", 
"boolLib.DISCH_THEN", "(", "fn", "th", "=>", "boolLib.SUBST_OCCS_TAC", "[", "(", "[", "3", "]", 
",", "th", ")", "]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_ACCEPT_TAC", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "DIV_LESS_EQ" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 58030*)!x y z. x<y ==> ~(y + z = x)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN POP_ASSUM ( SUBST_ALL_TAC o SYM ) THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [ ] THEN SPEC_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 58182*)y:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 58194*)y:num" ] ) ) THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_CLAUSES , NOT_LESS_0 , LESS_MONO_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_197" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"boolLib.SUBST_ALL_TAC", "o", "HolKernel.SYM", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", 
"boolLib.MP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SPEC_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 58182*)y:num\"", "]", ")", ",", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 58194*)y:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_197" false tactictoe_tac2 tactictoe_tac1
end )
;
;
local
val ( eq , ls ) = CONJ_PAIR ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 58326*)k:num" ] ) ) ( REWRITE_RULE [ LESS_0 ] ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 58376*)SUC(r+p)" ] ) ) DIVISION ) ) )
;
in
val DIV_UNIQUE = store_thm ( "DIV_UNIQUE" , ( Parse.Term [ QUOTE " (*#loc 1 58450*)!n k q. (?r. (k = q*n + r) /\\ r<n) ==> (k DIV n = q)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN DISCH_THEN ( CHOOSE_THEN ( CONJUNCTS_THEN2 MP_TAC ( STRIP_THM_THEN SUBST_ALL_TAC o MATCH_MP LESS_ADD_1 ) ) ) THEN REWRITE_TAC [ ONE , MULT_CLAUSES , ADD_CLAUSES ] THEN DISCH_THEN ( fn th1 => MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN PURE_ONCE_REWRITE_TAC [ SYM ( SPEC_ALL NOT_LESS ) ] THEN CONJ_TAC THEN DISCH_THEN ( fn th2 => MP_TAC ( TRANS ( SYM eq ) th1 ) THEN STRIP_THM_THEN SUBST_ALL_TAC ( MATCH_MP LESS_ADD_1 th2 ) ) ) THEN REWRITE_TAC [ ] THENL [ MATCH_MP_TAC lemma , MATCH_MP_TAC ( ONCE_REWRITE_RULE [ EQ_SYM_EQ ] lemma ) ] THEN REWRITE_TAC [ MULT_CLAUSES , GSYM ADD_ASSOC , ONCE_REWRITE_RULE [ ADD_SYM ] LESS_MONO_ADD_EQ ] THEN GEN_REWRITE_TAC ( RAND_CONV o RAND_CONV o RAND_CONV ) empty_rewrites [ RIGHT_ADD_DISTRIB ] THEN GEN_REWRITE_TAC ( RAND_CONV o RAND_CONV ) empty_rewrites [ ADD_SYM ] THEN REWRITE_TAC [ GSYM ADD_ASSOC ] THEN GEN_REWRITE_TAC ( RAND_CONV ) empty_rewrites [ ADD_SYM ] THEN REWRITE_TAC [ GSYM ADD_ASSOC , ONCE_REWRITE_RULE [ ADD_SYM ] LESS_MONO_ADD_EQ ] THENL [ REWRITE_TAC [ LEFT_ADD_DISTRIB ] THEN REWRITE_TAC [ RIGHT_ADD_DISTRIB ] THEN REWRITE_TAC [ MULT_CLAUSES , GSYM ADD_ASSOC ] THEN GEN_REWRITE_TAC ( RAND_CONV ) empty_rewrites [ ADD_SYM ] THEN REWRITE_TAC [ GSYM ADD_ASSOC , ONE , REWRITE_RULE [ ADD_CLAUSES ] ( ONCE_REWRITE_RULE [ ADD_SYM ] ( SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 59869*)0" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 59877*)n:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 59889*)r:num" ] ) ] LESS_MONO_ADD_EQ ) ) ] THEN REWRITE_TAC [ ADD_CLAUSES , LESS_0 ] , MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 60018*)SUC (r+p)" ] ) ) THEN REWRITE_TAC [ CONJUNCT2 ( SPEC_ALL ( MATCH_MP DIVISION ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 60112*)r+p" ] ) ) LESS_0 ) ) ) ] THEN REWRITE_TAC [ LEFT_ADD_DISTRIB , RIGHT_ADD_DISTRIB , MULT_CLAUSES , GSYM ADD_ASSOC , ADD1 ] THEN GEN_REWRITE_TAC ( RAND_CONV ) empty_rewrites [ ADD_SYM ] THEN REWRITE_TAC [ GSYM ADD_ASSOC , ONCE_REWRITE_RULE [ ADD_SYM ] LESS_EQ_MONO_ADD_EQ ] THEN GEN_REWRITE_TAC ( RAND_CONV ) empty_rewrites [ ADD_SYM ] THEN REWRITE_TAC [ GSYM ADD_ASSOC , ONCE_REWRITE_RULE [ ADD_SYM ] LESS_EQ_MONO_ADD_EQ ] THEN REWRITE_TAC [ ZERO_LESS_EQ , REWRITE_RULE [ ADD_CLAUSES ] ( SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 60666*)1" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 60674*)0" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 60682*)p:num" ] ) ] ADD_MONO_LESS_EQ ) ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_UNIQUE" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.CHOOSE_THEN", "(", "boolLib.CONJUNCTS_THEN2", "boolLib.MP_TAC", "(", 
"boolLib.STRIP_THM_THEN", "boolLib.SUBST_ALL_TAC", "o", "boolLib.MATCH_MP", 
hhsRecord.fetch "LESS_ADD_1" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_1\" ) )", 
")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"fn", "th1", "=>", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"fn", "th2", "=>", "boolLib.MP_TAC", "(", "HolKernel.TRANS", "(", "HolKernel.SYM", 
hhsRecord.fetch "eq" "let val ( eq , ls ) = boolLib.CONJ_PAIR ( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 58326*)k:num\" ] ) ) ( boolLib.REWRITE_RULE [ prim_recTheory.LESS_0 ] ( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 58376*)SUC(r+p)\" ] ) ) ( ( DB.fetch \"arithmetic\" \"DIVISION\" ) ) ) ) ) in eq end", 
")", "th1", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.STRIP_THM_THEN", "boolLib.SUBST_ALL_TAC", "(", "boolLib.MATCH_MP", 
hhsRecord.fetch "LESS_ADD_1" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_1\" ) )", 
"th2", ")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "lemma" "", ",", "boolLib.MATCH_MP_TAC", "(", 
"boolLib.ONCE_REWRITE_RULE", "[", "boolLib.EQ_SYM_EQ", "]", 
hhsRecord.fetch "lemma" "", ")", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", "boolLib.ONCE_REWRITE_RULE", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
hhsRecord.fetch "LESS_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_REWRITE_TAC", "(", "boolLib.RAND_CONV", "o", "boolLib.RAND_CONV", "o", 
"boolLib.RAND_CONV", ")", "boolLib.empty_rewrites", "[", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_REWRITE_TAC", "(", "boolLib.RAND_CONV", "o", "boolLib.RAND_CONV", ")", 
"boolLib.empty_rewrites", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_REWRITE_TAC", "(", "boolLib.RAND_CONV", ")", "boolLib.empty_rewrites", 
"[", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", "boolLib.ONCE_REWRITE_RULE", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
hhsRecord.fetch "LESS_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LEFT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"LEFT_ADD_DISTRIB\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_REWRITE_TAC", "(", "boolLib.RAND_CONV", ")", "boolLib.empty_rewrites", 
"[", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "(", "boolLib.ONCE_REWRITE_RULE", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"(", "boolLib.SPECL", "[", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 59869*)0\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 59877*)n:num\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 59889*)r:num\"", "]", ")", "]", 
hhsRecord.fetch "LESS_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD_EQ\" ) )", 
")", ")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_0", "]", ",", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_EQ_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 60018*)SUC (r+p)\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"HolKernel.CONJUNCT2", "(", "boolLib.SPEC_ALL", "(", "boolLib.MATCH_MP", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 60112*)r+p\"", "]", ")", ")", "prim_recTheory.LESS_0", ")", ")", ")", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LEFT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"LEFT_ADD_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_REWRITE_TAC", 
"(", "boolLib.RAND_CONV", ")", "boolLib.empty_rewrites", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", "boolLib.ONCE_REWRITE_RULE", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
hhsRecord.fetch "LESS_EQ_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO_ADD_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_REWRITE_TAC", "(", "boolLib.RAND_CONV", ")", "boolLib.empty_rewrites", 
"[", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", "boolLib.ONCE_REWRITE_RULE", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
hhsRecord.fetch "LESS_EQ_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO_ADD_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "(", "boolLib.SPECL", "[", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 60666*)1\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 60674*)0\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 60682*)p:num\"", "]", ")", "]", 
hhsRecord.fetch "ADD_MONO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ADD_MONO_LESS_EQ\" ) )", 
")", "]", "]" ] )
in hhsRecord.try_record_proof "DIV_UNIQUE" true tactictoe_tac2 tactictoe_tac1
end )
;
end
;
val lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 60742*)!n k q r. ((k = (q * n) + r) /\\ r < n) ==> (k DIV n = q)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 60878*)r:num" ] ) ) THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_199" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIV_UNIQUE" "( ( DB.fetch \"arithmetic\" \"DIV_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 60878*)r:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_199" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_UNIQUE = store_thm ( "MOD_UNIQUE" , ( Parse.Term [ QUOTE " (*#loc 1 60965*)!n k r. (?q. (k = (q * n) + r) /\\ r < n) ==> (k MOD n = r)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN MP_TAC ( DISCH_ALL ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 61084*)k:num" ] ) ) ( UNDISCH ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 61134*)n:num" ] ) ) DIVISION ) ) ) ) THEN FIRST_ASSUM ( fn th => fn g =>
let
val thm = MATCH_MP LESS_ADD_1 th
fun tcl t = ( SUBST_OCCS_TAC [ ( [ 1 ] , t ) ] )
in STRIP_THM_THEN tcl thm g
end ) THEN REWRITE_TAC [ LESS_0 , ONE , ADD_CLAUSES ] THEN IMP_RES_THEN ( IMP_RES_THEN SUBST1_TAC ) lemma THEN FIRST_ASSUM ( fn th => fn g => SUBST_OCCS_TAC [ ( [ 1 ] , th ) ] g ) THEN
let
val th = PURE_ONCE_REWRITE_RULE [ ADD_SYM ] EQ_MONO_ADD_EQ
in PURE_ONCE_REWRITE_TAC [ th ] THEN DISCH_THEN ( STRIP_THM_THEN ( fn th => fn g => ACCEPT_TAC ( SYM th ) g ) )
end
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_UNIQUE" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MP_TAC", "(", 
"boolLib.DISCH_ALL", "(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 61084*)k:num\"", "]", ")", ")", "(", "boolLib.UNDISCH", 
"(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 61134*)n:num\"", "]", ")", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
")", ")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.FIRST_ASSUM", "(", "fn", "th", "=>", "fn", "g", "=>", "(", "boolLib.STRIP_THM_THEN", 
hhsRecord.fetch "tcl" "let fun tcl t = ( boolLib.SUBST_OCCS_TAC [ ( [ 1 ] , t ) ] ) in tcl end", 
hhsRecord.fetch "thm" "( boolLib.MATCH_MP ( ( DB.fetch \"arithmetic\" \"LESS_ADD_1\" ) ) th )", 
"g", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", 
"(", "boolLib.IMP_RES_THEN", "boolLib.SUBST1_TAC", ")", hhsRecord.fetch "lemma" "", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", "(", 
"fn", "th", "=>", "fn", "g", "=>", "boolLib.SUBST_OCCS_TAC", "[", "(", "[", "1", "]", ",", "th", ")", "]", 
"g", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "th" "( boolLib.PURE_ONCE_REWRITE_RULE [ ( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) ) ] ( ( DB.fetch \"arithmetic\" \"EQ_MONO_ADD_EQ\" ) ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.STRIP_THM_THEN", "(", "fn", "th", "=>", "fn", "g", "=>", "boolLib.ACCEPT_TAC", "(", 
"HolKernel.SYM", "th", ")", "g", ")", ")", ")" ] )
in hhsRecord.try_record_proof "MOD_UNIQUE" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIV_MULT = store_thm ( "DIV_MULT" , ( Parse.Term [ QUOTE " (*#loc 1 61817*)!n r. r < n ==> !q. (q*n + r) DIV n = q" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REPEAT_TCL STRIP_THM_THEN SUBST1_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 61934*)n:num" ] ) ) num_CASES ) THENL [ REWRITE_TAC [ NOT_LESS_0 ] , REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 62069*)r:num" ] ) ) THEN ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_MULT" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT_TCL", 
"boolLib.STRIP_THM_THEN", "boolLib.SUBST1_TAC", "(", "HolKernel.SPEC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 61934*)n:num\"", "]", ")", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.REWRITE_TAC", "[", "prim_recTheory.NOT_LESS_0", "]", ",", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIV_UNIQUE" "( ( DB.fetch \"arithmetic\" \"DIV_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 62069*)r:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "]" ] )
in hhsRecord.try_record_proof "DIV_MULT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_MOD = store_thm ( "LESS_MOD" , ( Parse.Term [ QUOTE " (*#loc 1 62152*)!n k. k < n ==> ((k MOD n) = k)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 62263*)0" ] ) ) THEN ASM_REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_MOD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 62263*)0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LESS_MOD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_EQ_0 = store_thm ( "MOD_EQ_0" , ( Parse.Term [ QUOTE " (*#loc 1 62364*)!n. 0<n ==> !k. ((k * n) MOD n) = 0" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN IMP_RES_THEN ( STRIP_ASSUME_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 62474*)k * n" ] ) ) ) DIVISION THEN MATCH_MP_TAC MOD_UNIQUE THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 62549*)k:num" ] ) ) THEN CONJ_TAC THENL [ REWRITE_TAC [ ADD_CLAUSES ] , FIRST_ASSUM ACCEPT_TAC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_EQ_0" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.STRIP_ASSUME_TAC", "o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 62474*)k * n\"", "]", ")", ")", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 62549*)k:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.FIRST_ASSUM", "boolLib.ACCEPT_TAC", "]" ] )
in hhsRecord.try_record_proof "MOD_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ZERO_MOD = store_thm ( "ZERO_MOD" , ( Parse.Term [ QUOTE " (*#loc 1 62681*)!n. 0<n ==> (0 MOD n = 0)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN IMP_RES_THEN ( MP_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 62771*)0" ] ) ) ) MOD_EQ_0 THEN REWRITE_TAC [ MULT_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ZERO_MOD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.MP_TAC", "o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 62771*)0\"", "]", ")", ")", ")", 
hhsRecord.fetch "MOD_EQ_0" "( ( DB.fetch \"arithmetic\" \"MOD_EQ_0\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ZERO_MOD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ZERO_DIV = store_thm ( "ZERO_DIV" , ( Parse.Term [ QUOTE " (*#loc 1 62868*)!n. 0<n ==> (0 DIV n = 0)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 62979*)0" ] ) ) THEN ASM_REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ZERO_DIV" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIV_UNIQUE" "( ( DB.fetch \"arithmetic\" \"DIV_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 62979*)0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ZERO_DIV" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_MULT = store_thm ( "MOD_MULT" , ( Parse.Term [ QUOTE " (*#loc 1 63082*)!n r. r < n ==> !q. (q * n + r) MOD n = r" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 63203*)q:num" ] ) ) THEN ASM_REWRITE_TAC [ ADD_CLAUSES , MULT_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_MULT" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 63203*)q:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MOD_MULT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_TIMES = store_thm ( "MOD_TIMES" , ( Parse.Term [ QUOTE " (*#loc 1 63310*)!n. 0<n ==> !q r. (((q * n) + r) MOD n) = (r MOD n)" ] ) ,
let
val tactictoe_tac1 =
let
fun SUBS th = SUBST_OCCS_TAC [ ( [ 1 ] , th ) ]
in REPEAT STRIP_TAC THEN IMP_RES_THEN ( TRY o SUBS o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 63483*)r:num" ] ) ) ) DIVISION THEN REWRITE_TAC [ ADD_ASSOC , SYM ( SPEC_ALL RIGHT_ADD_DISTRIB ) ] THEN IMP_RES_THEN ( ASSUME_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 63611*)r:num" ] ) ) ) DIVISION THEN IMP_RES_TAC MOD_MULT THEN FIRST_ASSUM MATCH_ACCEPT_TAC
end
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_TIMES" 
 ( String.concatWith " " 
 [ "(", "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.TRY", "o", 
hhsRecord.fetch "SUBS" "let fun SUBS th = boolLib.SUBST_OCCS_TAC [ ( [ 1 ] , th ) ] in SUBS end", 
"o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 63483*)r:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.IMP_RES_THEN", "(", "boolLib.ASSUME_TAC", "o", "HolKernel.SPEC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 63611*)r:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "MOD_MULT" "( ( DB.fetch \"arithmetic\" \"MOD_MULT\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.MATCH_ACCEPT_TAC", ")" ] )
in hhsRecord.try_record_proof "MOD_TIMES" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_TIMES_SUB = store_thm ( "MOD_TIMES_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 63758*)!n q r. 0 < n /\\ 0 < q /\\ r <= n ==> ((q * n - r) MOD n = (n - r) MOD n)" ] ) ,
let
val tactictoe_tac1 = NTAC 2 STRIP_TAC THEN STRUCT_CASES_TAC ( Q.SPEC [ QUOTE " (*#loc 1 63885*)q" ] num_CASES ) >>- 1 ?? REWRITE_TAC [ NOT_LESS_0 ] THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC bool_ss [ MULT , LESS_EQ_ADD_SUB , MOD_TIMES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_TIMES_SUB" 
 ( String.concatWith " " 
 [ "boolLib.NTAC", "2", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRUCT_CASES_TAC", 
"(", "Q.SPEC", "[", "HolKernel.QUOTE", "\" (*#loc 1 63885*)q\"", "]", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.NOT_LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.FULL_SIMP_TAC", "BasicProvers.bool_ss", "[", hhsRecord.fetch "MULT" "", 
",", 
hhsRecord.fetch "LESS_EQ_ADD_SUB" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD_SUB\" ) )", 
",", 
hhsRecord.fetch "MOD_TIMES" "( ( DB.fetch \"arithmetic\" \"MOD_TIMES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MOD_TIMES_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_PLUS = store_thm ( "MOD_PLUS" , ( Parse.Term [ QUOTE " (*#loc 1 64061*)!n. 0<n ==> !j k. (((j MOD n) + (k MOD n)) MOD n) = ((j+k) MOD n)" ] ) ,
let
val tactictoe_tac1 =
let
fun SUBS th = SUBST_OCCS_TAC [ ( [ 2 ] , th ) ]
in REPEAT STRIP_TAC THEN IMP_RES_TAC MOD_TIMES THEN IMP_RES_THEN ( TRY o SUBS o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 64278*)j:num" ] ) ) ) DIVISION THEN ASM_REWRITE_TAC [ SYM ( SPEC_ALL ADD_ASSOC ) ] THEN PURE_ONCE_REWRITE_TAC [ ADD_SYM ] THEN IMP_RES_THEN ( TRY o SUBS o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 64432*)k:num" ] ) ) ) DIVISION THEN ASM_REWRITE_TAC [ SYM ( SPEC_ALL ADD_ASSOC ) ]
end
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_PLUS" 
 ( String.concatWith " " 
 [ "(", "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "MOD_TIMES" "( ( DB.fetch \"arithmetic\" \"MOD_TIMES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.TRY", "o", 
hhsRecord.fetch "SUBS" "let fun SUBS th = boolLib.SUBST_OCCS_TAC [ ( [ 2 ] , th ) ] in SUBS end", 
"o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 64278*)j:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.TRY", "o", 
hhsRecord.fetch "SUBS" "let fun SUBS th = boolLib.SUBST_OCCS_TAC [ ( [ 2 ] , th ) ] in SUBS end", 
"o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 64432*)k:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "HolKernel.SYM", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
")", "]", ")" ] )
in hhsRecord.try_record_proof "MOD_PLUS" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_MOD = store_thm ( "MOD_MOD" , ( Parse.Term [ QUOTE " (*#loc 1 64551*)!n. 0<n ==> (!k. (k MOD n) MOD n = (k MOD n))" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_MOD THEN IMP_RES_THEN ( STRIP_ASSUME_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 64701*)k:num" ] ) ) ) DIVISION
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_MOD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_MOD" "( ( DB.fetch \"arithmetic\" \"LESS_MOD\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.STRIP_ASSUME_TAC", "o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 64701*)k:num\"", "]", ")", ")", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )" ] )
in hhsRecord.try_record_proof "MOD_MOD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_DIV_EQ_ZERO = save_thm ( "LESS_DIV_EQ_ZERO" , GENL [ ( ( Parse.Term [ QUOTE " (*#loc 1 64791*)r:num" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 64805*)n:num" ] ) ) ] ( DISCH_ALL ( PURE_REWRITE_RULE [ MULT , ADD ] ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 64870*)0" ] ) ) ( UNDISCH_ALL ( SPEC_ALL DIV_MULT ) ) ) ) ) )
;
;
val MULT_DIV = save_thm ( "MULT_DIV" , GEN_ALL ( PURE_REWRITE_RULE [ ADD_0 ] ( CONV_RULE RIGHT_IMP_FORALL_CONV ( SPECL [ ( ( Parse.Term [ QUOTE " (*#loc 1 65054*)n:num" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 65068*)0" ] ) ) ] DIV_MULT ) ) ) )
;
;
val ADD_DIV_ADD_DIV = store_thm ( "ADD_DIV_ADD_DIV" , ( Parse.Term [ QUOTE " (*#loc 1 65144*)!n. 0 < n ==> !x r. ((((x * n) + r) DIV n) = x + (r DIV n))" ] ) ,
let
val tactictoe_tac1 = CONV_TAC ( REDEPTH_CONV RIGHT_IMP_FORALL_CONV ) THEN REPEAT GEN_TAC THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 65305*)r < n" ] ) ) THENL [ IMP_RES_THEN SUBST1_TAC LESS_DIV_EQ_ZERO THEN DISCH_TAC THEN PURE_ONCE_REWRITE_TAC [ ADD_0 ] THEN MATCH_MP_TAC DIV_MULT THEN FIRST_ASSUM ACCEPT_TAC , DISCH_THEN ( CHOOSE_TAC o ( MATCH_MP ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 65537*)r:num" ] ) ) DA ) ) ) THEN POP_ASSUM ( CHOOSE_THEN STRIP_ASSUME_TAC ) THEN SUBST1_TAC ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 65639*)r = (q * n) + r'" ] ) ) ) THEN PURE_ONCE_REWRITE_TAC [ ADD_ASSOC ] THEN PURE_ONCE_REWRITE_TAC [ GSYM RIGHT_ADD_DISTRIB ] THEN IMP_RES_THEN ( fn t => REWRITE_TAC [ t ] ) DIV_MULT ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_DIV_ADD_DIV" 
 ( String.concatWith " " 
 [ "boolLib.CONV_TAC", "(", "boolLib.REDEPTH_CONV", "boolLib.RIGHT_IMP_FORALL_CONV", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_CASES_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 65305*)r < n\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.IMP_RES_THEN", 
"boolLib.SUBST1_TAC", 
hhsRecord.fetch "LESS_DIV_EQ_ZERO" "( ( DB.fetch \"arithmetic\" \"LESS_DIV_EQ_ZERO\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIV_MULT" "( ( DB.fetch \"arithmetic\" \"DIV_MULT\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ",", "boolLib.DISCH_THEN", "(", "boolLib.CHOOSE_TAC", "o", "(", 
"boolLib.MATCH_MP", "(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 65537*)r:num\"", "]", ")", ")", 
hhsRecord.fetch "DA" "( ( DB.fetch \"arithmetic\" \"DA\" ) )", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"boolLib.CHOOSE_THEN", "boolLib.STRIP_ASSUME_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUBST1_TAC", "(", 
"HolKernel.ASSUME", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 65639*)r = (q * n) + r'\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", 
"(", "fn", "t", "=>", "boolLib.REWRITE_TAC", "[", "t", "]", ")", 
hhsRecord.fetch "DIV_MULT" "( ( DB.fetch \"arithmetic\" \"DIV_MULT\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ADD_DIV_ADD_DIV" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_DIV_RWT = store_thm ( "ADD_DIV_RWT" , ( Parse.Term [ QUOTE " (*#loc 1 65872*)!n. 0 < n ==>         !m p. (m MOD n = 0) \\/ (p MOD n = 0) ==>               ((m + p) DIV n = m DIV n + p DIV n)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN IMP_RES_THEN ( ASSUME_TAC o GSYM ) DIVISION THEN MATCH_MP_TAC DIV_UNIQUE THENL [ Q.EXISTS_TAC [ QUOTE " (*#loc 1 66114*)p MOD n" ] THEN ASM_REWRITE_TAC [ RIGHT_ADD_DISTRIB , GSYM ADD_ASSOC , EQ_ADD_RCANCEL ] THEN SIMP_TAC bool_ss [ Once ( GSYM ADD_0 ) , SimpRHS ] THEN FIRST_X_ASSUM ( SUBST1_TAC o SYM ) THEN ASM_REWRITE_TAC [ ] , Q.EXISTS_TAC [ QUOTE " (*#loc 1 66340*)m MOD n" ] THEN ASM_REWRITE_TAC [ RIGHT_ADD_DISTRIB ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 66419*)p DIV n * n = p" ] SUBST1_TAC THENL [ SIMP_TAC bool_ss [ Once ( GSYM ADD_0 ) , SimpLHS ] THEN FIRST_X_ASSUM ( SUBST1_TAC o SYM ) THEN ASM_REWRITE_TAC [ ] , ALL_TAC ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 66624*)m DIV n * n + p + m MOD n = m DIV n * n + m MOD n + p" ] ( fn th => ASM_REWRITE_TAC [ th ] ) THEN REWRITE_TAC [ GSYM ADD_ASSOC , EQ_ADD_LCANCEL ] THEN MATCH_ACCEPT_TAC ADD_COMM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_DIV_RWT" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"boolLib.ASSUME_TAC", "o", "boolLib.GSYM", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIV_UNIQUE" "( ( DB.fetch \"arithmetic\" \"DIV_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 66114*)p MOD n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", 
hhsRecord.fetch "EQ_ADD_RCANCEL" "( ( DB.fetch \"arithmetic\" \"EQ_ADD_RCANCEL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", "boolLib.Once", "(", "boolLib.GSYM", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ")", ",", 
"boolSimps.SimpRHS", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.FIRST_X_ASSUM", "(", "boolLib.SUBST1_TAC", "o", "HolKernel.SYM", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", ",", "Q.EXISTS_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 66340*)m MOD n\"", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 66419*)p DIV n * n = p\"", "]", 
"boolLib.SUBST1_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", "boolLib.Once", "(", "boolLib.GSYM", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ")", ",", 
"boolSimps.SimpLHS", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.FIRST_X_ASSUM", "(", "boolLib.SUBST1_TAC", "o", "HolKernel.SYM", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", ",", "boolLib.ALL_TAC", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", 
"\" (*#loc 1 66624*)m DIV n * n + p + m MOD n = m DIV n * n + m MOD n + p\"", 
"]", "(", "fn", "th", "=>", "boolLib.ASM_REWRITE_TAC", "[", "th", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", 
hhsRecord.fetch "EQ_ADD_LCANCEL" "( ( DB.fetch \"arithmetic\" \"EQ_ADD_LCANCEL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_ACCEPT_TAC", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ADD_DIV_RWT" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val NOT_MULT_LESS_0 = prove ( ( ( Parse.Term [ QUOTE " (*#loc 1 66862*)!m n. 0<m /\\ 0<n ==> 0 < m*n" ] ) ) ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN REWRITE_TAC [ NOT_LESS_0 ] THEN STRIP_TAC THEN REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_213" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.NOT_LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_213" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_MULT_MOD = store_thm ( "MOD_MULT_MOD" , ( Parse.Term [ QUOTE " (*#loc 1 67067*)!m n. 0<n /\\ 0<m  ==> !x. ((x MOD (n * m)) MOD n = x MOD n)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM ( ASSUME_TAC o ( MATCH_MP NOT_MULT_LESS_0 ) ) THEN GEN_TAC THEN POP_ASSUM ( CHOOSE_TAC o ( MATCH_MP ( SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 67282*)x:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 67294*)m * n" ] ) ] DA ) ) ) THEN POP_ASSUM ( CHOOSE_THEN STRIP_ASSUME_TAC ) THEN SUBST1_TAC ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 67385*)x = (q * (n * m)) + r" ] ) ) ) THEN POP_ASSUM ( SUBST1_TAC o ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 67452*)q:num" ] ) ) ) o MATCH_MP MOD_MULT ) THEN PURE_ONCE_REWRITE_TAC [ MULT_SYM ] THEN PURE_ONCE_REWRITE_TAC [ GSYM MULT_ASSOC ] THEN PURE_ONCE_REWRITE_TAC [ MULT_SYM ] THEN STRIP_ASSUME_TAC ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 67644*)0 < n /\\ 0 < m" ] ) ) ) THEN PURE_ONCE_REWRITE_TAC [ UNDISCH_ALL ( SPEC_ALL MOD_TIMES ) ] THEN REFL_TAC
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_MULT_MOD" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", "(", 
"boolLib.ASSUME_TAC", "o", "(", "boolLib.MATCH_MP", 
hhsRecord.fetch "NOT_MULT_LESS_0" "", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"boolLib.CHOOSE_TAC", "o", "(", "boolLib.MATCH_MP", "(", "boolLib.SPECL", "[", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 67282*)x:num\"", "]", ")", ",", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 67294*)m * n\"", "]", ")", "]", 
hhsRecord.fetch "DA" "( ( DB.fetch \"arithmetic\" \"DA\" ) )", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"boolLib.CHOOSE_THEN", "boolLib.STRIP_ASSUME_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUBST1_TAC", "(", 
"HolKernel.ASSUME", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 67385*)x = (q * (n * m)) + r\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"boolLib.SUBST1_TAC", "o", "(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 67452*)q:num\"", "]", ")", ")", ")", "o", 
"boolLib.MATCH_MP", 
hhsRecord.fetch "MOD_MULT" "( ( DB.fetch \"arithmetic\" \"MOD_MULT\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_SYM" "( ( DB.fetch \"arithmetic\" \"MULT_SYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_SYM" "( ( DB.fetch \"arithmetic\" \"MULT_SYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.STRIP_ASSUME_TAC", "(", "HolKernel.ASSUME", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 67644*)0 < n /\\\\ 0 < m\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", "boolLib.UNDISCH_ALL", "(", 
"boolLib.SPEC_ALL", 
hhsRecord.fetch "MOD_TIMES" "( ( DB.fetch \"arithmetic\" \"MOD_TIMES\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REFL_TAC" ] )
in hhsRecord.try_record_proof "MOD_MULT_MOD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIV_ONE = save_thm ( "DIV_ONE" , GEN_ALL ( REWRITE_RULE [ REWRITE_RULE [ ONE ] MULT_RIGHT_1 ] ( MP ( SPECL [ ( ( Parse.Term [ QUOTE " (*#loc 1 67856*)SUC 0" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 67871*)q:num" ] ) ) ] MULT_DIV ) ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 67910*)0" ] ) ) LESS_0 ) ) ) )
;
;
val DIV_1 = save_thm ( "DIV_1" , REWRITE_RULE [ SYM ONE ] DIV_ONE )
;
;
val DIVMOD_ID = store_thm ( "DIVMOD_ID" , ( Parse.Term [ QUOTE " (*#loc 1 68037*)!n. 0 < n ==> (n DIV n = 1) /\\ (n MOD n = 0)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THENL [ MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 68160*)0" ] THEN ASM_REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES ] , MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 68264*)1" ] THEN ASM_REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIVMOD_ID" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIV_UNIQUE" "( ( DB.fetch \"arithmetic\" \"DIV_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 68160*)0\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 68264*)1\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "DIVMOD_ID" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val Less_lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 68355*)!m n. m<n ==> ?p. (n = m + p) /\\ 0<p" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN INDUCT_TAC THENL [ REWRITE_TAC [ NOT_LESS_0 ] , REWRITE_TAC [ LESS_THM ] THEN DISCH_THEN ( DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC ) THENL [ EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 68569*)SUC 0" ] ) ) THEN REWRITE_TAC [ LESS_0 , ADD_CLAUSES ] , RES_TAC THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 68657*)SUC p" ] ) ) THEN ASM_REWRITE_TAC [ ADD_CLAUSES , LESS_0 ] ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_216" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", "prim_recTheory.NOT_LESS_0", "]", ",", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.LESS_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.DISJ_CASES_THEN2", "boolLib.SUBST1_TAC", "boolLib.ASSUME_TAC", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.EXISTS_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 68569*)SUC 0\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.RES_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 68657*)SUC p\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_0", "]", "]", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_216" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val Less_MULT_lemma = prove ( ( ( Parse.Term [ QUOTE " (*#loc 1 68755*)!r m p. 0<p ==> r<m ==> r < p*m" ] ) ) ,
let
val tactictoe_tac1 =
let
val lem1 = MATCH_MP LESS_LESS_EQ_TRANS ( CONJ ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 68862*)m:num" ] ) ) LESS_SUC_REFL ) ( SPECL [ ( ( Parse.Term [ QUOTE " (*#loc 1 68912*)SUC m" ] ) ) , ( ( Parse.Term [ QUOTE " (*#loc 1 68927*)p * (SUC m)" ] ) ) ] LESS_EQ_ADD ) )
in GEN_TAC THEN REPEAT INDUCT_TAC THEN REWRITE_TAC [ NOT_LESS_0 ] THEN DISCH_TAC THEN REWRITE_TAC [ LESS_THM ] THEN DISCH_THEN ( DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC ) THEN PURE_ONCE_REWRITE_TAC [ MULT ] THEN PURE_ONCE_REWRITE_TAC [ ADD_SYM ] THENL [ ACCEPT_TAC lem1 , ACCEPT_TAC ( MATCH_MP LESS_TRANS ( CONJ ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 69298*)r < m" ] ) ) ) lem1 ) ) ]
end
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_217" 
 ( String.concatWith " " 
 [ "(", "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.NOT_LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.LESS_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.DISJ_CASES_THEN2", "boolLib.SUBST1_TAC", "boolLib.ASSUME_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", hhsRecord.fetch "MULT" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.ACCEPT_TAC", 
hhsRecord.fetch "lem1" "( boolLib.MATCH_MP ( ( DB.fetch \"arithmetic\" \"LESS_LESS_EQ_TRANS\" ) ) ( HolKernel.CONJ ( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 68862*)m:num\" ] ) ) prim_recTheory.LESS_SUC_REFL ) ( boolLib.SPECL [ ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 68912*)SUC m\" ] ) ) , ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 68927*)p * (SUC m)\" ] ) ) ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) ) ) ) )", 
",", "boolLib.ACCEPT_TAC", "(", "boolLib.MATCH_MP", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"(", "HolKernel.CONJ", "(", "HolKernel.ASSUME", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 69298*)r < m\"", "]", ")", ")", ")", 
hhsRecord.fetch "lem1" "( boolLib.MATCH_MP ( ( DB.fetch \"arithmetic\" \"LESS_LESS_EQ_TRANS\" ) ) ( HolKernel.CONJ ( HolKernel.SPEC ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 68862*)m:num\" ] ) ) prim_recTheory.LESS_SUC_REFL ) ( boolLib.SPECL [ ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 68912*)SUC m\" ] ) ) , ( ( Parse.Term [ HolKernel.QUOTE \" (*#loc 1 68927*)p * (SUC m)\" ] ) ) ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) ) ) ) )", 
")", ")", "]", ")" ] )
in hhsRecord.try_record_proof "tactictoe_prove_217" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val Less_MULT_ADD_lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 69364*)!m n r r'. 0<m /\\ 0<n /\\ r<m /\\ r'<n ==> r'*m + r < n*m" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN CHOOSE_THEN STRIP_ASSUME_TAC ( MATCH_MP Less_lemma ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 69512*)r<m" ] ) ) ) ) THEN CHOOSE_THEN STRIP_ASSUME_TAC ( MATCH_MP Less_lemma ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 69591*)r'<n" ] ) ) ) ) THEN ASM_REWRITE_TAC [ ] THEN PURE_ONCE_REWRITE_TAC [ RIGHT_ADD_DISTRIB ] THEN PURE_ONCE_REWRITE_TAC [ ADD_SYM ] THEN PURE_ONCE_REWRITE_TAC [ LESS_MONO_ADD_EQ ] THEN SUBST1_TAC ( SYM ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 69794*)m = r + p" ] ) ) ) ) THEN IMP_RES_TAC Less_MULT_lemma
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_218" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CHOOSE_THEN", 
"boolLib.STRIP_ASSUME_TAC", "(", "boolLib.MATCH_MP", 
hhsRecord.fetch "Less_lemma" "", "(", "HolKernel.ASSUME", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 69512*)r<m\"", "]", ")", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CHOOSE_THEN", 
"boolLib.STRIP_ASSUME_TAC", "(", "boolLib.MATCH_MP", 
hhsRecord.fetch "Less_lemma" "", "(", "HolKernel.ASSUME", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 69591*)r'<n\"", "]", ")", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUBST1_TAC", "(", 
"HolKernel.SYM", "(", "HolKernel.ASSUME", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 69794*)m = r + p\"", "]", ")", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "Less_MULT_lemma" "" ] )
in hhsRecord.try_record_proof "tactictoe_prove_218" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIV_DIV_DIV_MULT = store_thm ( "DIV_DIV_DIV_MULT" , ( Parse.Term [ QUOTE " (*#loc 1 69907*)!m n. 0<m /\\ 0<n ==> !x. ((x DIV m) DIV n = x  DIV (m * n))" ] ) ,
let
val tactictoe_tac1 = CONV_TAC ( ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV ) THEN REPEAT STRIP_TAC THEN REPEAT_TCL CHOOSE_THEN ( CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC ) ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 70139*)x:num" ] ) ) ( MATCH_MP DA ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 70174*)0 < m" ] ) ) ) ) ) THEN REPEAT_TCL CHOOSE_THEN ( CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC ) ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 70279*)q:num" ] ) ) ( MATCH_MP DA ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 70314*)0 < n" ] ) ) ) ) ) THEN IMP_RES_THEN ( fn t => REWRITE_TAC [ t ] ) DIV_MULT THEN IMP_RES_THEN ( fn t => REWRITE_TAC [ t ] ) DIV_MULT THEN PURE_ONCE_REWRITE_TAC [ RIGHT_ADD_DISTRIB ] THEN PURE_ONCE_REWRITE_TAC [ GSYM MULT_ASSOC ] THEN PURE_ONCE_REWRITE_TAC [ GSYM ADD_ASSOC ] THEN ASSUME_TAC ( MATCH_MP NOT_MULT_LESS_0 ( CONJ ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 70658*)0 < n" ] ) ) ) ( ASSUME ( ( Parse.Term [ QUOTE " (*#loc 1 70681*)0 < m" ] ) ) ) ) ) THEN CONV_TAC ( ( RAND_CONV o RAND_CONV ) ( REWR_CONV MULT_SYM ) ) THEN CONV_TAC SYM_CONV THEN PURE_ONCE_REWRITE_TAC [ ADD_INV_0_EQ ] THEN FIRST_ASSUM ( fn t => REWRITE_TAC [ MATCH_MP ADD_DIV_ADD_DIV t ] ) THEN PURE_ONCE_REWRITE_TAC [ ADD_INV_0_EQ ] THEN MATCH_MP_TAC LESS_DIV_EQ_ZERO THEN IMP_RES_TAC Less_MULT_ADD_lemma
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_DIV_DIV_MULT" 
 ( String.concatWith " " 
 [ "boolLib.CONV_TAC", "(", "boolLib.ONCE_DEPTH_CONV", 
"boolLib.RIGHT_IMP_FORALL_CONV", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REPEAT_TCL", "boolLib.CHOOSE_THEN", "(", "boolLib.CONJUNCTS_THEN2", 
"boolLib.SUBST1_TAC", "boolLib.ASSUME_TAC", ")", "(", "HolKernel.SPEC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 70139*)x:num\"", "]", ")", ")", "(", 
"boolLib.MATCH_MP", 
hhsRecord.fetch "DA" "( ( DB.fetch \"arithmetic\" \"DA\" ) )", "(", 
"HolKernel.ASSUME", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 70174*)0 < m\"", "]", ")", ")", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT_TCL", 
"boolLib.CHOOSE_THEN", "(", "boolLib.CONJUNCTS_THEN2", "boolLib.SUBST1_TAC", 
"boolLib.ASSUME_TAC", ")", "(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 70279*)q:num\"", "]", ")", ")", "(", "boolLib.MATCH_MP", 
hhsRecord.fetch "DA" "( ( DB.fetch \"arithmetic\" \"DA\" ) )", "(", 
"HolKernel.ASSUME", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 70314*)0 < n\"", "]", ")", ")", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"fn", "t", "=>", "boolLib.REWRITE_TAC", "[", "t", "]", ")", 
hhsRecord.fetch "DIV_MULT" "( ( DB.fetch \"arithmetic\" \"DIV_MULT\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"fn", "t", "=>", "boolLib.REWRITE_TAC", "[", "t", "]", ")", 
hhsRecord.fetch "DIV_MULT" "( ( DB.fetch \"arithmetic\" \"DIV_MULT\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASSUME_TAC", "(", 
"boolLib.MATCH_MP", hhsRecord.fetch "NOT_MULT_LESS_0" "", "(", "HolKernel.CONJ", 
"(", "HolKernel.ASSUME", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 70658*)0 < n\"", "]", ")", ")", ")", "(", "HolKernel.ASSUME", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 70681*)0 < m\"", "]", ")", ")", ")", ")", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", "(", 
"(", "boolLib.RAND_CONV", "o", "boolLib.RAND_CONV", ")", "(", "boolLib.REWR_CONV", 
hhsRecord.fetch "MULT_SYM" "( ( DB.fetch \"arithmetic\" \"MULT_SYM\" ) )", 
")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", 
"boolLib.SYM_CONV", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_INV_0_EQ" "( ( DB.fetch \"arithmetic\" \"ADD_INV_0_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"(", "fn", "t", "=>", "boolLib.REWRITE_TAC", "[", "boolLib.MATCH_MP", 
hhsRecord.fetch "ADD_DIV_ADD_DIV" "( ( DB.fetch \"arithmetic\" \"ADD_DIV_ADD_DIV\" ) )", 
"t", "]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_INV_0_EQ" "( ( DB.fetch \"arithmetic\" \"ADD_INV_0_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_DIV_EQ_ZERO" "( ( DB.fetch \"arithmetic\" \"LESS_DIV_EQ_ZERO\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "Less_MULT_ADD_lemma" "" ] )
in hhsRecord.try_record_proof "DIV_DIV_DIV_MULT" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val POS_ADD = prove ( ( Parse.Term [ QUOTE " (*#loc 1 71051*)!m n. 0<m+n = 0<m \\/ 0<n" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN STRUCT_CASES_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 71131*)m:num" ] ) ) num_CASES ) THEN STRUCT_CASES_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 71186*)n:num" ] ) ) num_CASES ) THEN ASM_REWRITE_TAC [ ADD_CLAUSES , prim_recTheory.LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_220" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRUCT_CASES_TAC", 
"(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 71131*)m:num\"", "]", ")", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.STRUCT_CASES_TAC", "(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 71186*)n:num\"", "]", ")", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_220" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val POS_MULT = prove ( ( Parse.Term [ QUOTE " (*#loc 1 71294*)!m n. 0<m*n = 0<m /\\ 0<n" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN STRUCT_CASES_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 71374*)m:num" ] ) ) num_CASES ) THEN STRUCT_CASES_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 71429*)n:num" ] ) ) num_CASES ) THEN ASM_REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES , prim_recTheory.LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_221" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRUCT_CASES_TAC", 
"(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 71374*)m:num\"", "]", ")", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.STRUCT_CASES_TAC", "(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 71429*)n:num\"", "]", ")", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_221" false tactictoe_tac2 tactictoe_tac1
end )
;
;
local
open prim_recTheory
;
in
val SUC_PRE = store_thm ( "SUC_PRE" , ( Parse.Term [ QUOTE " (*#loc 1 71603*)0 < m <=> (SUC (PRE m) = m)" ] ) ,
let
val tactictoe_tac1 = STRUCT_CASES_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 71668*)m:num" ] ) ) num_CASES ) THEN REWRITE_TAC [ PRE , NOT_LESS_0 , LESS_0 , NOT_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUC_PRE" 
 ( String.concatWith " " 
 [ "boolLib.STRUCT_CASES_TAC", "(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 71668*)m:num\"", "]", ")", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "prim_recTheory.PRE", ",", "prim_recTheory.NOT_LESS_0", ",", 
"prim_recTheory.LESS_0", ",", "numTheory.NOT_SUC", "]" ] )
in hhsRecord.try_record_proof "SUC_PRE" false tactictoe_tac2 tactictoe_tac1
end )
;
end
val LESS_MONO_LEM = GEN_ALL ( REWRITE_RULE [ ADD_CLAUSES ] ( SPECL ( map Term [ [ QUOTE " (*#loc 1 71830*)0" ] , [ QUOTE " (*#loc 1 71835*)y:num" ] , [ QUOTE " (*#loc 1 71844*)x:num" ] ] ) ( ONCE_REWRITE_RULE [ ADD_SYM ] LESS_MONO_ADD ) ) )
;
;
val DIV_LESS = store_thm ( "DIV_LESS" , ( Parse.Term [ QUOTE " (*#loc 1 71947*)!n d. 0<n /\\ 1<d ==> n DIV d < n" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ ONE ] THEN REPEAT STRIP_TAC THEN IMP_RES_TAC prim_recTheory.SUC_LESS THEN CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 72135*)n:num" ] ) ) ( UNDISCH ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 72162*)d:num" ] ) ) DIVISION ) ) ) THEN RULE_ASSUM_TAC ( REWRITE_RULE [ POS_ADD ] ) THEN MP_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 72255*)d:num" ] ) ) ADD_DIV_ADD_DIV ) THEN ASM_REWRITE_TAC [ ] THEN DISCH_THEN ( fn th => REWRITE_TAC [ th ] ) THEN MP_TAC ( SPECL ( map Term [ [ QUOTE " (*#loc 1 72384*)n MOD d" ] , [ QUOTE " (*#loc 1 72395*)d:num" ] ] ) LESS_DIV_EQ_ZERO ) THEN ASM_REWRITE_TAC [ ] THEN DISCH_THEN ( fn th => REWRITE_TAC [ th , ADD_CLAUSES ] ) THEN SUBGOAL_THEN ( ( Parse.Term [ QUOTE " (*#loc 1 72530*)?m. d = SUC m" ] ) ) ( CHOOSE_THEN SUBST_ALL_TAC ) THENL [ EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 72600*)PRE d" ] ) ) THEN IMP_RES_TAC SUC_PRE THEN ASM_REWRITE_TAC [ ] , REWRITE_TAC [ MULT_CLAUSES , GSYM ADD_ASSOC ] THEN MATCH_MP_TAC LESS_MONO_LEM THEN PAT_ASSUM ( ( Parse.Term [ QUOTE " (*#loc 1 72763*)x \\/ y" ] ) ) MP_TAC THEN REWRITE_TAC [ POS_ADD , POS_MULT ] THEN STRIP_TAC THENL [ DISJ1_TAC THEN RULE_ASSUM_TAC ( REWRITE_RULE [ LESS_MONO_EQ ] ) , ALL_TAC ] THEN ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_LESS" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.IMP_RES_TAC", "prim_recTheory.SUC_LESS", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJUNCTS_THEN2", 
"boolLib.SUBST_ALL_TAC", "boolLib.ASSUME_TAC", "(", "HolKernel.SPEC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 72135*)n:num\"", "]", ")", ")", "(", 
"boolLib.UNDISCH", "(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 72162*)d:num\"", "]", ")", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.RULE_ASSUM_TAC", "(", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "POS_ADD" "", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MP_TAC", "(", 
"HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 72255*)d:num\"", "]", ")", ")", 
hhsRecord.fetch "ADD_DIV_ADD_DIV" "( ( DB.fetch \"arithmetic\" \"ADD_DIV_ADD_DIV\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"fn", "th", "=>", "boolLib.REWRITE_TAC", "[", "th", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MP_TAC", "(", 
"boolLib.SPECL", "(", "map", "Parse.Term", "[", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 72384*)n MOD d\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 72395*)d:num\"", "]", "]", ")", 
hhsRecord.fetch "LESS_DIV_EQ_ZERO" "( ( DB.fetch \"arithmetic\" \"LESS_DIV_EQ_ZERO\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"fn", "th", "=>", "boolLib.REWRITE_TAC", "[", "th", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.SUBGOAL_THEN", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 72530*)?m. d = SUC m\"", "]", ")", ")", "(", "boolLib.CHOOSE_THEN", 
"boolLib.SUBST_ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.EXISTS_TAC", 
"(", "(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 72600*)PRE d\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "SUC_PRE" "( ( DB.fetch \"arithmetic\" \"SUC_PRE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", ",", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_MONO_LEM" "( boolLib.GEN_ALL ( boolLib.REWRITE_RULE [ ( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) ) ] ( boolLib.SPECL ( map Parse.Term [ [ HolKernel.QUOTE \" (*#loc 1 71830*)0\" ] , [ HolKernel.QUOTE \" (*#loc 1 71835*)y:num\" ] , [ HolKernel.QUOTE \" (*#loc 1 71844*)x:num\" ] ] ) ( boolLib.ONCE_REWRITE_RULE [ ( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) ) ] ( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD\" ) ) ) ) ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.PAT_ASSUM", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 72763*)x \\\\/ y\"", "]", ")", ")", 
"boolLib.MP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", hhsRecord.fetch "POS_ADD" "", ",", 
hhsRecord.fetch "POS_MULT" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.DISJ1_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.RULE_ASSUM_TAC", 
"(", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
"]", ")", ",", "boolLib.ALL_TAC", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "]" ] )
in hhsRecord.try_record_proof "DIV_LESS" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_LESS = Q.store_thm ( "MOD_LESS" , [ QUOTE " (*#loc 1 72987*)!m n. 0 < n ==> m MOD n < n" ] ,
let
val tactictoe_tac1 = METIS_TAC [ DIVISION ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_LESS" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MOD_LESS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_MODULUS = Q.store_thm ( "ADD_MODULUS" , [ QUOTE " (*#loc 1 73088*)(!n x. 0 < n ==> ((x + n) MOD n = x MOD n)) /\\  (!n x. 0 < n ==> ((n + x) MOD n = x MOD n))" ] ,
let
val tactictoe_tac1 = METIS_TAC [ ADD_SYM , MOD_PLUS , DIVMOD_ID , MOD_MOD , ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_MODULUS" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", ",", 
hhsRecord.fetch "MOD_PLUS" "( ( DB.fetch \"arithmetic\" \"MOD_PLUS\" ) )", 
",", 
hhsRecord.fetch "DIVMOD_ID" "( ( DB.fetch \"arithmetic\" \"DIVMOD_ID\" ) )", 
",", hhsRecord.fetch "MOD_MOD" "( ( DB.fetch \"arithmetic\" \"MOD_MOD\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ADD_MODULUS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_MODULUS_LEFT = save_thm ( "ADD_MODULUS_LEFT" , CONJUNCT1 ADD_MODULUS )
;
;
val ADD_MODULUS_RIGHT = save_thm ( "ADD_MODULUS_RIGHT" , CONJUNCT2 ADD_MODULUS )
;
;
val DIV_P = store_thm ( "DIV_P" , ( Parse.Term [ QUOTE " (*#loc 1 73435*)!P p q. 0 < q ==>             (P (p DIV q) = ?k r. (p = k * q + r) /\\ r < q /\\ P k)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [ MAP_EVERY Q.EXISTS_TAC [ [ QUOTE " (*#loc 1 73606*)p DIV q" ] , [ QUOTE " (*#loc 1 73617*)p MOD q" ] ] THEN ASM_REWRITE_TAC [ ] THEN MATCH_MP_TAC DIVISION THEN FIRST_ASSUM ACCEPT_TAC , Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 73735*)p DIV q = k" ] ( fn th => SUBST1_TAC th THEN FIRST_ASSUM ACCEPT_TAC ) THEN MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 73896*)r" ] THEN ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_P" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.MAP_EVERY", 
"Q.EXISTS_TAC", "[", "[", "HolKernel.QUOTE", "\" (*#loc 1 73606*)p DIV q\"", "]", ",", 
"[", "HolKernel.QUOTE", "\" (*#loc 1 73617*)p MOD q\"", "]", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ",", "Q.SUBGOAL_THEN", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 73735*)p DIV q = k\"", "]", "(", "fn", "th", "=>", "boolLib.SUBST1_TAC", 
"th", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIV_UNIQUE" "( ( DB.fetch \"arithmetic\" \"DIV_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 73896*)r\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "]" ] )
in hhsRecord.try_record_proof "DIV_P" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIV_P_UNIV = store_thm ( "DIV_P_UNIV" , ( Parse.Term [ QUOTE " (*#loc 1 73976*)!P m n. 0 < n ==> (P (m DIV n) = !q r. (m = q * n + r) /\\ r < n ==> P q)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [ Q_TAC SUFF_TAC [ QUOTE " (*#loc 1 74134*)m DIV n = q" ] >>- 1 ?? ( DISCH_THEN ( SUBST1_TAC o SYM ) THEN ASM_REWRITE_TAC [ ] ) THEN MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 74271*)r" ] THEN ASM_REWRITE_TAC [ ] , FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 74349*)m MOD n" ] THEN MATCH_MP_TAC DIVISION THEN ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_P_UNIV" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.Q_TAC", "boolLib.SUFF_TAC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 74134*)m DIV n = q\"", "]", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.DISCH_THEN", "(", 
"boolLib.SUBST1_TAC", "o", "HolKernel.SYM", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIV_UNIQUE" "( ( DB.fetch \"arithmetic\" \"DIV_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 74271*)r\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", ",", "boolLib.FIRST_X_ASSUM", "boolLib.MATCH_MP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 74349*)m MOD n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "]" ] )
in hhsRecord.try_record_proof "DIV_P_UNIV" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_P = store_thm ( "MOD_P" , ( Parse.Term [ QUOTE " (*#loc 1 74456*)!P p q. 0 < q ==>             (P (p MOD q) = ?k r. (p = k * q + r) /\\ r < q /\\ P r)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [ MAP_EVERY Q.EXISTS_TAC [ [ QUOTE " (*#loc 1 74627*)p DIV q" ] , [ QUOTE " (*#loc 1 74638*)p MOD q" ] ] THEN ASM_REWRITE_TAC [ ] THEN MATCH_MP_TAC DIVISION THEN FIRST_ASSUM ACCEPT_TAC , Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 74756*)p MOD q = r" ] ( fn th => SUBST1_TAC th THEN FIRST_ASSUM ACCEPT_TAC ) THEN MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 74917*)k" ] THEN ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_P" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.MAP_EVERY", 
"Q.EXISTS_TAC", "[", "[", "HolKernel.QUOTE", "\" (*#loc 1 74627*)p DIV q\"", "]", ",", 
"[", "HolKernel.QUOTE", "\" (*#loc 1 74638*)p MOD q\"", "]", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ",", "Q.SUBGOAL_THEN", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 74756*)p MOD q = r\"", "]", "(", "fn", "th", "=>", "boolLib.SUBST1_TAC", 
"th", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 74917*)k\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "]" ] )
in hhsRecord.try_record_proof "MOD_P" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_P_UNIV = store_thm ( "MOD_P_UNIV" , ( Parse.Term [ QUOTE " (*#loc 1 74997*)!P m n. 0 < n ==>             (P (m MOD n) = !q r. (m = q * n + r) /\\ r < n ==> P r)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [ Q_TAC SUFF_TAC [ QUOTE " (*#loc 1 75167*)m MOD n = r" ] >>- 1 ?? ( DISCH_THEN ( SUBST1_TAC o SYM ) THEN ASM_REWRITE_TAC [ ] ) THEN MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 75304*)q" ] THEN ASM_REWRITE_TAC [ ] , FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 75382*)m DIV n" ] THEN MATCH_MP_TAC DIVISION THEN ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_P_UNIV" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.Q_TAC", "boolLib.SUFF_TAC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 75167*)m MOD n = r\"", "]", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.DISCH_THEN", "(", 
"boolLib.SUBST1_TAC", "o", "HolKernel.SYM", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 75304*)q\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", ",", "boolLib.FIRST_X_ASSUM", "boolLib.MATCH_MP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 75382*)m DIV n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "]" ] )
in hhsRecord.try_record_proof "MOD_P_UNIV" false tactictoe_tac2 tactictoe_tac1
end )
;
;
fun move_var_left s =
let
val v = mk_var ( s , ( Parse.Type [ QUOTE " (*#loc 1 75502*):num" ] ) )
;
val th1 = GSYM ( SPEC v MULT_COMM )
;
val th2 = GSYM ( SPEC v MULT_ASSOC )
;
val th3 = CONV_RULE ( STRIP_QUANT_CONV ( LAND_CONV ( LAND_CONV ( REWR_CONV MULT_COMM ) THENC REWR_CONV ( GSYM MULT_ASSOC ) ) ) ) th2
;
in FREEZE_THEN ( fn th1 => FREEZE_THEN ( fn th2 => FREEZE_THEN ( fn th3 => CONV_TAC ( REDEPTH_CONV ( FIRST_CONV ( map ( CHANGED_CONV o REWR_CONV ) [ th1 , th2 , th3 ] ) ) ) ) th3 ) th2 ) th1
end
;
val MOD_TIMES2 = store_thm ( "MOD_TIMES2" , ( Parse.Term [ QUOTE " (*#loc 1 76220*)!n. 0 < n ==>         !j k. (j MOD n * k MOD n) MOD n = (j * k) MOD n" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN IMP_RES_THEN ( Q.SPEC_THEN [ QUOTE " (*#loc 1 76347*)j" ] STRIP_ASSUME_TAC ) DIVISION THEN IMP_RES_THEN ( Q.SPEC_THEN [ QUOTE " (*#loc 1 76411*)k" ] STRIP_ASSUME_TAC ) DIVISION THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 76462*)q = j DIV n" ] THEN POP_ASSUM ( K ALL_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 76523*)r = j MOD n" ] THEN POP_ASSUM ( K ALL_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 76584*)u = k DIV n" ] THEN POP_ASSUM ( K ALL_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 76645*)v = k MOD n" ] THEN POP_ASSUM ( K ALL_TAC ) THEN NTAC 2 ( FIRST_X_ASSUM SUBST_ALL_TAC ) THEN REWRITE_TAC [ LEFT_ADD_DISTRIB , RIGHT_ADD_DISTRIB , ADD_ASSOC ] THEN move_var_left "n" THEN REWRITE_TAC [ GSYM LEFT_ADD_DISTRIB ] THEN ONCE_REWRITE_TAC [ MULT_COMM ] THEN IMP_RES_THEN ( fn th => REWRITE_TAC [ th ] ) MOD_TIMES
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_TIMES2" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 76347*)j\"", "]", 
"boolLib.STRIP_ASSUME_TAC", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", "(", 
"Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 76411*)k\"", "]", 
"boolLib.STRIP_ASSUME_TAC", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 76462*)q = j DIV n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 76523*)r = j MOD n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 76584*)u = k DIV n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 76645*)v = k MOD n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.NTAC", "2", "(", 
"boolLib.FIRST_X_ASSUM", "boolLib.SUBST_ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LEFT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"LEFT_ADD_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "move_var_left" "let fun move_var_left s = ( boolLib.FREEZE_THEN ( fn th1 => boolLib.FREEZE_THEN ( fn th2 => boolLib.FREEZE_THEN ( fn th3 => boolLib.CONV_TAC ( boolLib.REDEPTH_CONV ( boolLib.FIRST_CONV ( map ( boolLib.CHANGED_CONV o boolLib.REWR_CONV ) [ th1 , th2 , th3 ] ) ) ) ) ( boolLib.CONV_RULE ( boolLib.STRIP_QUANT_CONV ( boolLib.LAND_CONV ( boolLib.LAND_CONV ( boolLib.REWR_CONV ( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) ) ) hhs_infixl0_open boolLib.THENC hhs_infixl0_close boolLib.REWR_CONV ( boolLib.GSYM ( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) ) ) ) ) ) ( boolLib.GSYM ( HolKernel.SPEC ( HolKernel.mk_var ( s , ( Parse.Type [ HolKernel.QUOTE \" (*#loc 1 75502*):num\" ] ) ) ) ( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) ) ) ) ) ) ( boolLib.GSYM ( HolKernel.SPEC ( HolKernel.mk_var ( s , ( Parse.Type [ HolKernel.QUOTE \" (*#loc 1 75502*):num\" ] ) ) ) ( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) ) ) ) ) ( boolLib.GSYM ( HolKernel.SPEC ( HolKernel.mk_var ( s , ( Parse.Type [ HolKernel.QUOTE \" (*#loc 1 75502*):num\" ] ) ) ) ( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) ) ) ) ) in move_var_left end", 
"\"n\"", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "LEFT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"LEFT_ADD_DISTRIB\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_THEN", 
"(", "fn", "th", "=>", "boolLib.REWRITE_TAC", "[", "th", "]", ")", 
hhsRecord.fetch "MOD_TIMES" "( ( DB.fetch \"arithmetic\" \"MOD_TIMES\" ) )" ] )
in hhsRecord.try_record_proof "MOD_TIMES2" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_COMMON_FACTOR = store_thm ( "MOD_COMMON_FACTOR" , ( Parse.Term [ QUOTE " (*#loc 1 77020*)!n p q. 0 < n /\\ 0 < q ==> (n * (p MOD q) = (n * p) MOD (n * q))" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 77126*)q" ] MP_TAC DIVISION THEN ASM_REWRITE_TAC [ ] THEN DISCH_THEN ( Q.SPEC_THEN [ QUOTE " (*#loc 1 77201*)p" ] STRIP_ASSUME_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 77243*)u = p DIV q" ] THEN POP_ASSUM ( K ALL_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 77304*)v = p MOD q" ] THEN POP_ASSUM ( K ALL_TAC ) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [ LEFT_ADD_DISTRIB ] THEN move_var_left "u" THEN ASM_SIMP_TAC bool_ss [ MOD_TIMES , LESS_MULT2 ] THEN SUFF_TAC ( Parse.Term [ QUOTE " (*#loc 1 77511*)n * v < n * q" ] ) THENL [ mesonLib.MESON_TAC [ LESS_MOD ] , ALL_TAC ] THEN SUFF_TAC ( Parse.Term [ QUOTE " (*#loc 1 77630*)?m. n = SUC m" ] ) THENL [ STRIP_TAC THEN ASM_REWRITE_TAC [ LESS_MULT_MONO ] , mesonLib.ASM_MESON_TAC [ LESS_REFL , num_CASES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_COMMON_FACTOR" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 77126*)q\"", "]", "boolLib.MP_TAC", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", 
"(", "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 77201*)p\"", "]", 
"boolLib.STRIP_ASSUME_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 77243*)u = p DIV q\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 77304*)v = p MOD q\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_X_ASSUM", 
"boolLib.SUBST_ALL_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LEFT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"LEFT_ADD_DISTRIB\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "move_var_left" "let fun move_var_left s = ( boolLib.FREEZE_THEN ( fn th1 => boolLib.FREEZE_THEN ( fn th2 => boolLib.FREEZE_THEN ( fn th3 => boolLib.CONV_TAC ( boolLib.REDEPTH_CONV ( boolLib.FIRST_CONV ( map ( boolLib.CHANGED_CONV o boolLib.REWR_CONV ) [ th1 , th2 , th3 ] ) ) ) ) ( boolLib.CONV_RULE ( boolLib.STRIP_QUANT_CONV ( boolLib.LAND_CONV ( boolLib.LAND_CONV ( boolLib.REWR_CONV ( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) ) ) hhs_infixl0_open boolLib.THENC hhs_infixl0_close boolLib.REWR_CONV ( boolLib.GSYM ( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) ) ) ) ) ) ( boolLib.GSYM ( HolKernel.SPEC ( HolKernel.mk_var ( s , ( Parse.Type [ HolKernel.QUOTE \" (*#loc 1 75502*):num\" ] ) ) ) ( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) ) ) ) ) ) ( boolLib.GSYM ( HolKernel.SPEC ( HolKernel.mk_var ( s , ( Parse.Type [ HolKernel.QUOTE \" (*#loc 1 75502*):num\" ] ) ) ) ( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) ) ) ) ) ( boolLib.GSYM ( HolKernel.SPEC ( HolKernel.mk_var ( s , ( Parse.Type [ HolKernel.QUOTE \" (*#loc 1 75502*):num\" ] ) ) ) ( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) ) ) ) ) in move_var_left end", 
"\"u\"", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.ASM_SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MOD_TIMES" "( ( DB.fetch \"arithmetic\" \"MOD_TIMES\" ) )", 
",", 
hhsRecord.fetch "LESS_MULT2" "( ( DB.fetch \"arithmetic\" \"LESS_MULT2\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUFF_TAC", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 77511*)n * v < n * q\"", "]", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "mesonLib.MESON_TAC", 
"[", 
hhsRecord.fetch "LESS_MOD" "( ( DB.fetch \"arithmetic\" \"LESS_MOD\" ) )", 
"]", ",", "boolLib.ALL_TAC", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.SUFF_TAC", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 77630*)?m. n = SUC m\"", "]", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_MULT_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_MULT_MONO\" ) )", 
"]", ",", "mesonLib.ASM_MESON_TAC", "[", "prim_recTheory.LESS_REFL", ",", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "MOD_COMMON_FACTOR" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val X_MOD_Y_EQ_X = store_thm ( "X_MOD_Y_EQ_X" , ( Parse.Term [ QUOTE " (*#loc 1 77815*)!x y. 0 < y ==> ((x MOD y = x) = x < y)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN EQ_TAC THENL [ mesonLib.ASM_MESON_TAC [ DIVISION ] , STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 78003*)0" ] THEN ASM_REWRITE_TAC [ MULT_CLAUSES , ADD_CLAUSES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "X_MOD_Y_EQ_X" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"mesonLib.ASM_MESON_TAC", "[", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"]", ",", "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 78003*)0\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "X_MOD_Y_EQ_X" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIV_LE_MONOTONE = store_thm ( "DIV_LE_MONOTONE" , ( Parse.Term [ QUOTE " (*#loc 1 78118*)!n x y. 0 < n /\\ x <= y ==> x DIV n <= y DIV n" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 78211*)~(n = 0)" ] ASSUME_TAC THENL [ ASM_REWRITE_TAC [ NOT_ZERO_LT_ZERO ] , ALL_TAC ] THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 78316*)n" ] MP_TAC DIVISION THEN ASM_REWRITE_TAC [ ] THEN DISCH_THEN ( fn th => Q.SPEC_THEN [ QUOTE " (*#loc 1 78400*)x" ] STRIP_ASSUME_TAC th THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 78464*)y" ] STRIP_ASSUME_TAC th ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 78509*)q = x DIV n" ] THEN POP_ASSUM ( K ALL_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 78570*)r = y DIV n" ] THEN POP_ASSUM ( K ALL_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 78631*)d = x MOD n" ] THEN POP_ASSUM ( K ALL_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 78692*)e = y MOD n" ] THEN POP_ASSUM ( K ALL_TAC ) THEN SRW_TAC [ ] [ ] THEN CCONTR_TAC THEN POP_ASSUM ( ASSUME_TAC o REWRITE_RULE [ NOT_LEQ ] ) THEN Q.SPECL_THEN [ [ QUOTE " (*#loc 1 78847*)SUC r" ] , [ QUOTE " (*#loc 1 78856*)n" ] , [ QUOTE " (*#loc 1 78861*)q" ] ] MP_TAC LE_MULT_RCANCEL THEN ASM_REWRITE_TAC [ ] THEN STRIP_TAC THEN POP_ASSUM ( ASSUME_TAC o REWRITE_RULE [ MULT_CLAUSES ] ) THEN Q.SPECL_THEN [ [ QUOTE " (*#loc 1 79066*)e" ] , [ QUOTE " (*#loc 1 79071*)n" ] , [ QUOTE " (*#loc 1 79076*)r * n" ] ] MP_TAC LT_ADD_LCANCEL THEN ASM_REWRITE_TAC [ ] THEN STRIP_TAC THEN Q.SPECL_THEN [ [ QUOTE " (*#loc 1 79176*)q * n" ] , [ QUOTE " (*#loc 1 79185*)d" ] ] ASSUME_TAC LESS_EQ_ADD THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 79283*)r * n + e < r * n + e" ] ( CONTR_TAC o MATCH_MP LESS_REFL ) THEN MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 79397*)q * n + d" ] THEN ASM_REWRITE_TAC [ ] THEN MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 79492*)r * n + n" ] THEN ASM_REWRITE_TAC [ ] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 79580*)q * n" ] THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_LE_MONOTONE" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 78211*)~(n = 0)\"", "]", "boolLib.ASSUME_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]", ",", "boolLib.ALL_TAC", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 78316*)n\"", "]", 
"boolLib.MP_TAC", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", 
"(", "fn", "th", "=>", "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 78400*)x\"", "]", 
"boolLib.STRIP_ASSUME_TAC", "th", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 78464*)y\"", "]", "boolLib.STRIP_ASSUME_TAC", "th", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 78509*)q = x DIV n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 78570*)r = y DIV n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 78631*)d = x MOD n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 78692*)e = y MOD n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.CCONTR_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.POP_ASSUM", "(", "boolLib.ASSUME_TAC", "o", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "NOT_LEQ" "( ( DB.fetch \"arithmetic\" \"NOT_LEQ\" ) )", "]", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPECL_THEN", "[", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 78847*)SUC r\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 78856*)n\"", "]", ",", "[", "HolKernel.QUOTE", "\" (*#loc 1 78861*)q\"", 
"]", "]", "boolLib.MP_TAC", 
hhsRecord.fetch "LE_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_RCANCEL\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"boolLib.ASSUME_TAC", "o", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPECL_THEN", "[", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 79066*)e\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 79071*)n\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 79076*)r * n\"", "]", "]", "boolLib.MP_TAC", 
hhsRecord.fetch "LT_ADD_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_ADD_LCANCEL\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPECL_THEN", "[", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 79176*)q * n\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 79185*)d\"", "]", "]", "boolLib.ASSUME_TAC", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 79283*)r * n + e < r * n + e\"", "]", "(", 
"boolLib.CONTR_TAC", "o", "boolLib.MATCH_MP", "prim_recTheory.LESS_REFL", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_EQ_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 79397*)q * n + d\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_EQ_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 79492*)r * n + n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 79580*)q * n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "DIV_LE_MONOTONE" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val LE_LT1 = store_thm ( "LE_LT1" , ( Parse.Term [ QUOTE " (*#loc 1 79654*)!x y. x <= y = x < y + 1" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ LESS_OR_EQ , GSYM ADD1 , IMP_ANTISYM_RULE ( SPEC_ALL prim_recTheory.LESS_LEMMA1 ) ( SPEC_ALL prim_recTheory.LESS_LEMMA2 ) ] THEN REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LE_LT1" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", ",", 
"boolLib.IMP_ANTISYM_RULE", "(", "boolLib.SPEC_ALL", "prim_recTheory.LESS_LEMMA1", 
")", "(", "boolLib.SPEC_ALL", "prim_recTheory.LESS_LEMMA2", ")", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.EQ_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]" ] )
in hhsRecord.try_record_proof "LE_LT1" false tactictoe_tac2 tactictoe_tac1
end )
;
val X_LE_DIV = store_thm ( "X_LE_DIV" , ( Parse.Term [ QUOTE " (*#loc 1 79979*)!x y z. 0 < z ==> (x <= y DIV z = x * z <= y)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 80068*)z" ] MP_TAC DIVISION THEN ASM_REWRITE_TAC [ ] THEN DISCH_THEN ( Q.SPEC_THEN [ QUOTE " (*#loc 1 80145*)y" ] STRIP_ASSUME_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 80187*)q = y DIV z" ] THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 80221*)r = y MOD z" ] THEN ASM_REWRITE_TAC [ ] THEN EQ_TAC THENL [ STRIP_TAC THEN MATCH_MP_TAC LESS_EQ_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 80347*)q * z" ] THEN ASM_SIMP_TAC bool_ss [ LE_MULT_RCANCEL , LESS_EQ_ADD ] , STRIP_TAC THEN REWRITE_TAC [ LE_LT1 ] THEN Q_TAC SUFF_TAC [ QUOTE " (*#loc 1 80481*)x * z < (q + 1) * z" ] >>- 1 ?? SIMP_TAC bool_ss [ LT_MULT_RCANCEL ] THEN REWRITE_TAC [ RIGHT_ADD_DISTRIB , MULT_CLAUSES ] THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 80689*)q * z + r" ] THEN ASM_SIMP_TAC bool_ss [ LT_ADD_LCANCEL ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "X_LE_DIV" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 80068*)z\"", "]", "boolLib.MP_TAC", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", 
"(", "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 80145*)y\"", "]", 
"boolLib.STRIP_ASSUME_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 80187*)q = y DIV z\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 80221*)r = y MOD z\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 80347*)q * z\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "LE_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_RCANCEL\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
"]", ",", "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LE_LT1" "( ( DB.fetch \"arithmetic\" \"LE_LT1\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.Q_TAC", 
"boolLib.SUFF_TAC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 80481*)x * z < (q + 1) * z\"", "]", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "LT_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_MULT_RCANCEL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQ_LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 80689*)q * z + r\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "LT_ADD_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_ADD_LCANCEL\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "X_LE_DIV" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val X_LT_DIV = store_thm ( "X_LT_DIV" , ( Parse.Term [ QUOTE " (*#loc 1 80796*)!x y z. 0 < z ==> (x < y DIV z = (x + 1) * z <= y)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 80890*)z" ] MP_TAC DIVISION THEN ASM_REWRITE_TAC [ ] THEN DISCH_THEN ( Q.SPEC_THEN [ QUOTE " (*#loc 1 80967*)y" ] STRIP_ASSUME_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 81009*)q = y DIV z" ] THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 81043*)r = y MOD z" ] THEN ASM_REWRITE_TAC [ ] THEN EQ_TAC THENL [ STRIP_TAC THEN MATCH_MP_TAC LESS_EQ_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 81169*)q * z" ] THEN ASM_SIMP_TAC bool_ss [ LE_MULT_RCANCEL , LESS_EQ_ADD ] THEN ASM_SIMP_TAC bool_ss [ LE_LT1 , LT_ADD_RCANCEL ] , STRIP_TAC THEN CCONTR_TAC THEN POP_ASSUM ( ASSUME_TAC o REWRITE_RULE [ NOT_LESS ] ) THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 81410*)(x + 1) * z  <= x * z + r" ] ASSUME_TAC THENL [ MATCH_MP_TAC LESS_EQ_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 81514*)q * z + r" ] THEN ASM_SIMP_TAC bool_ss [ LE_ADD_RCANCEL , LE_MULT_RCANCEL ] , POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [ RIGHT_ADD_DISTRIB , MULT_CLAUSES , LE_ADD_LCANCEL , GSYM NOT_LESS , LT_ADD_LCANCEL ] ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "X_LT_DIV" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 80890*)z\"", "]", "boolLib.MP_TAC", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", 
"(", "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 80967*)y\"", "]", 
"boolLib.STRIP_ASSUME_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 81009*)q = y DIV z\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 81043*)r = y MOD z\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 81169*)q * z\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "LE_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_RCANCEL\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "LE_LT1" "( ( DB.fetch \"arithmetic\" \"LE_LT1\" ) )", ",", 
hhsRecord.fetch "LT_ADD_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_ADD_RCANCEL\" ) )", 
"]", ",", "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.CCONTR_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.POP_ASSUM", "(", "boolLib.ASSUME_TAC", "o", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 81410*)(x + 1) * z  <= x * z + r\"", "]", 
"boolLib.ASSUME_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 81514*)q * z + r\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "LE_ADD_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_ADD_RCANCEL\" ) )", 
",", 
hhsRecord.fetch "LE_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_RCANCEL\" ) )", 
"]", ",", "boolLib.POP_ASSUM", "boolLib.MP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "LE_ADD_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_ADD_LCANCEL\" ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LT_ADD_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_ADD_LCANCEL\" ) )", 
"]", "]", "]" ] )
in hhsRecord.try_record_proof "X_LT_DIV" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIV_LT_X = store_thm ( "DIV_LT_X" , ( Parse.Term [ QUOTE " (*#loc 1 81824*)!x y z. 0 < z ==> (y DIV z < x = y < x * z)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN REWRITE_TAC [ GSYM NOT_LESS_EQUAL ] THEN AP_TERM_TAC THEN MATCH_MP_TAC X_LE_DIV THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_LT_X" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.GSYM", 
hhsRecord.fetch "NOT_LESS_EQUAL" "( ( DB.fetch \"arithmetic\" \"NOT_LESS_EQUAL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.AP_TERM_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "X_LE_DIV" "( ( DB.fetch \"arithmetic\" \"X_LE_DIV\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "DIV_LT_X" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIV_LE_X = store_thm ( "DIV_LE_X" , ( Parse.Term [ QUOTE " (*#loc 1 82049*)!x y z. 0 < z ==> (y DIV z <= x = y < (x + 1) * z)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN CONV_TAC ( FORK_CONV ( REWR_CONV ( GSYM NOT_LESS ) , REWR_CONV ( GSYM NOT_LESS_EQUAL ) ) ) THEN AP_TERM_TAC THEN MATCH_MP_TAC X_LT_DIV THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_LE_X" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", "(", 
"boolLib.FORK_CONV", "(", "boolLib.REWR_CONV", "(", "boolLib.GSYM", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
")", ",", "boolLib.REWR_CONV", "(", "boolLib.GSYM", 
hhsRecord.fetch "NOT_LESS_EQUAL" "( ( DB.fetch \"arithmetic\" \"NOT_LESS_EQUAL\" ) )", 
")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.AP_TERM_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "X_LT_DIV" "( ( DB.fetch \"arithmetic\" \"X_LT_DIV\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "DIV_LE_X" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIV_EQ_X = store_thm ( "DIV_EQ_X" , ( Parse.Term [ QUOTE " (*#loc 1 82352*)!x y z. 0 < z ==> ((y DIV z = x) = x * z <= y /\\ y < SUC x * z)" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ EQ_LESS_EQ , DIV_LE_X , X_LE_DIV , GSYM ADD1 , AC CONJ_COMM CONJ_ASSOC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_EQ_X" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "EQ_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"EQ_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "DIV_LE_X" "( ( DB.fetch \"arithmetic\" \"DIV_LE_X\" ) )", 
",", 
hhsRecord.fetch "X_LE_DIV" "( ( DB.fetch \"arithmetic\" \"X_LE_DIV\" ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", ",", 
"simpLib.AC", "boolLib.CONJ_COMM", "boolLib.CONJ_ASSOC", "]" ] )
in hhsRecord.try_record_proof "DIV_EQ_X" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIV_MOD_MOD_DIV = store_thm ( "DIV_MOD_MOD_DIV" , ( Parse.Term [ QUOTE " (*#loc 1 82568*)!m n k. 0 < n /\\ 0 < k ==> ((m DIV n) MOD k = (m MOD (n * k)) DIV n)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 82683*)0 < n * k" ] ASSUME_TAC THENL [ ASM_REWRITE_TAC [ ZERO_LESS_MULT ] , ALL_TAC ] THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 82787*)n * k" ] MP_TAC DIVISION THEN ASM_REWRITE_TAC [ ] THEN DISCH_THEN ( Q.SPEC_THEN [ QUOTE " (*#loc 1 82866*)m" ] STRIP_ASSUME_TAC ) THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 82908*)q = m DIV (n * k)" ] THEN Q.ABBREV_TAC [ QUOTE " (*#loc 1 82948*)r = m MOD (n * k)" ] THEN markerLib.RM_ALL_ABBREVS_TAC THEN ASM_REWRITE_TAC [ ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 83052*)q * (n * k) = (q * k) * n" ] SUBST1_TAC THENL [ SIMP_TAC bool_ss [ AC MULT_ASSOC MULT_COMM ] , ALL_TAC ] THEN ASM_SIMP_TAC bool_ss [ ADD_DIV_ADD_DIV , MOD_TIMES ] THEN MATCH_MP_TAC LESS_MOD THEN ASM_SIMP_TAC bool_ss [ DIV_LT_X ] THEN FULL_SIMP_TAC bool_ss [ AC MULT_ASSOC MULT_COMM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_MOD_MOD_DIV" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 82683*)0 < n * k\"", "]", "boolLib.ASSUME_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "ZERO_LESS_MULT" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_MULT\" ) )", 
"]", ",", "boolLib.ALL_TAC", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 82787*)n * k\"", "]", 
"boolLib.MP_TAC", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", 
"(", "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 82866*)m\"", "]", 
"boolLib.STRIP_ASSUME_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 82908*)q = m DIV (n * k)\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 82948*)r = m MOD (n * k)\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"markerLib.RM_ALL_ABBREVS_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 83052*)q * (n * k) = (q * k) * n\"", "]", 
"boolLib.SUBST1_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", "simpLib.AC", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", ",", "boolLib.ALL_TAC", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.ASM_SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_DIV_ADD_DIV" "( ( DB.fetch \"arithmetic\" \"ADD_DIV_ADD_DIV\" ) )", 
",", 
hhsRecord.fetch "MOD_TIMES" "( ( DB.fetch \"arithmetic\" \"MOD_TIMES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_MOD" "( ( DB.fetch \"arithmetic\" \"LESS_MOD\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "DIV_LT_X" "( ( DB.fetch \"arithmetic\" \"DIV_LT_X\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", "simpLib.AC", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "DIV_MOD_MOD_DIV" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MULT_EQ_DIV = store_thm ( "MULT_EQ_DIV" , ( Parse.Term [ QUOTE " (*#loc 1 83390*)0 < x ==> ((x * y = z) = (y = z DIV x) /\\ (z MOD x = 0))" ] ) ,
let
val tactictoe_tac1 = STRIP_TAC THEN EQ_TAC THENL [ DISCH_THEN ( SUBST_ALL_TAC o SYM ) THEN ONCE_REWRITE_TAC [ MULT_COMM ] THEN ASM_SIMP_TAC bool_ss [ MOD_EQ_0 , MULT_DIV ] , Q.SPEC_THEN [ QUOTE " (*#loc 1 83627*)x" ] MP_TAC DIVISION THEN ASM_REWRITE_TAC [ ] THEN DISCH_THEN ( Q.SPEC_THEN [ QUOTE " (*#loc 1 83704*)z" ] STRIP_ASSUME_TAC ) THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC bool_ss [ ADD_CLAUSES , MULT_COMM ] THEN ONCE_REWRITE_TAC [ EQ_SYM_EQ ] THEN FIRST_ASSUM ACCEPT_TAC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_EQ_DIV" 
 ( String.concatWith " " 
 [ "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.EQ_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.DISCH_THEN", "(", "boolLib.SUBST_ALL_TAC", "o", "HolKernel.SYM", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ONCE_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MOD_EQ_0" "( ( DB.fetch \"arithmetic\" \"MOD_EQ_0\" ) )", 
",", 
hhsRecord.fetch "MULT_DIV" "( ( DB.fetch \"arithmetic\" \"MULT_DIV\" ) )", 
"]", ",", "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 83627*)x\"", "]", 
"boolLib.MP_TAC", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", 
"(", "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 83704*)z\"", "]", 
"boolLib.STRIP_ASSUME_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.FULL_SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ONCE_REWRITE_TAC", "[", "boolLib.EQ_SYM_EQ", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", "]" ] )
in hhsRecord.try_record_proof "MULT_EQ_DIV" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NUMERAL_MULT_EQ_DIV = store_thm ( "NUMERAL_MULT_EQ_DIV" , ( Parse.Term [ QUOTE " (*#loc 1 83945*)((NUMERAL (BIT1 x) * y = NUMERAL z) =        (y = NUMERAL z DIV NUMERAL (BIT1 x)) /\\        (NUMERAL z MOD NUMERAL(BIT1 x) = 0)) /\\     ((NUMERAL (BIT2 x) * y = NUMERAL z) =        (y = NUMERAL z DIV NUMERAL (BIT2 x)) /\\        (NUMERAL z MOD NUMERAL(BIT2 x) = 0))" ] ) ,
let
val tactictoe_tac1 = CONJ_TAC THEN MATCH_MP_TAC MULT_EQ_DIV THEN REWRITE_TAC [ NUMERAL_DEF , BIT1 , BIT2 , ADD_CLAUSES , LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NUMERAL_MULT_EQ_DIV" 
 ( String.concatWith " " 
 [ "boolLib.CONJ_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MULT_EQ_DIV" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_DIV\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", hhsRecord.fetch "BIT1" "( ( DB.fetch \"arithmetic\" \"BIT1\" ) )", ",", 
hhsRecord.fetch "BIT2" "( ( DB.fetch \"arithmetic\" \"BIT2\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "NUMERAL_MULT_EQ_DIV" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_EQ_0_DIVISOR = Q.store_thm ( "MOD_EQ_0_DIVISOR" , [ QUOTE " (*#loc 1 84380*)0 < n ==> ((k MOD n = 0) = (?d. k = d * n))" ] ,
let
val tactictoe_tac1 = DISCH_TAC THEN EQ_TAC >>- 1 ?? ( DISCH_TAC THEN EXISTS_TAC ( Parse.Term [ QUOTE " (*#loc 1 84489*)k DIV n" ] ) THEN MATCH_MP_TAC EQ_SYM THEN SRW_TAC [ ] [ Once MULT_SYM ] THEN MATCH_MP_TAC ( MP_CANON ( DISCH_ALL ( # 2 ( EQ_IMP_RULE ( UNDISCH MULT_EQ_DIV ) ) ) ) ) THEN SRW_TAC [ ] [ ] ) THEN SRW_TAC [ ] [ ] THEN SRW_TAC [ ] [ MOD_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_EQ_0_DIVISOR" 
 ( String.concatWith " " 
 [ "boolLib.DISCH_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.EQ_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.DISCH_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 84489*)k DIV n\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
"boolLib.EQ_SYM", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.SRW_TAC", "[", "]", "[", "boolLib.Once", 
hhsRecord.fetch "MULT_SYM" "( ( DB.fetch \"arithmetic\" \"MULT_SYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
"(", "boolLib.MP_CANON", "(", "boolLib.DISCH_ALL", "(", "#", "2", "(", 
"HolKernel.EQ_IMP_RULE", "(", "boolLib.UNDISCH", 
hhsRecord.fetch "MULT_EQ_DIV" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_DIV\" ) )", 
")", ")", ")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.SRW_TAC", "[", "]", "[", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "MOD_EQ_0" "( ( DB.fetch \"arithmetic\" \"MOD_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MOD_EQ_0_DIVISOR" false tactictoe_tac2 tactictoe_tac1
end )
;
val MOD_SUC = Q.store_thm ( "MOD_SUC" , [ QUOTE " (*#loc 1 84749*)0 < y /\\ (SUC x <> (SUC (x DIV y)) * y) ==> ((SUC x) MOD y = SUC (x MOD y))" ] ,
let
val tactictoe_tac1 = STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 84885*)x DIV y" ] THEN [ QUOTE " (*#loc 1 84900*)x = x DIV y * y + x MOD y" ] by PROVE_TAC [ DIVISION ] THEN [ QUOTE " (*#loc 1 84957*)x MOD y < y" ] by PROVE_TAC [ MOD_LESS ] THEN FULL_SIMP_TAC bool_ss [ prim_recTheory.INV_SUC_EQ , ADD_CLAUSES , MULT_CLAUSES ] THEN MATCH_MP_TAC LESS_NOT_SUC THEN CONJ_TAC >>- 1 ?? FIRST_ASSUM ACCEPT_TAC THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN [ QUOTE " (*#loc 1 85191*)SUC x = SUC (x DIV y * y + x MOD y)" ] by ( AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC ) THEN FULL_SIMP_TAC bool_ss [ ADD_SUC ] THEN PROVE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_SUC" 
 ( String.concatWith " " 
 [ "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 84885*)x DIV y\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 84900*)x = x DIV y * y + x MOD y\"", "]", 
"hhs_infixl8_open BasicProvers.by hhs_infixl8_close", 
"BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 84957*)x MOD y < y\"", "]", 
"hhs_infixl8_open BasicProvers.by hhs_infixl8_close", 
"BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "MOD_LESS" "( ( DB.fetch \"arithmetic\" \"MOD_LESS\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", "prim_recTheory.INV_SUC_EQ", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_NOT_SUC" "( ( DB.fetch \"arithmetic\" \"LESS_NOT_SUC\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.SPOSE_NOT_THEN", "boolLib.STRIP_ASSUME_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 85191*)SUC x = SUC (x DIV y * y + x MOD y)\"", "]", 
"hhs_infixl8_open BasicProvers.by hhs_infixl8_close", "(", 
"boolLib.AP_TERM_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.FIRST_ASSUM", "boolLib.ACCEPT_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "MOD_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
val MOD_SUC_IFF = Q.store_thm ( "MOD_SUC_IFF" , [ QUOTE " (*#loc 1 85384*)0 < y ==> ((SUC x MOD y = SUC (x MOD y)) <=> (SUC x <> SUC (x DIV y) * y))" ] ,
let
val tactictoe_tac1 = PROVE_TAC [ MOD_SUC , SUC_NOT , MOD_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_SUC_IFF" 
 ( String.concatWith " " 
 [ "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "MOD_SUC" "( ( DB.fetch \"arithmetic\" \"MOD_SUC\" ) )", ",", 
hhsRecord.fetch "SUC_NOT" "( ( DB.fetch \"arithmetic\" \"SUC_NOT\" ) )", ",", 
hhsRecord.fetch "MOD_EQ_0" "( ( DB.fetch \"arithmetic\" \"MOD_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MOD_SUC_IFF" false tactictoe_tac2 tactictoe_tac1
end )
;
val ONE_MOD = Q.store_thm ( "ONE_MOD" , [ QUOTE " (*#loc 1 85544*)1 < n ==> (1 MOD n = 1)" ] ,
let
val tactictoe_tac1 = STRIP_TAC THEN [ QUOTE " (*#loc 1 85592*)0 < n" ] by ( MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC ( Parse.Term [ QUOTE " (*#loc 1 85657*)1" ] ) THEN SRW_TAC [ ] [ LESS_SUC_REFL , ONE ] ) THEN SUFF_TAC ( Parse.Term [ QUOTE " (*#loc 1 85724*)SUC 0 MOD n = SUC (0 MOD n)" ] ) >>- 1 ?? SRW_TAC [ ] [ ZERO_MOD , ONE ] THEN MATCH_MP_TAC MOD_SUC THEN SRW_TAC [ ] [ ZERO_DIV , MULT , ADD , LESS_NOT_EQ , GSYM ONE ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ONE_MOD" 
 ( String.concatWith " " 
 [ "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 85592*)0 < n\"", "]", 
"hhs_infixl8_open BasicProvers.by hhs_infixl8_close", "(", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 85657*)1\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "prim_recTheory.LESS_SUC_REFL", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUFF_TAC", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 85724*)SUC 0 MOD n = SUC (0 MOD n)\"", "]", ")", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", 
hhsRecord.fetch "ZERO_MOD" "( ( DB.fetch \"arithmetic\" \"ZERO_MOD\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_SUC" "( ( DB.fetch \"arithmetic\" \"MOD_SUC\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", 
hhsRecord.fetch "ZERO_DIV" "( ( DB.fetch \"arithmetic\" \"ZERO_DIV\" ) )", 
",", hhsRecord.fetch "MULT" "", ",", hhsRecord.fetch "ADD" "", ",", 
"prim_recTheory.LESS_NOT_EQ", ",", "boolLib.GSYM", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]" ] )
in hhsRecord.try_record_proof "ONE_MOD" false tactictoe_tac2 tactictoe_tac1
end )
;
val ONE_MOD_IFF = Q.store_thm ( "ONE_MOD_IFF" , [ QUOTE " (*#loc 1 85930*)1 < n <=> 0 < n /\\ (1 MOD n = 1)" ] ,
let
val tactictoe_tac1 = EQ_TAC >>- 1 ?? ( SRW_TAC [ ] [ ONE_MOD ] THEN MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC ( Parse.Term [ QUOTE " (*#loc 1 86066*)1" ] ) THEN SRW_TAC [ ] [ LESS_SUC_REFL , ONE ] ) THEN STRUCT_CASES_TAC ( SPEC ( Parse.Term [ QUOTE " (*#loc 1 86147*)n:num" ] ) num_CASES ) >>- 1 ?? ( SIMP_TAC bool_ss [ LESS_REFL ] ) THEN SIMP_TAC bool_ss [ ONE ] THEN STRIP_TAC THEN MATCH_MP_TAC LESS_MONO THEN Q.MATCH_RENAME_TAC [ QUOTE " (*#loc 1 86319*)0 < m" ] THEN FULL_STRUCT_CASES_TAC ( SPEC ( Parse.Term [ QUOTE " (*#loc 1 86365*)m:num" ] ) num_CASES ) >>- 1 ?? ( FULL_SIMP_TAC bool_ss [ MOD_ONE , SUC_NOT ] ) THEN SIMP_TAC bool_ss [ LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ONE_MOD_IFF" 
 ( String.concatWith " " 
 [ "boolLib.EQ_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "BasicProvers.SRW_TAC", "[", 
"]", "[", 
hhsRecord.fetch "ONE_MOD" "( ( DB.fetch \"arithmetic\" \"ONE_MOD\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 86066*)1\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "prim_recTheory.LESS_SUC_REFL", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRUCT_CASES_TAC", 
"(", "HolKernel.SPEC", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 86147*)n:num\"", "]", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", "prim_recTheory.LESS_REFL", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
"prim_recTheory.LESS_MONO", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.MATCH_RENAME_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 86319*)0 < m\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.FULL_STRUCT_CASES_TAC", "(", "HolKernel.SPEC", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 86365*)m:num\"", "]", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MOD_ONE" "( ( DB.fetch \"arithmetic\" \"MOD_ONE\" ) )", ",", 
hhsRecord.fetch "SUC_NOT" "( ( DB.fetch \"arithmetic\" \"SUC_NOT\" ) )", "]", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "ONE_MOD_IFF" false tactictoe_tac2 tactictoe_tac1
end )
;
val MOD_LESS_EQ = Q.store_thm ( "MOD_LESS_EQ" , [ QUOTE " (*#loc 1 86525*)0 < y ==> x MOD y <= x" ] ,
let
val tactictoe_tac1 = STRIP_TAC THEN Cases_on [ QUOTE " (*#loc 1 86581*)x < y" ] >>- 1 ?? ( MATCH_MP_TAC ( snd ( EQ_IMP_RULE ( SPEC_ALL LESS_OR_EQ ) ) ) THEN DISJ2_TAC THEN MATCH_MP_TAC LESS_MOD THEN POP_ASSUM ACCEPT_TAC ) THEN MATCH_MP_TAC LESS_EQ_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 86798*)y" ] THEN CONJ_TAC >>- 1 ?? ( MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN MATCH_MP_TAC MOD_LESS THEN FIRST_ASSUM ACCEPT_TAC ) THEN IMP_RES_TAC NOT_LESS
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_LESS_EQ" 
 ( String.concatWith " " 
 [ "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.Cases_on", "[", "HolKernel.QUOTE", "\" (*#loc 1 86581*)x < y\"", "]", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.MATCH_MP_TAC", "(", 
"HolKernel.snd", "(", "HolKernel.EQ_IMP_RULE", "(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
")", ")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.DISJ2_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_MOD" "( ( DB.fetch \"arithmetic\" \"LESS_MOD\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", 
"boolLib.ACCEPT_TAC", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 86798*)y\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_IMP_LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_IMP_LESS_OR_EQ\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_LESS" "( ( DB.fetch \"arithmetic\" \"MOD_LESS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.IMP_RES_TAC", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )" ] )
in hhsRecord.try_record_proof "MOD_LESS_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
val MOD_LIFT_PLUS = Q.store_thm ( "MOD_LIFT_PLUS" , [ QUOTE " (*#loc 1 87015*)0 < n /\\ k < n - x MOD n ==> ((x + k) MOD n = x MOD n + k)" ] ,
let
val tactictoe_tac1 = Q.ID_SPEC_TAC [ QUOTE " (*#loc 1 87094*)k" ] THEN INDUCT_TAC >>- 1 ?? ( SIMP_TAC bool_ss [ ADD_0 ] ) THEN STRIP_TAC THEN [ QUOTE " (*#loc 1 87180*)x + SUC k = SUC (x + k)" ] by ( SIMP_TAC bool_ss [ ADD_CLAUSES ] ) THEN [ QUOTE " (*#loc 1 87257*)k < n - x MOD n" ] by ( MATCH_MP_TAC prim_recTheory.SUC_LESS THEN FIRST_ASSUM ACCEPT_TAC ) THEN FULL_SIMP_TAC bool_ss [ ] THEN MATCH_MP_TAC EQ_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 87441*)SUC (x MOD n + k)" ] THEN CONJ_TAC >>- 1 ?? ( MATCH_MP_TAC EQ_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 87536*)SUC ((x + k) MOD n)" ] THEN CONJ_TAC >>- 1 ?? ( MATCH_MP_TAC MOD_SUC THEN CONJ_TAC >>- 1 ?? FIRST_ASSUM ACCEPT_TAC THEN FULL_SIMP_TAC bool_ss [ ADD_SYM , ADD , SUB_LEFT_LESS , MULT_CLAUSES ] THEN [ QUOTE " (*#loc 1 87750*)SUC ((k + x) MOD n + (k + x) DIV n * n) < n + (k + x) DIV n * n" ] by PROVE_TAC [ LESS_MONO_ADD , ADD_SUC , ADD_SYM ] THEN PROVE_TAC [ DIVISION , ADD_SYM , LESS_REFL ] ) THEN AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC ) THEN SIMP_TAC bool_ss [ ADD_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_LIFT_PLUS" 
 ( String.concatWith " " 
 [ "Q.ID_SPEC_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 87094*)k\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 87180*)x + SUC k = SUC (x + k)\"", "]", 
"hhs_infixl8_open BasicProvers.by hhs_infixl8_close", "(", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 87257*)k < n - x MOD n\"", "]", 
"hhs_infixl8_open BasicProvers.by hhs_infixl8_close", "(", 
"boolLib.MATCH_MP_TAC", "prim_recTheory.SUC_LESS", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.FULL_SIMP_TAC", "BasicProvers.bool_ss", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
"boolLib.EQ_TRANS", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.EXISTS_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 87441*)SUC (x MOD n + k)\"", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.MATCH_MP_TAC", 
"boolLib.EQ_TRANS", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.EXISTS_TAC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 87536*)SUC ((x + k) MOD n)\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_SUC" "( ( DB.fetch \"arithmetic\" \"MOD_SUC\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.FULL_SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", ",", 
hhsRecord.fetch "ADD" "", ",", 
hhsRecord.fetch "SUB_LEFT_LESS" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_LESS\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 87750*)SUC ((k + x) MOD n + (k + x) DIV n * n) < n + (k + x) DIV n * n\"", 
"]", "hhs_infixl8_open BasicProvers.by hhs_infixl8_close", 
"BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "LESS_MONO_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_ADD\" ) )", 
",", hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", 
",", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
",", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
",", "prim_recTheory.LESS_REFL", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.AP_TERM_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", "]" ] )
in hhsRecord.try_record_proof "MOD_LIFT_PLUS" false tactictoe_tac2 tactictoe_tac1
end )
;
val MOD_LIFT_PLUS_IFF = Q.store_thm ( "MOD_LIFT_PLUS_IFF" , [ QUOTE " (*#loc 1 88075*)0 < n ==> (((x + k) MOD n = x MOD n + k) = (k < n - x MOD n))" ] ,
let
val tactictoe_tac1 = PROVE_TAC [ SUB_LEFT_LESS , ADD_SYM , MOD_LESS , MOD_LIFT_PLUS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_LIFT_PLUS_IFF" 
 ( String.concatWith " " 
 [ "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "SUB_LEFT_LESS" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_LESS\" ) )", 
",", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
",", 
hhsRecord.fetch "MOD_LESS" "( ( DB.fetch \"arithmetic\" \"MOD_LESS\" ) )", 
",", 
hhsRecord.fetch "MOD_LIFT_PLUS" "( ( DB.fetch \"arithmetic\" \"MOD_LIFT_PLUS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MOD_LIFT_PLUS_IFF" false tactictoe_tac2 tactictoe_tac1
end )
;
val num_case_cong = save_thm ( "num_case_cong" , Prim_rec.case_cong_thm num_CASES num_case_def )
;
;
val SUC_ELIM_THM = store_thm ( "SUC_ELIM_THM" , ( ( Parse.Term [ QUOTE " (*#loc 1 88350*)!P. (!n. P (SUC n) n) = (!n. (0 < n ==> P n (n-1)))" ] ) ) ,
let
val tactictoe_tac1 = GEN_TAC THEN EQ_TAC THENL [ REPEAT STRIP_TAC THEN FIRST_ASSUM ( MP_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 88502*)n-1" ] ) ) ) THEN SIMP_TAC bool_ss [ SUB_LEFT_SUC , ONE , SUB_MONO_EQ , SUB_0 , GSYM NOT_LESS ] THEN COND_CASES_TAC THENL [ STRIP_ASSUME_TAC ( SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 88688*)n:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 88701*)SUC 0" ] ) ] LESS_LESS_CASES ) THENL [ FULL_SIMP_TAC bool_ss [ ] , IMP_RES_TAC LESS_LESS_SUC ] , REWRITE_TAC [ ] ] , REPEAT STRIP_TAC THEN FIRST_ASSUM ( MP_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 88924*)n+1" ] ) ) ) THEN SIMP_TAC bool_ss [ GSYM ADD1 , SUC_SUB1 , LESS_0 ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUC_ELIM_THM" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.EQ_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", "(", 
"boolLib.MP_TAC", "o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 88502*)n-1\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "SUB_LEFT_SUC" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_SUC\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
"boolLib.GSYM", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.COND_CASES_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", 
"[", "boolLib.STRIP_ASSUME_TAC", "(", "boolLib.SPECL", "[", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 88688*)n:num\"", "]", ")", ",", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 88701*)SUC 0\"", "]", ")", "]", 
hhsRecord.fetch "LESS_LESS_CASES" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"simpLib.FULL_SIMP_TAC", "BasicProvers.bool_ss", "[", "]", ",", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_LESS_SUC" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_SUC\" ) )", 
"]", ",", "boolLib.REWRITE_TAC", "[", "]", "]", ",", "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", "(", 
"boolLib.MP_TAC", "o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 88924*)n+1\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", "boolLib.GSYM", 
hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", ",", 
hhsRecord.fetch "SUC_SUB1" "( ( DB.fetch \"arithmetic\" \"SUC_SUB1\" ) )", 
",", "prim_recTheory.LESS_0", "]", "]" ] )
in hhsRecord.try_record_proof "SUC_ELIM_THM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUC_ELIM_NUMERALS = store_thm ( "SUC_ELIM_NUMERALS" , ( Parse.Term [ QUOTE " (*#loc 1 89060*)!f g. (!n. g (SUC n) = f n (SUC n)) =           (!n. g (NUMERAL (BIT1 n)) =                f (NUMERAL (BIT1 n) - 1) (NUMERAL (BIT1 n))) /\\           (!n. g (NUMERAL (BIT2 n)) =                f (NUMERAL (BIT1 n)) (NUMERAL (BIT2 n)))" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC bool_ss [ NUMERAL_DEF , BIT1 , BIT2 , ALT_ZERO , ADD_CLAUSES , SUB_MONO_EQ , SUB_0 ] THEN REPEAT STRIP_TAC THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 89483*)n" ] STRIP_ASSUME_TAC EVEN_OR_ODD THEN POP_ASSUM ( Q.X_CHOOSE_THEN [ QUOTE " (*#loc 1 89550*)m" ] SUBST_ALL_TAC o REWRITE_RULE [ EVEN_EXISTS , ODD_EXISTS , TIMES2 ] ) THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUC_ELIM_NUMERALS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", hhsRecord.fetch "BIT1" "( ( DB.fetch \"arithmetic\" \"BIT1\" ) )", ",", 
hhsRecord.fetch "BIT2" "( ( DB.fetch \"arithmetic\" \"BIT2\" ) )", ",", 
hhsRecord.fetch "ALT_ZERO" "( ( DB.fetch \"arithmetic\" \"ALT_ZERO\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 89483*)n\"", "]", 
"boolLib.STRIP_ASSUME_TAC", 
hhsRecord.fetch "EVEN_OR_ODD" "( ( DB.fetch \"arithmetic\" \"EVEN_OR_ODD\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"Q.X_CHOOSE_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 89550*)m\"", "]", 
"boolLib.SUBST_ALL_TAC", "o", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "EVEN_EXISTS" "( ( DB.fetch \"arithmetic\" \"EVEN_EXISTS\" ) )", 
",", 
hhsRecord.fetch "ODD_EXISTS" "( ( DB.fetch \"arithmetic\" \"ODD_EXISTS\" ) )", 
",", hhsRecord.fetch "TIMES2" "( ( DB.fetch \"arithmetic\" \"TIMES2\" ) )", "]", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]" ] )
in hhsRecord.try_record_proof "SUC_ELIM_NUMERALS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_SUBR2 = prove ( ( Parse.Term [ QUOTE " (*#loc 1 89686*)!m n. m - (m + n) = 0" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ SUB_EQ_0 , LESS_EQ_ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_253" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "SUB_EQ_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_253" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_ELIM_THM = store_thm ( "SUB_ELIM_THM" , ( Parse.Term [ QUOTE " (*#loc 1 89803*)P (a - b) = !d. ((b = a + d) ==> P 0) /\\ ((a = b + d) ==> P d)" ] ) ,
let
val tactictoe_tac1 = DISJ_CASES_TAC ( SPECL [ ( Parse.Term [ QUOTE " (*#loc 1 89897*)a:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 89910*)b:num" ] ) ] LESS_EQ_CASES ) THEN FIRST_ASSUM ( X_CHOOSE_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 89971*)e:num" ] ) ) o REWRITE_RULE [ LESS_EQ_EXISTS ] ) THEN ASM_REWRITE_TAC [ ADD_SUB , ONCE_REWRITE_RULE [ ADD_SYM ] ADD_SUB , ADD_SUBR2 ] THEN REWRITE_TAC [ ONCE_REWRITE_RULE [ ADD_SYM ] EQ_MONO_ADD_EQ ] THEN CONV_TAC ( DEPTH_CONV FORALL_AND_CONV ) THEN GEN_REWRITE_TAC ( RAND_CONV o ONCE_DEPTH_CONV ) empty_rewrites [ EQ_SYM_EQ ] THEN REWRITE_TAC [ GSYM ADD_ASSOC , ADD_INV_0_EQ , ADD_EQ_0 ] THENL [ EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [ ] THEN FIRST_ASSUM ( fn th => MATCH_MP_TAC th THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 90469*)e:num" ] ) ) ) , EQ_TAC THENL [ DISCH_TAC THEN CONJ_TAC THEN GEN_TAC THEN DISCH_THEN ( REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC ) , DISCH_THEN ( MATCH_MP_TAC o CONJUNCT2 ) ] ] THEN ASM_REWRITE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_ELIM_THM" 
 ( String.concatWith " " 
 [ "boolLib.DISJ_CASES_TAC", "(", "boolLib.SPECL", "[", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 89897*)a:num\"", "]", ")", ",", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 89910*)b:num\"", "]", ")", "]", 
hhsRecord.fetch "LESS_EQ_CASES" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"(", "boolLib.X_CHOOSE_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 89971*)e:num\"", "]", ")", ")", "o", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "LESS_EQ_EXISTS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_EXISTS\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_SUB" "( ( DB.fetch \"arithmetic\" \"ADD_SUB\" ) )", ",", 
"boolLib.ONCE_REWRITE_RULE", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
hhsRecord.fetch "ADD_SUB" "( ( DB.fetch \"arithmetic\" \"ADD_SUB\" ) )", ",", 
hhsRecord.fetch "ADD_SUBR2" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.ONCE_REWRITE_RULE", "[", 
hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", "]", 
hhsRecord.fetch "EQ_MONO_ADD_EQ" "( ( DB.fetch \"arithmetic\" \"EQ_MONO_ADD_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", "(", 
"boolLib.DEPTH_CONV", "boolLib.FORALL_AND_CONV", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.GEN_REWRITE_TAC", 
"(", "boolLib.RAND_CONV", "o", "boolLib.ONCE_DEPTH_CONV", ")", 
"boolLib.empty_rewrites", "[", "boolLib.EQ_SYM_EQ", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", 
hhsRecord.fetch "ADD_INV_0_EQ" "( ( DB.fetch \"arithmetic\" \"ADD_INV_0_EQ\" ) )", 
",", 
hhsRecord.fetch "ADD_EQ_0" "( ( DB.fetch \"arithmetic\" \"ADD_EQ_0\" ) )", 
"]", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", "(", 
"fn", "th", "=>", "boolLib.MATCH_MP_TAC", "th", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 90469*)e:num\"", "]", ")", ")", ")", ",", 
"boolLib.EQ_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.DISCH_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.CONJ_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.DISCH_THEN", "(", "boolLib.REPEAT_TCL", "boolLib.CONJUNCTS_THEN", 
"boolLib.SUBST_ALL_TAC", ")", ",", "boolLib.DISCH_THEN", "(", "boolLib.MATCH_MP_TAC", 
"o", "HolKernel.CONJUNCT2", ")", "]", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "SUB_ELIM_THM" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val PRE_ELIM_THM = store_thm ( "PRE_ELIM_THM" , ( Parse.Term [ QUOTE " (*#loc 1 90728*)P (PRE n) = !m. ((n = 0) ==> P 0) /\\ ((n = SUC m) ==> P m)" ] ) ,
let
val tactictoe_tac1 = SPEC_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 90805*)n:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 90817*)n:num" ] ) ) THEN INDUCT_TAC THEN REWRITE_TAC [ NOT_SUC , INV_SUC_EQ , GSYM NOT_SUC , PRE ] THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [ FIRST_ASSUM ( SUBST1_TAC o SYM ) THEN FIRST_ASSUM ACCEPT_TAC , FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "PRE_ELIM_THM" 
 ( String.concatWith " " 
 [ "boolLib.SPEC_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 90805*)n:num\"", "]", ")", ",", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 90817*)n:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"numTheory.NOT_SUC", ",", "prim_recTheory.INV_SUC_EQ", ",", "boolLib.GSYM", 
"numTheory.NOT_SUC", ",", "prim_recTheory.PRE", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.FIRST_ASSUM", "(", "boolLib.SUBST1_TAC", "o", "HolKernel.SYM", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ",", "boolLib.FIRST_ASSUM", "boolLib.MATCH_MP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REFL_TAC", "]" ] )
in hhsRecord.try_record_proof "PRE_ELIM_THM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = print "Additional properties of EXP\n"
;
val MULT_INCREASES = store_thm ( "MULT_INCREASES" , ( Parse.Term [ QUOTE " (*#loc 1 91155*)!m n. 1 < m /\\ 0 < n ==> SUC n <= m * n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THENL [ REWRITE_TAC [ NOT_LESS_0 ] , REWRITE_TAC [ MULT , GSYM LESS_EQ ] THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [ ADD_COMM ] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN REWRITE_TAC [ MULT_EQ_0 ] THEN STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC ( REWRITE_RULE [ ONE , LESS_REFL ] ) THEN FIRST_ASSUM ACCEPT_TAC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MULT_INCREASES" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", "prim_recTheory.NOT_LESS_0", "]", ",", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT" "", ",", "boolLib.GSYM", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_ADD_NONZERO" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_NONZERO\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MULT_EQ_0" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_0\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", 
"boolLib.SUBST_ALL_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.RULE_ASSUM_TAC", "(", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"prim_recTheory.LESS_REFL", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", "]" ] )
in hhsRecord.try_record_proof "MULT_INCREASES" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_ALWAYS_BIG_ENOUGH = store_thm ( "EXP_ALWAYS_BIG_ENOUGH" , ( Parse.Term [ QUOTE " (*#loc 1 91625*)!b. 1 < b ==> !n. ?m. n <= b EXP m" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL [ REWRITE_TAC [ ZERO_LESS_EQ ] , POP_ASSUM STRIP_ASSUME_TAC THEN Q.ASM_CASES_TAC [ QUOTE " (*#loc 1 91802*)SUC n <= b EXP m" ] THENL [ mesonLib.ASM_MESON_TAC [ ] , SUBGOAL_THEN ( Parse.Term [ QUOTE " (*#loc 1 91883*)n = b EXP m" ] ) STRIP_ASSUME_TAC THENL [ POP_ASSUM ( MP_TAC o REWRITE_RULE [ GSYM LESS_EQ ] ) THEN POP_ASSUM ( STRIP_ASSUME_TAC o REWRITE_RULE [ LESS_OR_EQ ] ) THEN ASM_REWRITE_TAC [ ] , ALL_TAC ] THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 92132*)SUC m" ] THEN REWRITE_TAC [ EXP ] THEN POP_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC MULT_INCREASES THEN ASM_REWRITE_TAC [ ] THEN REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC ( Q.SPEC [ QUOTE " (*#loc 1 92320*)b" ] num_CASES ) THENL [ IMP_RES_TAC NOT_LESS_0 , REWRITE_TAC [ GSYM NOT_ZERO_LT_ZERO , NOT_EXP_0 ] ] ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_ALWAYS_BIG_ENOUGH" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
"]", ",", "boolLib.POP_ASSUM", "boolLib.STRIP_ASSUME_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ASM_CASES_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 91802*)SUC n <= b EXP m\"", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"mesonLib.ASM_MESON_TAC", "[", "]", ",", "boolLib.SUBGOAL_THEN", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 91883*)n = b EXP m\"", "]", ")", 
"boolLib.STRIP_ASSUME_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.POP_ASSUM", "(", 
"boolLib.MP_TAC", "o", "boolLib.REWRITE_RULE", "[", "boolLib.GSYM", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", "]", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"boolLib.STRIP_ASSUME_TAC", "o", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", ",", "boolLib.ALL_TAC", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 92132*)SUC m\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EXP" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", 
"boolLib.SUBST_ALL_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MULT_INCREASES" "( ( DB.fetch \"arithmetic\" \"MULT_INCREASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT_TCL", 
"boolLib.STRIP_THM_THEN", "boolLib.SUBST_ALL_TAC", "(", "Q.SPEC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 92320*)b\"", "]", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.IMP_RES_TAC", "prim_recTheory.NOT_LESS_0", ",", "boolLib.REWRITE_TAC", "[", 
"boolLib.GSYM", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
",", 
hhsRecord.fetch "NOT_EXP_0" "( ( DB.fetch \"arithmetic\" \"NOT_EXP_0\" ) )", 
"]", "]", "]", "]" ] )
in hhsRecord.try_record_proof "EXP_ALWAYS_BIG_ENOUGH" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_EQ_0 = store_thm ( "EXP_EQ_0" , ( Parse.Term [ QUOTE " (*#loc 1 92492*)!n m. (n EXP m = 0) = (n = 0) /\\ (0 < m)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN STRUCT_CASES_TAC ( Q.SPEC [ QUOTE " (*#loc 1 92585*)m" ] num_CASES ) THEN REWRITE_TAC [ EXP , GSYM NOT_ZERO_LT_ZERO , ONE , NOT_SUC , MULT_EQ_0 ] THEN EQ_TAC THEN STRIP_TAC THENL [ REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC ( Q.SPEC [ QUOTE " (*#loc 1 92762*)n" ] num_CASES ) THEN REWRITE_TAC [ ] THEN IMP_RES_TAC NOT_EXP_0 , ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_EQ_0" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRUCT_CASES_TAC", 
"(", "Q.SPEC", "[", "HolKernel.QUOTE", "\" (*#loc 1 92585*)m\"", "]", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "EXP" "", ",", "boolLib.GSYM", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"numTheory.NOT_SUC", ",", 
hhsRecord.fetch "MULT_EQ_0" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_0\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REPEAT_TCL", 
"boolLib.STRIP_THM_THEN", "boolLib.SUBST_ALL_TAC", "(", "Q.SPEC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 92762*)n\"", "]", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.IMP_RES_TAC", 
hhsRecord.fetch "NOT_EXP_0" "( ( DB.fetch \"arithmetic\" \"NOT_EXP_0\" ) )", 
",", "boolLib.ASM_REWRITE_TAC", "[", "]", "]" ] )
in hhsRecord.try_record_proof "EXP_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ZERO_LT_EXP = store_thm ( "ZERO_LT_EXP" , ( Parse.Term [ QUOTE " (*#loc 1 92906*)0 < x EXP y = 0 < x \\/ (y = 0)" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ NOT_ZERO_LT_ZERO , EXP_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ZERO_LT_EXP" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
",", 
hhsRecord.fetch "EXP_EQ_0" "( ( DB.fetch \"arithmetic\" \"EXP_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ZERO_LT_EXP" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_1 = store_thm ( "EXP_1" , ( Parse.Term [ QUOTE " (*#loc 1 93021*)!n. (1 EXP n = 1) /\\ (n EXP 1 = n)" ] ) ,
let
val tactictoe_tac1 = CONV_TAC ( QUANT_CONV ( FORK_CONV ( ALL_CONV , REWRITE_CONV [ ONE ] ) ) ) THEN REWRITE_TAC [ EXP , MULT_CLAUSES ] THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ MULT_EQ_1 , EXP ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_1" 
 ( String.concatWith " " 
 [ "boolLib.CONV_TAC", "(", "boolLib.QUANT_CONV", "(", "boolLib.FORK_CONV", "(", 
"boolLib.ALL_CONV", ",", "boolLib.REWRITE_CONV", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_EQ_1" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_1\" ) )", 
",", hhsRecord.fetch "EXP" "", "]" ] )
in hhsRecord.try_record_proof "EXP_1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_EQ_1 = store_thm ( "EXP_EQ_1" , ( Parse.Term [ QUOTE " (*#loc 1 93267*)!n m. (n EXP m = 1) = (n = 1) \\/ (m = 0)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [ POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC [ QUOTE " (*#loc 1 93405*)m" ] THEN INDUCT_TAC THEN REWRITE_TAC [ EXP , MULT_EQ_1 ] THEN STRIP_TAC THEN ASM_REWRITE_TAC [ ] , ASM_REWRITE_TAC [ EXP_1 ] , ASM_REWRITE_TAC [ EXP ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_EQ_1" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.POP_ASSUM", 
"boolLib.MP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.ID_SPEC_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 93405*)m\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MULT_EQ_1" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_1\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", ",", "boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "EXP_1" "( ( DB.fetch \"arithmetic\" \"EXP_1\" ) )", "]", ",", 
"boolLib.ASM_REWRITE_TAC", "[", hhsRecord.fetch "EXP" "", "]", "]" ] )
in hhsRecord.try_record_proof "EXP_EQ_1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val expbase_le_mono = prove ( ( Parse.Term [ QUOTE " (*#loc 1 93602*)1 < b /\\ m <= n ==> b ** m <= b ** n" ] ) ,
let
val tactictoe_tac1 = STRIP_TAC THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 93678*)?q. n = m + q" ] STRIP_ASSUME_TAC >>- 1 ?? METIS_TAC [ LESS_EQUAL_ADD ] THEN SRW_TAC [ ] [ EXP_ADD ] THEN SRW_TAC [ ] [ Once ( GSYM MULT_RIGHT_1 ) , SimpLHS ] THEN ASM_REWRITE_TAC [ LE_MULT_LCANCEL , EXP_EQ_0 , ONE , GSYM LESS_EQ , ZERO_LT_EXP ] THEN METIS_TAC [ ONE , LESS_TRANS , LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_262" 
 ( String.concatWith " " 
 [ "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.SUBGOAL_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 93678*)?q. n = m + q\"", "]", 
"boolLib.STRIP_ASSUME_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", 
"1", "hhs_infixl0_open boolLib.?? hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_EQUAL_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ADD\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", 
"[", "]", "[", 
hhsRecord.fetch "EXP_ADD" "( ( DB.fetch \"arithmetic\" \"EXP_ADD\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "boolLib.Once", "(", "boolLib.GSYM", 
hhsRecord.fetch "MULT_RIGHT_1" "( ( DB.fetch \"arithmetic\" \"MULT_RIGHT_1\" ) )", 
")", ",", "boolSimps.SimpLHS", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LE_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_LCANCEL\" ) )", 
",", 
hhsRecord.fetch "EXP_EQ_0" "( ( DB.fetch \"arithmetic\" \"EXP_EQ_0\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"boolLib.GSYM", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", ",", 
hhsRecord.fetch "ZERO_LT_EXP" "( ( DB.fetch \"arithmetic\" \"ZERO_LT_EXP\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
",", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_262" false tactictoe_tac2 tactictoe_tac1
end )
;
val expbase_lt_mono = prove ( ( Parse.Term [ QUOTE " (*#loc 1 94007*)1 < b /\\ m < n ==> b ** m < b ** n" ] ) ,
let
val tactictoe_tac1 = STRIP_TAC THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 94081*)?q. n = m + q" ] STRIP_ASSUME_TAC >>- 1 ?? METIS_TAC [ LESS_ADD , ADD_COMM ] THEN SRW_TAC [ ] [ EXP_ADD ] THEN SRW_TAC [ ] [ Once ( GSYM MULT_RIGHT_1 ) , SimpLHS ] THEN ASM_REWRITE_TAC [ LT_MULT_LCANCEL , ZERO_LT_EXP ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 94311*)0 < b" ] ASSUME_TAC >>- 1 ?? METIS_TAC [ ONE , LESS_TRANS , LESS_0 ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 94398*)1 < b ** q \\/ b ** q < 1 \\/ (b ** q = 1)" ] STRIP_ASSUME_TAC >>- 1 ?? METIS_TAC [ LESS_CASES , LESS_OR_EQ ] THEN ASM_REWRITE_TAC [ ] THENL [ Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 94556*)b ** q = 0" ] ASSUME_TAC >>- 1 ?? METIS_TAC [ LESS_MONO_EQ , NOT_LESS_0 , num_CASES , ONE ] THEN FULL_SIMP_TAC ( srw_ss ( ) ) [ EXP_EQ_0 , NOT_LESS_0 ] , FULL_SIMP_TAC ( srw_ss ( ) ) [ EXP_EQ_1 ] THEN FULL_SIMP_TAC ( srw_ss ( ) ) [ LESS_REFL , ADD_CLAUSES ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_263" 
 ( String.concatWith " " 
 [ "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.SUBGOAL_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 94081*)?q. n = m + q\"", "]", 
"boolLib.STRIP_ASSUME_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", 
"1", "hhs_infixl0_open boolLib.?? hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_ADD\" ) )", 
",", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", 
"[", "]", "[", 
hhsRecord.fetch "EXP_ADD" "( ( DB.fetch \"arithmetic\" \"EXP_ADD\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "boolLib.Once", "(", "boolLib.GSYM", 
hhsRecord.fetch "MULT_RIGHT_1" "( ( DB.fetch \"arithmetic\" \"MULT_RIGHT_1\" ) )", 
")", ",", "boolSimps.SimpLHS", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LT_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_MULT_LCANCEL\" ) )", 
",", 
hhsRecord.fetch "ZERO_LT_EXP" "( ( DB.fetch \"arithmetic\" \"ZERO_LT_EXP\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 94311*)0 < b\"", "]", "boolLib.ASSUME_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
",", "prim_recTheory.LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", 
"\" (*#loc 1 94398*)1 < b ** q \\\\/ b ** q < 1 \\\\/ (b ** q = 1)\"", "]", 
"boolLib.STRIP_ASSUME_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", 
"1", "hhs_infixl0_open boolLib.?? hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_CASES" "( ( DB.fetch \"arithmetic\" \"LESS_CASES\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 94556*)b ** q = 0\"", "]", "boolLib.ASSUME_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", "prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "EXP_EQ_0" "( ( DB.fetch \"arithmetic\" \"EXP_EQ_0\" ) )", 
",", "prim_recTheory.NOT_LESS_0", "]", ",", "simpLib.FULL_SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "EXP_EQ_1" "( ( DB.fetch \"arithmetic\" \"EXP_EQ_1\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"(", "BasicProvers.srw_ss", "(", ")", ")", "[", "prim_recTheory.LESS_REFL", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_263" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_BASE_LE_MONO = store_thm ( "EXP_BASE_LE_MONO" , ( Parse.Term [ QUOTE " (*#loc 1 94866*)!b. 1 < b ==> !n m. b ** m <= b ** n = m <= n" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ expbase_lt_mono , expbase_le_mono , NOT_LESS_EQUAL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_BASE_LE_MONO" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", hhsRecord.fetch "expbase_lt_mono" "", ",", 
hhsRecord.fetch "expbase_le_mono" "", ",", 
hhsRecord.fetch "NOT_LESS_EQUAL" "( ( DB.fetch \"arithmetic\" \"NOT_LESS_EQUAL\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EXP_BASE_LE_MONO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_BASE_LT_MONO = store_thm ( "EXP_BASE_LT_MONO" , ( Parse.Term [ QUOTE " (*#loc 1 95040*)!b. 1 < b ==> !n m. b ** m < b ** n = m < n" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ expbase_lt_mono , expbase_le_mono , NOT_LESS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_BASE_LT_MONO" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", hhsRecord.fetch "expbase_lt_mono" "", ",", 
hhsRecord.fetch "expbase_le_mono" "", ",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EXP_BASE_LT_MONO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_BASE_INJECTIVE = store_thm ( "EXP_BASE_INJECTIVE" , ( Parse.Term [ QUOTE " (*#loc 1 95210*)!b. 1 < b ==> !n m. (b EXP n = b EXP m) = (n = m)" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ LESS_EQUAL_ANTISYM , LESS_EQ_REFL , EXP_BASE_LE_MONO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_BASE_INJECTIVE" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
",", 
hhsRecord.fetch "EXP_BASE_LE_MONO" "( ( DB.fetch \"arithmetic\" \"EXP_BASE_LE_MONO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EXP_BASE_INJECTIVE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_BASE_LEQ_MONO_IMP = store_thm ( "EXP_BASE_LEQ_MONO_IMP" , ( Parse.Term [ QUOTE " (*#loc 1 95400*)!n m b. 0 < b /\\ m <= n ==> b ** m <= b ** n" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_EQUAL_ADD THEN ASM_REWRITE_TAC [ EXP_ADD ] THEN SRW_TAC [ ] [ Once ( GSYM MULT_RIGHT_1 ) , SimpLHS ] THEN ASM_REWRITE_TAC [ LE_MULT_LCANCEL , EXP_EQ_0 , ONE , GSYM LESS_EQ ] THEN FULL_SIMP_TAC bool_ss [ GSYM NOT_ZERO_LT_ZERO , EXP_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_BASE_LEQ_MONO_IMP" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_EQUAL_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ADD\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "EXP_ADD" "( ( DB.fetch \"arithmetic\" \"EXP_ADD\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", 
"[", "]", "[", "boolLib.Once", "(", "boolLib.GSYM", 
hhsRecord.fetch "MULT_RIGHT_1" "( ( DB.fetch \"arithmetic\" \"MULT_RIGHT_1\" ) )", 
")", ",", "boolSimps.SimpLHS", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LE_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_LCANCEL\" ) )", 
",", 
hhsRecord.fetch "EXP_EQ_0" "( ( DB.fetch \"arithmetic\" \"EXP_EQ_0\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"boolLib.GSYM", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", "boolLib.GSYM", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
",", 
hhsRecord.fetch "EXP_EQ_0" "( ( DB.fetch \"arithmetic\" \"EXP_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EXP_BASE_LEQ_MONO_IMP" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_BASE_LEQ_MONO_SUC_IMP = save_thm ( "EXP_BASE_LEQ_MONO_SUC_IMP" , ( REWRITE_RULE [ LESS_0 ] o Q.INST [ [ QUOTE " (*#loc 1 95832*)b" ] |-> [ QUOTE " (*#loc 1 95840*)SUC b" ] ] o SPEC_ALL ) EXP_BASE_LEQ_MONO_IMP )
;
;
val EXP_BASE_LE_IFF = store_thm ( "EXP_BASE_LE_IFF" , ( Parse.Term [ QUOTE " (*#loc 1 95943*)b ** m <= b ** n <=>       (b = 0) /\\ (n = 0) \\/ (b = 0) /\\ 0 < m \\/ (b = 1) \\/ 1 < b /\\ m <= n" ] ) ,
let
val tactictoe_tac1 = Q.SPEC_THEN [ QUOTE " (*#loc 1 96058*)b" ] STRUCT_CASES_TAC num_CASES THEN ASM_REWRITE_TAC [ NOT_SUC , NOT_LESS_0 ] THENL [ Q.SPEC_THEN [ QUOTE " (*#loc 1 96158*)m" ] STRUCT_CASES_TAC num_CASES THEN ASM_REWRITE_TAC [ LESS_REFL , EXP , ONE , SUC_NOT ] THENL [ Q.SPEC_THEN [ QUOTE " (*#loc 1 96271*)n" ] STRUCT_CASES_TAC num_CASES THEN ASM_REWRITE_TAC [ NOT_SUC , EXP , ONE , LESS_EQ_REFL , MULT_CLAUSES , NOT_SUC_LESS_EQ_0 ] , ASM_REWRITE_TAC [ LESS_0 , MULT_CLAUSES , ZERO_LESS_EQ ] ] , EQ_TAC THENL [ ASM_CASES_TAC ( Parse.Term [ QUOTE " (*#loc 1 96527*)1 < SUC n'" ] ) THEN SRW_TAC [ ] [ EXP_BASE_LE_MONO ] THEN FULL_SIMP_TAC ( srw_ss ( ) ) [ ONE , LESS_MONO_EQ , INV_SUC_EQ , GSYM NOT_ZERO_LT_ZERO ] , STRIP_TAC THEN ASM_REWRITE_TAC [ EXP_1 , LESS_EQ_REFL ] THEN MATCH_MP_TAC EXP_BASE_LEQ_MONO_IMP THEN ASM_REWRITE_TAC [ LESS_0 ] ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_BASE_LE_IFF" 
 ( String.concatWith " " 
 [ "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 96058*)b\"", "]", 
"boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "numTheory.NOT_SUC", ",", "prim_recTheory.NOT_LESS_0", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 96158*)m\"", "]", "boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "prim_recTheory.LESS_REFL", ",", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "SUC_NOT" "( ( DB.fetch \"arithmetic\" \"SUC_NOT\" ) )", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 96271*)n\"", "]", "boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "numTheory.NOT_SUC", ",", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
"]", ",", "boolLib.ASM_REWRITE_TAC", "[", "prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
"]", "]", ",", "boolLib.EQ_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", 
"[", "boolLib.ASM_CASES_TAC", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 96527*)1 < SUC n'\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", 
hhsRecord.fetch "EXP_BASE_LE_MONO" "( ( DB.fetch \"arithmetic\" \"EXP_BASE_LE_MONO\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", "prim_recTheory.INV_SUC_EQ", ",", "boolLib.GSYM", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]", ",", "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "EXP_1" "( ( DB.fetch \"arithmetic\" \"EXP_1\" ) )", ",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "EXP_BASE_LEQ_MONO_IMP" "( ( DB.fetch \"arithmetic\" \"EXP_BASE_LEQ_MONO_IMP\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "prim_recTheory.LESS_0", "]", "]", "]" ] )
in hhsRecord.try_record_proof "EXP_BASE_LE_IFF" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val X_LE_X_EXP = store_thm ( "X_LE_X_EXP" , ( Parse.Term [ QUOTE " (*#loc 1 96893*)0 < n ==> x <= x ** n" ] ) ,
let
val tactictoe_tac1 = Q.SPEC_THEN [ QUOTE " (*#loc 1 96934*)n" ] STRUCT_CASES_TAC num_CASES THEN REWRITE_TAC [ EXP , LESS_REFL , LESS_0 ] THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 97028*)x" ] STRUCT_CASES_TAC num_CASES THEN REWRITE_TAC [ ZERO_LESS_EQ , LE_MULT_CANCEL_LBARE , NOT_SUC , ZERO_LT_EXP , LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "X_LE_X_EXP" 
 ( String.concatWith " " 
 [ "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 96934*)n\"", "]", 
"boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EXP" "", ",", "prim_recTheory.LESS_REFL", ",", 
"prim_recTheory.LESS_0", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 97028*)x\"", "]", 
"boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "LE_MULT_CANCEL_LBARE" "( ( DB.fetch \"arithmetic\" \"LE_MULT_CANCEL_LBARE\" ) )", 
",", "numTheory.NOT_SUC", ",", 
hhsRecord.fetch "ZERO_LT_EXP" "( ( DB.fetch \"arithmetic\" \"ZERO_LT_EXP\" ) )", 
",", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "X_LE_X_EXP" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val X_LT_EXP_X = Q.store_thm ( "X_LT_EXP_X" , [ QUOTE " (*#loc 1 97209*)1 < b ==> x < b ** x" ] ,
let
val tactictoe_tac1 = Q.ID_SPEC_TAC [ QUOTE " (*#loc 1 97250*)x" ] THEN INDUCT_TAC >>- 1 ?? SIMP_TAC bool_ss [ LESS_0 , EXP , ONE ] THEN STRIP_TAC THEN FULL_SIMP_TAC bool_ss [ ] THEN Cases_on [ QUOTE " (*#loc 1 97383*)x = 0" ] >>- 1 ?? ASM_SIMP_TAC bool_ss [ EXP , MULT_RIGHT_1 , SYM ONE ] THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN EXISTS_TAC ( Parse.Term [ QUOTE " (*#loc 1 97511*)x + x" ] ) THEN CONJ_TAC >>- 1 ?? ( SIMP_TAC bool_ss [ ADD1 , ADD_MONO_LESS_EQ ] THEN SIMP_TAC bool_ss [ ONE ] THEN MATCH_MP_TAC LESS_OR THEN PROVE_TAC [ NOT_ZERO_LT_ZERO ] ) THEN SIMP_TAC bool_ss [ EXP ] THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN EXISTS_TAC ( Parse.Term [ QUOTE " (*#loc 1 97789*)b * x" ] ) THEN CONJ_TAC >>- 1 ?? ( SIMP_TAC bool_ss [ GSYM TIMES2 ] THEN MATCH_MP_TAC LESS_MONO_MULT THEN SIMP_TAC bool_ss [ TWO ] THEN MATCH_MP_TAC LESS_OR THEN FIRST_ASSUM ACCEPT_TAC ) THEN SIMP_TAC bool_ss [ LT_MULT_LCANCEL ] THEN CONJ_TAC >>- 1 ?? ( MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC ( Parse.Term [ QUOTE " (*#loc 1 98117*)1" ] ) THEN ASM_SIMP_TAC bool_ss [ ONE , prim_recTheory.LESS_0_0 ] ) THEN FIRST_ASSUM ACCEPT_TAC
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "X_LT_EXP_X" 
 ( String.concatWith " " 
 [ "Q.ID_SPEC_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 97250*)x\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", "prim_recTheory.LESS_0", ",", hhsRecord.fetch "EXP" "", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.Cases_on", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 97383*)x = 0\"", "]", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MULT_RIGHT_1" "( ( DB.fetch \"arithmetic\" \"MULT_RIGHT_1\" ) )", 
",", "HolKernel.SYM", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQ_LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 97511*)x + x\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", ",", 
hhsRecord.fetch "ADD_MONO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ADD_MONO_LESS_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_OR" "( ( DB.fetch \"arithmetic\" \"LESS_OR\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", hhsRecord.fetch "EXP" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQ_LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 97789*)b * x\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", "boolLib.GSYM", 
hhsRecord.fetch "TIMES2" "( ( DB.fetch \"arithmetic\" \"TIMES2\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_MONO_MULT" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_MULT\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_OR" "( ( DB.fetch \"arithmetic\" \"LESS_OR\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "LT_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_MULT_LCANCEL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONJ_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 98117*)1\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"prim_recTheory.LESS_0_0", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_ASSUM", 
"boolLib.ACCEPT_TAC" ] )
in hhsRecord.try_record_proof "X_LT_EXP_X" false tactictoe_tac2 tactictoe_tac1
end )
;
local
fun Cases_on q = Q.SPEC_THEN q STRUCT_CASES_TAC num_CASES
;
in
val ZERO_EXP = Q.store_thm ( "ZERO_EXP" , [ QUOTE " (*#loc 1 98328*)0 ** x = if x = 0 then 1 else 0" ] ,
let
val tactictoe_tac1 = Cases_on [ QUOTE " (*#loc 1 98375*)x" ] THEN SIMP_TAC bool_ss [ EXP , numTheory.NOT_SUC , MULT ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ZERO_EXP" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "Cases_on" "let fun Cases_on q = Q.SPEC_THEN q boolLib.STRUCT_CASES_TAC ( ( DB.fetch \"arithmetic\" \"num_CASES\" ) ) in Cases_on end", 
"[", "HolKernel.QUOTE", "\" (*#loc 1 98375*)x\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", hhsRecord.fetch "EXP" "", ",", "numTheory.NOT_SUC", ",", 
hhsRecord.fetch "MULT" "", "]" ] )
in hhsRecord.try_record_proof "ZERO_EXP" false tactictoe_tac2 tactictoe_tac1
end )
;
val X_LT_EXP_X_IFF = Q.store_thm ( "X_LT_EXP_X_IFF" , [ QUOTE " (*#loc 1 98489*)x < b ** x <=> 1 < b \\/ (x = 0)" ] ,
let
val tactictoe_tac1 = EQ_TAC >>- 1 ?? ( Cases_on [ QUOTE " (*#loc 1 98556*)b" ] >>- 1 ?? ( Cases_on [ QUOTE " (*#loc 1 98584*)x" ] THEN SIMP_TAC bool_ss [ ZERO_EXP , SUC_NOT , NOT_LESS_0 ] ) THEN Q.MATCH_RENAME_TAC [ QUOTE " (*#loc 1 98678*)x < SUC b ** x ==> 1 < SUC b \\/ (x = 0)" ] THEN Cases_on [ QUOTE " (*#loc 1 98739*)b" ] >>- 1 ?? ( SIMP_TAC bool_ss [ EXP_1 , SYM ONE ] THEN SIMP_TAC bool_ss [ ONE , LESS_THM , NOT_LESS_0 ] ) THEN SIMP_TAC bool_ss [ LESS_MONO_EQ , ONE , LESS_0 ] ) THEN STRIP_TAC >>- 1 ?? ( POP_ASSUM MP_TAC THEN ACCEPT_TAC X_LT_EXP_X ) THEN ASM_SIMP_TAC bool_ss [ EXP , ONE , LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "X_LT_EXP_X_IFF" 
 ( String.concatWith " " 
 [ "boolLib.EQ_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", 
hhsRecord.fetch "Cases_on" "let fun Cases_on q = Q.SPEC_THEN q boolLib.STRUCT_CASES_TAC ( ( DB.fetch \"arithmetic\" \"num_CASES\" ) ) in Cases_on end", 
"[", "HolKernel.QUOTE", "\" (*#loc 1 98556*)b\"", "]", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", 
hhsRecord.fetch "Cases_on" "let fun Cases_on q = Q.SPEC_THEN q boolLib.STRUCT_CASES_TAC ( ( DB.fetch \"arithmetic\" \"num_CASES\" ) ) in Cases_on end", 
"[", "HolKernel.QUOTE", "\" (*#loc 1 98584*)x\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ZERO_EXP" "( ( DB.fetch \"arithmetic\" \"ZERO_EXP\" ) )", 
",", hhsRecord.fetch "SUC_NOT" "( ( DB.fetch \"arithmetic\" \"SUC_NOT\" ) )", 
",", "prim_recTheory.NOT_LESS_0", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.MATCH_RENAME_TAC", "[", 
"HolKernel.QUOTE", 
"\" (*#loc 1 98678*)x < SUC b ** x ==> 1 < SUC b \\\\/ (x = 0)\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "Cases_on" "let fun Cases_on q = Q.SPEC_THEN q boolLib.STRUCT_CASES_TAC ( ( DB.fetch \"arithmetic\" \"num_CASES\" ) ) in Cases_on end", 
"[", "HolKernel.QUOTE", "\" (*#loc 1 98739*)b\"", "]", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "EXP_1" "( ( DB.fetch \"arithmetic\" \"EXP_1\" ) )", ",", 
"HolKernel.SYM", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"prim_recTheory.LESS_THM", ",", "prim_recTheory.NOT_LESS_0", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"prim_recTheory.LESS_0", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.POP_ASSUM", 
"boolLib.MP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ACCEPT_TAC", 
hhsRecord.fetch "X_LT_EXP_X" "( ( DB.fetch \"arithmetic\" \"X_LT_EXP_X\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "X_LT_EXP_X_IFF" false tactictoe_tac2 tactictoe_tac1
end )
;
end
val LT_MULT_IMP = prove ( ( Parse.Term [ QUOTE " (*#loc 1 99063*)a < b /\\ x < y ==> a * x < b * y" ] ) ,
let
val tactictoe_tac1 = STRIP_TAC THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 99135*)0 < y" ] ASSUME_TAC >>- 1 ?? METIS_TAC [ NOT_ZERO_LT_ZERO , NOT_LESS_0 ] THEN METIS_TAC [ LE_MULT_LCANCEL , LT_MULT_RCANCEL , LESS_EQ_LESS_TRANS , LESS_OR_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_273" 
 ( String.concatWith " " 
 [ "boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.SUBGOAL_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 99135*)0 < y\"", "]", 
"boolLib.ASSUME_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
",", "prim_recTheory.NOT_LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LE_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_LCANCEL\" ) )", 
",", 
hhsRecord.fetch "LT_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_MULT_RCANCEL\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_LESS_TRANS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_273" false tactictoe_tac2 tactictoe_tac1
end )
;
val LE_MULT_IMP = prove ( ( Parse.Term [ QUOTE " (*#loc 1 99381*)a <= b /\\ x <= y ==> a * x <= b * y" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ LE_MULT_LCANCEL , LE_MULT_RCANCEL , LESS_EQ_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_274" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LE_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_LCANCEL\" ) )", 
",", 
hhsRecord.fetch "LE_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_RCANCEL\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_274" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_LT_MONO_0 = prove ( ( Parse.Term [ QUOTE " (*#loc 1 99517*)!n. 0 < n ==> !a b. a < b ==> a EXP n < b EXP n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN SRW_TAC [ ] [ NOT_LESS_0 , LESS_0 , EXP ] THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 99643*)n" ] STRIP_ASSUME_TAC num_CASES THEN FULL_SIMP_TAC ( srw_ss ( ) ) [ EXP , MULT_CLAUSES , LESS_0 ] THEN SRW_TAC [ ] [ LT_MULT_IMP ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_275" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "prim_recTheory.NOT_LESS_0", ",", "prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "EXP" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 99643*)n\"", "]", "boolLib.STRIP_ASSUME_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", ")", "[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", hhsRecord.fetch "LT_MULT_IMP" "", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_275" false tactictoe_tac2 tactictoe_tac1
end )
;
val EXP_LE_MONO_0 = prove ( ( Parse.Term [ QUOTE " (*#loc 1 99797*)!n. 0 < n ==> !a b. a <= b ==> a EXP n <= b EXP n" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN SRW_TAC [ ] [ EXP , LESS_EQ_REFL ] THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 99919*)n" ] STRIP_ASSUME_TAC num_CASES THEN FULL_SIMP_TAC ( srw_ss ( ) ) [ EXP , MULT_CLAUSES , LESS_0 ] THEN SRW_TAC [ ] [ LE_MULT_IMP ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_276" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 99919*)n\"", "]", "boolLib.STRIP_ASSUME_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", ")", "[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", hhsRecord.fetch "LE_MULT_IMP" "", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_276" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_EXP_LT_MONO = store_thm ( "EXP_EXP_LT_MONO" , ( Parse.Term [ QUOTE " (*#loc 1 100099*)!a b. a EXP n < b EXP n = a < b /\\ 0 < n" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ EXP_LT_MONO_0 , NOT_LESS , EXP_LE_MONO_0 , EXP , LESS_REFL , NOT_ZERO_LT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_EXP_LT_MONO" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", hhsRecord.fetch "EXP_LT_MONO_0" "", ",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", hhsRecord.fetch "EXP_LE_MONO_0" "", ",", hhsRecord.fetch "EXP" "", ",", 
"prim_recTheory.LESS_REFL", ",", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EXP_EXP_LT_MONO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_EXP_LE_MONO = store_thm ( "EXP_EXP_LE_MONO" , ( Parse.Term [ QUOTE " (*#loc 1 100303*)!a b. a EXP n <= b EXP n = a <= b \\/ (n = 0)" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ EXP_LE_MONO_0 , NOT_LESS_EQUAL , EXP_LT_MONO_0 , EXP , LESS_EQ_REFL , NOT_ZERO_LT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_EXP_LE_MONO" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", hhsRecord.fetch "EXP_LE_MONO_0" "", ",", 
hhsRecord.fetch "NOT_LESS_EQUAL" "( ( DB.fetch \"arithmetic\" \"NOT_LESS_EQUAL\" ) )", 
",", hhsRecord.fetch "EXP_LT_MONO_0" "", ",", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
",", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EXP_EXP_LE_MONO" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_EXP_INJECTIVE = store_thm ( "EXP_EXP_INJECTIVE" , ( Parse.Term [ QUOTE " (*#loc 1 100524*)!b1 b2 x. (b1 EXP x = b2 EXP x) = (x = 0) \\/ (b1 = b2)" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ EXP_EXP_LE_MONO , LESS_EQUAL_ANTISYM , LESS_EQ_REFL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_EXP_INJECTIVE" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "EXP_EXP_LE_MONO" "( ( DB.fetch \"arithmetic\" \"EXP_EXP_LE_MONO\" ) )", 
",", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EXP_EXP_INJECTIVE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_SUB = Q.store_thm ( "EXP_SUB" , [ QUOTE " (*#loc 1 100690*)!p q n. 0 < n /\\ q <= p ==> (n ** (p - q) = n ** p DIV n ** q)" ] ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN ( Parse.Term [ QUOTE " (*#loc 1 100786*)0 < n ** p /\\ 0 < n ** q" ] ) via ( STRIP_ASSUME_TAC ( Q.SPEC [ QUOTE " (*#loc 1 100852*)n" ] num_CASES ) THEN RW_TAC bool_ss [ ] THEN FULL_SIMP_TAC bool_ss [ ZERO_LESS_EXP , LESS_REFL ] ) THEN RW_TAC bool_ss [ DIV_P ] THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 101014*)0" ] THEN RW_TAC bool_ss [ GSYM EXP_ADD , ADD_CLAUSES ] THEN METIS_TAC [ SUB_ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_SUB" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 100786*)0 < n ** p /\\\\ 0 < n ** q\"", "]", ")", 
"hhs_infixl8_open boolLib.via hhs_infixl8_close", "(", 
"boolLib.STRIP_ASSUME_TAC", "(", "Q.SPEC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 100852*)n\"", "]", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.RW_TAC", 
"BasicProvers.bool_ss", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ZERO_LESS_EXP" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EXP\" ) )", 
",", "prim_recTheory.LESS_REFL", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.RW_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "DIV_P" "( ( DB.fetch \"arithmetic\" \"DIV_P\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 101014*)0\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.RW_TAC", 
"BasicProvers.bool_ss", "[", "boolLib.GSYM", 
hhsRecord.fetch "EXP_ADD" "( ( DB.fetch \"arithmetic\" \"EXP_ADD\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "SUB_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_ADD\" ) )", "]" ] )
in hhsRecord.try_record_proof "EXP_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_SUB_NUMERAL = store_thm ( "EXP_SUB_NUMERAL" , ( Parse.Term [ QUOTE " (*#loc 1 101154*)0 < n ==>      (n ** (NUMERAL (BIT1 x)) DIV n = n ** (NUMERAL (BIT1 x) - 1)) /\\      (n ** (NUMERAL (BIT2 x)) DIV n = n ** (NUMERAL (BIT1 x)))" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THENL [ Q.SPECL_THEN [ [ QUOTE " (*#loc 1 101347*)NUMERAL (BIT1 x)" ] , [ QUOTE " (*#loc 1 101367*)1" ] , [ QUOTE " (*#loc 1 101372*)n" ] ] ( MP_TAC o GSYM ) EXP_SUB THEN REWRITE_TAC [ EXP_1 ] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [ NUMERAL_DEF , BIT1 , ALT_ZERO , ADD_CLAUSES , LESS_EQ_MONO , ZERO_LESS_EQ ] , Q.SPECL_THEN [ [ QUOTE " (*#loc 1 101595*)NUMERAL (BIT2 x)" ] , [ QUOTE " (*#loc 1 101615*)1" ] , [ QUOTE " (*#loc 1 101620*)n" ] ] ( MP_TAC o GSYM ) EXP_SUB THEN REWRITE_TAC [ EXP_1 ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 101702*)NUMERAL (BIT2 x) - 1 = NUMERAL (BIT1 x)" ] SUBST1_TAC THENL [ REWRITE_TAC [ NUMERAL_DEF , BIT1 , BIT2 , ALT_ZERO , ADD_CLAUSES , SUB_MONO_EQ , SUB_0 ] , ALL_TAC ] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [ NUMERAL_DEF , BIT2 , BIT1 , ALT_ZERO , ADD_CLAUSES , LESS_EQ_MONO , ZERO_LESS_EQ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_SUB_NUMERAL" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "Q.SPECL_THEN", "[", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 101347*)NUMERAL (BIT1 x)\"", "]", ",", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 101367*)1\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 101372*)n\"", "]", "]", "(", "boolLib.MP_TAC", "o", "boolLib.GSYM", ")", 
hhsRecord.fetch "EXP_SUB" "( ( DB.fetch \"arithmetic\" \"EXP_SUB\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EXP_1" "( ( DB.fetch \"arithmetic\" \"EXP_1\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", 
"boolLib.MATCH_MP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", hhsRecord.fetch "BIT1" "( ( DB.fetch \"arithmetic\" \"BIT1\" ) )", ",", 
hhsRecord.fetch "ALT_ZERO" "( ( DB.fetch \"arithmetic\" \"ALT_ZERO\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
"]", ",", "Q.SPECL_THEN", "[", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 101595*)NUMERAL (BIT2 x)\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 101615*)1\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 101620*)n\"", "]", "]", "(", "boolLib.MP_TAC", "o", "boolLib.GSYM", ")", 
hhsRecord.fetch "EXP_SUB" "( ( DB.fetch \"arithmetic\" \"EXP_SUB\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EXP_1" "( ( DB.fetch \"arithmetic\" \"EXP_1\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", 
"\" (*#loc 1 101702*)NUMERAL (BIT2 x) - 1 = NUMERAL (BIT1 x)\"", "]", 
"boolLib.SUBST1_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", hhsRecord.fetch "BIT1" "( ( DB.fetch \"arithmetic\" \"BIT1\" ) )", ",", 
hhsRecord.fetch "BIT2" "( ( DB.fetch \"arithmetic\" \"BIT2\" ) )", ",", 
hhsRecord.fetch "ALT_ZERO" "( ( DB.fetch \"arithmetic\" \"ALT_ZERO\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", "]", 
",", "boolLib.ALL_TAC", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.DISCH_THEN", "boolLib.MATCH_MP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", hhsRecord.fetch "BIT2" "( ( DB.fetch \"arithmetic\" \"BIT2\" ) )", ",", 
hhsRecord.fetch "BIT1" "( ( DB.fetch \"arithmetic\" \"BIT1\" ) )", ",", 
hhsRecord.fetch "ALT_ZERO" "( ( DB.fetch \"arithmetic\" \"ALT_ZERO\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "EXP_SUB_NUMERAL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = export_rewrites [ "EXP_SUB_NUMERAL" ]
;
val EXP_BASE_MULT = store_thm ( "EXP_BASE_MULT" , ( Parse.Term [ QUOTE " (*#loc 1 102143*)!z x y. (x * y) ** z = (x ** z) * (y ** z)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_SIMP_TAC bool_ss [ EXP , MULT_CLAUSES , AC MULT_ASSOC MULT_COMM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_BASE_MULT" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "simpLib.AC", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EXP_BASE_MULT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP_EXP_MULT = store_thm ( "EXP_EXP_MULT" , ( Parse.Term [ QUOTE " (*#loc 1 102328*)!z x y. x ** (y * z) = (x ** y) ** z" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN ASM_REWRITE_TAC [ EXP , MULT_CLAUSES , EXP_1 , EXP_ADD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP_EXP_MULT" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", hhsRecord.fetch "EXP_1" "( ( DB.fetch \"arithmetic\" \"EXP_1\" ) )", ",", 
hhsRecord.fetch "EXP_ADD" "( ( DB.fetch \"arithmetic\" \"EXP_ADD\" ) )", "]" ] )
in hhsRecord.try_record_proof "EXP_EXP_MULT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = print "Minimums and maximums\n"
;
val MAX = new_definition ( "MAX_DEF" , ( Parse.Term [ QUOTE " (*#loc 1 102523*)MAX m n = if m < n then n else m" ] ) )
;
;
val MIN = new_definition ( "MIN_DEF" , ( Parse.Term [ QUOTE " (*#loc 1 102600*)MIN m n = if m < n then m else n" ] ) )
;
;
val ARW = RW_TAC bool_ss
;
val MAX_COMM = store_thm ( "MAX_COMM" , ( Parse.Term [ QUOTE " (*#loc 1 102706*)!m n. MAX m n = MAX n m" ] ) ,
let
val tactictoe_tac1 = ARW [ MAX ] THEN FULL_SIMP_TAC bool_ss [ NOT_LESS ] THEN IMP_RES_TAC LESS_ANTISYM THEN IMP_RES_TAC LESS_EQUAL_ANTISYM
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MAX_COMM" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "ARW" "( BasicProvers.RW_TAC BasicProvers.bool_ss )", "[", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_ANTISYM\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )" ] )
in hhsRecord.try_record_proof "MAX_COMM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_COMM = store_thm ( "MIN_COMM" , ( Parse.Term [ QUOTE " (*#loc 1 102897*)!m n. MIN m n = MIN n m" ] ) ,
let
val tactictoe_tac1 = ARW [ MIN ] THEN FULL_SIMP_TAC bool_ss [ NOT_LESS ] THEN IMP_RES_TAC LESS_ANTISYM THEN IMP_RES_TAC LESS_EQUAL_ANTISYM
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_COMM" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "ARW" "( BasicProvers.RW_TAC BasicProvers.bool_ss )", "[", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_ANTISYM\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )" ] )
in hhsRecord.try_record_proof "MIN_COMM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MAX_ASSOC = store_thm ( "MAX_ASSOC" , ( Parse.Term [ QUOTE " (*#loc 1 103090*)!m n p. MAX m (MAX n p) = MAX (MAX m n) p" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ MAX ] THEN PROVE_TAC [ NOT_LESS , LESS_EQ_TRANS , LESS_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MAX_ASSOC" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
",", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MAX_ASSOC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_ASSOC = store_thm ( "MIN_ASSOC" , ( Parse.Term [ QUOTE " (*#loc 1 103263*)!m n p. MIN m (MIN n p) = MIN (MIN m n) p" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ MIN ] THEN PROVE_TAC [ NOT_LESS , LESS_EQ_TRANS , LESS_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_ASSOC" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
",", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MIN_ASSOC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_MAX_EQ = store_thm ( "MIN_MAX_EQ" , ( Parse.Term [ QUOTE " (*#loc 1 103438*)!m n. (MIN m n = MAX m n) = (m = n)" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ MAX , MIN ] THEN PROVE_TAC [ NOT_LESS , LESS_EQUAL_ANTISYM , LESS_ANTISYM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_MAX_EQ" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", ",", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )", 
",", 
hhsRecord.fetch "LESS_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_ANTISYM\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MIN_MAX_EQ" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_MAX_LT = store_thm ( "MIN_MAX_LT" , ( Parse.Term [ QUOTE " (*#loc 1 103619*)!m n. (MIN m n < MAX m n) = ~(m = n)" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ MAX , MIN ] THEN PROVE_TAC [ LESS_REFL , NOT_LESS , LESS_OR_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_MAX_LT" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", ",", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", "prim_recTheory.LESS_REFL", ",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MIN_MAX_LT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_MAX_LE = store_thm ( "MIN_MAX_LE" , ( Parse.Term [ QUOTE " (*#loc 1 103790*)!m n. MIN m n <= MAX m n" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ MAX , MIN ] THEN PROVE_TAC [ LESS_OR_EQ , NOT_LESS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_MAX_LE" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", ",", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MIN_MAX_LE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_MAX_PRED = store_thm ( "MIN_MAX_PRED" , ( Parse.Term [ QUOTE " (*#loc 1 103942*)!P m n. P m /\\ P n ==> P (MIN m n) /\\ P (MAX m n)" ] ) ,
let
val tactictoe_tac1 = PROVE_TAC [ MIN , MAX ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_MAX_PRED" 
 ( String.concatWith " " 
 [ "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", ",", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", "]" ] )
in hhsRecord.try_record_proof "MIN_MAX_PRED" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_LT = store_thm ( "MIN_LT" , ( Parse.Term [ QUOTE " (*#loc 1 104060*)!n m p. (MIN m n < p = m < p \\/ n < p) /\\             (p < MIN m n = p < m /\\ p < n)" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ MIN ] THEN PROVE_TAC [ NOT_LESS , LESS_OR_EQ , LESS_ANTISYM , LESS_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_LT" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_ANTISYM\" ) )", 
",", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MIN_LT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MAX_LT = store_thm ( "MAX_LT" , ( Parse.Term [ QUOTE " (*#loc 1 104281*)!n m p. (p < MAX m n = p < m \\/ p < n) /\\             (MAX m n < p = m < p /\\ n < p)" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ MAX ] THEN PROVE_TAC [ NOT_LESS , LESS_OR_EQ , LESS_ANTISYM , LESS_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MAX_LT" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_ANTISYM\" ) )", 
",", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MAX_LT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_LE = store_thm ( "MIN_LE" , ( Parse.Term [ QUOTE " (*#loc 1 104502*)!n m p. (MIN m n <= p = m <= p \\/ n <= p) /\\             (p <= MIN m n = p <= m /\\ p <= n)" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ MIN ] THEN PROVE_TAC [ LESS_OR_EQ , NOT_LESS , LESS_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_LE" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MIN_LE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MAX_LE = store_thm ( "MAX_LE" , ( Parse.Term [ QUOTE " (*#loc 1 104715*)!n m p. (p <= MAX m n = p <= m \\/ p <= n) /\\             (MAX m n <= p = m <= p /\\ n <= p)" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC bool_ss [ MAX ] THEN PROVE_TAC [ LESS_OR_EQ , NOT_LESS , LESS_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MAX_LE" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MAX_LE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_0 = store_thm ( "MIN_0" , ( Parse.Term [ QUOTE " (*#loc 1 104926*)!n. (MIN n 0 = 0) /\\ (MIN 0 n = 0)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ MIN ] THEN PROVE_TAC [ NOT_LESS_0 , NOT_LESS , LESS_OR_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_0" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", "prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MIN_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MAX_0 = store_thm ( "MAX_0" , ( Parse.Term [ QUOTE " (*#loc 1 105076*)!n. (MAX n 0 = n) /\\ (MAX 0 n = n)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ MAX ] THEN PROVE_TAC [ NOT_LESS_0 , NOT_LESS , LESS_OR_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MAX_0" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", "prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MAX_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MAX_EQ_0 = store_thm ( "MAX_EQ_0[simp]" , ( Parse.Term [ QUOTE " (*#loc 1 105240*)(MAX m n = 0) <=> (m = 0) /\\ (n = 0)" ] ) ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ MAX , EQ_IMP_THM ] THEN FULL_SIMP_TAC ( srw_ss ( ) ) [ NOT_LESS_0 , NOT_LESS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MAX_EQ_0" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", ",", 
"boolLib.EQ_IMP_THM", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.FULL_SIMP_TAC", "(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
"prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MAX_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_EQ_0 = store_thm ( "MIN_EQ_0[simp]" , ( Parse.Term [ QUOTE " (*#loc 1 105417*)(MIN m n = 0) <=> (m = 0) \\/ (n = 0)" ] ) ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ MIN , EQ_IMP_THM ] THEN FULL_SIMP_TAC ( srw_ss ( ) ) [ NOT_LESS_0 , NOT_LESS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_EQ_0" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", ",", 
"boolLib.EQ_IMP_THM", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.FULL_SIMP_TAC", "(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
"prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MIN_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MIN_IDEM = store_thm ( "MIN_IDEM" , ( Parse.Term [ QUOTE " (*#loc 1 105586*)!n. MIN n n = n" ] ) ,
let
val tactictoe_tac1 = PROVE_TAC [ MIN ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MIN_IDEM" 
 ( String.concatWith " " 
 [ "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "MIN" "( ( DB.fetch \"arithmetic\" \"MIN_DEF\" ) )", "]" ] )
in hhsRecord.try_record_proof "MIN_IDEM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MAX_IDEM = store_thm ( "MAX_IDEM" , ( Parse.Term [ QUOTE " (*#loc 1 105669*)!n. MAX n n = n" ] ) ,
let
val tactictoe_tac1 = PROVE_TAC [ MAX ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MAX_IDEM" 
 ( String.concatWith " " 
 [ "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "MAX" "( ( DB.fetch \"arithmetic\" \"MAX_DEF\" ) )", "]" ] )
in hhsRecord.try_record_proof "MAX_IDEM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXISTS_GREATEST = store_thm ( "EXISTS_GREATEST" , ( Parse.Term [ QUOTE " (*#loc 1 105766*)!P. (?x. P x) /\\ (?x:num. !y. y > x ==> ~P y) =     ?x. P x /\\ !y. y > x ==> ~P y" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN EQ_TAC THENL [ REWRITE_TAC [ GREATER_DEF ] THEN DISCH_THEN ( CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC ) THEN SUBGOAL_THEN ( ( Parse.Term [ QUOTE " (*#loc 1 105997*)(?x. !y. x < y ==> ~P y) = (?x. (\\x. !y. x < y ==> ~P y) x)" ] ) ) SUBST1_TAC THENL [ BETA_TAC THEN REFL_TAC , DISCH_THEN ( MP_TAC o MATCH_MP WOP ) THEN BETA_TAC THEN CONV_TAC ( DEPTH_CONV NOT_FORALL_CONV ) THEN STRIP_TAC THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 106259*)n:num" ] ) ) THEN ASM_REWRITE_TAC [ ] THEN NTAC 2 ( POP_ASSUM MP_TAC ) THEN STRUCT_CASES_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 106367*)n:num" ] ) ) num_CASES ) THEN REPEAT STRIP_TAC THENL [ UNDISCH_THEN ( ( Parse.Term [ QUOTE " (*#loc 1 106446*)!y. 0 < y ==> ~P y" ] ) ) ( MP_TAC o CONV_RULE ( ONCE_DEPTH_CONV CONTRAPOS_CONV ) ) THEN REWRITE_TAC [ ] THEN STRIP_TAC THEN RES_TAC THEN MP_TAC ( SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 106622*)x:num" ] ) ) LESS_0_CASES ) THEN ASM_REWRITE_TAC [ ] THEN DISCH_THEN ( SUBST_ALL_TAC o SYM ) THEN ASM_REWRITE_TAC [ ] , POP_ASSUM ( MP_TAC o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 106785*)n':num" ] ) ) ) THEN REWRITE_TAC [ prim_recTheory.LESS_SUC_REFL ] THEN DISCH_THEN ( CHOOSE_THEN MP_TAC ) THEN SUBGOAL_THEN ( ( Parse.Term [ QUOTE " (*#loc 1 106931*)!x y. ~(x ==> ~y) = x /\\ y" ] ) ) ( fn th => REWRITE_TAC [ th ] THEN STRIP_TAC ) THENL [ REWRITE_TAC [ NOT_IMP ] , UNDISCH_THEN ( ( Parse.Term [ QUOTE " (*#loc 1 107086*)!y. SUC n' < y ==> ~P y" ] ) ) ( MP_TAC o CONV_RULE ( ONCE_DEPTH_CONV CONTRAPOS_CONV ) o SPEC ( ( Parse.Term [ QUOTE " (*#loc 1 107209*)y:num" ] ) ) ) THEN ASM_REWRITE_TAC [ NOT_LESS , LESS_OR_EQ ] THEN DISCH_THEN ( DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC ) THENL [ IMP_RES_TAC LESS_LESS_SUC , ASM_REWRITE_TAC [ ] ] ] ] ] , REPEAT STRIP_TAC THEN EXISTS_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 107454*)x:num" ] ) ) THEN ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXISTS_GREATEST" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.EQ_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "GREATER_DEF" "( ( DB.fetch \"arithmetic\" \"GREATER_DEF\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.CONJUNCTS_THEN2", "boolLib.STRIP_ASSUME_TAC", "boolLib.MP_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUBGOAL_THEN", "(", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 105997*)(?x. !y. x < y ==> ~P y) = (?x. (\\\\x. !y. x < y ==> ~P y) x)\"", 
"]", ")", ")", "boolLib.SUBST1_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.BETA_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REFL_TAC", ",", 
"boolLib.DISCH_THEN", "(", "boolLib.MP_TAC", "o", "boolLib.MATCH_MP", 
hhsRecord.fetch "WOP" "( ( DB.fetch \"arithmetic\" \"WOP\" ) )", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.BETA_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", "(", 
"boolLib.DEPTH_CONV", "boolLib.NOT_FORALL_CONV", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EXISTS_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 106259*)n:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.NTAC", "2", "(", 
"boolLib.POP_ASSUM", "boolLib.MP_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRUCT_CASES_TAC", 
"(", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 106367*)n:num\"", "]", ")", ")", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.UNDISCH_THEN", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 106446*)!y. 0 < y ==> ~P y\"", "]", ")", ")", "(", "boolLib.MP_TAC", "o", 
"boolLib.CONV_RULE", "(", "boolLib.ONCE_DEPTH_CONV", "boolLib.CONTRAPOS_CONV", ")", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.RES_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MP_TAC", "(", 
"HolKernel.SPEC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 106622*)x:num\"", "]", ")", ")", 
hhsRecord.fetch "LESS_0_CASES" "( ( DB.fetch \"arithmetic\" \"LESS_0_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.SUBST_ALL_TAC", "o", "HolKernel.SYM", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", ",", "boolLib.POP_ASSUM", "(", "boolLib.MP_TAC", "o", "HolKernel.SPEC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 106785*)n':num\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.LESS_SUC_REFL", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.CHOOSE_THEN", "boolLib.MP_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SUBGOAL_THEN", "(", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 106931*)!x y. ~(x ==> ~y) = x /\\\\ y\"", "]", ")", ")", "(", "fn", "th", 
"=>", "boolLib.REWRITE_TAC", "[", "th", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", "boolLib.NOT_IMP", "]", ",", "boolLib.UNDISCH_THEN", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 107086*)!y. SUC n' < y ==> ~P y\"", "]", ")", ")", 
"(", "boolLib.MP_TAC", "o", "boolLib.CONV_RULE", "(", "boolLib.ONCE_DEPTH_CONV", 
"boolLib.CONTRAPOS_CONV", ")", "o", "HolKernel.SPEC", "(", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 107209*)y:num\"", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"boolLib.DISJ_CASES_THEN2", "boolLib.ASSUME_TAC", "boolLib.SUBST_ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_LESS_SUC" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_SUC\" ) )", 
",", "boolLib.ASM_REWRITE_TAC", "[", "]", "]", "]", "]", "]", ",", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.EXISTS_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 107454*)x:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "]" ] )
in hhsRecord.try_record_proof "EXISTS_GREATEST" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXISTS_NUM = store_thm ( "EXISTS_NUM" , ( Parse.Term [ QUOTE " (*#loc 1 107537*)!P. (?n. P n) = P 0 \\/ (?m. P (SUC m))" ] ) ,
let
val tactictoe_tac1 = PROVE_TAC [ num_CASES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXISTS_NUM" 
 ( String.concatWith " " 
 [ "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "EXISTS_NUM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val FORALL_NUM = store_thm ( "FORALL_NUM" , ( Parse.Term [ QUOTE " (*#loc 1 107653*)!P. (!n. P n) = P 0 /\\ !n. P (SUC n)" ] ) ,
let
val tactictoe_tac1 = PROVE_TAC [ num_CASES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "FORALL_NUM" 
 ( String.concatWith " " 
 [ "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "FORALL_NUM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val BOUNDED_FORALL_THM = Q.store_thm ( "BOUNDED_FORALL_THM" , [ QUOTE " (*#loc 1 107784*)!c. 0<c ==> ((!n. n < c ==> P n) = P (c-1) /\\ !n. n < (c-1) ==> P n)" ] ,
let
val tactictoe_tac1 = RW_TAC boolSimps.bool_ss [ ] THEN EQ_TAC THENL [ REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THENL [ METIS_TAC [ ONE , LESS_ADD_SUC , ADD_SYM , SUB_RIGHT_LESS ] , MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 108105*)c-1" ] THEN ASM_REWRITE_TAC [ SUB_LESS_EQ , SUB_LEFT_LESS ] ] , METIS_TAC [ SUB_LESS_OR , LESS_OR_EQ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "BOUNDED_FORALL_THM" 
 ( String.concatWith " " 
 [ "BasicProvers.RW_TAC", "boolSimps.bool_ss", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.FIRST_ASSUM", "boolLib.MATCH_MP_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "metisLib.METIS_TAC", 
"[", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "LESS_ADD_SUC" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_SUC\" ) )", 
",", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
",", 
hhsRecord.fetch "SUB_RIGHT_LESS" "( ( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_LESS\" ) ) )", 
"]", ",", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_EQ_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 108105*)c-1\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "SUB_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "SUB_LEFT_LESS" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_LESS\" ) )", 
"]", "]", ",", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "SUB_LESS_OR" "( ( DB.fetch \"arithmetic\" \"SUB_LESS_OR\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "BOUNDED_FORALL_THM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val BOUNDED_EXISTS_THM = Q.store_thm ( "BOUNDED_EXISTS_THM" , [ QUOTE " (*#loc 1 108280*)!c. 0<c ==> ((?n. n < c /\\ P n) = P (c-1) \\/ ?n. n < (c-1) /\\ P n)" ] ,
let
val tactictoe_tac1 = REPEAT ( STRIP_TAC ORELSE EQ_TAC ) THENL [ METIS_TAC [ SUB_LESS_OR , LESS_REFL , LESS_EQ_LESS_TRANS , LESS_LESS_CASES ] , METIS_TAC [ num_CASES , LESS_REFL , SUC_SUB1 , LESS_SUC_REFL ] , METIS_TAC [ SUB_LEFT_LESS , ADD1 , SUC_LESS ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "BOUNDED_EXISTS_THM" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "(", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.ORELSE hhs_infixl0_close", "boolLib.EQ_TAC", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "metisLib.METIS_TAC", 
"[", 
hhsRecord.fetch "SUB_LESS_OR" "( ( DB.fetch \"arithmetic\" \"SUB_LESS_OR\" ) )", 
",", "prim_recTheory.LESS_REFL", ",", 
hhsRecord.fetch "LESS_EQ_LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_LESS_TRANS\" ) )", 
",", 
hhsRecord.fetch "LESS_LESS_CASES" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_CASES\" ) )", 
"]", ",", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
",", "prim_recTheory.LESS_REFL", ",", 
hhsRecord.fetch "SUC_SUB1" "( ( DB.fetch \"arithmetic\" \"SUC_SUB1\" ) )", 
",", "prim_recTheory.LESS_SUC_REFL", "]", ",", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "SUB_LEFT_LESS" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_LESS\" ) )", 
",", hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", ",", 
"prim_recTheory.SUC_LESS", "]", "]" ] )
in hhsRecord.try_record_proof "BOUNDED_EXISTS_THM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val transitive_monotone = Q.store_thm ( "transitive_monotone" , [ QUOTE " (*#loc 1 108648*)!R f. transitive R /\\ (!n. R (f n) (f (SUC n))) ==>           !m n. m < n ==> R (f m) (f n)" ] ,
let
val tactictoe_tac1 = NTAC 3 STRIP_TAC THEN INDUCT_TAC THEN ( INDUCT_TAC >>- 1 ?? REWRITE_TAC [ NOT_LESS_0 ] ) >>- 1 ?? ( POP_ASSUM MP_TAC THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 108886*)n" ] STRUCT_CASES_TAC num_CASES THEN METIS_TAC [ LESS_0 , relationTheory.transitive_def ] ) THEN METIS_TAC [ LESS_THM , relationTheory.transitive_def ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "transitive_monotone" 
 ( String.concatWith " " 
 [ "boolLib.NTAC", "3", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"prim_recTheory.NOT_LESS_0", "]", ")", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "(", "boolLib.POP_ASSUM", 
"boolLib.MP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 108886*)n\"", "]", 
"boolLib.STRUCT_CASES_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
"prim_recTheory.LESS_0", ",", "relationTheory.transitive_def", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
"prim_recTheory.LESS_THM", ",", "relationTheory.transitive_def", "]" ] )
in hhsRecord.try_record_proof "transitive_monotone" false tactictoe_tac2 tactictoe_tac1
end )
;
val STRICTLY_INCREASING_TC = save_thm ( "STRICTLY_INCREASING_TC" , transitive_monotone |> Q.ISPEC [ QUOTE " (*#loc 1 109140*)$<" ] |> SIMP_RULE bool_ss [ Q.prove ( [ QUOTE " (*#loc 1 109184*)transitive $<" ] ,
let
val tactictoe_tac1 = METIS_TAC [ relationTheory.transitive_def , LESS_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_308" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", "relationTheory.transitive_def", ",", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_308" false tactictoe_tac2 tactictoe_tac1
end ) ] )
;
val STRICTLY_INCREASING_ONE_ONE = Q.store_thm ( "STRICTLY_INCREASING_ONE_ONE" , [ QUOTE " (*#loc 1 109345*)!f. (!n. f n < f (SUC n)) ==> ONE_ONE f" ] ,
let
val tactictoe_tac1 = REWRITE_TAC [ ONE_ONE_THM ] THEN METIS_TAC [ STRICTLY_INCREASING_TC , NOT_LESS , LESS_OR_EQ , LESS_EQUAL_ANTISYM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "STRICTLY_INCREASING_ONE_ONE" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "boolLib.ONE_ONE_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "STRICTLY_INCREASING_TC" "( ( DB.fetch \"arithmetic\" \"STRICTLY_INCREASING_TC\" ) )", 
",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "STRICTLY_INCREASING_ONE_ONE" false tactictoe_tac2 tactictoe_tac1
end )
;
val ONE_ONE_INV_IMAGE_BOUNDED = Q.store_thm ( "ONE_ONE_INV_IMAGE_BOUNDED" , [ QUOTE " (*#loc 1 109576*)ONE_ONE (f:num->num) ==> !b. ?a. !x. f x <= b ==> x <= a" ] ,
let
val tactictoe_tac1 = REWRITE_TAC [ ONE_ONE_THM ] THEN DISCH_TAC THEN INDUCT_TAC THENL [ REWRITE_TAC [ LESS_EQ_0 ] THEN Q.ASM_CASES_TAC [ QUOTE " (*#loc 1 109759*)?z. f z = 0" ] THENL [ POP_ASSUM CHOOSE_TAC THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 109838*)z" ] THEN REPEAT STRIP_TAC THEN VALIDATE ( FIRST_X_ASSUM ( ASSUME_TAC o UNDISCH o Q.SPECL [ [ QUOTE " (*#loc 1 109944*)x" ] , [ QUOTE " (*#loc 1 109949*)z" ] ] ) ) THEN ASM_REWRITE_TAC [ LESS_EQ_REFL ] , Q.EXISTS_TAC [ QUOTE " (*#loc 1 110020*)0" ] THEN REPEAT STRIP_TAC THEN RES_TAC ] , POP_ASSUM CHOOSE_TAC THEN REWRITE_TAC [ LE ] THEN Q.ASM_CASES_TAC [ QUOTE " (*#loc 1 110138*)?z. f z = SUC b" ] THENL [ POP_ASSUM CHOOSE_TAC THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 110221*)MAX a z" ] THEN REWRITE_TAC [ MAX_LE ] THEN REPEAT STRIP_TAC THENL [ VALIDATE ( FIRST_X_ASSUM ( ASSUME_TAC o UNDISCH o Q.SPECL [ [ QUOTE " (*#loc 1 110378*)x" ] , [ QUOTE " (*#loc 1 110383*)z" ] ] ) ) THEN ASM_REWRITE_TAC [ LESS_EQ_REFL ] , RES_TAC THEN ASM_REWRITE_TAC [ ] ] , Q.EXISTS_TAC [ QUOTE " (*#loc 1 110498*)a" ] THEN REPEAT STRIP_TAC THEN RES_TAC ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ONE_ONE_INV_IMAGE_BOUNDED" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "boolLib.ONE_ONE_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ASM_CASES_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 109759*)?z. f z = 0\"", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.POP_ASSUM", 
"boolLib.CHOOSE_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.EXISTS_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 109838*)z\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.VALIDATE", "(", "boolLib.FIRST_X_ASSUM", "(", "boolLib.ASSUME_TAC", "o", 
"boolLib.UNDISCH", "o", "Q.SPECL", "[", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 109944*)x\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 109949*)z\"", "]", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
"]", ",", "Q.EXISTS_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 110020*)0\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.RES_TAC", "]", ",", "boolLib.POP_ASSUM", "boolLib.CHOOSE_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LE" "( ( DB.fetch \"arithmetic\" \"LE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ASM_CASES_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 110138*)?z. f z = SUC b\"", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.POP_ASSUM", 
"boolLib.CHOOSE_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.EXISTS_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 110221*)MAX a z\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "MAX_LE" "( ( DB.fetch \"arithmetic\" \"MAX_LE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.VALIDATE", "(", "boolLib.FIRST_X_ASSUM", "(", "boolLib.ASSUME_TAC", "o", 
"boolLib.UNDISCH", "o", "Q.SPECL", "[", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 110378*)x\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 110383*)z\"", "]", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
"]", ",", "boolLib.RES_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", "]", ",", "Q.EXISTS_TAC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 110498*)a\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.RES_TAC", "]", "]" ] )
in hhsRecord.try_record_proof "ONE_ONE_INV_IMAGE_BOUNDED" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ONE_ONE_UNBOUNDED = Q.store_thm ( "ONE_ONE_UNBOUNDED" , [ QUOTE " (*#loc 1 110601*)!f. ONE_ONE (f:num->num) ==> !b.?n. b < f n" ] ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN POP_ASSUM ( CHOOSE_TAC o Q.SPEC [ QUOTE " (*#loc 1 110705*)b" ] o MATCH_MP ONE_ONE_INV_IMAGE_BOUNDED ) THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 110771*)SUC a" ] THEN REWRITE_TAC [ GSYM NOT_LESS_EQUAL ] THEN DISCH_TAC THEN RES_TAC THEN POP_ASSUM ( ACCEPT_TAC o REWRITE_RULE [ GSYM LESS_EQ , LESS_REFL ] )
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ONE_ONE_UNBOUNDED" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"boolLib.CHOOSE_TAC", "o", "Q.SPEC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 110705*)b\"", "]", "o", "boolLib.MATCH_MP", 
hhsRecord.fetch "ONE_ONE_INV_IMAGE_BOUNDED" "( ( DB.fetch \"arithmetic\" \"ONE_ONE_INV_IMAGE_BOUNDED\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 110771*)SUC a\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.GSYM", 
hhsRecord.fetch "NOT_LESS_EQUAL" "( ( DB.fetch \"arithmetic\" \"NOT_LESS_EQUAL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.RES_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"boolLib.ACCEPT_TAC", "o", "boolLib.REWRITE_RULE", "[", "boolLib.GSYM", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", ",", 
"prim_recTheory.LESS_REFL", "]", ")" ] )
in hhsRecord.try_record_proof "ONE_ONE_UNBOUNDED" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val STRICTLY_INCREASING_UNBOUNDED = Q.store_thm ( "STRICTLY_INCREASING_UNBOUNDED" , [ QUOTE " (*#loc 1 111008*)!f. (!n. f n < f (SUC n)) ==> !b.?n. b < f n" ] ,
let
val tactictoe_tac1 = METIS_TAC [ STRICTLY_INCREASING_ONE_ONE , ONE_ONE_UNBOUNDED ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "STRICTLY_INCREASING_UNBOUNDED" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "STRICTLY_INCREASING_ONE_ONE" "( ( DB.fetch \"arithmetic\" \"STRICTLY_INCREASING_ONE_ONE\" ) )", 
",", 
hhsRecord.fetch "ONE_ONE_UNBOUNDED" "( ( DB.fetch \"arithmetic\" \"ONE_ONE_UNBOUNDED\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "STRICTLY_INCREASING_UNBOUNDED" false tactictoe_tac2 tactictoe_tac1
end )
;
val STRICTLY_DECREASING_TC = Q.prove ( [ QUOTE " (*#loc 1 111159*)!f. (!n. f (SUC n) < f n) ==> !m n. m < n ==> f n < f m" ] ,
let
val tactictoe_tac1 = NTAC 2 STRIP_TAC THEN ( transitive_monotone |> Q.ISPECL [ [ QUOTE " (*#loc 1 111280*)\\x y. y < x" ] , [ QUOTE " (*#loc 1 111294*)f:num->num" ] ] |> SIMP_RULE bool_ss [ ] |> MATCH_MP_TAC ) THEN SRW_TAC [ ] [ relationTheory.transitive_def ] THEN METIS_TAC [ LESS_TRANS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_313" 
 ( String.concatWith " " 
 [ "boolLib.NTAC", "2", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", 
hhsRecord.fetch "transitive_monotone" "( ( DB.fetch \"arithmetic\" \"transitive_monotone\" ) )", 
"hhs_infixl0_open HolKernel.|> hhs_infixl0_close", "Q.ISPECL", "[", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 111280*)\\\\x y. y < x\"", "]", ",", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 111294*)f:num->num\"", "]", "]", 
"hhs_infixl0_open HolKernel.|> hhs_infixl0_close", "simpLib.SIMP_RULE", 
"BasicProvers.bool_ss", "[", "]", 
"hhs_infixl0_open HolKernel.|> hhs_infixl0_close", "boolLib.MATCH_MP_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "relationTheory.transitive_def", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_313" false tactictoe_tac2 tactictoe_tac1
end )
;
val STRICTLY_DECREASING_ONE_ONE = Q.prove ( [ QUOTE " (*#loc 1 111481*)!f. (!n. f (SUC n) < f n) ==> ONE_ONE f" ] ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ ONE_ONE_THM ] THEN METIS_TAC [ STRICTLY_DECREASING_TC , NOT_LESS , LESS_OR_EQ , LESS_EQUAL_ANTISYM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_314" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", "boolLib.ONE_ONE_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "STRICTLY_DECREASING_TC" "", ",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_314" false tactictoe_tac2 tactictoe_tac1
end )
;
val NOT_STRICTLY_DECREASING = Q.store_thm ( "NOT_STRICTLY_DECREASING" , [ QUOTE " (*#loc 1 111708*)!f. ~(!n. f (SUC n) < f n)" ] ,
let
val tactictoe_tac1 = NTAC 2 STRIP_TAC THEN IMP_RES_TAC STRICTLY_DECREASING_TC THEN IMP_RES_TAC STRICTLY_DECREASING_ONE_ONE THEN IMP_RES_TAC ONE_ONE_UNBOUNDED THEN POP_ASSUM ( Q.SPEC_THEN [ QUOTE " (*#loc 1 111918*)f 0" ] STRIP_ASSUME_TAC ) THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 111962*)n" ] STRIP_ASSUME_TAC num_CASES >>- 1 ?? METIS_TAC [ LESS_NOT_EQ ] THEN METIS_TAC [ LESS_ANTISYM , LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NOT_STRICTLY_DECREASING" 
 ( String.concatWith " " 
 [ "boolLib.NTAC", "2", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "STRICTLY_DECREASING_TC" "", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "STRICTLY_DECREASING_ONE_ONE" "", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "ONE_ONE_UNBOUNDED" "( ( DB.fetch \"arithmetic\" \"ONE_ONE_UNBOUNDED\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 111918*)f 0\"", "]", 
"boolLib.STRIP_ASSUME_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 111962*)n\"", "]", "boolLib.STRIP_ASSUME_TAC", 
hhsRecord.fetch "num_CASES" "( ( DB.fetch \"arithmetic\" \"num_CASES\" ) )", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
"prim_recTheory.LESS_NOT_EQ", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_ANTISYM\" ) )", 
",", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "NOT_STRICTLY_DECREASING" false tactictoe_tac2 tactictoe_tac1
end )
;
val ABS_DIFF_def = new_definition ( "ABS_DIFF_def" , ( Parse.Term [ QUOTE " (*#loc 1 112126*)ABS_DIFF n m = if n < m then m - n else n - m" ] ) )
;
val ABS_DIFF_SYM = Q.store_thm ( "ABS_DIFF_SYM" , [ QUOTE " (*#loc 1 112228*)!n m. ABS_DIFF n m = ABS_DIFF m n" ] ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ ABS_DIFF_def ] THEN METIS_TAC [ LESS_ANTISYM , NOT_LESS , LESS_OR_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_SYM" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "ABS_DIFF_def" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_def\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_ANTISYM\" ) )", 
",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_SYM" false tactictoe_tac2 tactictoe_tac1
end )
;
val ABS_DIFF_COMM = save_thm ( "ABS_DIFF_COMM" , ABS_DIFF_SYM )
;
val ABS_DIFF_EQS = Q.store_thm ( "ABS_DIFF_EQS" , [ QUOTE " (*#loc 1 112458*)!n. ABS_DIFF n n = 0" ] ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ ABS_DIFF_def , SUB_EQUAL_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_EQS" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "ABS_DIFF_def" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_def\" ) )", 
",", 
hhsRecord.fetch "SUB_EQUAL_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQUAL_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_EQS" false tactictoe_tac2 tactictoe_tac1
end )
;
val _ = export_rewrites [ "ABS_DIFF_EQS" ]
;
val ABS_DIFF_EQ_0 = Q.store_thm ( "ABS_DIFF_EQ_0" , [ QUOTE " (*#loc 1 112617*)!n m. (ABS_DIFF n m = 0) <=> (n = m)" ] ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ ABS_DIFF_def , LESS_OR_EQ , SUB_EQ_0 ] THEN METIS_TAC [ LESS_ANTISYM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_EQ_0" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "ABS_DIFF_def" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_def\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "SUB_EQ_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQ_0\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_ANTISYM\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_EQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
val ABS_DIFF_ZERO = Q.store_thm ( "ABS_DIFF_ZERO" , [ QUOTE " (*#loc 1 112792*)!n. (ABS_DIFF n 0 = n) /\\ (ABS_DIFF 0 n = n)" ] ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ ABS_DIFF_def , SUB_0 ] THEN METIS_TAC [ NOT_LESS_0 , NOT_ZERO_LT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_ZERO" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "ABS_DIFF_def" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_def\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
"prim_recTheory.NOT_LESS_0", ",", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_ZERO" false tactictoe_tac2 tactictoe_tac1
end )
;
val _ = export_rewrites [ "ABS_DIFF_ZERO" ]
;
val ABS_DIFF_SUC = Q.store_thm ( "ABS_DIFF_SUC" , [ QUOTE " (*#loc 1 113016*)!n m. (ABS_DIFF (SUC n) (SUC m)) = (ABS_DIFF n m)" ] ,
let
val tactictoe_tac1 = REWRITE_TAC [ ABS_DIFF_def , LESS_MONO_EQ , SUB_MONO_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_SUC" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ABS_DIFF_def" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_def\" ) )", 
",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
fun owr commth = CONV_RULE ( ONCE_DEPTH_CONV ( REWR_CONV commth ) )
;
;
val LESS_EQ_TRANS' = REWRITE_RULE [ GSYM AND_IMP_INTRO ] LESS_EQ_TRANS
;
;
val AND_IMP_INTRO' = owr CONJ_COMM AND_IMP_INTRO
;
;
val LESS_EQ_TRANS'' = REWRITE_RULE [ GSYM AND_IMP_INTRO' ] LESS_EQ_TRANS
;
;
val LESS_EQ_ADD' = owr ADD_COMM LESS_EQ_ADD
;
;
val LESS_EQ_SUC_REFL' = SPEC_ALL LESS_EQ_SUC_REFL
;
;
val leq_ss = MATCH_MP ( MATCH_MP LESS_EQ_TRANS'' LESS_EQ_SUC_REFL' ) LESS_EQ_SUC_REFL'
;
;
val imp_leq_ss = MATCH_MP LESS_EQ_TRANS'' leq_ss
;
;
val ABS_DIFF_SUC_LE = Q.store_thm ( "ABS_DIFF_SUC_LE" , [ QUOTE " (*#loc 1 113684*)!x z. ABS_DIFF x (SUC z) <= SUC (ABS_DIFF x z)" ] ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ABS_DIFF_ZERO , ABS_DIFF_SUC , ADD , ADD_0 , GSYM ADD_SUC , LESS_EQ_REFL , LESS_EQ_MONO , ZERO_LESS_EQ , leq_ss ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_SUC_LE" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ABS_DIFF_ZERO" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_ZERO\" ) )", 
",", 
hhsRecord.fetch "ABS_DIFF_SUC" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_SUC\" ) )", 
",", hhsRecord.fetch "ADD" "", ",", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ",", 
"boolLib.GSYM", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", ",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "leq_ss" "( boolLib.MATCH_MP ( boolLib.MATCH_MP ( boolLib.REWRITE_RULE [ boolLib.GSYM ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end boolLib.CONJ_COMM boolLib.AND_IMP_INTRO ) ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) ) ) ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"LESS_EQ_SUC_REFL\" ) ) ) ) ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"LESS_EQ_SUC_REFL\" ) ) ) )", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_SUC_LE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ABS_DIFF_PLUS_LE = Q.store_thm ( "ABS_DIFF_PLUS_LE" , [ QUOTE " (*#loc 1 113948*)!x z y. ABS_DIFF x (y + z) <= y + (ABS_DIFF x z)" ] ,
let
val tactictoe_tac1 = GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ ADD , LESS_EQ_REFL ] THEN MATCH_MP_TAC ( MATCH_MP LESS_EQ_TRANS' ( SPEC_ALL ABS_DIFF_SUC_LE ) ) THEN ASM_REWRITE_TAC [ LESS_EQ_MONO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_PLUS_LE" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD" "", ",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
"(", "boolLib.MATCH_MP", 
hhsRecord.fetch "LESS_EQ_TRANS'" "( boolLib.REWRITE_RULE [ boolLib.GSYM boolLib.AND_IMP_INTRO ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) ) )", 
"(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "ABS_DIFF_SUC_LE" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_SUC_LE\" ) )", 
")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_PLUS_LE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ABS_DIFF_PLUS_LE' = owr ADD_COMM ABS_DIFF_PLUS_LE
;
;
val [ ADT_splemx , ADT_splemx' ] = map ( owr ABS_DIFF_COMM ) [ ABS_DIFF_PLUS_LE , ABS_DIFF_PLUS_LE' ]
;
;
val ABS_DIFF_LE_SUM = Q.store_thm ( "ABS_DIFF_LE_SUM" , [ QUOTE " (*#loc 1 114408*)ABS_DIFF x z <= x + z" ] ,
let
val tactictoe_tac1 = REWRITE_TAC [ ABS_DIFF_def ] THEN COND_CASES_TAC THEN MATCH_MP_TAC ( MATCH_MP LESS_EQ_TRANS' ( SPEC_ALL SUB_LESS_EQ ) ) THEN REWRITE_TAC [ LESS_EQ_ADD , LESS_EQ_ADD' ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_LE_SUM" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ABS_DIFF_def" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_def\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.COND_CASES_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", "(", "boolLib.MATCH_MP", 
hhsRecord.fetch "LESS_EQ_TRANS'" "( boolLib.REWRITE_RULE [ boolLib.GSYM boolLib.AND_IMP_INTRO ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) ) )", 
"(", "boolLib.SPEC_ALL", 
hhsRecord.fetch "SUB_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_LESS_EQ\" ) )", 
")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LESS_EQ_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_ADD'" "( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) ) ( ( DB.fetch \"arithmetic\" \"LESS_EQ_ADD\" ) ) )", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_LE_SUM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ABS_DIFF_LE_SUM' = owr ADD_COMM ABS_DIFF_LE_SUM
;
;
val [ ADT_sslem , ADT_sslem' ] = map ( MATCH_MP imp_leq_ss ) [ ABS_DIFF_LE_SUM , ABS_DIFF_LE_SUM' ]
;
;
val ABS_DIFF_TRIANGLE_lem = Q.store_thm ( "ABS_DIFF_TRIANGLE_lem" , [ QUOTE " (*#loc 1 114823*)!x y. x <= ABS_DIFF x y + y" ] ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ABS_DIFF_ZERO , ABS_DIFF_SUC , ADD , ADD_0 , GSYM ADD_SUC , LESS_EQ_REFL , LESS_EQ_MONO , ZERO_LESS_EQ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_TRIANGLE_lem" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ABS_DIFF_ZERO" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_ZERO\" ) )", 
",", 
hhsRecord.fetch "ABS_DIFF_SUC" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_SUC\" ) )", 
",", hhsRecord.fetch "ADD" "", ",", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ",", 
"boolLib.GSYM", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", ",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_TRIANGLE_lem" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ABS_DIFF_TRIANGLE_lem' = owr ABS_DIFF_COMM ( owr ADD_COMM ABS_DIFF_TRIANGLE_lem )
;
;
val ABS_DIFF_TRIANGLE = Q.store_thm ( "ABS_DIFF_TRIANGLE" , [ QUOTE " (*#loc 1 115148*)!x y z. ABS_DIFF x z <= ABS_DIFF x y + ABS_DIFF y z" ] ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ABS_DIFF_ZERO , ABS_DIFF_SUC , ADD , ADD_0 , GSYM ADD_SUC , LESS_EQ_REFL , LESS_EQ_MONO , ZERO_LESS_EQ , ABS_DIFF_TRIANGLE_lem , ABS_DIFF_TRIANGLE_lem' , ADT_sslem ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_TRIANGLE" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ABS_DIFF_ZERO" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_ZERO\" ) )", 
",", 
hhsRecord.fetch "ABS_DIFF_SUC" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_SUC\" ) )", 
",", hhsRecord.fetch "ADD" "", ",", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ",", 
"boolLib.GSYM", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", ",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "ABS_DIFF_TRIANGLE_lem" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_TRIANGLE_lem\" ) )", 
",", 
hhsRecord.fetch "ABS_DIFF_TRIANGLE_lem'" "( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_COMM\" ) ) ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) ) ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_TRIANGLE_lem\" ) ) ) )", 
",", 
hhsRecord.fetch "ADT_sslem" "let val [ ADT_sslem , ADT_sslem' ] = map ( boolLib.MATCH_MP ( boolLib.MATCH_MP ( boolLib.REWRITE_RULE [ boolLib.GSYM ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end boolLib.CONJ_COMM boolLib.AND_IMP_INTRO ) ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) ) ) ( boolLib.MATCH_MP ( boolLib.MATCH_MP ( boolLib.REWRITE_RULE [ boolLib.GSYM ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end boolLib.CONJ_COMM boolLib.AND_IMP_INTRO ) ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) ) ) ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"LESS_EQ_SUC_REFL\" ) ) ) ) ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"LESS_EQ_SUC_REFL\" ) ) ) ) ) ) [ ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_LE_SUM\" ) ) , ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) ) ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_LE_SUM\" ) ) ) ] in ADT_sslem end", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_TRIANGLE" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ABS_DIFF_ADD_SAME = Q.store_thm ( "ABS_DIFF_ADD_SAME" , [ QUOTE " (*#loc 1 115474*)!n m p. ABS_DIFF (n + p) (m + p) = ABS_DIFF n m" ] ,
let
val tactictoe_tac1 = GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ ADD_0 , GSYM ADD_SUC , ABS_DIFF_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_ADD_SAME" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ",", 
"boolLib.GSYM", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", ",", 
hhsRecord.fetch "ABS_DIFF_SUC" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_SUC\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_ADD_SAME" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LE_SUB_RCANCEL = Q.store_thm ( "LE_SUB_RCANCEL" , [ QUOTE " (*#loc 1 115685*)!m n p. n - m <= p - m <=> n <= m \\/ n <= p" ] ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ LESS_EQ_REFL , LESS_EQ_MONO , ZERO_LESS_EQ , NOT_SUC_LESS_EQ_0 , SUB_MONO_EQ , SUB_0 , SUB_EQ_0 , LESS_EQ_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LE_SUB_RCANCEL" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_EQ_0" "( ( DB.fetch \"arithmetic\" \"SUB_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "LE_SUB_RCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LT_SUB_RCANCEL = Q.store_thm ( "LT_SUB_RCANCEL" , [ QUOTE " (*#loc 1 115941*)!m n p. n - m < p - m <=> n < p /\\ m < p" ] ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN REWRITE_TAC [ GSYM NOT_LESS_EQUAL , LE_SUB_RCANCEL , DE_MORGAN_THM ] THEN MATCH_ACCEPT_TAC CONJ_COMM
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LT_SUB_RCANCEL" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
"boolLib.GSYM", 
hhsRecord.fetch "NOT_LESS_EQUAL" "( ( DB.fetch \"arithmetic\" \"NOT_LESS_EQUAL\" ) )", 
",", 
hhsRecord.fetch "LE_SUB_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_SUB_RCANCEL\" ) )", 
",", "boolLib.DE_MORGAN_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_ACCEPT_TAC", 
"boolLib.CONJ_COMM" ] )
in hhsRecord.try_record_proof "LT_SUB_RCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LE_SUB_LCANCEL = Q.store_thm ( "LE_SUB_LCANCEL" , [ QUOTE " (*#loc 1 116165*)!z y x. x - y <= x - z = z <= y \\/ x <= y" ] ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ SUB_MONO_EQ , LESS_EQ_MONO , LESS_EQ_REFL , SUB_0 , NOT_SUC_LESS_EQ_0 , ZERO_LESS_EQ , NOT_SUC_LESS_EQ , SUB_LESS_EQ , SUB_LE_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LE_SUB_LCANCEL" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "SUB_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "SUB_LE_SUC" "( boolLib.MATCH_MP ( ( DB.fetch \"arithmetic\" \"LESS_IMP_LESS_OR_EQ\" ) ) ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"SUB_LESS_SUC\" ) ) ) )", 
"]" ] )
in hhsRecord.try_record_proof "LE_SUB_LCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LT_SUB_LCANCEL = Q.store_thm ( "LT_SUB_LCANCEL" , [ QUOTE " (*#loc 1 116443*)!z y x. x - y < x - z = z < y /\\ z < x" ] ,
let
val tactictoe_tac1 = REWRITE_TAC [ GSYM NOT_LESS_EQUAL , LE_SUB_LCANCEL , DE_MORGAN_THM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LT_SUB_LCANCEL" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "NOT_LESS_EQUAL" "( ( DB.fetch \"arithmetic\" \"NOT_LESS_EQUAL\" ) )", 
",", 
hhsRecord.fetch "LE_SUB_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_SUB_LCANCEL\" ) )", 
",", "boolLib.DE_MORGAN_THM", "]" ] )
in hhsRecord.try_record_proof "LT_SUB_LCANCEL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ABS_DIFF_SUMS = Q.store_thm ( "ABS_DIFF_SUMS" , [ QUOTE " (*#loc 1 116605*)!n1 n2 m1 m2. ABS_DIFF (n1 + n2) (m1 + m2) <= ABS_DIFF n1 m1 + ABS_DIFF n2 m2" ] ,
let
val tactictoe_tac1 = REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [ ABS_DIFF_ZERO , ABS_DIFF_SUC , ADD , ADD_0 , GSYM ADD_SUC , LESS_EQ_REFL , LESS_EQ_MONO , ZERO_LESS_EQ , ADT_sslem' , ADT_sslem ] THENL [ REWRITE_TAC [ GSYM ( CONJUNCT2 ADD ) , ABS_DIFF_PLUS_LE ] , REWRITE_TAC [ ADD_SUC , ABS_DIFF_PLUS_LE' ] , REWRITE_TAC [ GSYM ( CONJUNCT2 ADD ) , ADT_splemx ] , REWRITE_TAC [ ADD_SUC , ADT_splemx' ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ABS_DIFF_SUMS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", 
hhsRecord.fetch "ABS_DIFF_ZERO" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_ZERO\" ) )", 
",", 
hhsRecord.fetch "ABS_DIFF_SUC" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_SUC\" ) )", 
",", hhsRecord.fetch "ADD" "", ",", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ",", 
"boolLib.GSYM", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", ",", 
hhsRecord.fetch "LESS_EQ_REFL" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_REFL\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "ADT_sslem'" "let val [ ADT_sslem , ADT_sslem' ] = map ( boolLib.MATCH_MP ( boolLib.MATCH_MP ( boolLib.REWRITE_RULE [ boolLib.GSYM ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end boolLib.CONJ_COMM boolLib.AND_IMP_INTRO ) ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) ) ) ( boolLib.MATCH_MP ( boolLib.MATCH_MP ( boolLib.REWRITE_RULE [ boolLib.GSYM ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end boolLib.CONJ_COMM boolLib.AND_IMP_INTRO ) ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) ) ) ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"LESS_EQ_SUC_REFL\" ) ) ) ) ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"LESS_EQ_SUC_REFL\" ) ) ) ) ) ) [ ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_LE_SUM\" ) ) , ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) ) ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_LE_SUM\" ) ) ) ] in ADT_sslem' end", 
",", 
hhsRecord.fetch "ADT_sslem" "let val [ ADT_sslem , ADT_sslem' ] = map ( boolLib.MATCH_MP ( boolLib.MATCH_MP ( boolLib.REWRITE_RULE [ boolLib.GSYM ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end boolLib.CONJ_COMM boolLib.AND_IMP_INTRO ) ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) ) ) ( boolLib.MATCH_MP ( boolLib.MATCH_MP ( boolLib.REWRITE_RULE [ boolLib.GSYM ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end boolLib.CONJ_COMM boolLib.AND_IMP_INTRO ) ] ( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) ) ) ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"LESS_EQ_SUC_REFL\" ) ) ) ) ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"LESS_EQ_SUC_REFL\" ) ) ) ) ) ) [ ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_LE_SUM\" ) ) , ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) ) ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_LE_SUM\" ) ) ) ] in ADT_sslem end", 
"]", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.REWRITE_TAC", "[", "boolLib.GSYM", "(", "HolKernel.CONJUNCT2", 
hhsRecord.fetch "ADD" "", ")", ",", 
hhsRecord.fetch "ABS_DIFF_PLUS_LE" "( ( DB.fetch \"arithmetic\" \"ABS_DIFF_PLUS_LE\" ) )", 
"]", ",", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", ",", 
hhsRecord.fetch "ABS_DIFF_PLUS_LE'" "( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) ) ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_PLUS_LE\" ) ) )", 
"]", ",", "boolLib.REWRITE_TAC", "[", "boolLib.GSYM", "(", "HolKernel.CONJUNCT2", 
hhsRecord.fetch "ADD" "", ")", ",", 
hhsRecord.fetch "ADT_splemx" "let val [ ADT_splemx , ADT_splemx' ] = map ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_COMM\" ) ) ) [ ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_PLUS_LE\" ) ) , ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) ) ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_PLUS_LE\" ) ) ) ] in ADT_splemx end", 
"]", ",", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_SUC" "( ( DB.fetch \"arithmetic\" \"ADD_SUC\" ) )", ",", 
hhsRecord.fetch "ADT_splemx'" "let val [ ADT_splemx , ADT_splemx' ] = map ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_COMM\" ) ) ) [ ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_PLUS_LE\" ) ) , ( let fun owr commth = boolLib.CONV_RULE ( boolLib.ONCE_DEPTH_CONV ( boolLib.REWR_CONV commth ) ) in owr end ( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) ) ( ( DB.fetch \"arithmetic\" \"ABS_DIFF_PLUS_LE\" ) ) ) ] in ADT_splemx' end", 
"]", "]" ] )
in hhsRecord.try_record_proof "ABS_DIFF_SUMS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = print "Miscellaneous theorems\n"
;
val FUNPOW_SUC = store_thm ( "FUNPOW_SUC" , ( Parse.Term [ QUOTE " (*#loc 1 117154*)!f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN INDUCT_TAC THENL [ REWRITE_TAC [ FUNPOW ] , ONCE_REWRITE_TAC [ FUNPOW ] THEN ASM_REWRITE_TAC [ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "FUNPOW_SUC" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "FUNPOW" "", "]", ",", "boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "FUNPOW" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "]" ] )
in hhsRecord.try_record_proof "FUNPOW_SUC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val FUNPOW_0 = store_thm ( "FUNPOW_0" , ( Parse.Term [ QUOTE " (*#loc 1 117382*)FUNPOW f 0 x = x" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ FUNPOW ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "FUNPOW_0" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", hhsRecord.fetch "FUNPOW" "", "]" ] )
in hhsRecord.try_record_proof "FUNPOW_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = export_rewrites [ "FUNPOW_0" ]
;
val FUNPOW_ADD = store_thm ( "FUNPOW_ADD" , ( Parse.Term [ QUOTE " (*#loc 1 117512*)!m n. FUNPOW f (m + n) x = FUNPOW f m (FUNPOW f n x)" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THENL [ REWRITE_TAC [ ADD_CLAUSES , FUNPOW ] , ASM_REWRITE_TAC [ ADD_CLAUSES , FUNPOW_SUC ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "FUNPOW_ADD" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "FUNPOW" "", "]", ",", "boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "FUNPOW_SUC" "( ( DB.fetch \"arithmetic\" \"FUNPOW_SUC\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "FUNPOW_ADD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val FUNPOW_1 = store_thm ( "FUNPOW_1" , ( Parse.Term [ QUOTE " (*#loc 1 117723*)FUNPOW f 1 x = f x" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ FUNPOW , ONE ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "FUNPOW_1" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", hhsRecord.fetch "FUNPOW" "", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]" ] )
in hhsRecord.try_record_proof "FUNPOW_1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = export_rewrites [ "FUNPOW_1" ]
;
val NRC_0 = save_thm ( "NRC_0" , CONJUNCT1 NRC )
;
;
val _ = export_rewrites [ "NRC_0" ]
;
val NRC_1 = store_thm ( "NRC_1" , ( Parse.Term [ QUOTE " (*#loc 1 117931*)NRC R 1 x y = R x y" ] ) ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ ONE , NRC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NRC_1" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "NRC" "", "]" ] )
in hhsRecord.try_record_proof "NRC_1" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = export_rewrites [ "NRC_1" ]
;
val NRC_ADD_I = store_thm ( "NRC_ADD_I" , ( Parse.Term [ QUOTE " (*#loc 1 118059*)!m n x y z. NRC R m x y /\\ NRC R n y z ==> NRC R (m + n) x z" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN SRW_TAC [ ] [ NRC , ADD ] THEN METIS_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NRC_ADD_I" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", hhsRecord.fetch "NRC" "", ",", hhsRecord.fetch "ADD" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", "]" ] )
in hhsRecord.try_record_proof "NRC_ADD_I" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NRC_ADD_E = store_thm ( "NRC_ADD_E" , ( Parse.Term [ QUOTE " (*#loc 1 118228*)!m n x z. NRC R (m + n) x z ==> ?y. NRC R m x y /\\ NRC R n y z" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN SRW_TAC [ ] [ NRC , ADD ] THEN METIS_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NRC_ADD_E" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", hhsRecord.fetch "NRC" "", ",", hhsRecord.fetch "ADD" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", "]" ] )
in hhsRecord.try_record_proof "NRC_ADD_E" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NRC_ADD_EQN = store_thm ( "NRC_ADD_EQN" , ( Parse.Term [ QUOTE " (*#loc 1 118403*)NRC R (m + n) x z = ?y. NRC R m x y /\\ NRC R n y z" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ NRC_ADD_I , NRC_ADD_E ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NRC_ADD_EQN" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "NRC_ADD_I" "( ( DB.fetch \"arithmetic\" \"NRC_ADD_I\" ) )", 
",", 
hhsRecord.fetch "NRC_ADD_E" "( ( DB.fetch \"arithmetic\" \"NRC_ADD_E\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "NRC_ADD_EQN" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NRC_SUC_RECURSE_LEFT = store_thm ( "NRC_SUC_RECURSE_LEFT" , ( Parse.Term [ QUOTE " (*#loc 1 118562*)NRC R (SUC n) x y = ?z. NRC R n x z /\\ R z y" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ NRC_1 , NRC_ADD_EQN , ADD1 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NRC_SUC_RECURSE_LEFT" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "NRC_1" "( ( DB.fetch \"arithmetic\" \"NRC_1\" ) )", ",", 
hhsRecord.fetch "NRC_ADD_EQN" "( ( DB.fetch \"arithmetic\" \"NRC_ADD_EQN\" ) )", 
",", hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", "]" ] )
in hhsRecord.try_record_proof "NRC_SUC_RECURSE_LEFT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val NRC_RTC = store_thm ( "NRC_RTC" , ( Parse.Term [ QUOTE " (*#loc 1 118693*)!n x y. NRC R n x y ==> RTC R x y" ] ) ,
let
val tactictoe_tac1 = INDUCT_TAC THEN SRW_TAC [ ] [ NRC , relationTheory.RTC_RULES ] THEN METIS_TAC [ relationTheory.RTC_RULES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "NRC_RTC" 
 ( String.concatWith " " 
 [ hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", hhsRecord.fetch "NRC" "", ",", "relationTheory.RTC_RULES", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
"relationTheory.RTC_RULES", "]" ] )
in hhsRecord.try_record_proof "NRC_RTC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val RTC_NRC = store_thm ( "RTC_NRC" , ( Parse.Term [ QUOTE " (*#loc 1 118878*)!x y. RTC R x y ==> ?n. NRC R n x y" ] ) ,
let
val tactictoe_tac1 = HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN PROVE_TAC [ NRC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "RTC_NRC" 
 ( String.concatWith " " 
 [ "boolLib.HO_MATCH_MP_TAC", "relationTheory.RTC_INDUCT", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", hhsRecord.fetch "NRC" "", "]" ] )
in hhsRecord.try_record_proof "RTC_NRC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val RTC_eq_NRC = store_thm ( "RTC_eq_NRC" , ( Parse.Term [ QUOTE " (*#loc 1 119035*)!R x y. RTC R x y = ?n. NRC R n x y" ] ) ,
let
val tactictoe_tac1 = PROVE_TAC [ RTC_NRC , NRC_RTC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "RTC_eq_NRC" 
 ( String.concatWith " " 
 [ "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "RTC_NRC" "( ( DB.fetch \"arithmetic\" \"RTC_NRC\" ) )", ",", 
hhsRecord.fetch "NRC_RTC" "( ( DB.fetch \"arithmetic\" \"NRC_RTC\" ) )", "]" ] )
in hhsRecord.try_record_proof "RTC_eq_NRC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val TC_eq_NRC = store_thm ( "TC_eq_NRC" , ( Parse.Term [ QUOTE " (*#loc 1 119152*)!R x y. TC R x y = ?n. NRC R (SUC n) x y" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ relationTheory.EXTEND_RTC_TC_EQN , RTC_eq_NRC , NRC ] THEN PROVE_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "TC_eq_NRC" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "relationTheory.EXTEND_RTC_TC_EQN", ",", 
hhsRecord.fetch "RTC_eq_NRC" "( ( DB.fetch \"arithmetic\" \"RTC_eq_NRC\" ) )", 
",", hhsRecord.fetch "NRC" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", "]" ] )
in hhsRecord.try_record_proof "TC_eq_NRC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val LESS_EQUAL_DIFF = store_thm ( "LESS_EQUAL_DIFF" , ( Parse.Term [ QUOTE " (*#loc 1 119342*)!m n : num. m <= n ==> ?k. m = n - k" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN SPEC_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 119422*)m:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 119435*)m:num" ] ) ) THEN SPEC_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 119466*)n:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 119479*)n:num" ] ) ) THEN INDUCT_TAC THENL [ REWRITE_TAC [ LESS_EQ_0 , SUB_0 ] , REWRITE_TAC [ LE ] THEN PROVE_TAC [ SUB_0 , SUB_MONO_EQ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "LESS_EQUAL_DIFF" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SPEC_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 119422*)m:num\"", "]", ")", ",", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 119435*)m:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.SPEC_TAC", "(", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 119466*)n:num\"", "]", ")", ",", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 119479*)n:num\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
",", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", "]", 
",", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LE" "( ( DB.fetch \"arithmetic\" \"LE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", hhsRecord.fetch "SUB_0" "( ( DB.fetch \"arithmetic\" \"SUB_0\" ) )", ",", 
hhsRecord.fetch "SUB_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_MONO_EQ\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "LESS_EQUAL_DIFF" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_2 = store_thm ( "MOD_2" , ( Parse.Term [ QUOTE " (*#loc 1 119664*)!n. n MOD 2 = if EVEN n then 0 else 1" ] ) ,
let
val tactictoe_tac1 = GEN_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN ASM_CASES_TAC ( Parse.Term [ QUOTE " (*#loc 1 119774*)EVEN n" ] ) THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [ EVEN_EXISTS , GSYM ODD_EVEN , ODD_EXISTS , ADD1 ] THEN STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 119945*)m" ] THENL [ PROVE_TAC [ MULT_COMM , ADD_0 , TWO , prim_recTheory.LESS_0 ] , ( KNOW_TAC ( Parse.Term [ QUOTE " (*#loc 1 120039*)(?m' : num. 2 * m + 1 = 2 * m') = F" ] ) >>- 1 ?? PROVE_TAC [ EVEN_EXISTS , ODD_EXISTS , ADD1 , EVEN_ODD ] ) THEN DISCH_THEN ( fn th => REWRITE_TAC [ th ] ) THEN PROVE_TAC [ MULT_COMM , ONE , TWO , prim_recTheory.LESS_0 , LESS_MONO_EQ ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_2" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_CASES_TAC", "(", 
"Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 119774*)EVEN n\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", 
"boolLib.MP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "EVEN_EXISTS" "( ( DB.fetch \"arithmetic\" \"EVEN_EXISTS\" ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "ODD_EVEN" "( ( DB.fetch \"arithmetic\" \"ODD_EVEN\" ) )", 
",", 
hhsRecord.fetch "ODD_EXISTS" "( ( DB.fetch \"arithmetic\" \"ODD_EXISTS\" ) )", 
",", hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", 
"boolLib.SUBST1_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.EXISTS_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 119945*)m\"", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
",", hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ",", 
hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", ",", 
"prim_recTheory.LESS_0", "]", ",", "(", "boolLib.KNOW_TAC", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", 
"\" (*#loc 1 120039*)(?m' : num. 2 * m + 1 = 2 * m') = F\"", "]", ")", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "EVEN_EXISTS" "( ( DB.fetch \"arithmetic\" \"EVEN_EXISTS\" ) )", 
",", 
hhsRecord.fetch "ODD_EXISTS" "( ( DB.fetch \"arithmetic\" \"ODD_EXISTS\" ) )", 
",", hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", ",", 
hhsRecord.fetch "EVEN_ODD" "( ( DB.fetch \"arithmetic\" \"EVEN_ODD\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", 
"(", "fn", "th", "=>", "boolLib.REWRITE_TAC", "[", "th", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", ",", 
"prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "MOD_2" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val EVEN_MOD2 = store_thm ( "EVEN_MOD2" , ( Parse.Term [ QUOTE " (*#loc 1 120361*)!x. EVEN x = (x MOD 2 = 0)" ] ) ,
let
val tactictoe_tac1 = PROVE_TAC [ MOD_2 , SUC_NOT , ONE ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EVEN_MOD2" 
 ( String.concatWith " " 
 [ "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "MOD_2" "( ( DB.fetch \"arithmetic\" \"MOD_2\" ) )", ",", 
hhsRecord.fetch "SUC_NOT" "( ( DB.fetch \"arithmetic\" \"SUC_NOT\" ) )", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]" ] )
in hhsRecord.try_record_proof "EVEN_MOD2" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val GSYM_MOD_PLUS' = GSYM ( SPEC_ALL ( UNDISCH_ALL ( SPEC_ALL MOD_PLUS ) ) )
;
;
val MOD_LESS' = UNDISCH ( Q.SPECL [ [ QUOTE " (*#loc 1 120537*)a" ] , [ QUOTE " (*#loc 1 120542*)n" ] ] MOD_LESS )
;
;
val SUC_MOD_lem = Q.prove ( [ QUOTE " (*#loc 1 120589*)0 < n ==> (SUC a MOD n = if SUC (a MOD n) = n then 0 else SUC (a MOD n))" ] ,
let
val tactictoe_tac1 = DISCH_TAC THEN REWRITE_TAC [ SUC_ONE_ADD ] THEN CONV_TAC ( LHS_CONV ( REWR_CONV_A GSYM_MOD_PLUS' ) ) THEN MP_TAC ( Q.SPECL [ [ QUOTE " (*#loc 1 120788*)n" ] , [ QUOTE " (*#loc 1 120793*)1" ] ] LESS_LESS_CASES ) THEN STRIP_TAC THENL [ ASM_REWRITE_TAC [ MOD_1 , ADD_0 ] , RULE_ASSUM_TAC ( REWRITE_RULE [ GSYM LESS_EQ_IFF_LESS_SUC , ONE , LESS_EQ_0 ] ) THEN FULL_SIMP_TAC bool_ss [ NOT_LESS_0 ] , IMP_RES_TAC LESS_MOD THEN ASM_REWRITE_TAC [ ] THEN COND_CASES_TAC >>- 1 ?? ASM_SIMP_TAC bool_ss [ DIVMOD_ID ] THEN irule LESS_MOD THEN ASSUME_TAC MOD_LESS' THEN RULE_ASSUM_TAC ( REWRITE_RULE [ GSYM SUC_ONE_ADD , Once LESS_EQ , Once LESS_OR_EQ ] ) THEN REWRITE_TAC [ GSYM SUC_ONE_ADD ] THEN FIRST_X_ASSUM DISJ_CASES_TAC THEN FULL_SIMP_TAC bool_ss [ NOT_LESS_0 ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_348" 
 ( String.concatWith " " 
 [ "boolLib.DISCH_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "SUC_ONE_ADD" "( ( DB.fetch \"arithmetic\" \"SUC_ONE_ADD\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.CONV_TAC", "(", 
"boolLib.LHS_CONV", "(", "boolLib.REWR_CONV_A", 
hhsRecord.fetch "GSYM_MOD_PLUS'" "( boolLib.GSYM ( boolLib.SPEC_ALL ( boolLib.UNDISCH_ALL ( boolLib.SPEC_ALL ( ( DB.fetch \"arithmetic\" \"MOD_PLUS\" ) ) ) ) ) )", 
")", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MP_TAC", "(", 
"Q.SPECL", "[", "[", "HolKernel.QUOTE", "\" (*#loc 1 120788*)n\"", "]", ",", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 120793*)1\"", "]", "]", 
hhsRecord.fetch "LESS_LESS_CASES" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_CASES\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "MOD_1" "( ( DB.fetch \"arithmetic\" \"MOD_1\" ) )", ",", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", "]", ",", 
"boolLib.RULE_ASSUM_TAC", "(", "boolLib.REWRITE_RULE", "[", "boolLib.GSYM", 
hhsRecord.fetch "LESS_EQ_IFF_LESS_SUC" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_IFF_LESS_SUC\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_0\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.FULL_SIMP_TAC", "BasicProvers.bool_ss", "[", "prim_recTheory.NOT_LESS_0", 
"]", ",", "boolLib.IMP_RES_TAC", 
hhsRecord.fetch "LESS_MOD" "( ( DB.fetch \"arithmetic\" \"LESS_MOD\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.COND_CASES_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "DIVMOD_ID" "( ( DB.fetch \"arithmetic\" \"DIVMOD_ID\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.irule", 
hhsRecord.fetch "LESS_MOD" "( ( DB.fetch \"arithmetic\" \"LESS_MOD\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASSUME_TAC", 
hhsRecord.fetch "MOD_LESS'" "( boolLib.UNDISCH ( Q.SPECL [ [ HolKernel.QUOTE \" (*#loc 1 120537*)a\" ] , [ HolKernel.QUOTE \" (*#loc 1 120542*)n\" ] ] ( ( DB.fetch \"arithmetic\" \"MOD_LESS\" ) ) ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.RULE_ASSUM_TAC", 
"(", "boolLib.REWRITE_RULE", "[", "boolLib.GSYM", 
hhsRecord.fetch "SUC_ONE_ADD" "( ( DB.fetch \"arithmetic\" \"SUC_ONE_ADD\" ) )", 
",", "boolLib.Once", 
hhsRecord.fetch "LESS_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_EQ\" ) )", ",", 
"boolLib.Once", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "SUC_ONE_ADD" "( ( DB.fetch \"arithmetic\" \"SUC_ONE_ADD\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_X_ASSUM", 
"boolLib.DISJ_CASES_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"simpLib.FULL_SIMP_TAC", "BasicProvers.bool_ss", "[", "prim_recTheory.NOT_LESS_0", 
"]", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_348" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUC_MOD = store_thm ( "SUC_MOD" , ( Parse.Term [ QUOTE " (*#loc 1 121426*)!n a b. 0 < n ==> ((SUC a MOD n = SUC b MOD n) = (a MOD n = b MOD n))" ] ) ,
let
val tactictoe_tac1 = ASM_SIMP_TAC bool_ss [ SUC_MOD_lem ] THEN REPEAT STRIP_TAC THEN REVERSE EQ_TAC >>- 1 ?? SIMP_TAC bool_ss [ ] THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC [ numTheory.NOT_SUC , SUC_NOT , INV_SUC_EQ ] THEN ASM_REWRITE_TAC [ Once ( GSYM INV_SUC_EQ ) ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUC_MOD" 
 ( String.concatWith " " 
 [ "simpLib.ASM_SIMP_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "SUC_MOD_lem" "", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REVERSE", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.COND_CASES_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.REWRITE_TAC", "[", "numTheory.NOT_SUC", ",", 
hhsRecord.fetch "SUC_NOT" "( ( DB.fetch \"arithmetic\" \"SUC_NOT\" ) )", ",", 
"prim_recTheory.INV_SUC_EQ", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "boolLib.Once", "(", "boolLib.GSYM", "prim_recTheory.INV_SUC_EQ", ")", "]" ] )
in hhsRecord.try_record_proof "SUC_MOD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ADD_MOD = Q.store_thm ( "ADD_MOD" , [ QUOTE " (*#loc 1 121789*)!n a b p. (0 < n:num) ==>             (((a + p) MOD n = (b + p) MOD n) =              (a MOD n = b MOD n))" ] ,
let
val tactictoe_tac1 = GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN HO_MATCH_MP_TAC INDUCTION THEN SIMP_TAC bool_ss [ ADD_CLAUSES , SUC_MOD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ADD_MOD" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.HO_MATCH_MP_TAC", "numTheory.INDUCTION", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", hhsRecord.fetch "SUC_MOD" "( ( DB.fetch \"arithmetic\" \"SUC_MOD\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "ADD_MOD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_ELIM = Q.store_thm ( "MOD_ELIM" , [ QUOTE " (*#loc 1 122059*)!P x n. 0 < n /\\ P x /\\ (!y. P (y + n) ==> P y) ==> P (x MOD n)" ] ,
let
val tactictoe_tac1 = GEN_TAC THEN HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN REPEAT STRIP_TAC THEN ASM_CASES_TAC ( ( Parse.Term [ QUOTE " (*#loc 1 122224*)x >= n" ] ) ) THENL [ ( Parse.Term [ QUOTE " (*#loc 1 122247*)P ((x - n) MOD n):bool" ] ) via ( Q.PAT_ASSUM [ QUOTE " (*#loc 1 122297*)!x'. A x' ==> !n. Q x' n" ] ( MP_TAC o Q.SPEC [ QUOTE " (*#loc 1 122341*)x-n" ] ) THEN ( Parse.Term [ QUOTE " (*#loc 1 122359*)x-n < x" ] ) via FULL_SIMP_TAC bool_ss [ GREATER_OR_EQ , SUB_RIGHT_LESS , GREATER_DEF ] THEN METIS_TAC [ NOT_ZERO_LT_ZERO , ADD_SYM , LESS_ADD_NONZERO , LESS_TRANS , SUB_ADD , GREATER_OR_EQ , GREATER_DEF , LESS_OR_EQ , SUB_RIGHT_LESS ] ) THEN ( Parse.Term [ QUOTE " (*#loc 1 122620*)?z. x = z + n" ] ) via ( Q.EXISTS_TAC [ QUOTE " (*#loc 1 122656*)x - n" ] THEN METIS_TAC [ SUB_ADD , GREATER_OR_EQ , GREATER_DEF , LESS_OR_EQ ] ) THEN RW_TAC bool_ss [ ] THEN METIS_TAC [ SUB_ADD , GREATER_OR_EQ , GREATER_DEF , LESS_OR_EQ , ADD_MODULUS ] , METIS_TAC [ LESS_MOD , NOT_LESS , LESS_OR_EQ , GREATER_OR_EQ , GREATER_DEF ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_ELIM" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.HO_MATCH_MP_TAC", 
hhsRecord.fetch "COMPLETE_INDUCTION" "( ( DB.fetch \"arithmetic\" \"COMPLETE_INDUCTION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_CASES_TAC", "(", "(", "Parse.Term", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 122224*)x >= n\"", "]", ")", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 122247*)P ((x - n) MOD n):bool\"", "]", ")", 
"hhs_infixl8_open boolLib.via hhs_infixl8_close", "(", "Q.PAT_ASSUM", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 122297*)!x'. A x' ==> !n. Q x' n\"", "]", "(", 
"boolLib.MP_TAC", "o", "Q.SPEC", "[", "HolKernel.QUOTE", "\" (*#loc 1 122341*)x-n\"", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 122359*)x-n < x\"", "]", ")", 
"hhs_infixl8_open boolLib.via hhs_infixl8_close", "simpLib.FULL_SIMP_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "GREATER_OR_EQ" "( ( DB.fetch \"arithmetic\" \"GREATER_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "SUB_RIGHT_LESS" "( ( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_LESS\" ) ) )", 
",", 
hhsRecord.fetch "GREATER_DEF" "( ( DB.fetch \"arithmetic\" \"GREATER_DEF\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
",", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
",", 
hhsRecord.fetch "LESS_ADD_NONZERO" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_NONZERO\" ) )", 
",", 
hhsRecord.fetch "LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_TRANS\" ) )", 
",", hhsRecord.fetch "SUB_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_ADD\" ) )", 
",", 
hhsRecord.fetch "GREATER_OR_EQ" "( ( DB.fetch \"arithmetic\" \"GREATER_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "GREATER_DEF" "( ( DB.fetch \"arithmetic\" \"GREATER_DEF\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "SUB_RIGHT_LESS" "( ( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_LESS\" ) ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 122620*)?z. x = z + n\"", "]", ")", 
"hhs_infixl8_open boolLib.via hhs_infixl8_close", "(", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 122656*)x - n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "SUB_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_ADD\" ) )", ",", 
hhsRecord.fetch "GREATER_OR_EQ" "( ( DB.fetch \"arithmetic\" \"GREATER_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "GREATER_DEF" "( ( DB.fetch \"arithmetic\" \"GREATER_DEF\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.RW_TAC", "BasicProvers.bool_ss", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "SUB_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_ADD\" ) )", ",", 
hhsRecord.fetch "GREATER_OR_EQ" "( ( DB.fetch \"arithmetic\" \"GREATER_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "GREATER_DEF" "( ( DB.fetch \"arithmetic\" \"GREATER_DEF\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "ADD_MODULUS" "( ( DB.fetch \"arithmetic\" \"ADD_MODULUS\" ) )", 
"]", ",", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_MOD" "( ( DB.fetch \"arithmetic\" \"LESS_MOD\" ) )", 
",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "GREATER_OR_EQ" "( ( DB.fetch \"arithmetic\" \"GREATER_OR_EQ\" ) )", 
",", 
hhsRecord.fetch "GREATER_DEF" "( ( DB.fetch \"arithmetic\" \"GREATER_DEF\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "MOD_ELIM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DOUBLE_LT = store_thm ( "DOUBLE_LT" , ( Parse.Term [ QUOTE " (*#loc 1 122964*)!p q. 2 * p + 1 < 2 * q = 2 * p < 2 * q" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN ( EQ_TAC >>- 1 ?? PROVE_TAC [ ADD1 , prim_recTheory.SUC_LESS ] ) THEN STRIP_TAC THEN SIMP_TAC boolSimps.bool_ss [ GSYM ADD1 ] THEN MATCH_MP_TAC LESS_NOT_SUC THEN ASM_REWRITE_TAC [ ] THEN PROVE_TAC [ EVEN_ODD , EVEN_DOUBLE , ODD_DOUBLE ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DOUBLE_LT" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", "boolLib.EQ_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", ",", 
"prim_recTheory.SUC_LESS", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"boolSimps.bool_ss", "[", "boolLib.GSYM", 
hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_NOT_SUC" "( ( DB.fetch \"arithmetic\" \"LESS_NOT_SUC\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "EVEN_ODD" "( ( DB.fetch \"arithmetic\" \"EVEN_ODD\" ) )", 
",", 
hhsRecord.fetch "EVEN_DOUBLE" "( ( DB.fetch \"arithmetic\" \"EVEN_DOUBLE\" ) )", 
",", 
hhsRecord.fetch "ODD_DOUBLE" "( ( DB.fetch \"arithmetic\" \"ODD_DOUBLE\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "DOUBLE_LT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val EXP2_LT = store_thm ( "EXP2_LT" , ( Parse.Term [ QUOTE " (*#loc 1 123315*)!m n. n DIV 2 < 2 ** m = n < 2 ** SUC m" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN MP_TAC ( Q.SPEC [ QUOTE " (*#loc 1 123401*)2" ] DIVISION ) THEN ( KNOW_TAC ( Parse.Term [ QUOTE " (*#loc 1 123435*)0n < 2" ] ) >>- 1 ?? REWRITE_TAC [ TWO , prim_recTheory.LESS_0 ] ) THEN SIMP_TAC boolSimps.bool_ss [ ] THEN STRIP_TAC THEN DISCH_THEN ( MP_TAC o Q.SPEC [ QUOTE " (*#loc 1 123586*)n" ] ) THEN DISCH_THEN ( fn th => CONV_TAC ( RAND_CONV ( ONCE_REWRITE_CONV [ th ] ) ) ) THEN ONCE_REWRITE_TAC [ MULT_COMM ] THEN SIMP_TAC boolSimps.bool_ss [ EXP , MOD_2 ] THEN ( ASM_CASES_TAC ( Parse.Term [ QUOTE " (*#loc 1 123777*)EVEN n" ] ) THEN ASM_SIMP_TAC boolSimps.bool_ss [ ] ) THENL [ REWRITE_TAC [ TWO , ADD_0 , LESS_MULT_MONO ] , REWRITE_TAC [ DOUBLE_LT ] THEN REWRITE_TAC [ TWO , ADD_0 , LESS_MULT_MONO ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "EXP2_LT" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MP_TAC", "(", 
"Q.SPEC", "[", "HolKernel.QUOTE", "\" (*#loc 1 123401*)2\"", "]", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", "boolLib.KNOW_TAC", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 123435*)0n < 2\"", "]", ")", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", ",", 
"prim_recTheory.LESS_0", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"boolSimps.bool_ss", "[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.DISCH_THEN", "(", "boolLib.MP_TAC", "o", "Q.SPEC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 123586*)n\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", "(", 
"fn", "th", "=>", "boolLib.CONV_TAC", "(", "boolLib.RAND_CONV", "(", 
"boolLib.ONCE_REWRITE_CONV", "[", "th", "]", ")", ")", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ONCE_REWRITE_TAC", 
"[", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"boolSimps.bool_ss", "[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MOD_2" "( ( DB.fetch \"arithmetic\" \"MOD_2\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", "boolLib.ASM_CASES_TAC", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 123777*)EVEN n\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"boolSimps.bool_ss", "[", "]", ")", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", ",", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ",", 
hhsRecord.fetch "LESS_MULT_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_MULT_MONO\" ) )", 
"]", ",", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "DOUBLE_LT" "( ( DB.fetch \"arithmetic\" \"DOUBLE_LT\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", ",", 
hhsRecord.fetch "ADD_0" "( ( DB.fetch \"arithmetic\" \"ADD_0\" ) )", ",", 
hhsRecord.fetch "LESS_MULT_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_MULT_MONO\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "EXP2_LT" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_LESS = Q.store_thm ( "SUB_LESS" , [ QUOTE " (*#loc 1 124014*)!m n. 0 < n /\\ n <= m ==> m-n < m" ] ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN ( Parse.Term [ QUOTE " (*#loc 1 124079*)?p. m = p+n" ] ) via METIS_TAC [ LESS_EQ_EXISTS , ADD_SYM ] THEN RW_TAC bool_ss [ ADD_SUB ] THEN METIS_TAC [ LESS_ADD_NONZERO , NOT_ZERO_LT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_LESS" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "(", "Parse.Term", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 124079*)?p. m = p+n\"", "]", ")", 
"hhs_infixl8_open boolLib.via hhs_infixl8_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_EQ_EXISTS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_EXISTS\" ) )", 
",", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.RW_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_SUB" "( ( DB.fetch \"arithmetic\" \"ADD_SUB\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_ADD_NONZERO" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_NONZERO\" ) )", 
",", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_LESS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val SUB_MOD = Q.store_thm ( "SUB_MOD" , [ QUOTE " (*#loc 1 124262*)!m n. 0<n /\\ n <= m ==> ((m-n) MOD n = m MOD n)" ] ,
let
val tactictoe_tac1 = METIS_TAC [ ADD_MODULUS , ADD_SUB , LESS_EQ_EXISTS , ADD_SYM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "SUB_MOD" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "ADD_MODULUS" "( ( DB.fetch \"arithmetic\" \"ADD_MODULUS\" ) )", 
",", hhsRecord.fetch "ADD_SUB" "( ( DB.fetch \"arithmetic\" \"ADD_SUB\" ) )", 
",", 
hhsRecord.fetch "LESS_EQ_EXISTS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_EXISTS\" ) )", 
",", hhsRecord.fetch "ADD_SYM" "( ( DB.fetch \"arithmetic\" \"ADD_SYM\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "SUB_MOD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
fun Cases ( asl , g ) =
let
val ( v , _ ) = dest_forall g
;
in GEN_TAC THEN STRUCT_CASES_TAC ( SPEC v num_CASES )
end ( asl , g )
;
;
fun Cases_on v ( asl , g ) = STRUCT_CASES_TAC ( SPEC v num_CASES ) ( asl , g )
;
;
val ONE_LT_MULT_IMP = Q.store_thm ( "ONE_LT_MULT_IMP" , [ QUOTE " (*#loc 1 124614*)!p q. 1 < p /\\ 0 < q ==> 1 < p * q" ] ,
let
val tactictoe_tac1 = REPEAT Cases THEN RW_TAC bool_ss [ MULT_CLAUSES , ADD_CLAUSES ] THENL [ METIS_TAC [ LESS_REFL ] , POP_ASSUM ( K ALL_TAC ) THEN POP_ASSUM MP_TAC THEN RW_TAC bool_ss [ ONE , LESS_MONO_EQ ] THEN METIS_TAC [ LESS_IMP_LESS_ADD , ADD_ASSOC ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ONE_LT_MULT_IMP" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", 
hhsRecord.fetch "Cases" "let fun Cases ( asl , g ) = ( boolLib.GEN_TAC hhs_infixl0_open boolLib.THEN hhs_infixl0_close boolLib.STRUCT_CASES_TAC ( HolKernel.SPEC let val ( v , _ ) = boolLib.dest_forall g in v end ( ( DB.fetch \"arithmetic\" \"num_CASES\" ) ) ) ) ( asl , g ) in Cases end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.RW_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"metisLib.METIS_TAC", "[", "prim_recTheory.LESS_REFL", "]", ",", "boolLib.POP_ASSUM", 
"(", "HolKernel.K", "boolLib.ALL_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", 
"boolLib.MP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.RW_TAC", "BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_IMP_LESS_ADD" "( ( DB.fetch \"arithmetic\" \"LESS_IMP_LESS_ADD\" ) )", 
",", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "ONE_LT_MULT_IMP" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ONE_LT_MULT = Q.store_thm ( "ONE_LT_MULT" , [ QUOTE " (*#loc 1 124930*)!x y. 1 < x * y = 0 < x /\\ 1 < y \\/ 0 < y /\\ 1 < x" ] ,
let
val tactictoe_tac1 = REWRITE_TAC [ ONE ] THEN INDUCT_TAC THEN RW_TAC bool_ss [ ADD_CLAUSES , MULT_CLAUSES , LESS_REFL , LESS_0 ] THENL [ METIS_TAC [ NOT_SUC_LESS_EQ_0 , LESS_OR_EQ ] , Cases_on ( Parse.Term [ QUOTE " (*#loc 1 125150*)y:num" ] ) THEN RW_TAC bool_ss [ MULT_CLAUSES , ADD_CLAUSES , LESS_REFL , LESS_MONO_EQ , ZERO_LESS_ADD , LESS_0 ] THEN METIS_TAC [ ZERO_LESS_MULT ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ONE_LT_MULT" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.RW_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_REFL", ",", "prim_recTheory.LESS_0", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "metisLib.METIS_TAC", 
"[", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
",", 
hhsRecord.fetch "LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_OR_EQ\" ) )", 
"]", ",", 
hhsRecord.fetch "Cases_on" "let fun Cases_on v ( asl , g ) = boolLib.STRUCT_CASES_TAC ( HolKernel.SPEC v ( ( DB.fetch \"arithmetic\" \"num_CASES\" ) ) ) ( asl , g ) in Cases_on end", 
"(", "Parse.Term", "[", "HolKernel.QUOTE", "\" (*#loc 1 125150*)y:num\"", "]", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.RW_TAC", 
"BasicProvers.bool_ss", "[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", "prim_recTheory.LESS_REFL", ",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_ADD" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_ADD\" ) )", 
",", "prim_recTheory.LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "ZERO_LESS_MULT" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_MULT\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "ONE_LT_MULT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val ONE_LT_EXP = Q.store_thm ( "ONE_LT_EXP" , [ QUOTE " (*#loc 1 125349*)!x y. 1 < x ** y = 1 < x /\\ 0 < y" ] ,
let
val tactictoe_tac1 = GEN_TAC THEN INDUCT_TAC THEN RW_TAC bool_ss [ EXP , ONE_LT_MULT , LESS_REFL , LESS_0 , ZERO_LT_EXP ] THEN METIS_TAC [ SUC_LESS , ONE ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "ONE_LT_EXP" 
 ( String.concatWith " " 
 [ "boolLib.GEN_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.RW_TAC", 
"BasicProvers.bool_ss", "[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "ONE_LT_MULT" "( ( DB.fetch \"arithmetic\" \"ONE_LT_MULT\" ) )", 
",", "prim_recTheory.LESS_REFL", ",", "prim_recTheory.LESS_0", ",", 
hhsRecord.fetch "ZERO_LT_EXP" "( ( DB.fetch \"arithmetic\" \"ZERO_LT_EXP\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
"prim_recTheory.SUC_LESS", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", "]" ] )
in hhsRecord.try_record_proof "ONE_LT_EXP" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val findq_lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 125548*)~(n = 0) /\\ ~(m < 2 * n) ==> m - 2 * n < m - n" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN POP_ASSUM ( ASSUME_TAC o REWRITE_RULE [ NOT_LESS ] ) THEN SRW_TAC [ ] [ SUB_LEFT_LESS , SUB_RIGHT_ADD , SUB_RIGHT_LESS , ADD_CLAUSES , SUB_LEFT_ADD ] THENL [ MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 125844*)n" ] THEN ASM_REWRITE_TAC [ ] THEN SIMP_TAC bool_ss [ Once ( GSYM MULT_LEFT_1 ) , SimpLHS ] THEN REWRITE_TAC [ LT_MULT_RCANCEL ] THEN REWRITE_TAC [ TWO , ONE , LESS_MONO_EQ , prim_recTheory.LESS_0 ] THEN PROVE_TAC [ NOT_ZERO_LT_ZERO ] , Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 126100*)2 * n <= 1 * n" ] MP_TAC >>- 1 ?? PROVE_TAC [ LESS_EQ_TRANS , MULT_LEFT_1 ] THEN ASM_REWRITE_TAC [ LE_MULT_RCANCEL , TWO , ONE , LESS_EQ_MONO , NOT_SUC_LESS_EQ_0 ] , Q_TAC SUFF_TAC [ QUOTE " (*#loc 1 126302*)n < 2 * n" ] >>- 1 ?? PROVE_TAC [ ADD_COMM , LT_ADD_LCANCEL ] THEN Q_TAC SUFF_TAC [ QUOTE " (*#loc 1 126391*)1 * n < 2 * n" ] >>- 1 ?? SRW_TAC [ ] [ MULT_CLAUSES ] THEN SRW_TAC [ ] [ LT_MULT_RCANCEL ] THENL [ PROVE_TAC [ NOT_ZERO_LT_ZERO ] , SRW_TAC [ ] [ ONE , TWO , LESS_MONO_EQ , prim_recTheory.LESS_0 ] ] , PROVE_TAC [ NOT_LESS_EQUAL ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_359" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", 
"boolLib.ASSUME_TAC", "o", "boolLib.REWRITE_RULE", "[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "SUB_LEFT_LESS" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_LESS\" ) )", 
",", 
hhsRecord.fetch "SUB_RIGHT_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_ADD\" ) )", 
",", 
hhsRecord.fetch "SUB_RIGHT_LESS" "( ( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_LESS\" ) ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "SUB_LEFT_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_ADD\" ) )", 
"]", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_EQ_LESS_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_LESS_TRANS\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 125844*)n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", 
"BasicProvers.bool_ss", "[", "boolLib.Once", "(", "boolLib.GSYM", 
hhsRecord.fetch "MULT_LEFT_1" "( ( DB.fetch \"arithmetic\" \"MULT_LEFT_1\" ) )", 
")", ",", "boolSimps.SimpLHS", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", "[", 
hhsRecord.fetch "LT_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_MULT_RCANCEL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", "prim_recTheory.LESS_0", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.PROVE_TAC", 
"[", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]", ",", "Q.SUBGOAL_THEN", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 126100*)2 * n <= 1 * n\"", "]", "boolLib.MP_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_TRANS\" ) )", 
",", 
hhsRecord.fetch "MULT_LEFT_1" "( ( DB.fetch \"arithmetic\" \"MULT_LEFT_1\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", 
hhsRecord.fetch "LE_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_RCANCEL\" ) )", 
",", hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "LESS_EQ_MONO" "( ( DB.fetch \"arithmetic\" \"LESS_EQ_MONO\" ) )", 
",", 
hhsRecord.fetch "NOT_SUC_LESS_EQ_0" "( ( DB.fetch \"arithmetic\" \"NOT_SUC_LESS_EQ_0\" ) )", 
"]", ",", "boolLib.Q_TAC", "boolLib.SUFF_TAC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 126302*)n < 2 * n\"", "]", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
",", 
hhsRecord.fetch "LT_ADD_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_ADD_LCANCEL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.Q_TAC", 
"boolLib.SUFF_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 126391*)1 * n < 2 * n\"", 
"]", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", 
"[", "]", "[", 
hhsRecord.fetch "LT_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_MULT_RCANCEL\" ) )", 
"]", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]", ",", "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", ",", 
hhsRecord.fetch "LESS_MONO_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_MONO_EQ\" ) )", 
",", "prim_recTheory.LESS_0", "]", "]", ",", "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "NOT_LESS_EQUAL" "( ( DB.fetch \"arithmetic\" \"NOT_LESS_EQUAL\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_359" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val findq_thm =
let
open pairTheory relationTheory
;
val M = ( Parse.Term [ QUOTE " (*#loc 1 126691*)\\f (a,m,n). if n = 0 then a                         else let d = 2 * n                              in                                if m < d then a else f (2 * a, m, d)" ] )
;
val measure = ( Parse.Term [ QUOTE " (*#loc 1 126884*)measure (\\ (a:num,m:num,n:num). m - n)" ] )
;
val defn = new_definition ( "findq_def" , ( Parse.Term [ QUOTE " (*#loc 1 126970*)findq = WFREC " , ANTIQUOTE ( measure ) , QUOTE " (*#loc 1 126992*) " , ANTIQUOTE ( M ) , QUOTE " (*#loc 1 126995*)" ] ) )
;
val th0 = MP ( MATCH_MP WFREC_COROLLARY defn ) ( ISPEC ( rand measure ) prim_recTheory.WF_measure )
;
val lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 127139*)~(n = 0) ==> ((let d = 2 * n in if m < d then x                                       else if m - d < m - n then f d else z) =                     (let d = 2 * n in if m < d then x else f d))" ] ) ,
let
val tactictoe_tac1 = LET_ELIM_TAC THEN Q.ASM_CASES_TAC [ QUOTE " (*#loc 1 127374*)m < d" ] THEN ASM_REWRITE_TAC [ ] THEN Q.UNABBREV_TAC [ QUOTE " (*#loc 1 127430*)d" ] THEN SRW_TAC [ ] [ findq_lemma ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_360" 
 ( String.concatWith " " 
 [ "BasicProvers.LET_ELIM_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.ASM_CASES_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 127374*)m < d\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.UNABBREV_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 127430*)d\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", hhsRecord.fetch "findq_lemma" "", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_360" false tactictoe_tac2 tactictoe_tac1
end )
;
in save_thm ( "findq_thm" , SIMP_RULE ( srw_ss ( ) ) [ RESTRICT_DEF , prim_recTheory.measure_thm , lemma ] ( Q.SPEC [ QUOTE " (*#loc 1 127636*)(a,m,n)" ] th0 ) )
end
;
val findq_eq_0 = store_thm ( "findq_eq_0" , ( Parse.Term [ QUOTE " (*#loc 1 127702*)!a m n. (findq (a, m, n) = 0) = (a = 0)" ] ) ,
let
val tactictoe_tac1 = REPEAT GEN_TAC THEN Q_TAC SUFF_TAC [ QUOTE " (*#loc 1 127794*)!x a m n. (x = m - n) ==> ((findq (a, m, n) = 0) = (a = 0))" ] >>- 1 ?? SRW_TAC [ ] [ ] THEN HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [ findq_thm ] THEN SRW_TAC [ ] [ LET_THM ] THEN RULE_ASSUM_TAC ( SIMP_RULE ( bool_ss ++ boolSimps.DNF_ss ) [ ] ) THEN FIRST_X_ASSUM ( Q.SPECL_THEN [ [ QUOTE " (*#loc 1 128111*)2 * a" ] , [ QUOTE " (*#loc 1 128120*)m" ] , [ QUOTE " (*#loc 1 128125*)2 * n" ] ] MP_TAC ) THEN SRW_TAC [ ] [ findq_lemma , MULT_EQ_0 , TWO , ONE , NOT_SUC ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "findq_eq_0" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.GEN_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.Q_TAC", 
"boolLib.SUFF_TAC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 127794*)!x a m n. (x = m - n) ==> ((findq (a, m, n) = 0) = (a = 0))\"", 
"]", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.HO_MATCH_MP_TAC", 
hhsRecord.fetch "COMPLETE_INDUCTION" "( ( DB.fetch \"arithmetic\" \"COMPLETE_INDUCTION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REPEAT", 
"boolLib.STRIP_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "findq_thm" "( ( ( DB.fetch \"arithmetic\" \"findq_thm\" ) ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", 
"[", "]", "[", "boolLib.LET_THM", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.RULE_ASSUM_TAC", 
"(", "simpLib.SIMP_RULE", "(", "BasicProvers.bool_ss", 
"hhs_infixl0_open simpLib.++ hhs_infixl0_close", "boolSimps.DNF_ss", ")", "[", "]", 
")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_X_ASSUM", 
"(", "Q.SPECL_THEN", "[", "[", "HolKernel.QUOTE", "\" (*#loc 1 128111*)2 * a\"", "]", ",", 
"[", "HolKernel.QUOTE", "\" (*#loc 1 128120*)m\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 128125*)2 * n\"", "]", "]", "boolLib.MP_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", hhsRecord.fetch "findq_lemma" "", ",", 
hhsRecord.fetch "MULT_EQ_0" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_0\" ) )", 
",", hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"numTheory.NOT_SUC", "]" ] )
in hhsRecord.try_record_proof "findq_eq_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val findq_divisor = store_thm ( "findq_divisor" , ( Parse.Term [ QUOTE " (*#loc 1 128257*)n <= m ==> findq (a, m, n) * n <= a * m" ] ) ,
let
val tactictoe_tac1 = Q_TAC SUFF_TAC [ QUOTE " (*#loc 1 128327*)!x a m n. (x = m - n) /\\ n <= m ==>                    findq (a, m, n) * n <= a * m" ] >>- 1 ?? SRW_TAC [ ] [ ] THEN HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN SRW_TAC [ boolSimps.DNF_ss ] [ ] THEN ONCE_REWRITE_TAC [ findq_thm ] THEN SRW_TAC [ ] [ LET_THM , MULT_CLAUSES , ZERO_LESS_EQ , LE_MULT_LCANCEL , LESS_IMP_LESS_OR_EQ ] THEN FIRST_X_ASSUM ( Q.SPECL_THEN [ [ QUOTE " (*#loc 1 128694*)2 * a" ] , [ QUOTE " (*#loc 1 128703*)m" ] , [ QUOTE " (*#loc 1 128708*)2 * n" ] ] MP_TAC ) THEN ASM_SIMP_TAC ( srw_ss ( ) ) [ findq_lemma , GSYM NOT_LESS ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 128806*)findq (2 * a,m,2 * n) * (2 * n) =                   2 * (findq (2 * a, m, 2 * n) * n)" ] SUBST_ALL_TAC >>- 1 ?? SRW_TAC [ ] [ AC MULT_COMM MULT_ASSOC ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 128976*)2 * a * m = 2 * (a * m)" ] SUBST_ALL_TAC >>- 1 ?? SRW_TAC [ ] [ AC MULT_COMM MULT_ASSOC ] THEN SRW_TAC [ ] [ LT_MULT_LCANCEL , TWO , ONE , prim_recTheory.LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "findq_divisor" 
 ( String.concatWith " " 
 [ "boolLib.Q_TAC", "boolLib.SUFF_TAC", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 128327*)!x a m n. (x = m - n) /\\\\ n <= m ==>                    findq (a, m, n) * n <= a * m\"", 
"]", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.HO_MATCH_MP_TAC", 
hhsRecord.fetch "COMPLETE_INDUCTION" "( ( DB.fetch \"arithmetic\" \"COMPLETE_INDUCTION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"boolSimps.DNF_ss", "]", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ONCE_REWRITE_TAC", 
"[", 
hhsRecord.fetch "findq_thm" "( ( ( DB.fetch \"arithmetic\" \"findq_thm\" ) ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", 
"[", "]", "[", "boolLib.LET_THM", ",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ZERO_LESS_EQ" "( ( DB.fetch \"arithmetic\" \"ZERO_LESS_EQ\" ) )", 
",", 
hhsRecord.fetch "LE_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_LCANCEL\" ) )", 
",", 
hhsRecord.fetch "LESS_IMP_LESS_OR_EQ" "( ( DB.fetch \"arithmetic\" \"LESS_IMP_LESS_OR_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.FIRST_X_ASSUM", 
"(", "Q.SPECL_THEN", "[", "[", "HolKernel.QUOTE", "\" (*#loc 1 128694*)2 * a\"", "]", ",", 
"[", "HolKernel.QUOTE", "\" (*#loc 1 128703*)m\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 128708*)2 * n\"", "]", "]", "boolLib.MP_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", ")", "[", hhsRecord.fetch "findq_lemma" "", ",", 
"boolLib.GSYM", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", 
"\" (*#loc 1 128806*)findq (2 * a,m,2 * n) * (2 * n) =                   2 * (findq (2 * a, m, 2 * n) * n)\"", 
"]", "boolLib.SUBST_ALL_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", 
"1", "hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "simpLib.AC", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 128976*)2 * a * m = 2 * (a * m)\"", "]", 
"boolLib.SUBST_ALL_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", "simpLib.AC", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", 
"[", "]", "[", 
hhsRecord.fetch "LT_MULT_LCANCEL" "( ( DB.fetch \"arithmetic\" \"LT_MULT_LCANCEL\" ) )", 
",", hhsRecord.fetch "TWO" "( ( DB.fetch \"arithmetic\" \"TWO\" ) )", ",", 
hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "findq_divisor" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val divmod_lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 129162*)~(n = 0) /\\ ~(m < n) ==> m - n * findq (1, m, n) < m" ] ) ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ NOT_LESS , SUB_RIGHT_LESS , NOT_ZERO_LT_ZERO ] THENL [ ONCE_REWRITE_TAC [ ADD_COMM ] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN SRW_TAC [ ] [ MULT_EQ_0 , ONE , NOT_SUC , findq_eq_0 ] THEN SRW_TAC [ ] [ NOT_ZERO_LT_ZERO ] , PROVE_TAC [ LESS_LESS_EQ_TRANS ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_363" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "SUB_RIGHT_LESS" "( ( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_LESS\" ) ) )", 
",", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_ADD_NONZERO" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_NONZERO\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", 
hhsRecord.fetch "MULT_EQ_0" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_0\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"numTheory.NOT_SUC", ",", 
hhsRecord.fetch "findq_eq_0" "( ( DB.fetch \"arithmetic\" \"findq_eq_0\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", 
"[", "]", "[", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]", ",", "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "LESS_LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_EQ_TRANS\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_363" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIVMOD_THM =
let
open relationTheory pairTheory
;
val M = ( Parse.Term [ QUOTE " (*#loc 1 129561*)\\f (a,m,n). if n = 0 then (0,0)                         else if m < n then (a, m)                         else let q = findq (1, m, n)                              in                                f (a + q, m - n * q, n)" ] )
;
val measure = ( Parse.Term [ QUOTE " (*#loc 1 129805*)measure ((FST o SND) : num#num#num -> num)" ] )
;
val defn = new_definition ( "DIVMOD_DEF" , ( Parse.Term [ QUOTE " (*#loc 1 129896*)DIVMOD = WFREC " , ANTIQUOTE ( measure ) , QUOTE " (*#loc 1 129919*) " , ANTIQUOTE ( M ) , QUOTE " (*#loc 1 129922*)" ] ) )
;
val th0 = REWRITE_RULE [ prim_recTheory.WF_measure ] ( MATCH_MP WFREC_COROLLARY defn )
;
val th1 = SIMP_RULE ( srw_ss ( ) ) [ RESTRICT_DEF , prim_recTheory.measure_thm ] ( Q.SPEC [ QUOTE " (*#loc 1 130144*)(a,m,n)" ] th0 )
;
val lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 130186*)~(n = 0) /\\ ~(m < n) ==>       ((let q = findq (1,m,n) in if m - n * q < m then f q else z) =        (let q = findq (1,m,n) in f q))" ] ) ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ LET_THM , divmod_lemma ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_364" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", "boolLib.LET_THM", ",", 
hhsRecord.fetch "divmod_lemma" "", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_364" false tactictoe_tac2 tactictoe_tac1
end )
;
in save_thm ( "DIVMOD_THM" , SIMP_RULE ( srw_ss ( ) ) [ lemma ] th1 )
end
;
val core_divmod_sub_lemma = prove ( ( Parse.Term [ QUOTE " (*#loc 1 130472*)0 < n /\\ n * q <= m ==>     (m - n * q = if m < (q + 1) * n then m MOD n                  else m DIV n * n + m MOD n - q * n)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [ ASM_SIMP_TAC ( srw_ss ( ) ) [ SUB_RIGHT_EQ ] THEN DISJ1_TAC THEN Q_TAC SUFF_TAC [ QUOTE " (*#loc 1 130732*)m DIV n = q" ] >>- 1 ?? PROVE_TAC [ DIVISION , MULT_COMM ] THEN MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 130839*)m - n * q" ] THEN SRW_TAC [ ] [ SUB_LEFT_ADD ] THENL [ PROVE_TAC [ LESS_EQUAL_ANTISYM , MULT_COMM ] , METIS_TAC [ ADD_COMM , MULT_COMM , ADD_SUB ] , SRW_TAC [ ] [ SUB_RIGHT_LESS ] THEN FULL_SIMP_TAC ( srw_ss ( ) ) [ RIGHT_ADD_DISTRIB , MULT_CLAUSES , AC MULT_COMM MULT_ASSOC , AC ADD_COMM ADD_ASSOC ] ] , ASM_SIMP_TAC ( srw_ss ( ) ) [ GSYM DIVISION ] THEN SIMP_TAC ( srw_ss ( ) ) [ AC MULT_COMM MULT_ASSOC ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "tactictoe_prove_365" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.COND_CASES_TAC", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "simpLib.ASM_SIMP_TAC", 
"(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "SUB_RIGHT_EQ" "( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_EQ\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISJ1_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.Q_TAC", 
"boolLib.SUFF_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 130732*)m DIV n = q\"", 
"]", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
",", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIV_UNIQUE" "( ( DB.fetch \"arithmetic\" \"DIV_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 130839*)m - n * q\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", 
hhsRecord.fetch "SUB_LEFT_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_ADD\" ) )", 
"]", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )", 
",", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", ",", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
",", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
",", hhsRecord.fetch "ADD_SUB" "( ( DB.fetch \"arithmetic\" \"ADD_SUB\" ) )", 
"]", ",", "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "SUB_RIGHT_LESS" "( ( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_LESS\" ) ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.FULL_SIMP_TAC", 
"(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", "simpLib.AC", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
",", "simpLib.AC", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "]", ",", "simpLib.ASM_SIMP_TAC", "(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
"boolLib.GSYM", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", ")", "[", "simpLib.AC", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "tactictoe_prove_365" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MOD_SUB = store_thm ( "MOD_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 131357*)0 < n /\\ n * q <= m ==> ((m - n * q) MOD n = m MOD n)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 131484*)m DIV n - q" ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 131520*)~(n = 0)" ] ASSUME_TAC >>- 1 ?? SRW_TAC [ ] [ NOT_ZERO_LT_ZERO ] THEN ASM_SIMP_TAC ( srw_ss ( ) ) [ RIGHT_SUB_DISTRIB , DIVISION , SUB_RIGHT_ADD , LE_MULT_RCANCEL , DIV_LE_X , core_divmod_sub_lemma ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MOD_SUB" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 131484*)m DIV n - q\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 131520*)~(n = 0)\"", "]", "boolLib.ASSUME_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "RIGHT_SUB_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_SUB_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
",", 
hhsRecord.fetch "SUB_RIGHT_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_ADD\" ) )", 
",", 
hhsRecord.fetch "LE_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_RCANCEL\" ) )", 
",", 
hhsRecord.fetch "DIV_LE_X" "( ( DB.fetch \"arithmetic\" \"DIV_LE_X\" ) )", 
",", hhsRecord.fetch "core_divmod_sub_lemma" "", "]" ] )
in hhsRecord.try_record_proof "MOD_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIV_SUB = store_thm ( "DIV_SUB" , ( Parse.Term [ QUOTE " (*#loc 1 131772*)0 < n /\\ n * q <= m ==> ((m - n * q) DIV n = m DIV n - q)" ] ) ,
let
val tactictoe_tac1 = REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 131903*)m MOD n" ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 131935*)~(n = 0)" ] ASSUME_TAC >>- 1 ?? SRW_TAC [ ] [ NOT_ZERO_LT_ZERO ] THEN ASM_SIMP_TAC ( srw_ss ( ) ) [ DIVISION , RIGHT_SUB_DISTRIB , SUB_RIGHT_ADD , LE_MULT_RCANCEL , DIV_LE_X , core_divmod_sub_lemma ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIV_SUB" 
 ( String.concatWith " " 
 [ "boolLib.REPEAT", "boolLib.STRIP_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "DIV_UNIQUE" "( ( DB.fetch \"arithmetic\" \"DIV_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 131903*)m MOD n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 131935*)~(n = 0)\"", "]", "boolLib.ASSUME_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
",", 
hhsRecord.fetch "RIGHT_SUB_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_SUB_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "SUB_RIGHT_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_ADD\" ) )", 
",", 
hhsRecord.fetch "LE_MULT_RCANCEL" "( ( DB.fetch \"arithmetic\" \"LE_MULT_RCANCEL\" ) )", 
",", 
hhsRecord.fetch "DIV_LE_X" "( ( DB.fetch \"arithmetic\" \"DIV_LE_X\" ) )", 
",", hhsRecord.fetch "core_divmod_sub_lemma" "", "]" ] )
in hhsRecord.try_record_proof "DIV_SUB" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIVMOD_CORRECT = Q.store_thm ( "DIVMOD_CORRECT" , [ QUOTE " (*#loc 1 132201*)!m n a. 0<n ==> (DIVMOD (a,m,n) = (a + (m DIV n), m MOD n))" ] ,
let
val tactictoe_tac1 = HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN SRW_TAC [ DNF_ss ] [ AND_IMP_INTRO ] THEN PURE_ONCE_REWRITE_TAC [ DIVMOD_THM ] THEN RW_TAC bool_ss [ ] THENL [ METIS_TAC [ LESS_REFL ] , METIS_TAC [ LESS_REFL ] , METIS_TAC [ LESS_DIV_EQ_ZERO , ADD_CLAUSES ] , METIS_TAC [ LESS_MOD , ADD_CLAUSES ] , FIRST_X_ASSUM ( Q.SPECL_THEN [ [ QUOTE " (*#loc 1 132586*)m - n * q" ] , [ QUOTE " (*#loc 1 132599*)n" ] , [ QUOTE " (*#loc 1 132604*)a + q" ] ] MP_TAC ) THEN ASM_SIMP_TAC ( srw_ss ( ) ) [ SUB_RIGHT_LESS ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 132695*)m < n * q + m" ] ASSUME_TAC THENL [ SIMP_TAC bool_ss [ SimpRHS , Once ADD_COMM ] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN SRW_TAC [ ] [ MULT_EQ_0 , Abbr [ QUOTE " (*#loc 1 132856*)q" ] , findq_eq_0 , ONE , NOT_SUC ] , ALL_TAC ] THEN ASM_REWRITE_TAC [ ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 132956*)0 < m" ] ASSUME_TAC >>- 1 ?? PROVE_TAC [ NOT_LESS , LESS_LESS_EQ_TRANS ] THEN ASM_REWRITE_TAC [ ] THEN DISCH_THEN SUBST_ALL_TAC THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 133114*)n * q <= m" ] ASSUME_TAC >>- 1 ?? METIS_TAC [ findq_divisor , NOT_LESS , MULT_LEFT_1 , MULT_COMM ] THEN Q.SUBGOAL_THEN [ QUOTE " (*#loc 1 133234*)q <= m DIV n" ] ASSUME_TAC >>- 1 ?? SRW_TAC [ ] [ X_LE_DIV , MULT_COMM ] THEN SRW_TAC [ ] [ ] THENL [ ONCE_REWRITE_TAC [ GSYM ADD_ASSOC ] THEN REWRITE_TAC [ EQ_ADD_LCANCEL ] THEN ASM_SIMP_TAC ( srw_ss ( ) ) [ DIV_SUB ] THEN SRW_TAC [ ] [ SUB_LEFT_ADD ] >>- 1 ?? METIS_TAC [ LESS_EQUAL_ANTISYM ] THEN METIS_TAC [ ADD_SUB , ADD_COMM ] , ASM_SIMP_TAC ( srw_ss ( ) ) [ MOD_SUB ] ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIVMOD_CORRECT" 
 ( String.concatWith " " 
 [ "boolLib.HO_MATCH_MP_TAC", 
hhsRecord.fetch "COMPLETE_INDUCTION" "( ( DB.fetch \"arithmetic\" \"COMPLETE_INDUCTION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"boolSimps.DNF_ss", "]", "[", "boolLib.AND_IMP_INTRO", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.PURE_ONCE_REWRITE_TAC", "[", 
hhsRecord.fetch "DIVMOD_THM" "( ( ( DB.fetch \"arithmetic\" \"DIVMOD_THM\" ) ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.RW_TAC", 
"BasicProvers.bool_ss", "[", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "metisLib.METIS_TAC", 
"[", "prim_recTheory.LESS_REFL", "]", ",", "metisLib.METIS_TAC", "[", 
"prim_recTheory.LESS_REFL", "]", ",", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_DIV_EQ_ZERO" "( ( DB.fetch \"arithmetic\" \"LESS_DIV_EQ_ZERO\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_MOD" "( ( DB.fetch \"arithmetic\" \"LESS_MOD\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]", ",", "boolLib.FIRST_X_ASSUM", "(", "Q.SPECL_THEN", "[", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 132586*)m - n * q\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 132599*)n\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 132604*)a + q\"", "]", "]", "boolLib.MP_TAC", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "SUB_RIGHT_LESS" "( ( ( DB.fetch \"arithmetic\" \"SUB_RIGHT_LESS\" ) ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 132695*)m < n * q + m\"", "]", 
"boolLib.ASSUME_TAC", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"simpLib.SIMP_TAC", "BasicProvers.bool_ss", "[", "boolSimps.SimpRHS", ",", 
"boolLib.Once", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "LESS_ADD_NONZERO" "( ( DB.fetch \"arithmetic\" \"LESS_ADD_NONZERO\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", 
hhsRecord.fetch "MULT_EQ_0" "( ( DB.fetch \"arithmetic\" \"MULT_EQ_0\" ) )", 
",", "BasicProvers.Abbr", "[", "HolKernel.QUOTE", "\" (*#loc 1 132856*)q\"", "]", ",", 
hhsRecord.fetch "findq_eq_0" "( ( DB.fetch \"arithmetic\" \"findq_eq_0\" ) )", 
",", hhsRecord.fetch "ONE" "( ( DB.fetch \"arithmetic\" \"ONE\" ) )", ",", 
"numTheory.NOT_SUC", "]", ",", "boolLib.ALL_TAC", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.ASM_REWRITE_TAC", 
"[", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 132956*)0 < m\"", "]", "boolLib.ASSUME_TAC", 
"hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.PROVE_TAC", "[", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "LESS_LESS_EQ_TRANS" "( ( DB.fetch \"arithmetic\" \"LESS_LESS_EQ_TRANS\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.ASM_REWRITE_TAC", "[", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.DISCH_THEN", 
"boolLib.SUBST_ALL_TAC", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"Q.SUBGOAL_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 133114*)n * q <= m\"", "]", 
"boolLib.ASSUME_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "findq_divisor" "( ( DB.fetch \"arithmetic\" \"findq_divisor\" ) )", 
",", 
hhsRecord.fetch "NOT_LESS" "( ( DB.fetch \"arithmetic\" \"NOT_LESS\" ) )", 
",", 
hhsRecord.fetch "MULT_LEFT_1" "( ( DB.fetch \"arithmetic\" \"MULT_LEFT_1\" ) )", 
",", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SUBGOAL_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 133234*)q <= m DIV n\"", "]", 
"boolLib.ASSUME_TAC", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", 
hhsRecord.fetch "X_LE_DIV" "( ( DB.fetch \"arithmetic\" \"X_LE_DIV\" ) )", 
",", 
hhsRecord.fetch "MULT_COMM" "( ( DB.fetch \"arithmetic\" \"MULT_COMM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", 
"[", "]", "[", "]", "hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", 
"boolLib.ONCE_REWRITE_TAC", "[", "boolLib.GSYM", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.REWRITE_TAC", 
"[", 
hhsRecord.fetch "EQ_ADD_LCANCEL" "( ( DB.fetch \"arithmetic\" \"EQ_ADD_LCANCEL\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.ASM_SIMP_TAC", 
"(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "DIV_SUB" "( ( DB.fetch \"arithmetic\" \"DIV_SUB\" ) )", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", 
hhsRecord.fetch "SUB_LEFT_ADD" "( ( DB.fetch \"arithmetic\" \"SUB_LEFT_ADD\" ) )", 
"]", "hhs_infixl0_open boolLib.>>- hhs_infixl0_close", "1", 
"hhs_infixl0_open boolLib.?? hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "LESS_EQUAL_ANTISYM" "( ( DB.fetch \"arithmetic\" \"LESS_EQUAL_ANTISYM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "ADD_SUB" "( ( DB.fetch \"arithmetic\" \"ADD_SUB\" ) )", ",", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
"]", ",", "simpLib.ASM_SIMP_TAC", "(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "MOD_SUB" "( ( DB.fetch \"arithmetic\" \"MOD_SUB\" ) )", "]", 
"]", "]" ] )
in hhsRecord.try_record_proof "DIVMOD_CORRECT" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val DIVMOD_CALC = Q.store_thm ( "DIVMOD_CALC" , [ QUOTE " (*#loc 1 133676*)(!m n. 0<n ==> (m DIV n = FST(DIVMOD(0, m, n)))) /\\   (!m n. 0<n ==> (m MOD n = SND(DIVMOD(0, m, n))))" ] ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ DIVMOD_CORRECT , ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "DIVMOD_CALC" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "DIVMOD_CORRECT" "( ( DB.fetch \"arithmetic\" \"DIVMOD_CORRECT\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "DIVMOD_CALC" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_DEF = new_definition ( "MODEQ_DEF" , ( Parse.Term [ QUOTE " (*#loc 1 133876*)MODEQ n m1 m2 = ?a b. a * n + m1 = b * n + m2" ] ) )
;
;
val MODEQ_0_CONG = store_thm ( "MODEQ_0_CONG" , ( Parse.Term [ QUOTE " (*#loc 1 133978*)MODEQ 0 m1 m2 <=> (m1 = m2)" ] ) ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ MODEQ_DEF , MULT_CLAUSES , ADD_CLAUSES ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_0_CONG" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "MODEQ_DEF" "( ( DB.fetch \"arithmetic\" \"MODEQ_DEF\" ) )", 
",", 
hhsRecord.fetch "MULT_CLAUSES" "( ( DB.fetch \"arithmetic\" \"MULT_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MODEQ_0_CONG" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_NONZERO_MODEQUALITY = store_thm ( "MODEQ_NONZERO_MODEQUALITY" , ( Parse.Term [ QUOTE " (*#loc 1 134140*)0 < n ==> (MODEQ n m1 m2 <=> (m1 MOD n = m2 MOD n))" ] ) ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ MODEQ_DEF ] THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 134240*)n" ] ( fn th => th |> UNDISCH |> ASSUME_TAC ) DIVISION THEN POP_ASSUM ( fn th => Q.SPEC_THEN [ QUOTE " (*#loc 1 134331*)m1" ] STRIP_ASSUME_TAC th THEN Q.SPEC_THEN [ QUOTE " (*#loc 1 134395*)m2" ] STRIP_ASSUME_TAC th ) THEN MAP_EVERY Q.ABBREV_TAC [ [ QUOTE " (*#loc 1 134452*)q1 = m1 DIV n" ] , [ QUOTE " (*#loc 1 134469*)r1 = m1 MOD n" ] , [ QUOTE " (*#loc 1 134512*)q2 = m2 DIV n" ] , [ QUOTE " (*#loc 1 134529*)r2 = m2 MOD n" ] ] THEN markerLib.RM_ALL_ABBREVS_TAC THEN SRW_TAC [ ] [ EQ_IMP_THM ] THENL [ [ QUOTE " (*#loc 1 134622*)(a * n + (q1 * n + r1)) MOD n = r1" ] by ( MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 134712*)a + q1" ] THEN SIMP_TAC ( srw_ss ( ) ) [ MULT_ASSOC , RIGHT_ADD_DISTRIB , ADD_ASSOC ] THEN SRW_TAC [ ] [ ] ) THEN POP_ASSUM ( SUBST1_TAC o SYM ) THEN MATCH_MP_TAC MOD_UNIQUE THEN Q.EXISTS_TAC [ QUOTE " (*#loc 1 134919*)b + q2" ] THEN SRW_TAC [ ] [ ADD_ASSOC , RIGHT_ADD_DISTRIB ] , MAP_EVERY Q.EXISTS_TAC [ [ QUOTE " (*#loc 1 135007*)q2" ] , [ QUOTE " (*#loc 1 135013*)q1" ] ] THEN SRW_TAC [ ] [ AC ADD_ASSOC ADD_COMM ] ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_NONZERO_MODEQUALITY" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "MODEQ_DEF" "( ( DB.fetch \"arithmetic\" \"MODEQ_DEF\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 134240*)n\"", "]", "(", "fn", "th", "=>", "th", 
"hhs_infixl0_open HolKernel.|> hhs_infixl0_close", "boolLib.UNDISCH", 
"hhs_infixl0_open HolKernel.|> hhs_infixl0_close", "boolLib.ASSUME_TAC", ")", 
hhsRecord.fetch "DIVISION" "( ( DB.fetch \"arithmetic\" \"DIVISION\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.POP_ASSUM", "(", "fn", 
"th", "=>", "Q.SPEC_THEN", "[", "HolKernel.QUOTE", "\" (*#loc 1 134331*)m1\"", "]", 
"boolLib.STRIP_ASSUME_TAC", "th", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.SPEC_THEN", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 134395*)m2\"", "]", "boolLib.STRIP_ASSUME_TAC", 
"th", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MAP_EVERY", 
"Q.ABBREV_TAC", "[", "[", "HolKernel.QUOTE", "\" (*#loc 1 134452*)q1 = m1 DIV n\"", 
"]", ",", "[", "HolKernel.QUOTE", "\" (*#loc 1 134469*)r1 = m1 MOD n\"", "]", ",", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 134512*)q2 = m2 DIV n\"", "]", ",", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 134529*)r2 = m2 MOD n\"", "]", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"markerLib.RM_ALL_ABBREVS_TAC", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "boolLib.EQ_IMP_THM", "]", 
"hhs_infixl0_open boolLib.THENL hhs_infixl0_close", "[", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 134622*)(a * n + (q1 * n + r1)) MOD n = r1\"", "]", 
"hhs_infixl8_open BasicProvers.by hhs_infixl8_close", "(", 
"boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 134712*)a + q1\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "MULT_ASSOC" "( ( DB.fetch \"arithmetic\" \"MULT_ASSOC\" ) )", 
",", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
",", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", 
"[", "]", "[", "]", ")", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"boolLib.POP_ASSUM", "(", "boolLib.SUBST1_TAC", "o", "HolKernel.SYM", ")", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "boolLib.MATCH_MP_TAC", 
hhsRecord.fetch "MOD_UNIQUE" "( ( DB.fetch \"arithmetic\" \"MOD_UNIQUE\" ) )", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "Q.EXISTS_TAC", "[", 
"HolKernel.QUOTE", "\" (*#loc 1 134919*)b + q2\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
",", 
hhsRecord.fetch "RIGHT_ADD_DISTRIB" "( ( DB.fetch \"arithmetic\" \"RIGHT_ADD_DISTRIB\" ) )", 
"]", ",", "boolLib.MAP_EVERY", "Q.EXISTS_TAC", "[", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 135007*)q2\"", "]", ",", "[", "HolKernel.QUOTE", 
"\" (*#loc 1 135013*)q1\"", "]", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "simpLib.AC", 
hhsRecord.fetch "ADD_ASSOC" "( ( DB.fetch \"arithmetic\" \"ADD_ASSOC\" ) )", 
hhsRecord.fetch "ADD_COMM" "( ( DB.fetch \"arithmetic\" \"ADD_COMM\" ) )", 
"]", "]" ] )
in hhsRecord.try_record_proof "MODEQ_NONZERO_MODEQUALITY" true tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_THM = store_thm ( "MODEQ_THM" , ( Parse.Term [ QUOTE " (*#loc 1 135112*)MODEQ n m1 m2 <=> (n = 0) /\\ (m1 = m2) \\/ 0 < n /\\ (m1 MOD n = m2 MOD n)" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ MODEQ_0_CONG , MODEQ_NONZERO_MODEQUALITY , NOT_ZERO_LT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_THM" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "MODEQ_0_CONG" "( ( DB.fetch \"arithmetic\" \"MODEQ_0_CONG\" ) )", 
",", 
hhsRecord.fetch "MODEQ_NONZERO_MODEQUALITY" "( ( DB.fetch \"arithmetic\" \"MODEQ_NONZERO_MODEQUALITY\" ) )", 
",", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MODEQ_THM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_INTRO_CONG = store_thm ( "MODEQ_INTRO_CONG" , ( Parse.Term [ QUOTE " (*#loc 1 135322*)0 < n ==> MODEQ n e0 e1 ==> (e0 MOD n = e1 MOD n)" ] ) ,
let
val tactictoe_tac1 = METIS_TAC [ MODEQ_NONZERO_MODEQUALITY ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_INTRO_CONG" 
 ( String.concatWith " " 
 [ "metisLib.METIS_TAC", "[", 
hhsRecord.fetch "MODEQ_NONZERO_MODEQUALITY" "( ( DB.fetch \"arithmetic\" \"MODEQ_NONZERO_MODEQUALITY\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MODEQ_INTRO_CONG" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_PLUS_CONG = store_thm ( "MODEQ_PLUS_CONG" , ( Parse.Term [ QUOTE " (*#loc 1 135475*)MODEQ n x0 x1 ==> MODEQ n y0 y1 ==> MODEQ n (x0 + y0) (x1 + y1)" ] ) ,
let
val tactictoe_tac1 = Q.ID_SPEC_TAC [ QUOTE " (*#loc 1 135560*)n" ] THEN SIMP_TAC ( srw_ss ( ) ++ DNF_ss ) [ MODEQ_THM , LESS_REFL ] THEN SRW_TAC [ ] [ Once ( GSYM MOD_PLUS ) ] THEN SRW_TAC [ ] [ MOD_PLUS ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_PLUS_CONG" 
 ( String.concatWith " " 
 [ "Q.ID_SPEC_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 135560*)n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", "hhs_infixl0_open simpLib.++ hhs_infixl0_close", 
"boolSimps.DNF_ss", ")", "[", 
hhsRecord.fetch "MODEQ_THM" "( ( DB.fetch \"arithmetic\" \"MODEQ_THM\" ) )", 
",", "prim_recTheory.LESS_REFL", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "boolLib.Once", "(", "boolLib.GSYM", 
hhsRecord.fetch "MOD_PLUS" "( ( DB.fetch \"arithmetic\" \"MOD_PLUS\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "MOD_PLUS" "( ( DB.fetch \"arithmetic\" \"MOD_PLUS\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MODEQ_PLUS_CONG" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_MULT_CONG = store_thm ( "MODEQ_MULT_CONG" , ( Parse.Term [ QUOTE " (*#loc 1 135745*)MODEQ n x0 x1 ==> MODEQ n y0 y1 ==> MODEQ n (x0 * y0) (x1 * y1)" ] ) ,
let
val tactictoe_tac1 = Q.ID_SPEC_TAC [ QUOTE " (*#loc 1 135830*)n" ] THEN SIMP_TAC ( srw_ss ( ) ++ DNF_ss ) [ MODEQ_THM , LESS_REFL ] THEN SRW_TAC [ ] [ Once ( GSYM MOD_TIMES2 ) ] THEN SRW_TAC [ ] [ MOD_TIMES2 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_MULT_CONG" 
 ( String.concatWith " " 
 [ "Q.ID_SPEC_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 135830*)n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", "hhs_infixl0_open simpLib.++ hhs_infixl0_close", 
"boolSimps.DNF_ss", ")", "[", 
hhsRecord.fetch "MODEQ_THM" "( ( DB.fetch \"arithmetic\" \"MODEQ_THM\" ) )", 
",", "prim_recTheory.LESS_REFL", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", 
"]", "[", "boolLib.Once", "(", "boolLib.GSYM", 
hhsRecord.fetch "MOD_TIMES2" "( ( DB.fetch \"arithmetic\" \"MOD_TIMES2\" ) )", 
")", "]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", 
"BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "MOD_TIMES2" "( ( DB.fetch \"arithmetic\" \"MOD_TIMES2\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MODEQ_MULT_CONG" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_REFL = store_thm ( "MODEQ_REFL" , ( Parse.Term [ QUOTE " (*#loc 1 136009*)!x. MODEQ n x x" ] ) ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ MODEQ_THM , GSYM NOT_ZERO_LT_ZERO ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_REFL" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "MODEQ_THM" "( ( DB.fetch \"arithmetic\" \"MODEQ_THM\" ) )", 
",", "boolLib.GSYM", 
hhsRecord.fetch "NOT_ZERO_LT_ZERO" "( ( DB.fetch \"arithmetic\" \"NOT_ZERO_LT_ZERO\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MODEQ_REFL" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_SUC_CONG = store_thm ( "MODEQ_SUC_CONG" , ( Parse.Term [ QUOTE " (*#loc 1 136132*)MODEQ n x y ==> MODEQ n (SUC x) (SUC y)" ] ) ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ ADD1 ] >> irule MODEQ_PLUS_CONG >> SRW_TAC [ ] [ MODEQ_REFL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_SUC_CONG" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "ADD1" "( ( DB.fetch \"arithmetic\" \"ADD1\" ) )", "]", 
"hhs_infixl0_open boolLib.>> hhs_infixl0_close", "boolLib.irule", 
hhsRecord.fetch "MODEQ_PLUS_CONG" "( ( DB.fetch \"arithmetic\" \"MODEQ_PLUS_CONG\" ) )", 
"hhs_infixl0_open boolLib.>> hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", 
hhsRecord.fetch "MODEQ_REFL" "( ( DB.fetch \"arithmetic\" \"MODEQ_REFL\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MODEQ_SUC_CONG" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_EXP_CONG = store_thm ( "MODEQ_EXP_CONG" , ( Parse.Term [ QUOTE " (*#loc 1 136304*)MODEQ n x y ==> MODEQ n (x EXP e) (y EXP e)" ] ) ,
let
val tactictoe_tac1 = Q.ID_SPEC_TAC [ QUOTE " (*#loc 1 136369*)e" ] >> INDUCT_TAC >> SRW_TAC [ ] [ EXP , MODEQ_REFL ] >> irule MODEQ_MULT_CONG >> SRW_TAC [ ] [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_EXP_CONG" 
 ( String.concatWith " " 
 [ "Q.ID_SPEC_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 136369*)e\"", "]", 
"hhs_infixl0_open boolLib.>> hhs_infixl0_close", 
hhsRecord.fetch "INDUCT_TAC" "let fun INDUCT_TAC g = Prim_rec.INDUCT_THEN numTheory.INDUCTION boolLib.ASSUME_TAC g in INDUCT_TAC end", 
"hhs_infixl0_open boolLib.>> hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", hhsRecord.fetch "EXP" "", ",", 
hhsRecord.fetch "MODEQ_REFL" "( ( DB.fetch \"arithmetic\" \"MODEQ_REFL\" ) )", 
"]", "hhs_infixl0_open boolLib.>> hhs_infixl0_close", "boolLib.irule", 
hhsRecord.fetch "MODEQ_MULT_CONG" "( ( DB.fetch \"arithmetic\" \"MODEQ_MULT_CONG\" ) )", 
"hhs_infixl0_open boolLib.>> hhs_infixl0_close", "BasicProvers.SRW_TAC", "[", "]", 
"[", "]" ] )
in hhsRecord.try_record_proof "MODEQ_EXP_CONG" false tactictoe_tac2 tactictoe_tac1
end )
;
val EXP_MOD = save_thm ( "EXP_MOD" , MODEQ_EXP_CONG |> SIMP_RULE bool_ss [ GSYM NOT_LT_ZERO_EQ_ZERO , ASSUME ( Parse.Term [ QUOTE " (*#loc 1 136612*)0 < n" ] ) , MODEQ_THM ] |> INST [ ( Parse.Term [ QUOTE " (*#loc 1 136662*)y:num" ] ) |-> ( Parse.Term [ QUOTE " (*#loc 1 136678*)x MOD n" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 136693*)e1:num" ] ) |-> ( Parse.Term [ QUOTE " (*#loc 1 136710*)e:num" ] ) , ( Parse.Term [ QUOTE " (*#loc 1 136749*)e2:num" ] ) |-> ( Parse.Term [ QUOTE " (*#loc 1 136766*)e:num" ] ) ] |> SIMP_RULE bool_ss [ MATCH_MP MOD_MOD ( ASSUME ( Parse.Term [ QUOTE " (*#loc 1 136843*)0 < n" ] ) ) ] |> SYM |> DISCH_ALL )
;
val MODEQ_SYM = store_thm ( "MODEQ_SYM" , ( Parse.Term [ QUOTE " (*#loc 1 136937*)MODEQ n x y <=> MODEQ n y x" ] ) ,
let
val tactictoe_tac1 = SRW_TAC [ ] [ MODEQ_THM ] THEN METIS_TAC [ ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_SYM" 
 ( String.concatWith " " 
 [ "BasicProvers.SRW_TAC", "[", "]", "[", 
hhsRecord.fetch "MODEQ_THM" "( ( DB.fetch \"arithmetic\" \"MODEQ_THM\" ) )", 
"]", "hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "metisLib.METIS_TAC", "[", 
"]" ] )
in hhsRecord.try_record_proof "MODEQ_SYM" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_TRANS = store_thm ( "MODEQ_TRANS" , ( Parse.Term [ QUOTE " (*#loc 1 137062*)!x y z. MODEQ n x y /\\ MODEQ n y z ==> MODEQ n x z" ] ) ,
let
val tactictoe_tac1 = Q.ID_SPEC_TAC [ QUOTE " (*#loc 1 137134*)n" ] THEN SIMP_TAC ( srw_ss ( ) ++ DNF_ss ) [ MODEQ_THM , LESS_REFL ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_TRANS" 
 ( String.concatWith " " 
 [ "Q.ID_SPEC_TAC", "[", "HolKernel.QUOTE", "\" (*#loc 1 137134*)n\"", "]", 
"hhs_infixl0_open boolLib.THEN hhs_infixl0_close", "simpLib.SIMP_TAC", "(", 
"BasicProvers.srw_ss", "(", ")", "hhs_infixl0_open simpLib.++ hhs_infixl0_close", 
"boolSimps.DNF_ss", ")", "[", 
hhsRecord.fetch "MODEQ_THM" "( ( DB.fetch \"arithmetic\" \"MODEQ_THM\" ) )", 
",", "prim_recTheory.LESS_REFL", "]" ] )
in hhsRecord.try_record_proof "MODEQ_TRANS" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_NUMERAL = store_thm ( "MODEQ_NUMERAL" , ( Parse.Term [ QUOTE " (*#loc 1 137250*)(NUMERAL n <= NUMERAL m ==>      MODEQ (NUMERAL (BIT1 n)) (NUMERAL (BIT1 m))            (NUMERAL (BIT1 m) MOD NUMERAL (BIT1 n))) /\\     (NUMERAL n <= NUMERAL m ==>      MODEQ (NUMERAL (BIT1 n)) (NUMERAL (BIT2 m))            (NUMERAL (BIT2 m) MOD NUMERAL (BIT1 n))) /\\     (NUMERAL n <= NUMERAL m ==>      MODEQ (NUMERAL (BIT2 n)) (NUMERAL (BIT2 m))            (NUMERAL (BIT2 m) MOD NUMERAL (BIT2 n))) /\\     (NUMERAL n < NUMERAL m ==>      MODEQ (NUMERAL (BIT2 n)) (NUMERAL (BIT1 m))            (NUMERAL (BIT1 m) MOD NUMERAL (BIT2 n)))" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC ( srw_ss ( ) ) [ MODEQ_NONZERO_MODEQUALITY , BIT1 , BIT2 , ADD_CLAUSES , ALT_ZERO , NUMERAL_DEF , MOD_MOD , LESS_0 ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_NUMERAL" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "MODEQ_NONZERO_MODEQUALITY" "( ( DB.fetch \"arithmetic\" \"MODEQ_NONZERO_MODEQUALITY\" ) )", 
",", hhsRecord.fetch "BIT1" "( ( DB.fetch \"arithmetic\" \"BIT1\" ) )", ",", 
hhsRecord.fetch "BIT2" "( ( DB.fetch \"arithmetic\" \"BIT2\" ) )", ",", 
hhsRecord.fetch "ADD_CLAUSES" "( ( DB.fetch \"arithmetic\" \"ADD_CLAUSES\" ) )", 
",", 
hhsRecord.fetch "ALT_ZERO" "( ( DB.fetch \"arithmetic\" \"ALT_ZERO\" ) )", 
",", 
hhsRecord.fetch "NUMERAL_DEF" "( ( DB.fetch \"arithmetic\" \"NUMERAL_DEF\" ) )", 
",", hhsRecord.fetch "MOD_MOD" "( ( DB.fetch \"arithmetic\" \"MOD_MOD\" ) )", 
",", "prim_recTheory.LESS_0", "]" ] )
in hhsRecord.try_record_proof "MODEQ_NUMERAL" false tactictoe_tac2 tactictoe_tac1
end )
;
val MODEQ_MOD = store_thm ( "MODEQ_MOD" , ( Parse.Term [ QUOTE " (*#loc 1 137974*)0 < n ==> MODEQ n (x MOD n) x" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC ( srw_ss ( ) ) [ MODEQ_NONZERO_MODEQUALITY , MOD_MOD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_MOD" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "MODEQ_NONZERO_MODEQUALITY" "( ( DB.fetch \"arithmetic\" \"MODEQ_NONZERO_MODEQUALITY\" ) )", 
",", hhsRecord.fetch "MOD_MOD" "( ( DB.fetch \"arithmetic\" \"MOD_MOD\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MODEQ_MOD" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val MODEQ_0 = store_thm ( "MODEQ_0" , ( Parse.Term [ QUOTE " (*#loc 1 138110*)0 < n ==> MODEQ n n 0" ] ) ,
let
val tactictoe_tac1 = SIMP_TAC ( srw_ss ( ) ) [ MODEQ_NONZERO_MODEQUALITY , DIVMOD_ID , ZERO_MOD ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "MODEQ_0" 
 ( String.concatWith " " 
 [ "simpLib.SIMP_TAC", "(", "BasicProvers.srw_ss", "(", ")", ")", "[", 
hhsRecord.fetch "MODEQ_NONZERO_MODEQUALITY" "( ( DB.fetch \"arithmetic\" \"MODEQ_NONZERO_MODEQUALITY\" ) )", 
",", 
hhsRecord.fetch "DIVMOD_ID" "( ( DB.fetch \"arithmetic\" \"DIVMOD_ID\" ) )", 
",", 
hhsRecord.fetch "ZERO_MOD" "( ( DB.fetch \"arithmetic\" \"ZERO_MOD\" ) )", 
"]" ] )
in hhsRecord.try_record_proof "MODEQ_0" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val modss = simpLib.add_relsimp { refl = MODEQ_REFL , trans = MODEQ_TRANS , weakenings = [ MODEQ_INTRO_CONG ] , subsets = [ ] , rewrs = [ MODEQ_NUMERAL , MODEQ_MOD , MODEQ_0 ] } ( srw_ss ( ) ) ++ SSFRAG { dprocs = [ ] , ac = [ ] , rewrs = [ ] , congs = [ MODEQ_PLUS_CONG , MODEQ_MULT_CONG , MODEQ_SUC_CONG ] , filter = NONE , convs = [ ] , name = NONE }
;
val result1 = SIMP_CONV modss [ ASSUME ( Parse.Term [ QUOTE " (*#loc 1 138758*)0 < 6" ] ) , LESS_EQ_REFL , ASSUME ( Parse.Term [ QUOTE " (*#loc 1 138792*)2 < 3" ] ) , DIVMOD_ID , MULT_CLAUSES , ADD_CLAUSES , ASSUME ( Parse.Term [ QUOTE " (*#loc 1 138892*)7 MOD 6 = 1" ] ) ] ( Parse.Term [ QUOTE " (*#loc 1 138911*)(6 * x + 7 + 6 * y) MOD 6" ] )
;
;
val result2 = SIMP_CONV modss [ ASSUME ( Parse.Term [ QUOTE " (*#loc 1 139000*)0 < n" ] ) , MULT_CLAUSES , ADD_CLAUSES ] ( Parse.Term [ QUOTE " (*#loc 1 139054*)(4 + 3 * n + 1) MOD n" ] )
;
val _ = adjoin_to_theory { sig_ps = NONE , struct_ps = SOME ( fn ppstrm =>
let
val S = ( fn s => ( PP.add_string ppstrm s
; PP.add_newline ppstrm ) )
;
in S "val _ = TypeBase.write"
; S "  [TypeBasePure.mk_datatype_info"
; S "     {ax=TypeBasePure.ORIG prim_recTheory.num_Axiom,"
; S "      case_def=num_case_def,"
; S "      case_cong=num_case_cong,"
; S "      induction=TypeBasePure.ORIG numTheory.INDUCTION,"
; S "      nchotomy=num_CASES,"
; S "      size=SOME(Parse.Term`\\x:num. x`, TypeBasePure.ORIG boolTheory.REFL_CLAUSE),"
; S "      encode=NONE,"
; S "      fields=[],"
; S "      accessors=[],"
; S "      updates=[],"
; S "      recognizers=[],"
; S "      destructors=[CONJUNCT2(prim_recTheory.PRE)],"
; S "      lift=SOME(mk_var(\"numSyntax.lift_num\",Parse.Type`:'type -> num -> 'term`)),"
; S "      one_one=SOME prim_recTheory.INV_SUC_EQ,"
; S "      distinct=SOME numTheory.NOT_SUC}];"
end ) }
;
;
val datatype_num = store_thm ( "datatype_num" , ( Parse.Term [ QUOTE " (*#loc 1 140077*)DATATYPE (num 0 SUC)" ] ) ,
let
val tactictoe_tac1 = REWRITE_TAC [ DATATYPE_TAG_THM ]
val tactictoe_tac2 = hhsRecord.wrap_tactics_in "datatype_num" 
 ( String.concatWith " " 
 [ "boolLib.REWRITE_TAC", "[", "boolLib.DATATYPE_TAG_THM", "]" ] )
in hhsRecord.try_record_proof "datatype_num" false tactictoe_tac2 tactictoe_tac1
end )
;
;
val _ = ( )
;
val _ = hhsRecord.end_thy "arithmetic"