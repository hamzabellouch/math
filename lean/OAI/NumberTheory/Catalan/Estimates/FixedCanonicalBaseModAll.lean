import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow0
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow1
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow10
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow11
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow12
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow13
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow14
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow15
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow16
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow17
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow18
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow19
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow2
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow20
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow21
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow22
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow23
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow24
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow25
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow26
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow27
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow28
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow29
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow3
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow30
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow31
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow32
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow33
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow34
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow35
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow36
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow37
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow38
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow39
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow4
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow40
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow41
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow42
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow43
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow44
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow45
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow46
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow47
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow48
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow5
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow6
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow7
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow8
import OAI.NumberTheory.Catalan.Determinants.FixedCanonicalBaseModRow9

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem fixedIntegerBaseCanonical_mod_eq (r : Fin 49) (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  fin_cases r
  · exact fixedIntegerBaseCanonical_mod_row_0 k
  · exact fixedIntegerBaseCanonical_mod_row_1 k
  · exact fixedIntegerBaseCanonical_mod_row_2 k
  · exact fixedIntegerBaseCanonical_mod_row_3 k
  · exact fixedIntegerBaseCanonical_mod_row_4 k
  · exact fixedIntegerBaseCanonical_mod_row_5 k
  · exact fixedIntegerBaseCanonical_mod_row_6 k
  · exact fixedIntegerBaseCanonical_mod_row_7 k
  · exact fixedIntegerBaseCanonical_mod_row_8 k
  · exact fixedIntegerBaseCanonical_mod_row_9 k
  · exact fixedIntegerBaseCanonical_mod_row_10 k
  · exact fixedIntegerBaseCanonical_mod_row_11 k
  · exact fixedIntegerBaseCanonical_mod_row_12 k
  · exact fixedIntegerBaseCanonical_mod_row_13 k
  · exact fixedIntegerBaseCanonical_mod_row_14 k
  · exact fixedIntegerBaseCanonical_mod_row_15 k
  · exact fixedIntegerBaseCanonical_mod_row_16 k
  · exact fixedIntegerBaseCanonical_mod_row_17 k
  · exact fixedIntegerBaseCanonical_mod_row_18 k
  · exact fixedIntegerBaseCanonical_mod_row_19 k
  · exact fixedIntegerBaseCanonical_mod_row_20 k
  · exact fixedIntegerBaseCanonical_mod_row_21 k
  · exact fixedIntegerBaseCanonical_mod_row_22 k
  · exact fixedIntegerBaseCanonical_mod_row_23 k
  · exact fixedIntegerBaseCanonical_mod_row_24 k
  · exact fixedIntegerBaseCanonical_mod_row_25 k
  · exact fixedIntegerBaseCanonical_mod_row_26 k
  · exact fixedIntegerBaseCanonical_mod_row_27 k
  · exact fixedIntegerBaseCanonical_mod_row_28 k
  · exact fixedIntegerBaseCanonical_mod_row_29 k
  · exact fixedIntegerBaseCanonical_mod_row_30 k
  · exact fixedIntegerBaseCanonical_mod_row_31 k
  · exact fixedIntegerBaseCanonical_mod_row_32 k
  · exact fixedIntegerBaseCanonical_mod_row_33 k
  · exact fixedIntegerBaseCanonical_mod_row_34 k
  · exact fixedIntegerBaseCanonical_mod_row_35 k
  · exact fixedIntegerBaseCanonical_mod_row_36 k
  · exact fixedIntegerBaseCanonical_mod_row_37 k
  · exact fixedIntegerBaseCanonical_mod_row_38 k
  · exact fixedIntegerBaseCanonical_mod_row_39 k
  · exact fixedIntegerBaseCanonical_mod_row_40 k
  · exact fixedIntegerBaseCanonical_mod_row_41 k
  · exact fixedIntegerBaseCanonical_mod_row_42 k
  · exact fixedIntegerBaseCanonical_mod_row_43 k
  · exact fixedIntegerBaseCanonical_mod_row_44 k
  · exact fixedIntegerBaseCanonical_mod_row_45 k
  · exact fixedIntegerBaseCanonical_mod_row_46 k
  · exact fixedIntegerBaseCanonical_mod_row_47 k
  · exact fixedIntegerBaseCanonical_mod_row_48 k

end InternalCatalan

end

end

end OAI
