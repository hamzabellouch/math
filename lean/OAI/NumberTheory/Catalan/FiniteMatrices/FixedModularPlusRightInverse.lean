import Mathlib.Tactic.FinCases
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedModularPlusProductRows40To41

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_42 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 42 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 42 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_43 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 43 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 43 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_44 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 44 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 44 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_45 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 45 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 45 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_46 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 46 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 46 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_47 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 47 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 47 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_4 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 4 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 4 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_5 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 5 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 5 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_6 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 6 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 6 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_7 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 7 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 7 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse_row_8 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 8 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 8 k := by
  decide +kernel

theorem fixedLiteralModPlus_rightInverse_row_9 : ∀ k : Fin 48,
    (fixedLiteralModPlus * fixedLiteralInvPlus) 9 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 9 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModPlus_rightInverse :
    fixedLiteralModPlus * fixedLiteralInvPlus =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) := by
  ext r k
  fin_cases r
  · exact fixedLiteralModPlus_rightInverse_row_0 k
  · exact fixedLiteralModPlus_rightInverse_row_1 k
  · exact fixedLiteralModPlus_rightInverse_row_2 k
  · exact fixedLiteralModPlus_rightInverse_row_3 k
  · exact fixedLiteralModPlus_rightInverse_row_4 k
  · exact fixedLiteralModPlus_rightInverse_row_5 k
  · exact fixedLiteralModPlus_rightInverse_row_6 k
  · exact fixedLiteralModPlus_rightInverse_row_7 k
  · exact fixedLiteralModPlus_rightInverse_row_8 k
  · exact fixedLiteralModPlus_rightInverse_row_9 k
  · exact fixedLiteralModPlus_rightInverse_row_10 k
  · exact fixedLiteralModPlus_rightInverse_row_11 k
  · exact fixedLiteralModPlus_rightInverse_row_12 k
  · exact fixedLiteralModPlus_rightInverse_row_13 k
  · exact fixedLiteralModPlus_rightInverse_row_14 k
  · exact fixedLiteralModPlus_rightInverse_row_15 k
  · exact fixedLiteralModPlus_rightInverse_row_16 k
  · exact fixedLiteralModPlus_rightInverse_row_17 k
  · exact fixedLiteralModPlus_rightInverse_row_18 k
  · exact fixedLiteralModPlus_rightInverse_row_19 k
  · exact fixedLiteralModPlus_rightInverse_row_20 k
  · exact fixedLiteralModPlus_rightInverse_row_21 k
  · exact fixedLiteralModPlus_rightInverse_row_22 k
  · exact fixedLiteralModPlus_rightInverse_row_23 k
  · exact fixedLiteralModPlus_rightInverse_row_24 k
  · exact fixedLiteralModPlus_rightInverse_row_25 k
  · exact fixedLiteralModPlus_rightInverse_row_26 k
  · exact fixedLiteralModPlus_rightInverse_row_27 k
  · exact fixedLiteralModPlus_rightInverse_row_28 k
  · exact fixedLiteralModPlus_rightInverse_row_29 k
  · exact fixedLiteralModPlus_rightInverse_row_30 k
  · exact fixedLiteralModPlus_rightInverse_row_31 k
  · exact fixedLiteralModPlus_rightInverse_row_32 k
  · exact fixedLiteralModPlus_rightInverse_row_33 k
  · exact fixedLiteralModPlus_rightInverse_row_34 k
  · exact fixedLiteralModPlus_rightInverse_row_35 k
  · exact fixedLiteralModPlus_rightInverse_row_36 k
  · exact fixedLiteralModPlus_rightInverse_row_37 k
  · exact fixedLiteralModPlus_rightInverse_row_38 k
  · exact fixedLiteralModPlus_rightInverse_row_39 k
  · exact fixedLiteralModPlus_rightInverse_row_40 k
  · exact fixedLiteralModPlus_rightInverse_row_41 k
  · exact fixedLiteralModPlus_rightInverse_row_42 k
  · exact fixedLiteralModPlus_rightInverse_row_43 k
  · exact fixedLiteralModPlus_rightInverse_row_44 k
  · exact fixedLiteralModPlus_rightInverse_row_45 k
  · exact fixedLiteralModPlus_rightInverse_row_46 k
  · exact fixedLiteralModPlus_rightInverse_row_47 k

theorem fixedLiteralModPlus_det_ne_zero : fixedLiteralModPlus.det ≠ 0 := by
  intro hz
  have h := congrArg Matrix.det fixedLiteralModPlus_rightInverse
  rw [Matrix.det_mul, Matrix.det_one, hz, zero_mul] at h
  have hzero_ne_one : (0 : ZMod 101) ≠ 1 := by decide
  exact hzero_ne_one h

end InternalCatalan

end

end OAI
