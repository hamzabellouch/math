import Mathlib.Data.ZMod.Basic
import OAI.NumberTheory.Catalan.Estimates.PalindromicBlockInverse

namespace OAI

section

noncomputable section

namespace InternalCatalan

theorem fixedMatrix_det_ne_zero_of_integer_certificate
    (sigma : ℚ) (den : ℤ) (A : Matrix (Fin 48) (Fin 48) ℤ)
    (hA : A.map (fun x : ℤ => (x : ℚ)) = (den : ℚ) • fixedMatrix sigma)
    (hmod : (A.map (fun x : ℤ => (x : ZMod 101))).det ≠ 0) :
    (fixedMatrix sigma).det ≠ 0 := by
  intro hzero
  have hrat : (A.det : ℚ) = 0 := by
    rw [Int.cast_det, hA, Matrix.det_smul, hzero, mul_zero]
  have hint : A.det = 0 := by exact_mod_cast hrat
  apply hmod
  rw [← Int.cast_det, hint, Int.cast_zero]

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def fixedIntegerMatrix (A : Matrix (Fin 49) (Fin 48) ℤ) (sigma : ℤ) :
    Matrix (Fin 48) (Fin 48) ℤ :=
  fun r k => A r.castSucc k + sigma * A r.succ k

theorem fixedIntegerMatrix_cast_of_base_lift
    (A : Matrix (Fin 49) (Fin 48) ℤ) (den sigma : ℤ)
    (hbase : ∀ (r : Fin 49) (k : Fin 48),
      (A r k : ℚ) = (den : ℚ) * fixedBaseEntryRat r k) :
    (fixedIntegerMatrix A sigma).map (fun x : ℤ => (x : ℚ)) =
      (den : ℚ) • fixedMatrix (sigma : ℚ) := by
  ext r k
  change ((A r.castSucc k + sigma * A r.succ k : ℤ) : ℚ) =
    (den : ℚ) * (fixedBaseEntryRat r.castSucc k +
      (sigma : ℚ) * fixedBaseEntryRat r.succ k)
  rw [Int.cast_add, Int.cast_mul, hbase, hbase]
  ring

theorem fixedMatrix_det_ne_zero_of_base_certificate
    (A : Matrix (Fin 49) (Fin 48) ℤ) (den sigma : ℤ)
    (hbase : ∀ (r : Fin 49) (k : Fin 48),
      (A r k : ℚ) = (den : ℚ) * fixedBaseEntryRat r k)
    (hmod : ((fixedIntegerMatrix A sigma).map
      (fun x : ℤ => (x : ZMod 101))).det ≠ 0) :
    (fixedMatrix (sigma : ℚ)).det ≠ 0 :=
  fixedMatrix_det_ne_zero_of_integer_certificate (sigma : ℚ) den
    (fixedIntegerMatrix A sigma)
    (fixedIntegerMatrix_cast_of_base_lift A den sigma hbase) hmod

end InternalCatalan

end

end

end OAI
