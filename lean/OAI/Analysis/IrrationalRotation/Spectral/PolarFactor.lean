import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace OAI

namespace Invariant233.PolarFactor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem star_mul_self_unitary_mul (U : unitary (H →L[ℂ] H)) (A : H →L[ℂ] H) :
    star ((U : H →L[ℂ] H) * A) * ((U : H →L[ℂ] H) * A) = star A * A := by
  rw [star_mul]
  calc
    (star A * star (U : H →L[ℂ] H)) * ((U : H →L[ℂ] H) * A) =
        star A * (star (U : H →L[ℂ] H) * (U : H →L[ℂ] H)) * A := by
          simp only [mul_assoc]
    _ = star A * A := by simp

theorem abs_unitary_mul (U : unitary (H →L[ℂ] H)) (A : H →L[ℂ] H) :
    CFC.abs ((U : H →L[ℂ] H) * A) = CFC.abs A := by
  unfold CFC.abs
  rw [star_mul_self_unitary_mul]

theorem abs_unitary_mul_of_nonneg (U : unitary (H →L[ℂ] H))
    (A : H →L[ℂ] H) (hA : 0 ≤ A) :
    CFC.abs ((U : H →L[ℂ] H) * A) = A := by
  rw [abs_unitary_mul, CFC.abs_of_nonneg A hA]

theorem norm_unitary_mul (U : unitary (H →L[ℂ] H)) (A : H →L[ℂ] H) :
    ‖(U : H →L[ℂ] H) * A‖ = ‖A‖ := by
  exact (Unitary.linearIsometryEquiv U).toLinearIsometry.norm_toContinuousLinearMap_comp

theorem ker_unitary_mul (U : unitary (H →L[ℂ] H)) (A : H →L[ℂ] H) :
    ((U : H →L[ℂ] H) * A).ker = A.ker := by
  ext x
  change (U : H →L[ℂ] H) (A x) = 0 ↔ A x = 0
  constructor
  · intro hx
    apply norm_eq_zero.1
    rw [← Unitary.norm_map U (A x), hx, norm_zero]
  · intro hx
    simp [hx]

theorem unitary_mul_ne_zero (U : unitary (H →L[ℂ] H))
    {A : H →L[ℂ] H} (hA : A ≠ 0) : (U : H →L[ℂ] H) * A ≠ 0 := by
  intro hzero
  apply hA
  apply norm_eq_zero.1
  rw [← norm_unitary_mul U A, hzero, norm_zero]

theorem denseRange_of_nonneg_ker_eq_bot {A : H →L[ℂ] H}
    (hA : 0 ≤ A) (hker : A.ker = ⊥) : DenseRange A := by
  have hadj : A.adjoint = A := hA.star_eq
  have hclosure := A.orthogonal_ker
  rw [hker, Submodule.bot_orthogonal_eq_top, hadj] at hclosure
  exact Submodule.dense_iff_topologicalClosure_eq_top.2 hclosure.symm

theorem unitary_factor_unique_of_nonneg_ker_eq_bot
    (U V : unitary (H →L[ℂ] H)) {A : H →L[ℂ] H}
    (hA : 0 ≤ A) (hker : A.ker = ⊥)
    (h : (U : H →L[ℂ] H) * A = (V : H →L[ℂ] H) * A) : U = V := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  have hdense := denseRange_of_nonneg_ker_eq_bot hA hker
  have hfun : (U : H →L[ℂ] H) ∘ A = (V : H →L[ℂ] H) ∘ A :=
    congrArg (fun B : H →L[ℂ] H => (B : H → H)) h
  exact congrFun (hdense.equalizer (U : H →L[ℂ] H).continuous
    (V : H →L[ℂ] H).continuous hfun)

end Invariant233.PolarFactor

end OAI
