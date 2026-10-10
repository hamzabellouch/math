import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Basic

namespace OAI

noncomputable section
open scoped ENNReal lp

namespace Invariant233

abbrev SequenceHilbert (I : Type*) := lp (fun _ : I => ℂ) 2

namespace SequenceHilbert
variable {I : Type*}

def diagonalLinear (a : I → ℂ) (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C) :
    SequenceHilbert I →ₗ[ℂ] SequenceHilbert I where
  toFun x := ⟨fun i => a i * x i, by
    apply Memℓp.mono ((lp.memℓp x).norm.const_mul C)
    intro i
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)⟩
  map_add' x y := by
    apply lp.ext
    funext i
    exact mul_add _ _ _
  map_smul' c x := by
    apply lp.ext
    funext i
    change a i * (c * x i) = c * (a i * x i)
    ring

def diagonal (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    SequenceHilbert I →L[ℂ] SequenceHilbert I :=
  (diagonalLinear a C ha).mkContinuous C (by
    intro x
    calc
      ‖diagonalLinear a C ha x‖ ≤ ‖C • x‖ := by
        apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        intro i
        change ‖a i * x i‖ ≤ ‖C • x i‖
        rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)
      _ = C * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC])

def reindex (e : Equiv.Perm I) : SequenceHilbert I ≃ₗᵢ[ℂ] SequenceHilbert I where
  toFun x := ⟨fun i => x (e.symm i), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp x).summable (by norm_num))⟩
  invFun x := ⟨fun i => x (e i), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp x).summable (by norm_num))⟩
  left_inv x := by
    apply lp.ext
    funext i
    simp
  right_inv x := by
    apply lp.ext
    funext i
    simp
  map_add' x y := by
    apply lp.ext
    funext i
    rfl
  map_smul' c x := by
    apply lp.ext
    funext i
    rfl
  norm_map' x := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact congrArg (fun t : ℝ => t ^ (1 / (2 : ℝ≥0∞).toReal))
      (e.symm.tsum_eq (fun i => ‖x i‖ ^ (2 : ℝ≥0∞).toReal))

end SequenceHilbert
end Invariant233

end

end OAI
