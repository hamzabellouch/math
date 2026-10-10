import Mathlib
import OAI.Analysis.Unitarizability.SumObstruction

namespace OAI

noncomputable section
namespace Dixmier
namespace KernelObstruction
variable {G K : Type*} [Group G] [Fintype K]

lemma coefficients_real_smul (t : ℝ) (B : Fibre K →L[ℂ] Fibre K) :
    coefficients (t • B) = t • coefficients B := by
  ext ab
  rfl

lemma energy_real_smul (t : ℝ) (A : Op G K) : energy (t • A) = t ^ 2 * energy A := by
  have hb (x y : G) : block (t • A) x y = t • block A x y := by
    simp only [block, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  simp only [energy, hb, coefficients_real_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  exact tsum_mul_left

end KernelObstruction
namespace DirectSumObstruction
open Filter
variable {G : Type*} [Group G]

theorem scaled_direct_sum_obstruction (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j - T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop)
    {t : ℝ} (ht : 0 < t) :
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + t * κ) ∧ ¬ SimilarToUnitary π := by
  apply direct_sum_obstruction k hk (fun j => t • A j) (fun j => t • T j)
    (fun j g => by
      change (t • A j).comp (KernelObstruction.translation g) =
        (KernelObstruction.translation g).comp (t • A j)
      rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      exact congrArg (fun operator => t • operator) (hA j g).eq)
    (mul_nonneg ht.le hκ)
  · intro j
    simpa only [KernelObstruction.row, ContinuousLinearMap.comp_smul,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht] using mul_le_mul_of_nonneg_left (hr j) ht.le
  · intro j
    rw [← smul_sub t (A j) (T j)]
    simpa only [KernelObstruction.col, ContinuousLinearMap.smul_comp,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht] using mul_le_mul_of_nonneg_left (hc j) ht.le
  · intro j g
    have hscale : coboundary KernelObstruction.translation (t • T j) g =
        t • coboundary KernelObstruction.translation (T j) g := by
      simp only [coboundary, conjugate, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, smul_sub]
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (hb j g) ht.le
  · simpa only [KernelObstruction.energy_real_smul, mul_div_assoc] using
      he.const_mul_atTop (sq_pos_of_pos ht)

end DirectSumObstruction

end Dixmier
end

end OAI
