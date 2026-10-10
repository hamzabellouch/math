import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ExpandingSmoothCutoffs

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set
open scoped ContDiff

def scaledSmoothCutoff (d : ℕ) (r : ℝ) (x : Ambient d) : ℝ :=
  unitSmoothCutoff d (r⁻¹ • x)

theorem scaledSmoothCutoff_smooth (d : ℕ) (r : ℝ) :
    ContDiff ℝ ∞ (scaledSmoothCutoff d r) :=
  (unitSmoothCutoff d).contDiff.comp
    ((contDiff_id : ContDiff ℝ ∞ (fun x : Ambient d => x)).const_smul r⁻¹)

theorem scaledSmoothCutoff_zero (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x : Ambient d) (hx : 2 * r ≤ ‖x‖) : scaledSmoothCutoff d r x = 0 := by
  apply (unitSmoothCutoff d).zero_of_le_dist
  change 2 ≤ dist (r⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  exact (le_div_iff₀ hr).2 hx |>.trans_eq (div_eq_inv_mul _ _)

theorem scaledSmoothCutoff_support (d : ℕ) (r : ℝ) (hr : 0 < r) :
    tsupport (scaledSmoothCutoff d r) ⊆ closedBall (0 : Ambient d) (2 * r) := by
  apply closure_minimal ?_ isClosed_closedBall
  intro x hx
  by_contra h
  have hn : 2 * r < ‖x‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using! h
  exact hx (scaledSmoothCutoff_zero d r hr x hn.le)

theorem scaledSmoothCutoff_compact (d : ℕ) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (scaledSmoothCutoff d r) :=
  (isCompact_closedBall (0 : Ambient d) (2 * r)).of_isClosed_subset
    (isClosed_tsupport _) (scaledSmoothCutoff_support d r hr)

theorem scaledSmoothCutoff_one (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x : Ambient d) (hx : x ∈ ball (0 : Ambient d) r) : scaledSmoothCutoff d r x = 1 := by
  apply (unitSmoothCutoff d).one_of_mem_closedBall
  have hx' : ‖x‖ < r := by simpa only [mem_ball, dist_zero_right] using! hx
  change dist (r⁻¹ • x) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hh : ‖x‖ / r ≤ 1 := (div_le_one hr).2 hx'.le
  simpa only [div_eq_inv_mul] using! hh

theorem scaledSmoothCutoff_derivatives (d : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ r : ℝ, 0 < r → ∀ n x,
      ‖iteratedFDeriv ℝ n (scaledSmoothCutoff d r) x‖ ≤ C n * (r⁻¹) ^ n := by
  let β : 𝓢(Ambient d, ℝ) := (unitSmoothCutoff d).hasCompactSupport.toSchwartzMap
    (unitSmoothCutoff d).contDiff
  refine ⟨fun n => SchwartzMap.seminorm ℝ 0 n β, fun n => apply_nonneg _ _, ?_⟩
  intro r hr n x
  let S : Ambient d →L[ℝ] Ambient d := r⁻¹ • ContinuousLinearMap.id ℝ (Ambient d)
  have hS : ‖S‖ ≤ r⁻¹ := by
    calc
      ‖S‖ ≤ ‖r⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Ambient d)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ r⁻¹ * 1 := mul_le_mul
        (by rw [Real.norm_of_nonneg (inv_nonneg.mpr hr.le)])
        ContinuousLinearMap.norm_id_le (norm_nonneg _) (inv_nonneg.mpr hr.le)
      _ = _ := mul_one _
  have heq : scaledSmoothCutoff d r = β ∘ S := rfl
  rw [heq, S.iteratedFDeriv_comp_right (β.smooth n) x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n β (S x)‖ * ∏ _ : Fin n, ‖S‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ n β (S x)‖ * ‖S‖ ^ n := by simp
    _ ≤ SchwartzMap.seminorm ℝ 0 n β * (r⁻¹) ^ n :=
      mul_le_mul (β.norm_iteratedFDeriv_le_seminorm ℝ n (S x))
        (pow_le_pow_left₀ (norm_nonneg _) hS n) (by positivity) (apply_nonneg _ _)

end

end RieszRectifiability

end OAI
