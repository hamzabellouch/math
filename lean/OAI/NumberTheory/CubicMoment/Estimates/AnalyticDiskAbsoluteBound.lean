import OAI.NumberTheory.CubicMoment.Estimates.AnalyticDiskZeroMass

namespace OAI

/-! An absolute logarithmic-derivative bound away from the local zeros,
using the proved Jensen multiplicity bound and local expansion. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem normalized_disk_logDeriv_norm_bound (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf0 : f 0=1) {B r : ℝ} (hB : 1 < B) (hr : 0 < r)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖f z‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ (1/2:ℝ)) (hfz : f z ≠ 0)
    (hsep : ∀ w : ℂ, ‖w‖ ≤ (3/4:ℝ) → f w=0 → r ≤ ‖z-w‖) :
    ‖logDeriv f z‖ ≤
      (diskLogDerivativeConstant+1/(r*Real.log ((7/8:ℝ)/(3/4:ℝ))))*Real.log B := by
  classical
  obtain ⟨Z,hZ,herr⟩ := normalized_disk_logDeriv f hf hf0 hB hb
  have hm := normalized_disk_zero_mass f hf hf0 hB hb Z hZ
  have hsum : ‖∑ w ∈ Z, ((analyticOrderAt f w).toNat:ℂ)/(z-w)‖ ≤
      (1/r)*∑ w ∈ Z, ((analyticOrderAt f w).toNat:ℝ) := by
    calc
      _ ≤ ∑ w ∈ Z, ‖((analyticOrderAt f w).toNat:ℂ)/(z-w)‖ := norm_sum_le _ _
      _ ≤ ∑ w ∈ Z, (1/r)*((analyticOrderAt f w).toNat:ℝ) := by
        apply Finset.sum_le_sum
        intro w hw
        have hd := hsep w (hZ w |>.mp hw).1 (hZ w |>.mp hw).2
        rw [norm_div,Complex.norm_natCast]
        calc
          _ ≤ ((analyticOrderAt f w).toNat:ℝ)/r :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) hr hd
          _ = _ := by ring
      _ = _ := (Finset.mul_sum ..).symm
  have ht : ‖logDeriv f z‖ ≤
      ‖logDeriv f z-∑ w ∈ Z, ((analyticOrderAt f w).toNat:ℂ)/(z-w)‖+
        ‖∑ w ∈ Z, ((analyticOrderAt f w).toNat:ℂ)/(z-w)‖ := by
    simpa only [sub_add_cancel] using
      (norm_add_le (logDeriv f z-∑ w ∈ Z, ((analyticOrderAt f w).toNat:ℂ)/(z-w))
        (∑ w ∈ Z, ((analyticOrderAt f w).toNat:ℂ)/(z-w)))
  have hp := mul_le_mul_of_nonneg_left hm (le_of_lt (one_div_pos.mpr hr))
  calc
    ‖logDeriv f z‖ ≤ diskLogDerivativeConstant*Real.log B+
        (1/r)*((1/Real.log ((7/8:ℝ)/(3/4:ℝ)))*Real.log B) := by linarith [herr z hz hfz]
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
