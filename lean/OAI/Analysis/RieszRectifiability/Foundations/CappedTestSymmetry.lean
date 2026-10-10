import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CappedTransform

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

def symmetricScalarCappedTestKernel {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (g : Ambient d → ℝ) (x h : Ambient d) : ℝ :=
  cappedInverseDistancePow (m + 1) ε (0, h) *
    (inner ℝ e h * (g (x + h) - g (x - h)))

def symmetricScalarRieszTestKernel {d : ℕ} (m : ℕ) (e : Ambient d)
    (g : Ambient d → ℝ) (x h : Ambient d) : ℝ :=
  inverseDistancePow (m + 1) 0 h *
    (inner ℝ e h * (g (x + h) - g (x - h)))

theorem scalarCappedRieszKernel_add {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (x h : Ambient d) :
    scalarCappedRieszKernel m e ε (x, x + h) =
      -(cappedInverseDistancePow (m + 1) ε (0, h) * inner ℝ e h) := by
  have heq : x - (x + h) = -h := by abel
  simp only [scalarCappedRieszKernel, cappedRieszKernel, cappedInverseDistancePow,
    dist_eq_norm, heq, zero_sub, norm_neg, inner_smul_right, inner_neg_right]
  ring

theorem scalarCappedRieszKernel_sub {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (x h : Ambient d) :
    scalarCappedRieszKernel m e ε (x, x - h) =
      cappedInverseDistancePow (m + 1) ε (0, h) * inner ℝ e h := by
  have heq : x - (x - h) = h := by abel
  simp only [scalarCappedRieszKernel, cappedRieszKernel, cappedInverseDistancePow,
    dist_eq_norm, heq, zero_sub, norm_neg, inner_smul_right]

theorem scalarCappedTransform_symmetric_identity {d : ℕ} (m : ℕ)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε) (g : Ambient d → ℝ)
    (hgm : Measurable g) (hg : Integrable g volume) (x : Ambient d) :
    Integrable (symmetricScalarCappedTestKernel m e ε g x) volume ∧
      scalarCappedTransform m volume e ε g x =
        (-1 / 2 : ℝ) * ∫ h, symmetricScalarCappedTestKernel m e ε g x h := by
  let F : Ambient d → ℝ := fun y => g y * scalarCappedRieszKernel m e ε (x, y)
  have hF : Integrable F volume :=
    (scalarCappedTransform_integrable_and_bound m volume e ε hε g hgm hg x).1
  have heq : symmetricScalarCappedTestKernel m e ε g x =
      (fun h => -F (x + h) - F (x - h)) := by
    funext h
    dsimp only [symmetricScalarCappedTestKernel, F]
    rw [scalarCappedRieszKernel_add, scalarCappedRieszKernel_sub]
    ring
  have hp := hF.comp_add_left x
  have hm := hF.comp_sub_left x
  have hpneg : Integrable (fun h => -F (x + h)) volume := hp.neg
  have hI : Integrable (symmetricScalarCappedTestKernel m e ε g x) volume := by
    rw [heq]
    exact hp.neg.sub hm
  refine ⟨hI, ?_⟩
  rw [heq]
  dsimp only
  rw [integral_sub hpneg hm, integral_neg,
    integral_add_left_eq_self F x, integral_sub_left_eq_self F volume x]
  change (∫ y, F y) = (-1 / 2 : ℝ) * (-(∫ y, F y) - ∫ y, F y)
  ring

theorem symmetricScalarCappedTestKernel_norm_le {d : ℕ} (m : ℕ)
    (e : Ambient d) (ε : ℝ) (g : Ambient d → ℝ) (x h : Ambient d) :
    ‖symmetricScalarCappedTestKernel m e ε g x h‖ ≤
      ‖symmetricScalarRieszTestKernel m e g x h‖ := by
  by_cases hh : h = 0
  · subst h
    simp only [symmetricScalarCappedTestKernel, symmetricScalarRieszTestKernel,
      inner_zero_right, zero_mul, mul_zero, norm_zero, le_refl]
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hc : cappedInverseDistancePow (m + 1) ε (0, h) ≤
      inverseDistancePow (m + 1) 0 h := by
    simp only [cappedInverseDistancePow, inverseDistancePow, dist_zero_left]
    exact inv_anti₀ (pow_pos hn _) (pow_le_pow_left₀ hn.le (le_max_right _ _) _)
  simp only [symmetricScalarCappedTestKernel, symmetricScalarRieszTestKernel, norm_mul,
    Real.norm_of_nonneg (cappedInverseDistancePow_nonneg _ _ _),
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  exact mul_le_mul_of_nonneg_right hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end

end RieszRectifiability

end OAI
