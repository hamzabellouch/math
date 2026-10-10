import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! The variable-coefficient integral estimate needed for the WKB residual.
Only its integral, rather than its supremum times the interval length, enters. -/

open Set MeasureTheory
namespace DefocusingNLS

private theorem primitive_deriv (a b : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (r : ℝ) (hr : r ∈ Ioo a b) :
    HasDerivAt (fun s => ∫ t in a..s, f t) (f r) r := by
  have hi : IntervalIntegrable f volume a r := ContinuousOn.intervalIntegrable_of_Icc hr.1.le
    (hf.mono (Icc_subset_Icc le_rfl hr.2.le))
  exact intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hf.mono Ioo_subset_Icc_self) r hr)
    (hf.continuousAt (Icc_mem_nhds hr.1 hr.2))

private theorem primitive_continuous (a b : ℝ) (hab : a≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    ContinuousOn (fun s => ∫ t in a..s, f t) (Icc a b) := by
  have hi : IntervalIntegrable f volume a b := ContinuousOn.intervalIntegrable_of_Icc hab hf
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (show a ∈ uIcc a b from left_mem_uIcc)
  rwa [uIcc_of_le hab] at hc

theorem spectral_integral_gronwall (a b A : ℝ) (hab : a≤ b) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg0 : ∀ r ∈ Icc a b, 0≤ g r)
    (hbound : ∀ r ∈ Icc a b, f r≤ A+∫ t in a..r, g t*f t) :
    ∀ r ∈ Icc a b, f r≤ A*Real.exp (∫ t in a..r, g t) := by
  let P := fun r => ∫ t in a..r, g t
  let F := fun r => A+∫ t in a..r, g t*f t
  let Z := fun r => Real.exp (-P r)*F r
  have hPc : ContinuousOn P (Icc a b) := primitive_continuous a b hab g hg
  have hFc : ContinuousOn F (Icc a b) := continuousOn_const.add
    (primitive_continuous a b hab _ (hg.mul hf))
  have hZc : ContinuousOn Z (Icc a b) :=
    (Real.continuous_exp.comp_continuousOn hPc.neg).mul hFc
  have hZD (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt Z (Real.exp (-P r)*g r*(f r-F r)) r := by
    have hp := primitive_deriv a b g hg r hr
    have hF := (primitive_deriv a b _ (hg.mul hf) r hr).const_add A
    apply (hp.neg.exp.mul hF).congr_deriv
    dsimp only [F,P,Pi.neg_apply,Pi.mul_apply]
    ring
  have hanti : AntitoneOn Z (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hZc
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      exact (hZD r hr').differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      rw [(hZD r hr').deriv]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (Real.exp_pos _).le (hg0 r ⟨hr'.1.le,hr'.2.le⟩))
        (sub_nonpos.mpr (hbound r ⟨hr'.1.le,hr'.2.le⟩))
  intro r hr
  have hz := hanti ⟨le_rfl,hab⟩ hr hr.1
  have hza : Z a=A := by simp only [Z,P,F,intervalIntegral.integral_same,neg_zero,Real.exp_zero,add_zero,one_mul]
  rw [hza] at hz
  have hmul : F r≤ A*Real.exp (P r) := by
    have hh := mul_le_mul_of_nonneg_left hz (Real.exp_pos (P r)).le
    have he : Real.exp (P r)*Real.exp (-P r)=1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
    change Real.exp (P r)*(Real.exp (-P r)*F r)≤ Real.exp (P r)*A at hh
    rw [← mul_assoc,he,one_mul] at hh
    simpa only [mul_comm] using hh
  exact (hbound r hr).trans hmul

end DefocusingNLS

end OAI
