import OAI.Analysis.CircleDomains.Modulus.LinePayment

namespace OAI

/-! The smooth line estimate for a non-unit oscillation. This allows
uniform mollifications of a continuous Sobolev barrier to retain a
positive crossing cost without assuming an ACL theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_line_oscillation {f : ℝ → ℝ} {a b c : ℝ}
    (hf : ContDiff ℝ 1 f) (hc : c ∈ Icc a b) :
    (f c-f a)^2 ≤ (b-a)*(∫ x in a..b, deriv f x^2) := by
  have hi : IntervalIntegrable (deriv f) volume a b := hf.continuous_deriv_one.intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun x => deriv f x^2) volume a b := (hf.continuous_deriv_one.pow 2).intervalIntegrable a b
  have hsub : uIcc a c ⊆ uIcc a b :=
    uIcc_subset_uIcc_left (by simpa [uIcc_of_le (hc.1.trans hc.2)] using hc)
  have hiac := hi.mono_set hsub
  have hi2ac := hi2.mono_set hsub
  have hFTC : (∫ x in a..c, deriv f x) = f c-f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc.1
      (hf.continuous.continuousOn.mono (Icc_subset_Icc le_rfl hc.2))
      (fun x _ => (hf.differentiable_one x).hasDerivAt) hiac
  have hmono : (∫ x in a..c, deriv f x^2) ≤ ∫ x in a..b, deriv f x^2 :=
    intervalIntegral.integral_mono_interval le_rfl hc.1 hc.2
      (Eventually.of_forall (fun x => sq_nonneg (deriv f x))) hi2
  have henergy : 0 ≤ ∫ x in a..b, deriv f x^2 :=
    intervalIntegral.integral_nonneg_of_forall (hc.1.trans hc.2) (fun x => sq_nonneg _)
  calc
    _ = (∫ x in a..c, deriv f x)^2 := by rw [hFTC]
    _ ≤ (c-a)*(∫ x in a..c, deriv f x^2) := integral_sq_le_length_mul_integral_sq hc.1 hiac hi2ac
    _ ≤ (c-a)*(∫ x in a..b, deriv f x^2) := mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hc.1)
    _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_right hc.2 a) henergy

 theorem smooth_line_half_payment {f : ℝ → ℝ} {L c : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hc : c ∈ Icc (-L) L)
    (hosc : (1:ℝ)/2 ≤ f c-f (-L)) :
    1/(8*L) ≤ ∫ x in (-L)..L, deriv f x^2 := by
  have h := smooth_line_oscillation hf hc
  have hs : (1:ℝ)/4 ≤ (f c-f (-L))^2 := by
    nlinarith only [hosc,sq_nonneg (f c-f (-L)-1/2)]
  apply (div_le_iff₀ (by positivity : 0 < 8*L)).mpr
  nlinarith only [h,hs]

end CircleDomainRigidity

end

end OAI
