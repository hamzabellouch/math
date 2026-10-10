import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.Sobolev

theorem abs_two_mul_le_squares (a b : ℝ) : |2 * a * b| ≤ a^2 + b^2 := by
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]

theorem square_difference_le_interval_energy
    {f df : ℝ → ℝ} {a b x v : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t)
    (hx : x ∈ Icc a b) (hv : v ∈ Icc a b) :
    f x ^ 2 - f v ^ 2 ≤ ∫ t in a..b, (f t ^ 2 + df t ^ 2) := by
  have hsub : uIcc v x ⊆ Icc a b := uIcc_subset_Icc hv hx
  have hsq (t : ℝ) (ht : t ∈ uIcc v x) :
      HasDerivAt (fun r => f r ^ 2) (2 * f t * df t) t := by
    convert (hd t (hsub ht)).pow 2 using 1
    norm_num
  have hcd : ContinuousOn (fun t => 2 * f t * df t) (uIcc v x) :=
    ((continuousOn_const.mul hf).mul hdf).mono hsub
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hsq hcd.intervalIntegrable
  have hE : ContinuousOn (fun t => f t ^ 2 + df t ^ 2) (Icc a b) :=
    (hf.pow 2).add (hdf.pow 2)
  have hbound : ∀ᵐ t ∂volume.restrict (uIoc v x),
      ‖2 * f t * df t‖ ≤ f t ^ 2 + df t ^ 2 :=
    Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using abs_two_mul_le_squares (f t) (df t))
  have hnorm := intervalIntegral.norm_integral_le_abs_of_norm_le hbound
    ((hE.mono hsub).intervalIntegrable)
  have hu : uIoc v x ⊆ uIoc a b :=
    uIoc_subset_uIoc_of_uIcc_subset_uIcc (by simpa only [uIcc_of_le hab] using hsub)
  have hnonneg : ∀ᵐ t ∂volume.restrict (uIoc a b), 0 ≤ f t ^ 2 + df t ^ 2 :=
    Filter.Eventually.of_forall (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hmono := intervalIntegral.abs_integral_mono_interval hu hnonneg
    (hE.intervalIntegrable_of_Icc hab)
  have hI : 0 ≤ ∫ t in a..b, (f t ^ 2 + df t ^ 2) :=
    intervalIntegral.integral_nonneg_of_forall hab
      (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hFTC, Real.norm_eq_abs] at hnorm
  rw [abs_of_nonneg hI] at hmono
  exact (le_abs_self _).trans (hnorm.trans hmono)

theorem interval_point_square_bound
    {f df : ℝ → ℝ} {a b x : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t) (hx : x ∈ Icc a b) :
    f x ^ 2 ≤ (1 + 1 / (b - a)) * (∫ t in a..b, f t ^ 2) +
      ∫ t in a..b, df t ^ 2 := by
  let E : ℝ := ∫ t in a..b, (f t ^ 2 + df t ^ 2)
  have hpoint : ∀ v ∈ Icc a b, f x ^ 2 ≤ f v ^ 2 + E := by
    intro v hv
    have h := square_difference_le_interval_energy hab.le hf hdf hd hx hv
    dsimp only [E]
    linarith
  have hfi : IntervalIntegrable (fun t => f t^2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc hab.le
  have hdi : IntervalIntegrable (fun t => df t^2) volume a b :=
    (hdf.pow 2).intervalIntegrable_of_Icc hab.le
  have havg := intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f x ^ 2) volume a b)
    (hfi.add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add hfi intervalIntegrable_const] at havg
  simp only [intervalIntegral.integral_const, smul_eq_mul] at havg
  have hE : E = (∫ t in a..b, f t ^ 2) + ∫ t in a..b, df t ^ 2 := by
    exact intervalIntegral.integral_add hfi hdi
  rw [hE] at havg
  have hw : 0 < b - a := sub_pos.mpr hab
  have hi : (b - a) * (1 / (b - a)) = 1 := by field_simp [ne_of_gt hw]
  have hiscale := congrArg (fun r : ℝ => r * (∫ t in a..b, f t ^ 2)) hi
  have hscaled : (b - a) * (f x^2) ≤ (b - a) *
      ((1 + 1 / (b - a)) * (∫ t in a..b, f t^2) + ∫ t in a..b, df t^2) := by
    nlinarith only [havg, hiscale]
  exact le_of_mul_le_mul_left hscaled hw

end SmoothLocal.Sobolev

end

end OAI
