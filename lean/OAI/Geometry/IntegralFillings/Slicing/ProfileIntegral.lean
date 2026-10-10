import Mathlib
import OAI.Geometry.IntegralFillings.Slicing.Profiles

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SharpIntegralFillings.SmoothCutoff
open Set MeasureTheory Filter Metric
open scoped Topology NNReal

lemma dprofile_integrable {a : ℝ≥0} (ha : 0 < a) (t : ℝ) :
    Integrable (dprofile a t) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  have hc := (hC a t).2.1.continuous
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro isCompact_Icc
  exact fun x hx => dprofile_zero ha hx

lemma integral_dprofile {a : ℝ≥0} (ha : 0 < a) (t : ℝ) :
    (∫ x : ℝ, dprofile a t x) = 1 := by
  have ha' : 0 < (a:ℝ) := ha
  obtain ⟨C,hC⟩ := exists_profile_bounds
  have hc := (hC a t).2.1.continuous
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => dprofile_zero ha hx),
    integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (show t ≤ t+(a:ℝ)⁻¹ from le_add_of_nonneg_right (inv_nonneg.mpr ha'.le)),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => profile_hasDerivAt a t x)
      (hc.intervalIntegrable _ _)]
  simp [profile,ha'.ne',Real.smoothTransition.one_of_one_le]

lemma dprofile_mul_integrable {f : ℝ → ℝ} (hf : Integrable f) (a : ℝ≥0) (t : ℝ) :
    Integrable (fun x => dprofile a t x * f x) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  exact hf.bdd_mul (hC a t).2.1.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (hC a t).2.2 x)

theorem ae_tendsto_dprofile_integral {f : ℝ → ℝ} (hf : Integrable f) :
    ∀ᵐ t : ℝ, Tendsto (fun n : ℕ => ∫ x : ℝ,
      dprofile ((n:ℝ≥0)+1) t x * f x) atTop (𝓝 (f t)) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  let a : ℕ → ℝ≥0 := fun n => (n:ℝ≥0)+1
  let r : ℕ → ℝ := fun n => ((a n:ℝ))⁻¹
  have hap n : 0 < a n := by dsimp [a]; positivity
  have harp n : 0 < (a n:ℝ) := hap n
  have hrp n : 0 < r n := inv_pos.mpr (harp n)
  have hrt : Tendsto r atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall fun n => hrp n⟩
    exact tendsto_inv_atTop_zero.comp
      (show Tendsto (fun n : ℕ => (a n:ℝ)) atTop atTop from by
        simpa only [a,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using
          tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hf.locallyIntegrable 0]
    with t ht
  have hav := ht (fun _ : ℕ => t) r hrt
    (Eventually.of_forall fun n => by simp only [zero_mul]; exact mem_closedBall_self le_rfl)
  have hbound n : ‖(∫ x : ℝ, dprofile (a n) t x * f x)-f t‖ ≤
      (2*(C:ℝ)) * (⨍ x in closedBall t (r n), ‖f x-f t‖) := by
    have hk := dprofile_integrable (hap n) t
    have hprod := dprofile_mul_integrable hf (a n) t
    have heq : (∫ x : ℝ, dprofile (a n) t x * f x)-f t =
        ∫ x : ℝ, dprofile (a n) t x * (f x-f t) := by
      simp only [mul_sub,integral_sub hprod (hk.mul_const _),integral_mul_const,
        integral_dprofile (hap n),one_mul]
    rw [heq]
    have herr : Integrable (fun x : ℝ => dprofile (a n) t x * (f x-f t)) := by
      apply (hprod.sub (hk.mul_const (f t))).congr
      filter_upwards [] with x
      exact (mul_sub _ _ _).symm
    have hnz (x : ℝ) (hx : x ∉ closedBall t (r n)) : dprofile (a n) t x = 0 := by
      apply dprofile_zero (hap n)
      intro hi
      apply hx
      rw [Real.closedBall_eq_Icc]
      change t-r n ≤ x ∧ x ≤ t+r n
      exact ⟨by linarith [hi.1,hrp n],hi.2⟩
    have hloc : IntegrableOn (fun x : ℝ => ‖f x-f t‖) (closedBall t (r n)) :=
      (hf.integrableOn.sub (integrableOn_const (measure_closedBall_lt_top.ne))).norm
    calc
      ‖∫ x : ℝ, dprofile (a n) t x * (f x-f t)‖ ≤
          ∫ x : ℝ, ‖dprofile (a n) t x * (f x-f t)‖ := norm_integral_le_integral_norm _
      _ = ∫ x in closedBall t (r n), ‖dprofile (a n) t x * (f x-f t)‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hnz x hx,zero_mul,norm_zero])).symm
      _ ≤ ∫ x in closedBall t (r n), ((C:ℝ)*(a n:ℝ)) * ‖f x-f t‖ := by
        apply setIntegral_mono_on herr.norm.integrableOn (hloc.const_mul _) isClosed_closedBall.measurableSet
        intro x _
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [Real.norm_eq_abs,NNReal.coe_mul] using (hC (a n) t).2.2 x
      _ = (2*(C:ℝ)) * (⨍ x in closedBall t (r n), ‖f x-f t‖) := by
        rw [integral_const_mul,setAverage_eq,Real.volume_real_closedBall (hrp n).le,
          smul_eq_mul]
        dsimp [r]
        field_simp
  have hzero := squeeze_zero_norm hbound (by simpa only [mul_zero] using hav.const_mul (2*(C:ℝ)))
  simpa only [sub_add_cancel,zero_add] using hzero.add_const (f t)

end SharpIntegralFillings.SmoothCutoff
end

end OAI
