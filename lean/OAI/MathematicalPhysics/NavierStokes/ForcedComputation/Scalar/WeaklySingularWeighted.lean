import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.WeaklySingularOperator
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! Integrable majorants and exponential damping of weakly singular Volterra operators. -/

noncomputable section
namespace ForcedComputation.WeaklySingular

open Real MeasureTheory Set Filter
open scoped Topology Interval

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Any integrable nonnegative kernel majorant bounds the path operator norm. -/
theorem norm_integralOperator_le_integral {T : ℝ} (hT : 0 ≤ T)
    (K : ℝ → E →L[ℝ] E) (hK : ContinuousOn K (Ioi 0))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r)
    (b : ℝ → ℝ) (hbi : IntervalIntegrable b volume 0 T)
    (hb : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hKb : ∀ r ∈ Icc 0 T, ‖K r‖ ≤ b r) :
    ‖integralOperator E hT K hK C hC hbound‖ ≤ ∫ r in 0..T, b r := by
  have hmass : 0 ≤ ∫ r in 0..T, b r := intervalIntegral.integral_nonneg hT hb
  refine (integralOperator E hT K hK C hC hbound).opNorm_le_bound hmass ?_
  intro u
  rw [← (pathEquiv E T).norm_map (integralOperator E hT K hK C hC hbound u)]
  apply (ContinuousMap.norm_le _ (mul_nonneg hmass (norm_nonneg u))).mpr
  intro t
  change ‖∫ s in 0..t.val, K (t.val - s) (extendPath E hT u s)‖ ≤ _
  have hbt : IntervalIntegrable b volume 0 t.val := hbi.mono_set <| by
    rw [uIcc_of_le t.property.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl t.property.2
  have hbs : IntervalIntegrable (fun s => b (t.val - s)) volume 0 t.val := by
    simpa only [sub_zero, sub_self] using (hbt.comp_sub_left t.val).symm
  calc
    _ ≤ ∫ s in 0..t.val, b (t.val - s) * ‖u‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le t.property.1 _ (hbs.mul_const ‖u‖)
      exact ae_of_all _ fun s hs => by
        have hr : t.val - s ∈ Icc (0 : ℝ) T :=
          ⟨sub_nonneg.mpr hs.2, (sub_le_self _ hs.1.le).trans t.property.2⟩
        exact ((K (t.val - s)).le_opNorm _).trans <|
          mul_le_mul (hKb _ hr) (norm_extendPath_le E hT u s) (norm_nonneg _) (hb _ hr)
    _ = (∫ r in 0..t.val, b r) * ‖u‖ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_left,
        sub_self, sub_zero]
    _ ≤ (∫ r in 0..T, b r) * ‖u‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
      exact intervalIntegral.integral_mono_interval le_rfl t.property.1 t.property.2
        ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => hb r ⟨hr.1.le, hr.2⟩) hbi

/-- The scalar majorant after exponential time weighting. -/
def weightedProfile (rate r : ℝ) : ℝ := Real.exp (-rate * r) * inverseSqrt r

theorem weightedProfile_nonneg (rate r : ℝ) : 0 ≤ weightedProfile rate r :=
  mul_nonneg (Real.exp_pos _).le (inverseSqrt_nonneg r)

theorem weightedProfile_integrable {T : ℝ} (hT : 0 ≤ T) (rate : ℝ) :
    IntervalIntegrable (weightedProfile rate) volume 0 T :=
  (inverseSqrt_intervalIntegrable hT).continuousOn_mul
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)

theorem weightedProfile_le {rate r : ℝ} (hrate : 0 ≤ rate) (hr : 0 ≤ r) :
    weightedProfile rate r ≤ inverseSqrt r := by
  unfold weightedProfile
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrate) hr))
    (inverseSqrt_nonneg r)).trans_eq (one_mul _)

/-- On every finite interval the exponentially weighted singular mass tends to zero. -/
theorem weightedProfile_integral_tendsto {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun rate : ℝ => ∫ r in 0..T, weightedProfile rate r) atTop (𝓝 0) := by
  have hh := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := (0 : ℝ)) (b := T) (μ := volume) (l := atTop)
    (F := fun rate r : ℝ => weightedProfile rate r) (f := fun _ => (0 : ℝ))
    inverseSqrt
    (Eventually.of_forall fun rate =>
      (weightedProfile_integrable hT rate).aestronglyMeasurable_restrict_uIoc)
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with rate hrate
      exact ae_of_all _ fun r hr => by
        rw [uIoc_of_le hT] at hr
        simpa only [Real.norm_eq_abs, abs_of_nonneg (weightedProfile_nonneg rate r)] using
          weightedProfile_le hrate hr.1.le)
    (inverseSqrt_intervalIntegrable hT)
    (ae_of_all _ fun r hr => by
      rw [uIoc_of_le hT] at hr
      have he : Tendsto (fun rate : ℝ => Real.exp (-rate * r)) atTop (𝓝 0) := by
        simpa only [neg_mul, Function.comp_def, id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
          ((tendsto_id : Tendsto (fun rate : ℝ => rate) atTop atTop).atTop_mul_const hr.1)
      simpa only [weightedProfile, zero_mul] using he.mul_const (inverseSqrt r))
  simpa only [intervalIntegral.integral_zero] using hh

/-- Exponential conjugation changes only the time kernel. -/
def weightedKernel (rate : ℝ) (K : ℝ → E →L[ℝ] E) (r : ℝ) : E →L[ℝ] E :=
  Real.exp (-rate * r) • K r

theorem weightedKernel_continuous (rate : ℝ) (K : ℝ → E →L[ℝ] E)
    (hK : ContinuousOn K (Ioi 0)) : ContinuousOn (weightedKernel E rate K) (Ioi 0) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.smul hK)

theorem weightedKernel_bound {rate C : ℝ} (hrate : 0 ≤ rate) (hC : 0 ≤ C)
    (K : ℝ → E →L[ℝ] E) (hK : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r) :
    ∀ r, 0 ≤ r → ‖weightedKernel E rate K r‖ ≤ C * inverseSqrt r := by
  intro r hr
  calc
    _ = Real.exp (-rate * r) * ‖K r‖ := by
      rw [weightedKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-rate * r) * (C * inverseSqrt r) :=
      mul_le_mul_of_nonneg_left (hK r hr) (Real.exp_pos _).le
    _ = C * weightedProfile rate r := by unfold weightedProfile; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weightedProfile_le hrate hr) hC

theorem norm_weightedIntegralOperator_le {T rate C : ℝ} (hT : 0 ≤ T) (hrate : 0 ≤ rate)
    (K : ℝ → E →L[ℝ] E) (hK : ContinuousOn K (Ioi 0)) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r) :
    ‖integralOperator E hT (weightedKernel E rate K) (weightedKernel_continuous E rate K hK)
      C hC (weightedKernel_bound E hrate hC K hbound)‖ ≤
      C * ∫ r in 0..T, weightedProfile rate r := by
  rw [← intervalIntegral.integral_const_mul]
  apply norm_integralOperator_le_integral E hT _ _ C hC _ _
    ((weightedProfile_integrable hT rate).const_mul C)
    (fun r _ => mul_nonneg hC (weightedProfile_nonneg rate r))
  intro r hr
  calc
    _ = Real.exp (-rate * r) * ‖K r‖ := by
      rw [weightedKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-rate * r) * (C * inverseSqrt r) :=
      mul_le_mul_of_nonneg_left (hbound r hr.1) (Real.exp_pos _).le
    _ = _ := by unfold weightedProfile; ring

/-- Weighting makes the Volterra operator arbitrarily small without shortening the interval. -/
theorem exists_weightedIntegralOperator_norm_lt {T C : ℝ} (hT : 0 ≤ T)
    (K : ℝ → E →L[ℝ] E) (hK : ContinuousOn K (Ioi 0)) (hC : 0 ≤ C)
    (hbound : ∀ r, 0 ≤ r → ‖K r‖ ≤ C * inverseSqrt r) {q : ℝ} (hq : 0 < q) :
    ∃ rate : ℝ, ∃ hrate : 0 ≤ rate,
      ‖integralOperator E hT (weightedKernel E rate K) (weightedKernel_continuous E rate K hK)
        C hC (weightedKernel_bound E hrate hC K hbound)‖ < q := by
  have ht : Tendsto (fun rate : ℝ => C * ∫ r in 0..T, weightedProfile rate r)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (weightedProfile_integral_tendsto hT).const_mul C
  have he := (tendsto_order.1 ht).2 q hq
  obtain ⟨rate, hrate, hsmall⟩ := (eventually_ge_atTop (0 : ℝ)).and he |>.exists
  exact ⟨rate, hrate, (norm_weightedIntegralOperator_le E hT hrate K hK hC hbound).trans_lt hsmall⟩

end ForcedComputation.WeaklySingular

end

end OAI
