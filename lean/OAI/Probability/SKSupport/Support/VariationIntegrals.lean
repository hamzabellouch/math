import Mathlib
import OAI.Probability.SKSupport.Moments.PerturbationLimits

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def normalizedValueDifference (W : BrownianSystem Ω) (γ β : OrderParameter) (n : ℕ) : ℝ :=
  (value W (perturbation γ β n) 0 0-value W γ 0 0)/variationStep n

def variationTail (γ β : OrderParameter) (T : ℝ) : ℝ :=
  ∫ s in T..1, |extend β.val s-extend γ.val s|

lemma variationTail_nonneg (γ β : OrderParameter) {T : ℝ} (hT : T ≤ 1) : 0 ≤ variationTail γ β T :=
  intervalIntegral.integral_nonneg hT (fun _ _ => abs_nonneg _)

lemma variationTail_limit (γ β : OrderParameter) :
    Tendsto (fun n => variationTail γ β (diffusionHorizon n)) atTop (𝓝 0) := by
  let f := fun s => |extend β.val s-extend γ.val s|
  have hi : Integrable f := (β.integrable.sub γ.integrable).abs
  have he (n : ℕ) : variationTail γ β (diffusionHorizon n)=
      (∫ s in (0:ℝ)..1, f s)-(∫ s in (0:ℝ)..diffusionHorizon n, f s) := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := diffusionHorizon n))
      (hi.intervalIntegrable (a := diffusionHorizon n) (b := 1))
    change _ + variationTail γ β (diffusionHorizon n)=_ at hh
    linarith
  have hc := (hi.continuous_primitive 0).tendsto (1:ℝ) |>.comp diffusionHorizon_tendsto
  simpa only [he,sub_self,Function.comp_apply] using tendsto_const_nhds.sub hc (a := ∫ s in (0:ℝ)..1, f s)

lemma mixedQ_weighted_limit (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) :
    Tendsto (fun n => ∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*mixedQ W (perturbation γ β n) γ T s)
      atTop (𝓝 (∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s)) := by
  simp only [intervalIntegral.integral_of_le T.property.1]
  apply tendsto_integral_of_dominated_convergence (fun s => |extend β.val s-extend γ.val s|)
  · intro n
    exact ((β.measurable_extend.sub γ.measurable_extend).mul (mixedQ_continuous W (perturbation γ β n) γ T).measurable).aestronglyMeasurable
  · exact (β.integrable.sub γ.integrable).abs.integrableOn
  · intro n
    filter_upwards [] with s
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mixedQ_bounds W (perturbation γ β n) γ T s).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (mixedQ_bounds W (perturbation γ β n) γ T s).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (mixedQ_perturbation_limit W γ β T ⟨hs.1.le,hs.2⟩).const_mul _

lemma normalizedValueDifference_truncation (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) :
    |normalizedValueDifference W γ β n-(1/2:ℝ)*(∫ s in (0:ℝ)..(T:ℝ),
      (extend β.val s-extend γ.val s)*mixedQ W (perturbation γ β n) γ T s)| ≤ (3/2:ℝ)*variationTail γ β T := by
  let R := (differenceField W (perturbation γ β n) γ T.property.1 T.property.2).expected
    (mixedStripDrift W (perturbation γ β n) γ T) W T
  let I := ∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*mixedQ W (perturbation γ β n) γ T s
  have he := mixed_difference_integral W (perturbation γ β n) γ T
  simp only [perturbation_diff,mul_assoc,intervalIntegral.integral_const_mul] at he
  change value W (perturbation γ β n) 0 0-value W γ 0 0=R+(1/2:ℝ)*(variationStep n*I) at he
  have hb := mixed_difference_terminal_bound W (perturbation γ β n) γ T
  simp only [perturbation_diff,abs_mul,abs_of_nonneg (variationStep_pos n).le,intervalIntegral.integral_const_mul] at hb
  change |R| ≤ (3/2:ℝ)*(variationStep n*variationTail γ β T) at hb
  change |normalizedValueDifference W γ β n-(1/2:ℝ)*I| ≤ _
  have hid : normalizedValueDifference W γ β n-(1/2:ℝ)*I=R/variationStep n := by
    unfold normalizedValueDifference
    rw [he]
    field_simp [(variationStep_pos n).ne']
    ring
  rw [hid,abs_div,abs_of_pos (variationStep_pos n)]
  apply (div_le_iff₀ (variationStep_pos n)).mpr
  nlinarith only [hb]

lemma weighted_square_tail_bound (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) :
    |∫ s in (T:ℝ)..1, (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s| ≤ variationTail γ β T := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le T.property.2.le _ ((β.integrable.sub γ.integrable).abs.intervalIntegrable)
  filter_upwards [] with s hs
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (squareMoment_bounds W γ hs.2).2

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

lemma normalizedValueDifference_limit (W : BrownianSystem Ω) (γ β : OrderParameter) :
    Tendsto (normalizedValueDifference W γ β) atTop
      (𝓝 ((1/2:ℝ)*(∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k,hk⟩ := ((variationTail_limit γ β).eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/8))).exists
  let T := diffusionHorizonTime k
  have htail : variationTail γ β T < ε/8 := hk
  let I (n : ℕ) := (1/2:ℝ)*(∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*mixedQ W (perturbation γ β n) γ T s)
  let J := (1/2:ℝ)*(∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s)
  let K := (1/2:ℝ)*(∫ s in (T:ℝ)..1, (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s)
  let L := (1/2:ℝ)*(∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s)
  have hIL : Tendsto I atTop (𝓝 J) := (mixedQ_weighted_limit W γ β T).const_mul (1/2:ℝ)
  have hi := squareMoment_weighted_integrable W γ (β.integrable.sub γ.integrable)
  have hi0 : IntervalIntegrable (fun s => (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s) volume 0 T :=
    hi.mono_set (by rw [uIcc_of_le T.property.1,uIcc_of_le (by norm_num : (0:ℝ)≤1)];exact Icc_subset_Icc le_rfl T.property.2.le)
  have hi1 : IntervalIntegrable (fun s => (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s) volume T 1 :=
    hi.mono_set (by rw [uIcc_of_le T.property.2.le,uIcc_of_le (by norm_num : (0:ℝ)≤1)];exact Icc_subset_Icc T.property.1 le_rfl)
  have hL : L=J+K := by
    have hh := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
    dsimp only [L,J,K]
    rw [← hh,mul_add]
  have hK : |K| ≤ (1/2:ℝ)*variationTail γ β T := by
    dsimp only [K]
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    exact mul_le_mul_of_nonneg_left (weighted_square_tail_bound W γ β T) (by norm_num)
  filter_upwards [(Metric.tendsto_nhds.mp hIL) (ε/2) (by linarith)] with n hn
  change |normalizedValueDifference W γ β n-L| < ε
  have h1 := normalizedValueDifference_truncation W γ β T n
  change |normalizedValueDifference W γ β n-I n| ≤ (3/2:ℝ)*variationTail γ β T at h1
  rw [Real.dist_eq] at hn
  have hh := abs_sub_le (normalizedValueDifference W γ β n) (I n) L
  have hh' := abs_sub_le (I n) J L
  have hJL : |J-L|=|K| := by rw [hL];ring_nf;rw [abs_neg]
  rw [hJL] at hh'
  linarith

lemma penalty_integrable (γ : OrderParameter) :
    IntervalIntegrable (fun s : ℝ => s*extend γ.val s) volume 0 1 := by
  have hh := γ.integrable.intervalIntegrable (a := (0:ℝ)) (b := 1) |>.mul_continuousOn continuousOn_id
  simpa only [id_eq,mul_comm] using hh

lemma penalty_difference (γ β : OrderParameter) (n : ℕ) :
    (∫ s in (0:ℝ)..1, s*extend (perturbation γ β n).val s)-(∫ s in (0:ℝ)..1, s*extend γ.val s)=
      variationStep n*(∫ s in (0:ℝ)..1, s*(extend β.val s-extend γ.val s)) := by
  rw [← intervalIntegral.integral_sub (penalty_integrable _) (penalty_integrable _),← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change s*extend (perturbation γ β n).val s-s*extend γ.val s=variationStep n*(s*(extend β.val s-extend γ.val s))
  rw [← mul_sub,perturbation_diff]
  ring

lemma normalizedParisiDifference_eq (W : BrownianSystem Ω) (γ β : OrderParameter) (n : ℕ) :
    (parisi W (perturbation γ β n)-parisi W γ)/variationStep n=
      normalizedValueDifference W γ β n-(1/2:ℝ)*(∫ s in (0:ℝ)..1, s*(extend β.val s-extend γ.val s)) := by
  have he := penalty_difference γ β n
  have hn := (variationStep_pos n).ne'
  unfold parisi normalizedValueDifference
  field_simp [hn]
  nlinarith only [he]

theorem parisi_chord_derivative (W : BrownianSystem Ω) (γ β : OrderParameter) :
    Tendsto (fun n => (parisi W (perturbation γ β n)-parisi W γ)/variationStep n) atTop
      (𝓝 ((1/2:ℝ)*(∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*(squareMoment W γ (diffusion W γ) s-s)))) := by
  have hiq := squareMoment_weighted_integrable W γ (β.integrable.sub γ.integrable)
  have hit : IntervalIntegrable (fun s => (extend β.val s-extend γ.val s)*s) volume 0 1 :=
    (β.integrable.sub γ.integrable).intervalIntegrable.mul_continuousOn continuousOn_id
  change IntervalIntegrable (fun s => (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s) volume 0 1 at hiq
  have he : (1/2:ℝ)*(∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s)-
      (1/2:ℝ)*(∫ s in (0:ℝ)..1, s*(extend β.val s-extend γ.val s))=
      (1/2:ℝ)*(∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*(squareMoment W γ (diffusion W γ) s-s)) := by
    rw [← mul_sub,← intervalIntegral.integral_sub hiq (by simpa only [id_eq,mul_comm] using hit)]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    ring
  simpa only [normalizedParisiDifference_eq,he] using
    (normalizedValueDifference_limit W γ β).sub_const ((1/2:ℝ)*(∫ s in (0:ℝ)..1, s*(extend β.val s-extend γ.val s)))

theorem minimizer_variational_inequality (W : BrownianSystem Ω) (γ : OrderParameter)
    (hmin : IsMinimizer W γ) (β : OrderParameter) :
    0 ≤ ∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*(squareMoment W γ (diffusion W γ) s-s) := by
  have hz := ge_of_tendsto (parisi_chord_derivative W γ β) (Eventually.of_forall (fun n =>
    div_nonneg (sub_nonneg.mpr (hmin (perturbation γ β n))) (variationStep_pos n).le))
  linarith

end ZeroTemperatureSK

end
end

end OAI
