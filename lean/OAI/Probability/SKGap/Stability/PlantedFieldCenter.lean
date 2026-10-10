import Mathlib
import OAI.Probability.SKGap.Stability.GaugedField
import OAI.Probability.SKGap.Gaussian.SubgaussianAbsTail

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
namespace SKGapCutoff.Regression

lemma continuous_gaugedField {n : ℕ} (x : Spin n) : Continuous (gaugedField x) := by
  rw [show gaugedField x = fun g => gaugeFieldCLM x (fun p => sampledInteraction g p.1 p.2) by
    funext g; exact (gaugeFieldCLM_sampled x g).symm]
  exact (gaugeFieldCLM x).continuous.comp (continuous_pi fun p =>
    (continuous_apply p.2).comp ((continuous_apply p.1).comp (continuous_sampledInteraction n)))

noncomputable def plantedFieldCenter (β : ℝ) (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ z, f (β^2*((n:ℝ)-1)/(n:ℝ) + β*Real.sqrt (((n:ℝ)-2)/(n:ℝ))*z)
    ∂gaussianReal 0 1

lemma planted_field_average_tail (β : ℝ) {n : ℕ} (hn : 2 ≤ n) (x : Spin n)
    (f : ℝ → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, |f z| ≤ B)
    (ε : ℝ) (hε : 0 ≤ ε) :
    singleSpinPlantedLaw β x {g |
      ε ≤ |(∑ i : Fin n, f (gaugedField x g i))/(n:ℝ) - plantedFieldCenter β n f|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(8*B^2))) +
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(8*(K:ℝ)^2*β^2))) := by
  let E := {v : Fin n → ℝ |
    ε ≤ |(∑ i, f (v i))/(n:ℝ) - plantedFieldCenter β n f|}
  have hE : MeasurableSet E := by
    apply measurableSet_le measurable_const
    exact (((Finset.measurable_sum _ (fun i _ =>
      hf.continuous.measurable.comp (measurable_pi_apply i))).div_const _).sub_const _).abs
  have hl := planted_field_representation β hn x
  have hh := congrArg (fun μ : Measure (Fin n → ℝ) => μ E) hl
  rw [Measure.map_apply (continuous_gaugedField x).measurable hE,
    Measure.map_apply (by
      unfold sharedGaussianField
      exact Measurable.of_eval fun i =>
        (measurable_const.add (measurable_const.mul (measurable_pi_apply _))).add
          (measurable_const.mul (measurable_pi_apply _))) hE] at hh
  change singleSpinPlantedLaw β x ((gaugedField x) ⁻¹' E) ≤ _
  rw [hh]
  have ht := iid_common_shift_average_tail (n := n) (by omega)
    (β^2*((n:ℝ)-1)/(n:ℝ)) (β*Real.sqrt (((n:ℝ)-2)/(n:ℝ)))
    (β/Real.sqrt (n:ℝ)) f hf B hB hbound ε hε
  convert ht using 1
  congr 3
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [div_pow, Real.sq_sqrt hnR.le]
  field_simp

lemma planted_field_center_limit (β : ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (B : ℝ) (hbound : ∀ z, |f z| ≤ B) :
    Tendsto (fun n => plantedFieldCenter β n f) atTop
      (nhds (∫ z, f (β^2+β*z) ∂gaussianReal 0 1)) := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hfrac (c : ℝ) : Tendsto (fun n : ℕ => ((n:ℝ)-c)/(n:ℝ)) atTop (nhds 1) := by
    have ht := (tendsto_const_nhds (x := (1:ℝ))).sub (hn.const_mul c)
    simp only [mul_zero, sub_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    field_simp
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro n
    exact (hf.measurable.comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
  · exact integrable_const B
  · intro n
    exact Eventually.of_forall (fun z => by simpa using hbound _)
  · apply Eventually.of_forall
    intro z
    apply hf.continuousAt.tendsto.comp
    have hm : Tendsto (fun n : ℕ => β^2*((n:ℝ)-1)/(n:ℝ)) atTop (nhds (β^2)) := by
      simpa only [mul_one, mul_div_assoc] using (hfrac 1).const_mul (β^2)
    have ha := (Real.continuous_sqrt.continuousAt.tendsto.comp (hfrac 2)).const_mul β
    simp only [Real.sqrt_one, mul_one] at ha
    exact hm.add (ha.mul_const z)

lemma planted_field_average_exponential (β : ℝ) (hβ : 0 < β)
    (f : ℝ → ℝ) {K : ℝ≥0} (hK : 0 < K) (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 < B) (hbound : ∀ z, |f z| ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ x : Spin n,
      singleSpinPlantedLaw β x {g |
        ε ≤ |(∑ i : Fin n, f (gaugedField x g i))/(n:ℝ) -
          ∫ z, f (β^2+β*z) ∂gaussianReal 0 1|} ≤
        ENNReal.ofReal (Real.exp (-c*n)) := by
  let a : ℝ := (ε/2)^2/(8*B^2)
  let b : ℝ := (ε/2)^2/(8*(K:ℝ)^2*β^2)
  let c : ℝ := min a b / 2
  have hKr : (0:ℝ) < K := NNReal.coe_pos.mpr hK
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hcenter := tendsto_iff_norm_sub_tendsto_zero.mp
    (planted_field_center_limit β f hf.continuous B hbound)
  have hcenter' := hcenter.eventually_le_const (show (0:ℝ) < ε/2 by positivity)
  have hlarge : ∀ᶠ n : ℕ in atTop, Real.log 4 / c ≤ (n:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 2, hcenter', hlarge] with n hn hcen hnlarge
  intro x
  have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hsub : {g : GaussianCoordinates n |
      ε ≤ |(∑ i : Fin n, f (gaugedField x g i))/(n:ℝ) -
        ∫ z, f (β^2+β*z) ∂gaussianReal 0 1|} ⊆
      {g | ε/2 ≤ |(∑ i : Fin n, f (gaugedField x g i))/(n:ℝ) -
        plantedFieldCenter β n f|} := by
    intro g hg
    have ht := abs_add_le
      ((∑ i : Fin n, f (gaugedField x g i))/(n:ℝ) - plantedFieldCenter β n f)
      (plantedFieldCenter β n f - ∫ z, f (β^2+β*z) ∂gaussianReal 0 1)
    simp only [sub_add_sub_cancel] at ht
    simp only [Real.norm_eq_abs] at hcen
    change ε ≤ _ at hg
    change ε/2 ≤ _
    linarith
  apply (measure_mono hsub).trans
  apply (planted_field_average_tail β hn x f hf B hB.le hbound (ε/2) (by positivity)).trans
  have hca : 2*c ≤ a := by dsimp [c]; linarith [min_le_left a b]
  have hcb : 2*c ≤ b := by dsimp [c]; linarith [min_le_right a b]
  have h1 : Real.exp (-((ε/2)^2*(n:ℝ))/(8*B^2)) ≤ Real.exp (-2*c*n) := by
    apply Real.exp_le_exp.mpr
    have he : -((ε/2)^2*(n:ℝ))/(8*B^2) = -a*n := by dsimp [a]; ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hca hnR]
  have h2 : Real.exp (-((ε/2)^2*(n:ℝ))/(8*(K:ℝ)^2*β^2)) ≤ Real.exp (-2*c*n) := by
    apply Real.exp_le_exp.mpr
    have he : -((ε/2)^2*(n:ℝ))/(8*(K:ℝ)^2*β^2) = -b*n := by dsimp [b]; ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hcb hnR]
  have htail : 4*Real.exp (-2*c*n) ≤ Real.exp (-c*n) := by
    have hlog : Real.log 4 ≤ c*n := (div_le_iff₀ hc).mp hnlarge |>.trans_eq (mul_comm _ _)
    calc
      _ = Real.exp (Real.log 4 + (-2*c*n)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 4)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ 2*ENNReal.ofReal (Real.exp (-2*c*n)) +
        2*ENNReal.ofReal (Real.exp (-2*c*n)) :=
      add_le_add (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal h1))
        (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal h2))
    _ = ENNReal.ofReal (4*Real.exp (-2*c*n)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal htail

end SKGapCutoff.Regression

end

end OAI
