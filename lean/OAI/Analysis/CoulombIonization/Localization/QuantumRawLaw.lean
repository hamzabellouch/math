import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CoulombCoercivity

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_QuantumRawLaw_scope

open MeasureTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CoulombAtom

attribute [local irreducible] graphComponent fermionGraphValue

def graphRawDensity {N : ℕ} (F : fermionGraph N) (x : Configuration N) : ℝ :=
  ∑ s : Spins N, ‖graphComponent s none F x‖^2

lemma graphRawDensity_nonneg {N : ℕ} (F : fermionGraph N) (x : Configuration N) :
    0 ≤ graphRawDensity F x := sum_nonneg (fun _ _ => sq_nonneg _)

lemma graphRawDensity_measurable {N : ℕ} (F : fermionGraph N) :
    Measurable (graphRawDensity F) := by
  apply Finset.measurable_sum
  intro s _
  exact (Lp.stronglyMeasurable (graphComponent s none F)).measurable.norm.pow_const 2

lemma graphRawDensity_integrable {N : ℕ} (F : fermionGraph N) :
    Integrable (graphRawDensity F) := by
  apply integrable_finsetSum
  intro s _
  exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)

lemma graphRawDensity_integral {N : ℕ} (F : fermionGraph N) :
    ∫ x, graphRawDensity F x = ‖fermionGraphValue N F‖^2 := by
  change (∫ x, ∑ s : Spins N, ‖graphComponent s none F x‖^2) = _
  rw [integral_finsetSum _ (fun s _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))]
  simp_rw [← lp_norm_sq]
  have hv : ‖fermionGraphValue N F‖^2 = ∑ s : Spins N, ‖(F.val s).val none‖^2 := by
    change ‖(fermionGraphValue N F).val‖^2 = _
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [fermionGraphValue_apply]
  rw [hv]
  simp only [graphComponent_apply]

def graphRawLaw {N : ℕ} (F : fermionGraph N) : Measure (Configuration N) :=
  volume.withDensity (fun x => ENNReal.ofReal (graphRawDensity F x))

lemma graphRawLaw_univ {N : ℕ} (F : fermionGraph N) :
    graphRawLaw F univ = ENNReal.ofReal (‖fermionGraphValue N F‖^2) := by
  change (volume.withDensity (fun x => ENNReal.ofReal (graphRawDensity F x))) univ = _
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (graphRawDensity_integrable F)
    (ae_of_all _ (graphRawDensity_nonneg F))).symm.trans
      (congrArg ENNReal.ofReal (graphRawDensity_integral F))

lemma graphRawLaw_probability {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) : IsProbabilityMeasure (graphRawLaw F) := by
  constructor
  rw [graphRawLaw_univ, hn, ENNReal.ofReal_one]

lemma graphRawLaw_integral {N : ℕ} (F : fermionGraph N) (g : Configuration N → ℝ) :
    (∫ x, g x ∂graphRawLaw F) = ∫ x, graphRawDensity F x * g x := by
  rw [graphRawLaw, integral_withDensity_eq_integral_toReal_smul
    (graphRawDensity_measurable F).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (graphRawDensity_nonneg F _), smul_eq_mul]

lemma graphRawLaw_integrable_iff {N : ℕ} (F : fermionGraph N)
    {g : Configuration N → ℝ} :
    Integrable g (graphRawLaw F) ↔ Integrable (fun x => graphRawDensity F x * g x) := by
  rw [graphRawLaw, integrable_withDensity_iff_integrable_smul'
    (graphRawDensity_measurable F).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (graphRawDensity_nonneg F _), smul_eq_mul]

end CoulombAtom

end Work_QuantumRawLaw_scope

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace CoulombObservation

def compactNoiseWeight (u : ℝ) : ℝ :=
  if |u| < 1 then Real.exp (-(1 - u^2)⁻¹) else 0

def compactNoiseNormalizer : ℝ := (∫ u, compactNoiseWeight u)⁻¹

def compactNoiseDensity (u : ℝ) : ℝ := compactNoiseNormalizer * compactNoiseWeight u

def compactNoiseLaw : Measure ℝ :=
  volume.withDensity (fun u => ENNReal.ofReal (compactNoiseDensity u))

def compactNoiseScore (u : ℝ) : ℝ :=
  if |u| < 1 then -2*u / (1-u^2)^2 else 0

lemma compactNoiseWeight_measurable : Measurable compactNoiseWeight := by
  unfold compactNoiseWeight
  exact Measurable.ite (measurableSet_lt measurable_abs measurable_const)
    (by fun_prop) measurable_const

lemma compactNoiseScore_measurable : Measurable compactNoiseScore := by
  unfold compactNoiseScore
  exact Measurable.ite (measurableSet_lt measurable_abs measurable_const)
    (by fun_prop) measurable_const

lemma compactNoiseWeight_nonneg (u : ℝ) : 0 ≤ compactNoiseWeight u := by
  unfold compactNoiseWeight
  split_ifs <;> positivity

lemma compactNoiseWeight_le_one (u : ℝ) : compactNoiseWeight u ≤ 1 := by
  unfold compactNoiseWeight
  split_ifs with hu
  · apply Real.exp_le_one_iff.mpr
    have hh : 0 < 1-u^2 := by have := abs_lt.mp hu; nlinarith
    exact neg_nonpos.mpr (inv_nonneg.mpr hh.le)
  · norm_num

lemma compactNoiseWeight_even (u : ℝ) : compactNoiseWeight (-u) = compactNoiseWeight u := by
  simp [compactNoiseWeight]

lemma compactNoiseScore_odd : Function.Odd compactNoiseScore := by
  intro u
  simp only [compactNoiseScore, abs_neg, neg_sq]
  split_ifs <;> ring

lemma compactNoiseWeight_integrable : Integrable compactNoiseWeight := by
  have hi : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ))) := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrableOn_const (by rw [Real.volume_Icc]; finiteness)
  refine hi.mono' compactNoiseWeight_measurable.aestronglyMeasurable (ae_of_all _ ?_)
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (compactNoiseWeight_nonneg u)]
  by_cases hu : |u| < 1
  · rw [indicator_of_mem (by have := abs_lt.mp hu; constructor <;> linarith)]
    exact compactNoiseWeight_le_one u
  · rw [compactNoiseWeight, ite_eq_right hu]
    exact indicator_nonneg (fun _ _ => by norm_num) _

lemma compactNoiseWeight_support : Function.support compactNoiseWeight = Ioo (-1) 1 := by
  ext u
  simp only [Function.mem_support, mem_Ioo, compactNoiseWeight]
  by_cases hu : |u| < 1
  · simp [hu, Real.exp_ne_zero, abs_lt.mp hu]
  · have hh : ¬(-1 < u ∧ u < 1) := by simpa only [← abs_lt] using hu
    simp [hu, hh]

lemma compactNoiseWeight_integral_pos : 0 < ∫ u, compactNoiseWeight u := by
  rw [integral_pos_iff_support_of_nonneg compactNoiseWeight_nonneg compactNoiseWeight_integrable,
    compactNoiseWeight_support, Real.volume_Ioo]
  norm_num

lemma compactNoiseNormalizer_pos : 0 < compactNoiseNormalizer :=
  inv_pos.mpr compactNoiseWeight_integral_pos

lemma compactNoiseDensity_nonneg (u : ℝ) : 0 ≤ compactNoiseDensity u :=
  mul_nonneg compactNoiseNormalizer_pos.le (compactNoiseWeight_nonneg u)

lemma compactNoiseDensity_measurable : Measurable compactNoiseDensity :=
  compactNoiseWeight_measurable.const_mul _

lemma compactNoiseDensity_integrable : Integrable compactNoiseDensity :=
  compactNoiseWeight_integrable.const_mul _

lemma compactNoiseDensity_integral : (∫ u, compactNoiseDensity u) = 1 := by
  change (∫ u, compactNoiseNormalizer * compactNoiseWeight u) = 1
  rw [integral_const_mul, compactNoiseNormalizer]
  exact inv_mul_cancel₀ (ne_of_gt compactNoiseWeight_integral_pos)

instance compactNoiseLaw_probability : IsProbabilityMeasure compactNoiseLaw := by
  constructor
  rw [compactNoiseLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal compactNoiseDensity_integrable
      (ae_of_all _ compactNoiseDensity_nonneg), compactNoiseDensity_integral]
  norm_num

lemma compactNoiseLaw_integral (f : ℝ → ℝ) :
    (∫ u, f u ∂compactNoiseLaw) = ∫ u, compactNoiseDensity u * f u := by
  rw [compactNoiseLaw, integral_withDensity_eq_integral_toReal_smul
    compactNoiseDensity_measurable.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (compactNoiseDensity_nonneg _), smul_eq_mul]

end CoulombObservation

end

end OAI
