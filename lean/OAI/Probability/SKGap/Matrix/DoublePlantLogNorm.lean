import Mathlib
import OAI.Probability.SKGap.Terminal.SingleSpinPlantedLaw
import OAI.Probability.SKGap.Gaussian.ReplicaTailWeight

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
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace SKGapCutoff

noncomputable def doublePlantLogNorm (β : ℝ) {n : ℕ} (x y : Spin n) : ℝ :=
  β^2*((n:ℝ)-2)/2 + β^2*replicaOverlap x y^2/(2*n)

noncomputable def doubleSpinPlantedLaw (β : ℝ) {n : ℕ} (x y : Spin n) :
    Measure (GaussianCoordinates n) :=
  (disorderLaw β n).withDensity (fun g => ENNReal.ofReal
    (Real.exp (energy (sampledInteraction g) x + energy (sampledInteraction g) y -
      doublePlantLogNorm β x y)))

lemma doubleSpinPlantedLaw_eq_gaussianPi (β : ℝ) {n : ℕ} (hn : 0 < n)
    (x y : Spin n) :
    doubleSpinPlantedLaw β x y = Measure.pi (fun p : Fin n × Fin n =>
      gaussianReal (β^2/n * (upperCoefficient x p + upperCoefficient y p))
        (Real.toNNReal (β^2/n))) := by
  unfold doubleSpinPlantedLaw disorderLaw
  have hv : (Real.toNNReal (β^2/(n:ℝ)) : ℝ) = β^2/n :=
    Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc : (Real.toNNReal (β^2/(n:ℝ)) : ℝ) *
      (∑ p, (upperCoefficient x p + upperCoefficient y p)^2)/2 =
        doublePlantLogNorm β x y := by
    rw [hv, sum_upperCoefficient_add_sq]
    unfold doublePlantLogNorm
    field_simp
  simp_rw [combined_energy_sampled, ← hc]
  rw [gaussianPi_exponential_tilt]
  simp only [hv]

lemma doubleSpinPlantedLaw_probability (β : ℝ) {n : ℕ} (hn : 0 < n)
    (x y : Spin n) : IsProbabilityMeasure (doubleSpinPlantedLaw β x y) := by
  rw [doubleSpinPlantedLaw_eq_gaussianPi β hn]
  infer_instance

noncomputable def doublePlantNorm (β : ℝ) (n : ℕ) : ℝ :=
  ∫ g, partition (sampledInteraction g)^2 ∂disorderLaw β n

lemma doublePlantNorm_eq_sum (β : ℝ) {n : ℕ} (hn : 0 < n) :
    doublePlantNorm β n = ∑ x : Spin n, ∑ y : Spin n,
      Real.exp (doublePlantLogNorm β x y) := by
  rw [doublePlantNorm, integral_partition_sq_sampled β hn]
  simp only [doublePlantLogNorm, Real.exp_add, Finset.mul_sum]

lemma doublePlantNorm_pos (β : ℝ) {n : ℕ} (hn : 0 < n) :
    0 < doublePlantNorm β n := by
  rw [doublePlantNorm_eq_sum β hn]
  exact Finset.sum_pos (fun x _ => Finset.sum_pos (fun y _ => Real.exp_pos _)
    Finset.univ_nonempty) Finset.univ_nonempty

noncomputable def doublePlantWeight (β : ℝ) {n : ℕ} (x y : Spin n) : ℝ :=
  Real.exp (doublePlantLogNorm β x y) / doublePlantNorm β n

lemma doublePlantWeight_pos (β : ℝ) {n : ℕ} (hn : 0 < n) (x y : Spin n) :
    0 < doublePlantWeight β x y :=
  div_pos (Real.exp_pos _) (doublePlantNorm_pos β hn)

lemma doublePlantWeight_sum (β : ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ x : Spin n, ∑ y : Spin n, doublePlantWeight β x y = 1 := by
  simp only [doublePlantWeight, ← Finset.sum_div]
  rw [← doublePlantNorm_eq_sum β hn, div_self (doublePlantNorm_pos β hn).ne']

noncomputable def doublePlantedDisorderLaw (β : ℝ) (n : ℕ) :
    Measure (GaussianCoordinates n) :=
  (disorderLaw β n).withDensity (fun g => ENNReal.ofReal
    (partition (sampledInteraction g)^2/doublePlantNorm β n))

lemma doublePlantedDisorderLaw_probability (β : ℝ) {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (doublePlantedDisorderLaw β n) := by
  constructor
  rw [doublePlantedDisorderLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_partition_sq_sampled β n).div_const _)
    (Eventually.of_forall (fun g => div_nonneg (sq_nonneg _) (doublePlantNorm_pos β hn).le))]
  rw [integral_div]
  change ENNReal.ofReal (doublePlantNorm β n / doublePlantNorm β n) = 1
  rw [div_self (doublePlantNorm_pos β hn).ne', ENNReal.ofReal_one]

noncomputable def doubleGibbsLExpectation {n : ℕ}
    (q : GaussianCoordinates n → Spin n → Spin n → ℝ≥0∞)
    (g : GaussianCoordinates n) : ℝ≥0∞ :=
  ∑ x, ∑ y, ENNReal.ofReal (gibbs (sampledInteraction g) x) *
    ENNReal.ofReal (gibbs (sampledInteraction g) y) * q g x y

lemma measurable_doubleGibbsLExpectation {n : ℕ}
    (q : GaussianCoordinates n → Spin n → Spin n → ℝ≥0∞)
    (hq : ∀ x y, Measurable (fun g => q g x y)) :
    Measurable (doubleGibbsLExpectation q) := by
  unfold doubleGibbsLExpectation
  exact Finset.measurable_sum _ (fun x _ => Finset.measurable_sum _ (fun y _ =>
    ((((continuous_gibbs x).comp (continuous_sampledInteraction n)).measurable.ennreal_ofReal).mul
      (((continuous_gibbs y).comp (continuous_sampledInteraction n)).measurable.ennreal_ofReal)).mul
        (hq x y)))

lemma double_planted_gibbs_density (β : ℝ) {n : ℕ} (hn : 0 < n)
    (g : GaussianCoordinates n) (x y : Spin n) :
    (partition (sampledInteraction g)^2/doublePlantNorm β n) *
      gibbs (sampledInteraction g) x * gibbs (sampledInteraction g) y =
      doublePlantWeight β x y * Real.exp (energy (sampledInteraction g) x +
        energy (sampledInteraction g) y - doublePlantLogNorm β x y) := by
  unfold gibbs doublePlantWeight
  rw [Real.exp_sub, Real.exp_add]
  field_simp [(partition_pos (sampledInteraction g)).ne', (doublePlantNorm_pos β hn).ne']

lemma double_planted_gibbs_lintegral (β : ℝ) {n : ℕ} (hn : 0 < n)
    (q : GaussianCoordinates n → Spin n → Spin n → ℝ≥0∞)
    (hq : ∀ x y, Measurable (fun g => q g x y)) :
    (∫⁻ g, doubleGibbsLExpectation q g ∂doublePlantedDisorderLaw β n) =
      ∑ x : Spin n, ∑ y : Spin n, ENNReal.ofReal (doublePlantWeight β x y) *
        ∫⁻ g, q g x y ∂doubleSpinPlantedLaw β x y := by
  have hZ := (continuous_partition n).comp (continuous_sampledInteraction n)
  have hr : Measurable (fun g : GaussianCoordinates n => ENNReal.ofReal
      (partition (sampledInteraction g)^2/doublePlantNorm β n)) :=
    ((hZ.measurable.pow_const 2).div_const _).ennreal_ofReal
  have hE (x y : Spin n) : Measurable (fun g : GaussianCoordinates n =>
      ENNReal.ofReal (Real.exp (energy (sampledInteraction g) x +
        energy (sampledInteraction g) y - doublePlantLogNorm β x y))) := by
    exact (((((continuous_energy x).comp (continuous_sampledInteraction n)).measurable.add
      (((continuous_energy y).comp (continuous_sampledInteraction n)).measurable)).sub_const _).exp).ennreal_ofReal
  rw [doublePlantedDisorderLaw, lintegral_withDensity_eq_lintegral_mul _ hr
    (measurable_doubleGibbsLExpectation q hq)]
  have hp (g : GaussianCoordinates n) (x y : Spin n) :
      ENNReal.ofReal (partition (sampledInteraction g)^2/doublePlantNorm β n) *
        ENNReal.ofReal (gibbs (sampledInteraction g) x) *
        ENNReal.ofReal (gibbs (sampledInteraction g) y) =
      ENNReal.ofReal (doublePlantWeight β x y) * ENNReal.ofReal (Real.exp
        (energy (sampledInteraction g) x + energy (sampledInteraction g) y -
          doublePlantLogNorm β x y)) := by
    rw [← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (doublePlantNorm_pos β hn).le),
      ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg (sq_nonneg _) (doublePlantNorm_pos β hn).le)
        (gibbs_pos _ _).le), double_planted_gibbs_density β hn,
      ENNReal.ofReal_mul (doublePlantWeight_pos β hn x y).le]
  change (∫⁻ g, ENNReal.ofReal (partition (sampledInteraction g)^2/doublePlantNorm β n) *
    (∑ x, ∑ y, ENNReal.ofReal (gibbs (sampledInteraction g) x) *
      ENNReal.ofReal (gibbs (sampledInteraction g) y) * q g x y) ∂disorderLaw β n) = _
  simp only [Finset.mul_sum, ← mul_assoc]
  simp_rw [hp, mul_assoc]
  have hterm (x y : Spin n) : Measurable (fun g : GaussianCoordinates n =>
      ENNReal.ofReal (doublePlantWeight β x y) *
        (ENNReal.ofReal (Real.exp (energy (sampledInteraction g) x +
          energy (sampledInteraction g) y - doublePlantLogNorm β x y)) * q g x y)) :=
    measurable_const.mul ((hE x y).mul (hq x y))
  rw [lintegral_finsetSum Finset.univ (fun x _ =>
    Finset.measurable_sum _ (fun y _ => hterm x y))]
  apply Finset.sum_congr rfl
  intro x _
  rw [lintegral_finsetSum Finset.univ (fun y _ => hterm x y)]
  apply Finset.sum_congr rfl
  intro y _
  have hf : Measurable (fun g : GaussianCoordinates n =>
      ENNReal.ofReal (Real.exp (energy (sampledInteraction g) x +
        energy (sampledInteraction g) y - doublePlantLogNorm β x y)) * q g x y) :=
    (hE x y).mul (hq x y)
  rw [lintegral_const_mul _ hf, doubleSpinPlantedLaw,
    lintegral_withDensity_eq_lintegral_mul _ (hE x y) (hq x y)]
  rfl

lemma doublePlantWeight_eq_overlap_tilt (β : ℝ) {n : ℕ} (hn : 0 < n) (x y : Spin n) :
    doublePlantWeight β x y = Real.exp (β^2*replicaOverlap x y^2/(2*n)) /
      (∑ u : Spin n, ∑ v : Spin n, Real.exp (β^2*replicaOverlap u v^2/(2*n))) := by
  unfold doublePlantWeight doublePlantLogNorm doublePlantNorm
  rw [integral_partition_sq_sampled β hn, Real.exp_add,
    mul_div_mul_left _ _ (Real.exp_ne_zero _)]

lemma doublePlantWeight_overlap_tail (β q ε : ℝ) (hβq : β^2 < q) (hq : q < 1)
    (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    (∑ x : Spin n, ∑ y : Spin n, if ε*n < |replicaOverlap x y| then
      doublePlantWeight β x y else 0) ≤
        Real.exp (-((q-β^2)*ε^2*n/2)) * (Real.sqrt (1-q))⁻¹ := by
  let D := ∑ x : Spin n, ∑ y : Spin n, Real.exp (β^2*replicaOverlap x y^2/(2*n))
  have hD : ((2:ℝ)^n)^2 ≤ D := by
    have he (x y : Spin n) : (1:ℝ) ≤ Real.exp (β^2*replicaOverlap x y^2/(2*n)) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun y _ => he x y))
    simpa only [Finset.sum_const, Finset.card_univ, card_spin, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, mul_one, pow_two, D] using hh
  have hid : (∑ x : Spin n, ∑ y : Spin n, if ε*n < |replicaOverlap x y| then
      doublePlantWeight β x y else 0) =
      (∑ x : Spin n, ∑ y : Spin n, if ε*n < |replicaOverlap x y| then
        Real.exp (β^2*replicaOverlap x y^2/(2*n)) else 0) / D := by
    simp only [doublePlantWeight_eq_overlap_tilt β hn, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp [D]
  rw [hid]
  calc
    _ ≤ (∑ x : Spin n, ∑ y : Spin n, if ε*n < |replicaOverlap x y| then
        Real.exp (β^2*replicaOverlap x y^2/(2*n)) else 0) / ((2:ℝ)^n)^2 := by
      exact div_le_div_of_nonneg_left (Finset.sum_nonneg (fun x _ =>
        Finset.sum_nonneg (fun y _ => by split_ifs <;> positivity))) (by positivity) hD
    _ = (∑ x : Spin n, if ε*n < |magnetization x| then
        Real.exp (β^2*magnetization x^2/(2*n)) else 0) / (2:ℝ)^n := by
      simp_rw [sum_replicaOverlap _ (fun z => if ε*n < |z| then Real.exp (β^2*z^2/(2*n)) else 0)]
      simp only [Finset.sum_const, Finset.card_univ, card_spin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      field_simp
    _ ≤ _ := sign_square_tail_le β q ε hβq hq hε hn

end SKGapCutoff

end

end OAI
