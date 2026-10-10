import Mathlib
import OAI.Probability.SKGap.Brownian.ContinuousEnergy
import OAI.Probability.SKGap.Localization.UpperCoefficient

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
namespace SKGapCutoff

lemma gaussianPDFReal_tilt (v : ℝ≥0) (hv : v ≠ 0) (a x : ℝ) :
    gaussianPDFReal ((v : ℝ) * a) v x =
      gaussianPDFReal 0 v x * Real.exp (a*x - (v : ℝ)*a^2/2) := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  unfold gaussianPDFReal
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

lemma gaussianReal_exponential_tilt (v : ℝ≥0) (a : ℝ) :
    (gaussianReal 0 v).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a*x - (v : ℝ)*a^2/2))) =
        gaussianReal ((v : ℝ)*a) v := by
  by_cases hv : v = 0
  · subst v
    simp [dirac_withDensity]
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv]
  rw [← withDensity_mul _ (measurable_gaussianPDF 0 v) (by fun_prop)]
  congr 1
  funext x
  simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal_tilt v hv a x,
    ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)]

lemma pi_withDensity_ofReal_prod {ι : Type*} [Fintype ι]
    {E : Type*} [MeasurableSpace E] (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)]
    (f : ι → E → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hf0 : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun i => (hf i).restrict))
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hf0 i (x i))))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hf0 i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i |>.restrict)
    (Filter.Eventually.of_forall (hf0 i))

lemma gaussianPi_exponential_tilt {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)).withDensity
      (fun g => ENNReal.ofReal
        (Real.exp ((∑ i, a i * g i) - (v : ℝ)*(∑ i, a i ^ 2)/2))) =
      Measure.pi (fun i => gaussianReal ((v : ℝ)*a i) v) := by
  have hp (g : ι → ℝ) : Real.exp ((∑ i, a i * g i) - (v : ℝ)*(∑ i, a i ^ 2)/2) =
      ∏ i, Real.exp (a i*g i - (v : ℝ)*(a i)^2/2) := by
    rw [← Real.exp_sum]
    congr 1
    simp [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
  simp_rw [← gaussianReal_exponential_tilt v, hp]
  symm
  apply pi_withDensity_ofReal_prod
  · intro i
    simp_rw [Real.exp_sub, div_eq_mul_inv]
    exact (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (a i)).mul_const _
  · intro i x; positivity

noncomputable def singleSpinPlantedLaw (β : ℝ) {n : ℕ} (x : Spin n) :
    Measure (GaussianCoordinates n) :=
  (disorderLaw β n).withDensity (fun g => ENNReal.ofReal
    (Real.exp (energy (sampledInteraction g) x - β^2*((n : ℝ)-1)/4)))

lemma singleSpinPlantedLaw_eq_gaussianPi (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n) :
    singleSpinPlantedLaw β x = Measure.pi (fun p : Fin n × Fin n =>
      gaussianReal (β^2/n * upperCoefficient x p) (Real.toNNReal (β^2/n))) := by
  unfold singleSpinPlantedLaw disorderLaw
  have hv : (Real.toNNReal (β^2/(n : ℝ)) : ℝ) = β^2/n :=
    Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc : (Real.toNNReal (β^2/(n : ℝ)) : ℝ) * (∑ p, upperCoefficient x p ^ 2)/2 =
      β^2*((n : ℝ)-1)/4 := by
    rw [hv, sum_upperCoefficient_sq]
    field_simp
    ring
  simp_rw [energy_sampled, ← hc]
  rw [gaussianPi_exponential_tilt]
  simp only [hv]

lemma singleSpinPlantedLaw_probability (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n) :
    IsProbabilityMeasure (singleSpinPlantedLaw β x) := by
  rw [singleSpinPlantedLaw_eq_gaussianPi β hn]
  infer_instance

noncomputable def plantedDisorderLaw (β : ℝ) (n : ℕ) : Measure (GaussianCoordinates n) :=
  (disorderLaw β n).withDensity (fun g => ENNReal.ofReal
    (partition (sampledInteraction g) / (∫ h, partition (sampledInteraction h) ∂disorderLaw β n)))

lemma plantedDisorderLaw_probability (β : ℝ) {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (plantedDisorderLaw β n) := by
  have hZ : Integrable (fun g : GaussianCoordinates n => partition (sampledInteraction g))
      (disorderLaw β n) := by
    unfold partition
    exact integrable_finsetSum _ (fun x _ => integrable_exp_energy_sampled β x)
  have hm : 0 < ∫ g, partition (sampledInteraction g) ∂disorderLaw β n := by
    rw [integral_partition_sampled β hn]
    positivity
  constructor
  rw [plantedDisorderLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hZ.div_const _)
    (Filter.Eventually.of_forall (fun g => div_nonneg (le_of_lt (partition_pos _)) (le_of_lt hm)))]
  rw [integral_div, div_self (ne_of_gt hm), ENNReal.ofReal_one]

lemma planted_density_sum (β : ℝ) {n : ℕ} (hn : 0 < n) (g : GaussianCoordinates n) :
    partition (sampledInteraction g) / (∫ h, partition (sampledInteraction h) ∂disorderLaw β n) =
      ∑ x : Spin n, ((2 : ℝ)^n)⁻¹ *
        Real.exp (energy (sampledInteraction g) x - β^2*((n : ℝ)-1)/4) := by
  rw [integral_partition_sampled β hn]
  unfold partition
  simp_rw [Real.exp_sub, ← Finset.mul_sum, ← Finset.sum_div]
  ring

lemma plantedDisorderLaw_mixture (β : ℝ) {n : ℕ} (hn : 0 < n) :
    plantedDisorderLaw β n = ENNReal.ofReal (((2 : ℝ)^n)⁻¹) •
      Measure.sum (fun x : Spin n => singleSpinPlantedLaw β x) := by
  ext s hs
  rw [plantedDisorderLaw, withDensity_apply _ hs, Measure.smul_apply,
    Measure.sum_apply _ hs, tsum_fintype]
  simp_rw [singleSpinPlantedLaw, withDensity_apply _ hs]
  rw [← lintegral_finsetSum (s := Finset.univ) (fun x _ => by simp_rw [energy_sampled]; fun_prop)]
  rw [smul_eq_mul, ← lintegral_const_mul _ (by simp_rw [energy_sampled]; fun_prop)]
  apply lintegral_congr
  intro g
  rw [planted_density_sum β hn]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => by positivity)]
  simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((2 : ℝ)^n)⁻¹)]
  rw [Finset.mul_sum]

lemma lower_density_markov {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (r f : E → ℝ≥0∞) (hr : Measurable r) (hf : Measurable f)
    (A : Set E) (hA : MeasurableSet A) (c t : ℝ≥0∞)
    (hc : ∀ x ∈ A, c ≤ r x) (ht : ∀ x ∈ A, t ≤ f x) :
    (c*t) * μ A ≤ ∫⁻ x, f x ∂(μ.withDensity r) := by
  rw [lintegral_withDensity_eq_lintegral_mul μ hr hf]
  calc
    (c*t) * μ A = ∫⁻ _ in A, c*t ∂μ := by simp
    _ ≤ ∫⁻ x in A, r x * f x ∂μ :=
      setLIntegral_mono' hA (fun x hx => mul_le_mul' (hc x hx) (ht x hx))
    _ ≤ ∫⁻ x, r x * f x ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl

lemma lower_density_markov_div {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (r f : E → ℝ≥0∞) (hr : Measurable r) (hf : Measurable f)
    (A : Set E) (hA : MeasurableSet A) (c t : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcT : c ≠ ⊤) (ht0 : t ≠ 0) (htT : t ≠ ⊤)
    (hc : ∀ x ∈ A, c ≤ r x) (ht : ∀ x ∈ A, t ≤ f x) :
    μ A ≤ (∫⁻ x, f x ∂(μ.withDensity r)) / (c*t) := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hc0 ht0))
    (Or.inl (ENNReal.mul_ne_top hcT htT))).mpr
  simpa only [mul_comm] using lower_density_markov μ r f hr hf A hA c t hc ht

lemma planted_law_transfer (β : ℝ) {n : ℕ} (hn : 0 < n)
    (a s : ℝ) (f : GaussianCoordinates n → ℝ≥0∞) (hf : Measurable f) :
    (disorderLaw β n) {g | Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n) - a ≤
        Real.log (partition (sampledInteraction g)) ∧ ENNReal.ofReal (Real.exp (-s)) ≤ f g} ≤
      ENNReal.ofReal (Real.exp (a+s)) * ∫⁻ g, f g ∂plantedDisorderLaw β n := by
  let m := ∫ h, partition (sampledInteraction h) ∂disorderLaw β n
  let r := fun g : GaussianCoordinates n => ENNReal.ofReal (partition (sampledInteraction g) / m)
  let A := {g : GaussianCoordinates n | Real.log m - a ≤
        Real.log (partition (sampledInteraction g)) ∧ ENNReal.ofReal (Real.exp (-s)) ≤ f g}
  have hm : 0 < m := by dsimp [m]; rw [integral_partition_sampled β hn]; positivity
  have hZ := (continuous_partition n).comp (continuous_sampledInteraction n)
  have hr : Measurable r := by dsimp [r]; exact (hZ.measurable.div_const m).ennreal_ofReal
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const hZ.measurable.log).inter
      (measurableSet_le measurable_const hf)
  have hd : ∀ g ∈ A, ENNReal.ofReal (Real.exp (-a)) ≤ r g := by
    intro g hg
    apply ENNReal.ofReal_le_ofReal
    have he : -a ≤ Real.log (partition (sampledInteraction g) / m) := by
      rw [Real.log_div (partition_pos _).ne' hm.ne']
      linarith [hg.1]
    have hexp := Real.exp_le_exp.mpr he
    rwa [Real.exp_log (div_pos (partition_pos _) hm)] at hexp
  have h := lower_density_markov_div (disorderLaw β n) r f hr hf A hA
    (ENNReal.ofReal (Real.exp (-a))) (ENNReal.ofReal (Real.exp (-s)))
    (by positivity) ENNReal.ofReal_ne_top (by positivity) ENNReal.ofReal_ne_top hd
    (fun g hg => hg.2)
  have he : (ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal (Real.exp (-s)))⁻¹ =
      ENNReal.ofReal (Real.exp (a+s)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
    congr 2
    ring
  rw [div_eq_mul_inv, he, mul_comm] at h
  exact h

end SKGapCutoff

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal

end

end OAI
