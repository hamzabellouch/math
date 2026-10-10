import OAI.Analysis.ProductSpaces.ExponentialLaw

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section ExponentialFinite
variable {ι : Type uι} [Fintype ι]

def exponentialVector : Measure (ι → ℝ) := Measure.pi (fun _ => exponentialLaw)
instance : IsProbabilityMeasure (exponentialVector (ι := ι)) := by
  unfold exponentialVector
  infer_instance

lemma exponential_eval_hasLaw (i : ι) :
    HasLaw (fun x : ι → ℝ => x i) exponentialLaw exponentialVector :=
  (measurePreserving_eval (fun _ => exponentialLaw) i).hasLaw

lemma exponentialVector_positive : ∀ᵐ x : ι → ℝ ∂exponentialVector, ∀ i, 0 < x i := by
  apply ae_all_iff.mpr
  intro i
  exact ((exponential_eval_hasLaw i).ae_iff (by measurability)).mpr exponentialLaw_positive

lemma exponential_vector_complexMGF (z : ι → ℂ) (hz : ∀ i, (z i).re < 1) :
    (∫ x : ι → ℝ, Complex.exp (∑ i, z i * x i) ∂exponentialVector) =
      ∏ i, 1 / (1 - z i) := by
  simp only [Complex.exp_sum]
  unfold exponentialVector
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Complex.exp (z i * x))]
  apply Finset.prod_congr rfl
  intro i hi
  exact integral_complex_exp_exponentialLaw _ (hz i)

lemma exponential_vector_characteristic (a : ι → ℝ) (q : ℝ) :
    (∫ x : ι → ℝ, Complex.exp ((q : ℂ) * (∑ i, a i * x i) * Complex.I) ∂exponentialVector) =
      ∏ i, 1 / (1 - (q * a i : ℝ) * Complex.I) := by
  have he : (fun x : ι → ℝ => Complex.exp ((q : ℂ) * (∑ i, a i * x i) * Complex.I)) =
      (fun x => Complex.exp (∑ i, ((q * a i : ℝ) : ℂ) * Complex.I * x i)) := by
    funext x
    congr 1
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  exact exponential_vector_complexMGF _ (fun i => by simp)

def exponentialDifference (a : ι → ℝ) (z : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  ∑ i, a i * (z.1 i - z.2 i)

lemma exponential_difference_charFun (a : ι → ℝ) (q : ℝ) :
    charFun ((exponentialVector.prod exponentialVector).map (exponentialDifference a)) q =
      ∏ i, 1 / (1 + ((q * a i : ℝ) : ℂ) ^ 2) := by
  rw [charFun_apply_real, integral_map (by unfold exponentialDifference; fun_prop) (by fun_prop)]
  have he : (fun z : (ι → ℝ) × (ι → ℝ) =>
      Complex.exp ((q : ℂ) * exponentialDifference a z * Complex.I)) =
      (fun z => Complex.exp ((q : ℂ) * (∑ i, a i * z.1 i) * Complex.I) *
        Complex.exp ((-(q) : ℝ) * (∑ i, a i * z.2 i) * Complex.I)) := by
    funext z
    rw [← Complex.exp_add]
    congr 1
    simp only [exponentialDifference, mul_sub, Finset.sum_sub_distrib,
      Complex.ofReal_sub, Complex.ofReal_neg]
    ring
  rw [he, integral_prod_mul
      (fun x : ι → ℝ => Complex.exp ((q : ℂ) * (∑ i, a i * x i) * Complex.I))
      (fun x : ι → ℝ => Complex.exp ((-(q) : ℝ) * (∑ i, a i * x i) * Complex.I)),
    exponential_vector_characteristic, exponential_vector_characteristic,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [div_mul_div_comm, one_mul]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

def exponentialVariance (a : ι → ℝ) (u : ι → ℝ) : ℝ :=
  2 * ∑ i, a i ^ 2 * max (u i) 0

def exponentialMixture (a : ι → ℝ) (z : (ι → ℝ) × ℝ) : ℝ :=
  Real.sqrt (exponentialVariance a z.1) * z.2

lemma exponentialVariance_nonneg (a : ι → ℝ) (u : ι → ℝ) : 0 ≤ exponentialVariance a u := by
  unfold exponentialVariance
  positivity

lemma measurable_exponentialVariance (a : ι → ℝ) : Measurable (exponentialVariance a) := by
  unfold exponentialVariance
  fun_prop

lemma measurable_exponentialMixture (a : ι → ℝ) : Measurable (exponentialMixture a) :=
  (((measurable_exponentialVariance a).comp measurable_fst).sqrt).mul measurable_snd

lemma gaussian_scaled_characteristic (v q : ℝ) (hv : 0 ≤ v) :
    (∫ g : ℝ, Complex.exp ((q : ℂ) * ((Real.sqrt v * g : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1) =
      Complex.exp (-((v * q ^ 2 / 2 : ℝ) : ℂ)) := by
  have he : (fun g : ℝ => Complex.exp ((q : ℂ) * ((Real.sqrt v * g : ℝ) : ℂ) * Complex.I)) =
      (fun g : ℝ => Complex.exp (((q * Real.sqrt v : ℝ) : ℂ) * g * Complex.I)) := by
    funext g
    congr 1
    push_cast
    ring
  rw [he, ← charFun_apply_real, charFun_gaussianReal]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, NNReal.coe_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_pow]
  have hs : ((Real.sqrt v : ℝ) : ℂ) ^ 2 = (v : ℂ) := by exact_mod_cast Real.sq_sqrt hv
  rw [mul_pow, hs]
  ring

lemma exponential_mixture_charFun (a : ι → ℝ) (q : ℝ) :
    charFun ((exponentialVector.prod (gaussianReal 0 1)).map (exponentialMixture a)) q =
      ∏ i, 1 / (1 + ((q * a i : ℝ) : ℂ) ^ 2) := by
  rw [charFun_apply_real, integral_map (measurable_exponentialMixture a).aemeasurable (by fun_prop)]
  have hint : Integrable (fun z : (ι → ℝ) × ℝ =>
      Complex.exp ((q : ℂ) * exponentialMixture a z * Complex.I))
      (exponentialVector.prod (gaussianReal 0 1)) := by
    apply Integrable.of_bound (by exact ((by fun_prop : Measurable (fun x : ℝ =>
      Complex.exp ((q : ℂ) * x * Complex.I))).comp (measurable_exponentialMixture a)).aestronglyMeasurable) 1
    filter_upwards [] with z
    simp [Complex.norm_exp]
  rw [integral_prod _ hint]
  have he : (fun u : ι → ℝ => ∫ g : ℝ,
      Complex.exp ((q : ℂ) * exponentialMixture a (u, g) * Complex.I) ∂gaussianReal 0 1) =ᵐ[exponentialVector]
      (fun u => Complex.exp (∑ i, -(((q * a i : ℝ) : ℂ) ^ 2) * u i)) := by
    filter_upwards [exponentialVector_positive (ι := ι)] with u hu
    change (∫ g : ℝ, Complex.exp ((q : ℂ) * ((Real.sqrt (exponentialVariance a u) * g : ℝ) : ℂ) * Complex.I)
      ∂gaussianReal 0 1) = _
    rw [gaussian_scaled_characteristic _ _ (exponentialVariance_nonneg a u)]
    have hv : exponentialVariance a u * q ^ 2 / 2 = ∑ i, (q * a i) ^ 2 * u i := by
      have hmax : ∀ i, max (u i) 0 = u i := fun i => max_eq_left (hu i).le
      simp only [exponentialVariance, hmax]
      calc
        2 * (∑ i, a i ^ 2 * u i) * q ^ 2 / 2 = (∑ i, a i ^ 2 * u i) * q ^ 2 := by ring
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    rw [hv]
    congr 1
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
      ← Finset.sum_neg_distrib, neg_mul]

  rw [integral_congr_ae he, exponential_vector_complexMGF _ (fun i => by
    simp only [Complex.neg_re, ← Complex.ofReal_pow, Complex.ofReal_re]
    nlinarith [sq_nonneg (q * a i)])]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [sub_neg_eq_add]

lemma exponential_difference_mixture (a : ι → ℝ) :
    (exponentialVector.prod exponentialVector).map (exponentialDifference a) =
      (exponentialVector.prod (gaussianReal 0 1)).map (exponentialMixture a) := by
  apply Measure.ext_of_charFun
  funext q
  rw [exponential_difference_charFun, exponential_mixture_charFun]

end ExponentialFinite
end IndependentProducts

end

end OAI
