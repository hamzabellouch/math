import Mathlib
import OAI.Probability.ThreeStateClauses.InformationLoss
import OAI.Probability.ThreeStateClauses.ObservedMixtures

namespace OAI

/-! Countable Statistics. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

lemma pmf_measure_sum_dirac (p : PMF α) :
    p.toMeasure = Measure.sum (fun a ↦ p a • Measure.dirac a) := by
  simpa only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] using
    (Measure.sum_smul_dirac p.toMeasure).symm

lemma pmf_integrable_iff (p : PMF α) (f : α → ℝ) :
    Integrable f p.toMeasure ↔ Summable (fun a ↦ (p a).toReal*|f a|) := by
  rw [pmf_measure_sum_dirac, integrable_sum_dirac_iff (fun a ↦ p.apply_ne_top a)]
  rfl

lemma integral_pmf_tsum (p : PMF α) (f : α → ℝ) :
    (∫ a, f a ∂p.toMeasure) = ∑' a, (p a).toReal*f a := by
  rw [pmf_measure_sum_dirac, integral_sum_dirac (fun a ↦ p.apply_ne_top a)]
  rfl

omit [Countable β] [MeasurableSingletonClass β] in
lemma pmf_integrable_bind (p : PMF α) (K : α → PMF β) {f : β → ℝ}
    (hf : ∀ a, Integrable f (K a).toMeasure)
    (hn : Integrable (fun a ↦ ∫ b, |f b| ∂(K a).toMeasure) p.toMeasure) :
    Integrable f (p.bind K).toMeasure := by
  rw [pmf_measure_bind]
  apply integrable_sum_measure (fun a ↦ (hf a).smul_measure (p.apply_ne_top a))
  have h := (pmf_integrable_iff p _).mp hn
  simpa only [integral_smul_measure, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ ↦ abs_nonneg _))] using h

omit [Countable β] [MeasurableSingletonClass β] in
lemma integral_pmf_bind_integrable (p : PMF α) (K : α → PMF β) {f : β → ℝ}
    (hf : Integrable f (p.bind K).toMeasure) :
    (∫ b, f b ∂(p.bind K).toMeasure) = ∫ a, (∫ b, f b ∂(K a).toMeasure) ∂p.toMeasure := by
  rw [pmf_measure_bind] at hf ⊢
  rw [integral_sum_measure hf, integral_pmf_tsum]
  simp only [integral_smul_measure, smul_eq_mul]

omit [Countable α] [MeasurableSingletonClass α] in
lemma pmf_integrable_bind_finite {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (p : PMF ι) (K : ι → PMF α) {f : α → ℝ}
    (hf : ∀ i, Integrable f (K i).toMeasure) : Integrable f (p.bind K).toMeasure :=
  pmf_integrable_bind p K hf Integrable.of_finite

lemma pmf_integrable_map_iff (p : PMF α) (g : α → β) (f : β → ℝ) :
    Integrable f (p.map g).toMeasure ↔ Integrable (fun a ↦ f (g a)) p.toMeasure := by
  rw [← PMF.toMeasure_map g p (measurable_of_countable g)]
  exact integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable

lemma pmf_integrable_of_square (p : PMF α) {f : α → ℝ}
    (hf : Integrable (fun a ↦ f a^2) p.toMeasure) : Integrable f p.toMeasure := by
  apply ((integrable_const (1:ℝ)).add hf).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a ↦ by
    simp only [Real.norm_eq_abs, Pi.add_apply]
    nlinarith [sq_nonneg (|f a|-1), sq_abs (f a)])

lemma discrete_bayes_integral_integrable (p : Spin → PMF α) (i : Spin) {f : α → ℝ}
    (hf : Integrable f (discreteMarginal p).toMeasure) (hi : Integrable f (p i).toMeasure) :
    (∫ a, (discreteMessage p a).1 i*f a ∂(discreteMarginal p).toMeasure) =
      ∫ a, f a ∂(p i).toMeasure := by
  have hl := hf.bdd_mul (measurable_of_countable (fun a ↦ (discreteMessage p a).1 i)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a ↦ show ‖(discreteMessage p a).1 i‖ ≤ (3:ℝ) by
      rw [Real.norm_eq_abs, abs_of_nonneg (coordinate_nonneg _ _)]; exact coordinate_le_three _ _))
  rw [PMF.integral_eq_tsum _ _ hl, PMF.integral_eq_tsum _ _ hi]
  apply tsum_congr
  intro a
  simp only [smul_eq_mul, discreteMarginal_real, ← mul_assoc, discrete_bayes]

omit [Countable α] [MeasurableSingletonClass α] in
lemma integral_discreteMarginal_integrable (p : Spin → PMF α) {f : α → ℝ}
    (hf : ∀ i, Integrable f (p i).toMeasure) :
    (∫ a, f a ∂(discreteMarginal p).toMeasure) =
      ((∫ a, f a ∂(p 0).toMeasure)+(∫ a, f a ∂(p 1).toMeasure)+(∫ a, f a ∂(p 2).toMeasure))/3 := by
  rw [discreteMarginal, integral_pmf_bind_integrable _ _ (pmf_integrable_bind_finite _ _ hf), PMF.integral_eq_sum]
  simp only [Fin.sum_univ_three, uniformSpin_apply, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

lemma estimator_tv_lower_integrable (p : Spin → PMF α) {f : α → ℝ} {C : ℝ}
    (hf : ∀ i, Integrable (fun a ↦ f a^2) (p i).toMeasure) (hC : 0 < C)
    (hzero : (∫ a, f a ∂(discreteMarginal p).toMeasure) = 0)
    (hroot : (∫ a, f a ∂(p 0).toMeasure) = 2)
    (hsecond : (∫ a, f a^2 ∂(discreteMarginal p).toMeasure) ≤ C) :
    1/(3*C) ≤ ∫ m, tvMessage m ∂(discreteProbability p).toMeasure := by
  let v : α → ℝ := fun a ↦ (discreteMessage p a).1 0-1
  have hv (a : α) : |v a| ≤ 2 := coord_center_abs_le_two _ _
  have hf₂ : Integrable (fun a ↦ f a^2) (discreteMarginal p).toMeasure :=
    pmf_integrable_bind_finite _ _ hf
  have hf₁ := pmf_integrable_of_square _ hf₂
  have hv₂ := pmf_bounded_integrable (discreteMarginal p) (fun a ↦ show |v a^2| ≤ (2:ℝ)^2 by
    rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [hv a, abs_nonneg (v a), sq_abs (v a)])
  have hvf := hf₁.bdd_mul (measurable_of_countable v).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a ↦ show ‖v a‖ ≤ (2:ℝ) from hv a))
  have hcross : (∫ a, v a*f a ∂(discreteMarginal p).toMeasure) = 2 := by
    have he (a : α) : v a*f a = (discreteMessage p a).1 0*f a-f a := by dsimp [v]; ring
    simp_rw [he]
    rw [integral_sub (hf₁.bdd_mul (measurable_of_countable _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a ↦ show ‖(discreteMessage p a).1 0‖ ≤ (3:ℝ) by
        rw [Real.norm_eq_abs, abs_of_nonneg (coordinate_nonneg _ _)]; exact coordinate_le_three _ _))) hf₁,
      discrete_bayes_integral_integrable p 0 hf₁ (pmf_integrable_of_square _ (hf 0)), hroot, hzero, sub_zero]
  let r := 2/C
  have hr : r*C = 2 := div_mul_cancel₀ 2 hC.ne'
  have h := MeasureTheory.integral_nonneg (μ := (discreteMarginal p).toMeasure)
    (f := fun a ↦ (v a-r*f a)^2) (fun _ ↦ sq_nonneg _)
  rw [integral_scaled_square _ r hv₂ hf₂ hvf, hcross] at h
  have hb := mul_le_mul_of_nonneg_left hsecond (sq_nonneg r)
  have hr2 : r^2*C = 2*r := by
    have hh := congrArg (fun x : ℝ ↦ r*x) hr
    nlinarith only [hh]
  have hD : 4 ≤ C*(∫ a, v a^2 ∂(discreteMarginal p).toMeasure) := by
    have hs : 2*r ≤ ∫ a, v a^2 ∂(discreteMarginal p).toMeasure := by
      nlinarith only [h, hb, hr2]
    have hh := mul_le_mul_of_nonneg_left hs hC.le
    nlinarith only [hh, hr]
  have hT := integral_mono hv₂ (pmf_bounded_integrable (discreteMarginal p)
    (fun a ↦ show |12*tvMessage (discreteMessage p a)| ≤ 12 by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 12), abs_of_nonneg (tvMessage_nonneg _)];
      nlinarith [tvMessage_le_one (discreteMessage p a)]))
    (fun a ↦ coord_sq_le_tv (discreteMessage p a) 0)
  rw [integral_const_mul, ← integral_discreteProbability p continuous_tvMessage.measurable] at hT
  apply (div_le_iff₀ (by positivity : 0 < 3*C)).2
  have hh := mul_le_mul_of_nonneg_left hT hC.le
  nlinarith only [hD, hh]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma product_sum_integrable (p : PMF α) {f : α → ℝ} (hf : Integrable f p.toMeasure) (n : ℕ) :
    Integrable (fun v : Fin n → α ↦ ∑ j, f (v j)) (productPMF (fun _ ↦ p)).toMeasure := by
  rw [productPMF_measure]
  simpa [weightProduct] using integrable_weighted_sum (ι := Fin n) (a := fun _ : α ↦ (1:ℝ))
    (u := f) (integrable_const 1) (by simpa using hf)

lemma product_square_sum_integrable (p : PMF α) {f : α → ℝ}
    (hf : Integrable (fun a ↦ f a^2) p.toMeasure) (n : ℕ) :
    Integrable (fun v : Fin n → α ↦ (∑ j, f (v j))^2) (productPMF (fun _ ↦ p)).toMeasure := by
  rw [productPMF_measure]
  simpa [weightProduct] using integrable_weighted_sq_sum (ι := Fin n) (a := fun _ : α ↦ (1:ℝ))
    (u := f) (integrable_const 1) (by simpa using pmf_integrable_of_square p hf) (by simpa using hf)

lemma integral_product_sum_integrable (p : PMF α) {f : α → ℝ}
    (hf : Integrable f p.toMeasure) (n : ℕ) :
    (∫ v : Fin n → α, (∑ j, f (v j)) ∂(productPMF (fun _ ↦ p)).toMeasure) =
      (n:ℝ)*(∫ a, f a ∂p.toMeasure) := by
  rw [productPMF_measure]
  simpa [weightProduct] using integral_weighted_sum (ι := Fin n) (a := fun _ : α ↦ (1:ℝ))
    (u := f) (integrable_const 1) (by simpa using hf) (by simp)

lemma integral_product_sq_sum_integrable (p : PMF α) {f : α → ℝ}
    (hf : Integrable (fun a ↦ f a^2) p.toMeasure) (n : ℕ) :
    (∫ v : Fin n → α, (∑ j, f (v j))^2 ∂(productPMF (fun _ ↦ p)).toMeasure) =
      (n:ℝ)*(∫ a, f a^2 ∂p.toMeasure)+((n:ℝ)^2-n)*(∫ a, f a ∂p.toMeasure)^2 := by
  rw [productPMF_measure]
  simpa [weightProduct] using integral_weighted_sq_sum (ι := Fin n) (a := fun _ : α ↦ (1:ℝ))
    (u := f) (integrable_const 1) (by simpa using pmf_integrable_of_square p hf)
    (by simpa using hf) (by simp)

section Sigma
variable {β : ℕ → Type*} [∀ n, Countable (β n)] [∀ n, MeasurableSpace (β n)]
  [∀ n, MeasurableSingletonClass (β n)]

lemma sigmaPMF_integrable (ρ : PMF ℕ) (p : ∀ n, PMF (β n)) {f : Sigma β → ℝ}
    (hf : ∀ n, Integrable (fun a ↦ f ⟨n,a⟩) (p n).toMeasure)
    (hn : Integrable (fun n ↦ ∫ a, |f ⟨n,a⟩| ∂(p n).toMeasure) ρ.toMeasure) :
    Integrable f (sigmaPMF ρ p).toMeasure := by
  rw [sigmaPMF_eq_bind]
  apply pmf_integrable_bind
  · intro n
    exact (pmf_integrable_map_iff (p n) (Sigma.mk n) f).2 (hf n)
  · simpa only [integral_pmf_map] using hn

lemma integral_sigmaPMF_integrable (ρ : PMF ℕ) (p : ∀ n, PMF (β n)) {f : Sigma β → ℝ}
    (hf : Integrable f (sigmaPMF ρ p).toMeasure) :
    (∫ z, f z ∂(sigmaPMF ρ p).toMeasure) = ∫ n, (∫ a, f ⟨n,a⟩ ∂(p n).toMeasure) ∂ρ.toMeasure := by
  rw [sigmaPMF_eq_bind] at hf ⊢
  rw [integral_pmf_bind_integrable _ _ hf]
  simp only [integral_pmf_map]

end Sigma
end ThreeState.TreeClauses.Experiment

end

end OAI
