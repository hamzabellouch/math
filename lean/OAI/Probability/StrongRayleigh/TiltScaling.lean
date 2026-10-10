import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem336AdditiveD139

variable {F : Type u_1} [Fintype F]

lemma exp_bool_sum_eq_prod (h : F → ℝ) (x : F → Bool) :
    (Real.exp (∑ i : F, h i * boolReal (x i)) : ℂ) =
      ∏ i : F, if x i = true then (Real.exp (h i) : ℂ) else 1 := by
  classical
  rw [Real.exp_sum, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  cases x i <;> simp [boolReal]

lemma generating_monomial_rescale (h : F → ℝ) (x : F → Bool) (z : F → ℂ) :
    (∏ i : F, if x i = true then (Real.exp (h i) : ℂ) * z i else 1) =
      (Real.exp (∑ i : F, h i * boolReal (x i)) : ℂ) *
        ∏ i : F, if x i = true then z i else 1 := by
  classical
  rw [exp_bool_sum_eq_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases x i <;> simp

lemma finiteGeneratingValue_exp (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) :
    finiteGeneratingValue μ (fun i => (Real.exp (h i) : ℂ)) =
      (tiltPartition μ h : ℂ) := by
  classical
  unfold finiteGeneratingValue tiltPartition
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← exp_bool_sum_eq_prod, Complex.ofReal_mul]
  ring

lemma finiteGeneratingValue_of_tilt_atoms
    (μ ν : ProbabilityMeasure (F → Bool)) (h : F → ℝ)
    (hatom : ∀ x : F → Bool,
      ((ν : Measure (F → Bool)) {x}).toReal =
        Real.exp (∑ i : F, h i * boolReal (x i)) *
          ((μ : Measure (F → Bool)) {x}).toReal / tiltPartition μ h)
    (z : F → ℂ) :
    finiteGeneratingValue ν z =
      finiteGeneratingValue μ (fun i => (Real.exp (h i) : ℂ) * z i) /
        (tiltPartition μ h : ℂ) := by
  classical
  unfold finiteGeneratingValue
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hatom, Complex.ofReal_div, Complex.ofReal_mul,
    generating_monomial_rescale]
  ring

lemma stronglyRayleighFinite_of_tilt_atoms
    (μ ν : ProbabilityMeasure (F → Bool)) (h : F → ℝ)
    (hμ : StronglyRayleighFinite μ) (hZ : tiltPartition μ h ≠ 0)
    (hatom : ∀ x : F → Bool,
      ((ν : Measure (F → Bool)) {x}).toReal =
        Real.exp (∑ i : F, h i * boolReal (x i)) *
          ((μ : Measure (F → Bool)) {x}).toReal / tiltPartition μ h) :
    StronglyRayleighFinite ν := by
  intro z hz
  rw [finiteGeneratingValue_of_tilt_atoms μ ν h hatom z]
  apply div_ne_zero
  · apply hμ
    intro i
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos (Real.exp_pos (h i)) (hz i)
  · exact_mod_cast hZ

end Problem336AdditiveD139

end

end OAI
