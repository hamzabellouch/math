import OAI.NumberTheory.JointDickman.Counting.SamplingConcentration
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace OAI

/-! # Finite weighted Hoeffding inequality -/
namespace JointDickman
open Finset MeasureTheory ProbabilityTheory

noncomputable def finiteMassLaw {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a),hone]
    simp)

theorem finiteMassLaw_integral {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1) (f : A → ℝ) :
    ∫ a, f a ∂(finiteMassLaw p hp hone).toMeasure = finiteExpectation p f := by
  rw [PMF.integral_eq_sum]
  simp only [finiteMassLaw,PMF.ofFintype_apply,ENNReal.toReal_ofReal (hp _),
    smul_eq_mul,finiteExpectation]

theorem finite_hoeffding {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1)
    (f : A → ℝ) {a b : ℝ} (hf : ∀ x, f x ∈ Set.Icc a b) (t : ℝ) :
    finiteExpectation p (fun x => Real.exp (t * (f x - finiteExpectation p f))) ≤
      Real.exp ((b-a)^2*t^2/8) := by
  let : MeasurableSpace A := ⊤
  let μ : Measure A := (finiteMassLaw p hp hone).toMeasure
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := μ)
    (measurable_of_countable f).aemeasurable (ae_of_all μ hf)
  have hm := hsub.mgf_le t
  rw [mgf,finiteMassLaw_integral] at hm
  rw [finiteMassLaw_integral] at hm
  convert hm using 1
  congr 1
  simp only [NNReal.coe_pow,NNReal.coe_div,coe_nnnorm,NNReal.coe_ofNat,Real.norm_eq_abs,
    div_pow,sq_abs]
  ring

theorem finite_hoeffding_diameter {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hone : ∑ a, p a = 1)
    (f : A → ℝ) {c : ℝ} (hf : ∀ x y, |f x - f y| ≤ c) (t : ℝ) :
    finiteExpectation p (fun x => Real.exp (t * (f x - finiteExpectation p f))) ≤
      Real.exp (c^2*t^2/8) := by
  classical
  have hA : Nonempty A := by
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp at hone
  obtain ⟨a,_,ha⟩ := (univ : Finset A).exists_min_image f univ_nonempty
  have hbound (x : A) : f x ∈ Set.Icc (f a) (f a+c) :=
    ⟨ha x (mem_univ _),by have := (abs_le.mp (hf x a)).2; linarith⟩
  simpa only [add_sub_cancel_left] using finite_hoeffding p hp hone f hbound t

end JointDickman

end OAI
