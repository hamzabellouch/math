import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace SineProduct

lemma one_failure_le {I : Type*} [DecidableEq I] (s : Finset I) (h : I → ℝ)
    (h0 : ∀ i∈s, 0≤h i) (h1 : ∀ i∈s, h i≤1) :
    (∑ i∈s, (1-h i)*∏ j∈s.erase i, h j)+(∏ i∈s, h i)≤1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hp : ∀ i∈s, 0≤h i := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
    have hq : ∀ i∈s, h i≤1 := fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi)
    have hh := ih hp hq
    have hn : 0≤∑ i∈s, (1-h i)*∏ j∈s.erase i,h j := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (sub_nonneg.mpr (hq i hi))
        (Finset.prod_nonneg fun j hj ↦ hp j (Finset.mem_of_mem_erase hj))
    have he : (∑ i∈insert a s, (1-h i)*∏ j∈(insert a s).erase i, h j)=
        (1-h a)*(∏ j∈s,h j)+h a*(∑ i∈s, (1-h i)*∏ j∈s.erase i,h j) := by
      rw [Finset.sum_insert ha,Finset.erase_insert ha,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i≠a := fun he ↦ ha (he ▸ hi)
      rw [Finset.erase_insert_of_ne hia.symm,Finset.prod_insert (by simp [ha])]
      ring
    rw [he,Finset.prod_insert ha]
    nlinarith [mul_le_mul_of_nonneg_right (h1 a (Finset.mem_insert_self a s)) hn]

lemma coefficients_sq_le {I : Type*} [DecidableEq I] (s : Finset I) (θ : I → ℝ) :
    ∑ i∈s, (Real.cos (θ i)*∏ j∈s.erase i,Real.sin (θ j))^2≤1 := by
  have h := one_failure_le s (fun i ↦ Real.sin (θ i)^2) (fun _ _ ↦ sq_nonneg _)
    (fun i _ ↦ by nlinarith [Real.sin_sq_add_cos_sq (θ i),sq_nonneg (Real.cos (θ i))])
  have he : (∑ i∈s, (1-Real.sin (θ i)^2)*∏ j∈s.erase i,Real.sin (θ j)^2)=
      ∑ i∈s, (Real.cos (θ i)*∏ j∈s.erase i,Real.sin (θ j))^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow,← Finset.prod_pow]
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq (θ i)]
  rw [he] at h
  exact le_trans (le_add_of_nonneg_right (Finset.prod_nonneg fun _ _ ↦ sq_nonneg _)) h

lemma contraction_sq {I : Type*} [DecidableEq I] (s : Finset I) (θ d : I → ℝ) :
    (∑ i∈s, (Real.cos (θ i)*∏ j∈s.erase i,Real.sin (θ j))*d i)^2≤∑ i∈s,d i^2 := by
  exact (Finset.sum_mul_sq_le_sq_mul_sq s _ d).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (coefficients_sq_le s θ)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))

lemma deriv_sq_le {I : Type*} [DecidableEq I] (s : Finset I) (θ : I → ℝ → ℝ)
    (d : I → ℝ) (x : ℝ) (hd : ∀ i∈s, HasDerivAt (θ i) (d i) x) :
    (deriv (fun y ↦ ∏ i∈s,Real.sin (θ i y)) x)^2≤∑ i∈s,d i^2 := by
  have hp := HasDerivAt.fun_finsetProd (u := s) (fun i hi ↦ (hd i hi).sin)
  rw [hp.deriv]
  convert contraction_sq s (fun i ↦ θ i x) d using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma fderiv_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [DecidableEq I] (s : Finset I) (θ : I → E → ℝ) (x v : E)
    (hd : ∀ i∈s, DifferentiableAt ℝ (θ i) x) :
    (fderiv ℝ (fun y ↦ ∏ i∈s,Real.sin (θ i y)) x v)^2≤
      ∑ i∈s,(fderiv ℝ (θ i) x v)^2 := by
  have hp := HasFDerivAt.finsetProd (u := s) (fun i hi ↦ (hd i hi).hasFDerivAt.sin)
  rw [hp.fderiv,sum_apply]
  simp only [smul_apply,smul_eq_mul]
  convert contraction_sq s (fun i ↦ θ i x) (fun i ↦ fderiv ℝ (θ i) x v) using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SineProduct

end

end OAI
