import Mathlib
import OAI.Probability.SKGap.Terminal.PairConditioning

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

def siteVariance (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) : ℝ :=
  1-tanh (localField g h i x)^2

def weightedGradient (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (f : Spin n→ℝ) (x : Spin n) : ℝ :=
  siteVariance g h i x*spinGradient i f x

lemma pairConditional_signed_bound (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (f : Spin n→ℝ) (x : Spin n) (hc : |tanh (coupling g i j)| ≤ 1/1000) :
    -tanh (coupling g i j)*pairConditionalMean g h i j
      (fun x=>weightedGradient g h i f x*weightedGradient g h j f x) x-
    400000*tanh (coupling g i j)^2*pairConditionalMean g h i j
      (fun x=>|weightedGradient g h i f x*weightedGradient g h j f x|) x-
    400000*tanh (coupling g i j)^4*pairConditionalMean g h i j
      (fun x=>siteVariance g h i x*spinGradient i f x^2+siteVariance g h j x*spinGradient j f x^2) x ≤
    pairConditionalMean g h i j (fun x=>(f x-conditionalExpectation g h i f x)*
      (f x-conditionalExpectation g h j f x)) x := by
  simp_rw [pairConditionalMean_boltzmann g h i j hij,weightedGradient,siteVariance,
    conditionalDifference_local,pairUpdate_localField₁,pairUpdate_localField₂,
    pairUpdate_gradient₁ i j hij,pairUpdate_gradient₂,pairUpdate_left i j hij,pairUpdate_right]
  exact pairBoltzmann_signed_bound
    (localField g h i x-coupling g i j*spinValue (x j))
    (localField g h j x-coupling g i j*spinValue (x i))
    (coupling g i j) (fun a b=>f (pairUpdate i j x a b)) hc

lemma expectation_mono (g : Disorder n) (h : Fin n→ℝ) {F G : Spin n→ℝ}
    (hFG : ∀ x,F x ≤ G x) : expectation g h F ≤ expectation g h G := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (hFG x) (mass_nonneg g h x)

lemma gibbs_pair_signed_bound (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (f : Spin n→ℝ) (hc : |tanh (coupling g i j)| ≤ 1/1000) :
    -tanh (coupling g i j)*expectation g h
      (fun x=>weightedGradient g h i f x*weightedGradient g h j f x)-
    400000*tanh (coupling g i j)^2*expectation g h
      (fun x=>|weightedGradient g h i f x*weightedGradient g h j f x|)-
    400000*tanh (coupling g i j)^4*(expectation g h
      (fun x=>siteVariance g h i x*spinGradient i f x^2)+expectation g h
      (fun x=>siteVariance g h j x*spinGradient j f x^2)) ≤
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)*
      (f x-conditionalExpectation g h j f x)) := by
  have hh := expectation_mono g h (fun x=>pairConditional_signed_bound g h i j hij f x hc)
  simpa only [expectation_sub,expectation_const_mul,expectation_pairConditionalMean g h i j hij,
    expectation_add] using hh
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

lemma siteVariance_pos (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) :
    0 < siteVariance g h i x := by
  unfold siteVariance
  have ht := abs_tanh_lt_one (localField g h i x)
  have hs := (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mpr ht
  simp only [sq_abs,one_pow] at hs
  linarith only [hs]
lemma siteVariance_le_one (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) :
    siteVariance g h i x ≤ 1 := sub_le_self _ (sq_nonneg _)

lemma dirichlet_weighted (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    dirichlet g h f=∑ i,expectation g h (fun x=>siteVariance g h i x*spinGradient i f x^2) := by
  unfold dirichlet siteVariance
  simp_rw [conditionalSiteEnergy_local]

lemma symmetric_fourth_cost {ι : Type*} [Fintype ι] (U : ι→ι→ℝ) (D : ι→ℝ) {R : ℝ}
    (hU : ∀ i j,U i j=U j i) (hD : ∀ i,0 ≤ D i)
    (hR : ∀ i,∑ j,U i j^4 ≤ R) :
    (∑ i,∑ j,U i j^4*(D i+D j)) ≤ 2*R*(∑ i,D i) := by
  simp_rw [mul_add,Finset.sum_add_distrib]
  have h₁ : (∑ i,∑ j,U i j^4*D i) ≤ R*∑ i,D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hR i) (hD i)
  have h₂ : (∑ i,∑ j,U i j^4*D j)=(∑ i,∑ j,U i j^4*D i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hU j i]
  rw [h₂]
  linarith only [h₁]

lemma heatBathGenerator_square (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    expectation g h (fun x=>heatBathGenerator g h f x^2)=
      ∑ i,∑ j,expectation g h (fun x=>(f x-conditionalExpectation g h i f x)*
        (f x-conditionalExpectation g h j f x)) := by
  simp only [heatBathGenerator,sq,Finset.sum_mul,Finset.mul_sum,expectation_sum]
  rw [Finset.sum_comm]

theorem gibbs_signed_curvature (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) {R : ℝ}
    (hc : ∀ i j,|tanh (coupling g i j)| ≤ 1/1000)
    (hR : ∀ i,∑ j,tanh (coupling g i j)^4 ≤ R) :
    (1-800000*R)*dirichlet g h f-
      expectation g h (fun x=>∑ i,∑ j,tanh (coupling g i j)*
        weightedGradient g h i f x*weightedGradient g h j f x)-
      400000*expectation g h (fun x=>∑ i,∑ j,tanh (coupling g i j)^2*
        |weightedGradient g h i f x*weightedGradient g h j f x|) ≤
      expectation g h (fun x=>heatBathGenerator g h f x^2) := by
  let U := fun i j=>tanh (coupling g i j)
  let D := fun i=>expectation g h (fun x=>siteVariance g h i x*spinGradient i f x^2)
  let A := fun i j=>expectation g h (fun x=>weightedGradient g h i f x*weightedGradient g h j f x)
  let B := fun i j=>expectation g h (fun x=>|weightedGradient g h i f x*weightedGradient g h j f x|)
  let X := fun i j=>expectation g h (fun x=>(f x-conditionalExpectation g h i f x)*
    (f x-conditionalExpectation g h j f x))
  have hpair (i j : Fin n) : (if i=j then D i else 0)-U i j*A i j-
      400000*U i j^2*B i j-400000*U i j^4*(D i+D j) ≤ X i j := by
    by_cases hij : i=j
    · subst j
      have hX : X i i=D i := by
        dsimp [X,D,siteVariance]
        simp only [← sq,conditionalSiteEnergy_local]
      simp only [U,coupling_diag,tanh_zero,zero_mul,mul_zero,zero_pow (by omega : (2:ℕ) ≠ 0),
        zero_pow (by omega : (4:ℕ) ≠ 0),sub_zero,ite_true,hX,le_refl]
    · simpa only [ite_eq_right hij,zero_sub,neg_mul,U,A,B,D,X] using gibbs_pair_signed_bound g h i j hij f (hc i j)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ)=>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ)=>hpair i j))
  have hcost := symmetric_fourth_cost U D (fun i j=>congrArg tanh (coupling_symm g i j))
    (fun i=>expectation_nonneg g h (fun x=>mul_nonneg (siteVariance_pos g h i x).le (sq_nonneg _))) hR
  have hD : (∑ i,D i)=dirichlet g h f := (dirichlet_weighted g h f).symm
  have hX : (∑ i,∑ j,X i j)=expectation g h (fun x=>heatBathGenerator g h f x^2) :=
    (heatBathGenerator_square g h f).symm
  have hA : expectation g h (fun x=>∑ i,∑ j,tanh (coupling g i j)*
      weightedGradient g h i f x*weightedGradient g h j f x)=∑ i,∑ j,U i j*A i j := by
    simp only [expectation_sum,mul_assoc,expectation_const_mul,U,A]
  have hB : expectation g h (fun x=>∑ i,∑ j,tanh (coupling g i j)^2*
      |weightedGradient g h i f x*weightedGradient g h j f x|)=∑ i,∑ j,U i j^2*B i j := by
    simp only [expectation_sum,expectation_const_mul,U,B]
  simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true] at hsum
  simp only [← Finset.mul_sum,mul_assoc] at hsum
  rw [hD,hX] at hsum
  rw [hD] at hcost
  rw [hA,hB]
  nlinarith only [hsum,hcost]
end SKGap

end
end

end OAI
