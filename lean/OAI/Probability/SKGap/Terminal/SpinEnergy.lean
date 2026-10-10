import Mathlib
import OAI.Probability.SKGap.Terminal.FiniteSpinCalculus

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators

lemma sum_edges {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ e : Edge n,f e.1.1 e.1.2)=∑ i,∑ k,if i < k then f i k else 0 := by
  have he := Finset.sum_subtype (F:=inferInstance) (p:=fun p : Fin n×Fin n=>p.1 < p.2) (Finset.univ.filter (fun p : Fin n×Fin n=>p.1 < p.2))
    (by simp) (fun p=>f p.1 p.2)
  simpa only [Finset.sum_filter,Fintype.sum_prod_type] using he.symm

lemma edge_energy_formula {n : ℕ} (g : Disorder n) (x : Spin n) :
    hamiltonian g 0 x=∑ e : Edge n,g e*spinValue (x e.1.1)*spinValue (x e.1.2) := by
  let f : Fin n → Fin n → ℝ := fun i k=>spinValue (x i)*coupling g i k*spinValue (x k)
  have hsymm : ∀ i k,f i k=f k i := by intro i k; dsimp [f];rw [coupling_symm g i k];ring
  have hz : ∀ i,f i i=0 := by intro i;simp [f]
  have hf : (∑ i,∑ k,f i k)=2*∑ i,∑ k,if i < k then f i k else 0 := by
    have hh : ∀ i k,f i k=(if i < k then f i k else 0)+(if k < i then f k i else 0) := by
      intro i k
      rcases lt_trichotomy i k with h|rfl|h
      · simp [h,not_lt_of_gt h]
      · simp [hz]
      · simp only [ite_eq_right (not_lt_of_gt h),ite_eq_left h,zero_add];exact hsymm i k
    conv_lhs => arg 2; ext i; arg 2; ext k; rw [hh i k]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f:=fun i k=>if k < i then f k i else 0)]
    ring
  have he : (∑ e : Edge n,g e*spinValue (x e.1.1)*spinValue (x e.1.2))=
      ∑ i,∑ k,if i < k then f i k else 0 := by
    rw [← sum_edges f]
    apply Finset.sum_congr rfl
    intro e _
    simp only [f,coupling,dite_eq_left e.2]
    ring
  rw [he]
  change 1/2*(∑ i,∑ k,f i k)+ (∑ i,(0:Fin n→ℝ) i*spinValue (x i))=_
  simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]
  rw [hf];ring

lemma edge_symmetric_sum {n : ℕ} (u : Fin n → ℝ) :
    2*(∑ e : Edge n,u e.1.1*u e.1.2)=(∑ i,u i)^2-∑ i,u i^2 := by
  rw [sum_edges (fun i k=>u i*u k)]
  have hh : ∀ i k,u i*u k=(if i < k then u i*u k else 0)+
      (if k < i then u k*u i else 0)+(if i=k then u i^2 else 0) := by
    intro i k
    rcases lt_trichotomy i k with h|rfl|h
    · simp [h,not_lt_of_gt h,ne_of_lt h]
    · simp [sq]
    · simp [h,not_lt_of_gt h,ne_of_gt h,mul_comm]
  have hs : (∑ i,u i)^2=2*(∑ i,∑ k,if i < k then u i*u k else 0)+∑ i,u i^2 := by
    rw [sq,Finset.sum_mul_sum]
    conv_lhs => arg 2; ext i; arg 2; ext k; rw [hh i k]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f:=fun i k=>if k < i then u k*u i else 0)]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    ring
  linarith only [hs]

def spinMul {n : ℕ} (x y : Spin n) : Spin n := fun i => !(xor (x i) (y i))

lemma spinValue_mul {n : ℕ} (x y : Spin n) (i : Fin n) :
    spinValue (spinMul x y i)=spinValue (x i)*spinValue (y i) := by
  cases hx : x i <;> cases hy : y i <;> simp [spinMul,hx,hy,spinValue]

lemma spinMul_involutive {n : ℕ} (x : Spin n) : Function.Involutive (spinMul x) := by
  intro y;ext i
  cases hx : x i <;> cases hy : y i <;> simp [spinMul,hx,hy]

lemma sum_spinMul {n : ℕ} (x : Spin n) (f : Spin n→ℝ) :
    (∑ y,f (spinMul x y))=∑ y,f y :=
  Equiv.sum_comp (Function.Involutive.toPerm (spinMul x) (spinMul_involutive x)) f

lemma spin_exponential_sum {n : ℕ} (a : ℝ) :
    (∑ x : Spin n,exp (a*∑ i,spinValue (x i)))=(2*cosh a)^n := by
  simp_rw [Finset.mul_sum,exp_sum]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool)=>exp (a*spinValue b))]
  simp only [Fintype.sum_bool,spinValue_false,spinValue_true,mul_one,mul_neg_one,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,cosh_eq]
  congr 1;ring

end SKGap
end
end

end OAI
