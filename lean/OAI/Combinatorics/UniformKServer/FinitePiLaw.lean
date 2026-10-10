import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteProbability

namespace OAI

                                  
section

noncomputable section
namespace UniformKServer.FiniteProbability
open Finset
open scoped Classical
variable {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]

def Law.pi (P : ∀ i, Law (A i)) : Law (∀ i, A i) where
  weight a := ∏ i, (P i).weight (a i)
  nonneg a := prod_nonneg fun i _ => (P i).nonneg _
  total := by rw [←Fintype.prod_sum]; simp only [Law.total,prod_const_one]

theorem Law.expect_pi_product (P : ∀ i, Law (A i)) (f : ∀ i, A i → ℝ) :
    (Law.pi P).expect (fun a => ∏ i, f i (a i)) = ∏ i, (P i).expect (f i) := by
  simp only [Law.expect,Law.pi,←prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).weight a*f i a)).symm

theorem Law.expect_pi_coordinate (P : ∀ i, Law (A i)) (i : I) (f : A i → ℝ) :
    (Law.pi P).expect (fun a => f (a i)) = (P i).expect f := by
  let g : ∀ j, A j → ℝ := fun j a => if h : j=i then f (h ▸ a) else 1
  have hg (a : ∀ j, A j) : (∏ j, g j (a j))=f (a i) := by
    rw [prod_eq_single i]
    · simp only [g,dite_eq_left rfl]
    · intro j _ hj
      simp only [g,dite_eq_right hj]
    · simp
  have he := Law.expect_pi_product P g
  simp only [hg] at he
  rw [he,prod_eq_single i]
  · simp [g]
  · intro j _ hj
    simp only [g,dite_eq_right hj,Law.expect_const]
  · simp

theorem Law.expect_pi_separate (P : ∀ i, Law (A i)) (i : I)
    (f : A i → ℝ) (g : (∀ i, A i) → ℝ)
    (hg : ∀ a b, (∀ j, j ≠ i → a j=b j) → g a=g b) :
    (Law.pi P).expect (fun a => f (a i)*g a) =
      (P i).expect f*(Law.pi P).expect g := by
  by_cases he : Nonempty (∀ j, A j)
  · let : DecidableEq {j : I // j ≠ i} := fun a b => Classical.propDecidable (a=b)
    let a₀ : ∀ j, A j := Classical.choice he
    let e := Equiv.piSplitAt i A
    have hweight (x : A i × (∀ j : {j // j ≠ i}, A j.val)) :
        (Law.pi P).weight (e.symm x) = (P i).weight x.1 *
          ∏ j : {j // j ≠ i}, (P j.val).weight (x.2 j) := by
      change (∏ j, (P j).weight (e.symm x j))=_
      rw [←mul_prod_erase _ _ (mem_univ i)]
      have h0 : e.symm x i=x.1 := by simp [e,Equiv.piSplitAt]
      rw [h0]
      congr 1
      rw [Finset.prod_subtype (p:=fun j : I => j ≠ i) (univ.erase i) (by simp [eq_comm])]
      apply prod_congr rfl
      intro j _
      simp [e,Equiv.piSplitAt,j.property]
    have hg' (x : A i × (∀ j : {j // j ≠ i}, A j.val)) :
        g (e.symm x)=g (e.symm (a₀ i,x.2)) := by
      apply hg
      intro j hj
      simp [e,Equiv.piSplitAt,hj]
    have hfun (a : A i) (b : ∀ j : {j // j ≠ i}, A j.val) :
        (e.symm (a,b)) i=a := by simp [e,Equiv.piSplitAt]
    let Q := Law.pi (fun j : {j // j ≠ i} => P j.val)
    have hleft : (Law.pi P).expect (fun a => f (a i)*g a)=
        (P i).expect f * Q.expect (fun b => g (e.symm (a₀ i,b))) := by
      unfold Law.expect
      rw [←e.symm.sum_comp,Fintype.sum_prod_type]
      simp only [hweight,hfun,hg']
      simp only [Q,Law.pi]
      rw [sum_mul]
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      ring
    have hright : (Law.pi P).expect g=Q.expect (fun b => g (e.symm (a₀ i,b))) := by
      unfold Law.expect
      rw [←e.symm.sum_comp,Fintype.sum_prod_type]
      simp only [hweight,hg',mul_assoc,←mul_sum,←sum_mul,(P i).total,one_mul]
      rfl
    rw [hleft,hright]
  · have hzero : (∑ a : ∀ j, A j, (Law.pi P).weight a)=0 := by
      apply sum_eq_zero
      intro a _
      exact (he ⟨a⟩).elim
    have := (Law.pi P).total
    linarith

end UniformKServer.FiniteProbability

end


end

end OAI
