import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryShortDual

def shiftedDual (c : ℕ → ℂ) (D U n : ℕ) : ℂ :=
  if D≤n ∧ n-D<U then c (n-D) else 0

lemma shiftedDual_bound (c : ℕ → ℂ) (hc : ∀n,‖c n‖≤1) (D U n : ℕ) :
    ‖shiftedDual c D U n‖≤1 := by
  unfold shiftedDual
  split_ifs
  · exact hc _
  · simp

theorem dual_fubini (c F : ℕ → ℂ) (D U : ℕ) :
    (∑y∈range U,c y*∑k∈range D,F (y+1+k))=
      ∑m∈range (U+D),F m*∑j∈range D,shiftedDual c D U (m+j) := by
  let s := range U ×ˢ range D
  let t := (range (U+D) ×ˢ range D).filter (fun x => D≤x.1+x.2 ∧ x.1+x.2-D<U)
  have hi : (∑x∈s,c x.1*F (x.1+1+x.2))=
      ∑x∈t,F x.1*c (x.1+x.2-D) := by
    apply sum_bij (fun x _ => (x.1+1+x.2,D-(x.2+1)))
    · intro x hx
      rcases x with ⟨y,k⟩
      simp only [s,mem_product,Finset.mem_range] at hx
      simp only [t,mem_filter,mem_product,Finset.mem_range]
      omega
    · intro x hx z hz he
      rcases x with ⟨y,k⟩
      rcases z with ⟨v,j⟩
      simp only [s,mem_product,Finset.mem_range] at hx hz
      simp only [Prod.mk.injEq] at he
      congr 1 <;> omega
    · intro x hx
      rcases x with ⟨m,j⟩
      simp only [t,mem_filter,mem_product,Finset.mem_range] at hx
      refine ⟨(m+j-D,D-j-1),?_,?_⟩
      · simp only [s,mem_product,Finset.mem_range]
        omega
      · simp only [Prod.mk.injEq]
        omega
    · intro x hx
      rcases x with ⟨y,k⟩
      simp only [s,mem_product,Finset.mem_range] at hx
      have he : y+1+k+(D-(k+1))-D=y := by omega
      rw [he,mul_comm]
  calc
    _ = ∑x∈s,c x.1*F (x.1+1+x.2) := by simp only [s,sum_product,mul_sum]
    _ = ∑x∈t,F x.1*c (x.1+x.2-D) := hi
    _ = _ := by
      simp only [t,sum_filter,sum_product,shiftedDual,mul_sum]
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro j hj
      split_ifs <;> simp

end OrdinaryShortDual

end

end OAI
