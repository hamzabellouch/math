import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseGridZero

namespace OAI

section
section
namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

def piece (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) : Fin n → Fin t → ℚ :=
  fun i j => if i∈P j then (K j:ℚ)*y i/p j else 0

abbrev law (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) := SparseBundles.law (piece P y p K)

theorem piece_nonnegative (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j) :
    ∀ i j,0 ≤ piece P y p K i j := by
  intro i j
  dsimp only [piece]
  split_ifs
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hy i)) (hp j).le
  · exact le_rfl

theorem piece_cap (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (Δ : ℕ) (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j)
    (hm : ∀ j,∑ i∈P j,y i=p j) (hK : ∀ j,K j ≤ Δ) :
    ∀ i j,piece P y p K i j ≤ Δ := by
  intro i j
  by_cases hi : i∈P j
  · have hyP : y i ≤ p j := (single_le_sum (fun i _ => hy i) hi).trans_eq (hm j)
    have he : piece P y p K i j ≤ (K j:ℚ) := by
      simp only [piece,ite_eq_left hi]
      apply (div_le_iff₀ (hp j)).mpr
      exact mul_le_mul_of_nonneg_left hyP (Nat.cast_nonneg _)
    exact he.trans (Nat.cast_le.mpr (hK j))
  · simp only [piece,ite_eq_right hi]
    exact Nat.cast_nonneg _

theorem piece_sum (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (hp : ∀ j,0 < p j) (hm : ∀ j,∑ i∈P j,y i=p j) :
    ∀ j,(∑ i,piece P y p K i j)=(K j:ℚ) := by
  intro j
  simp only [piece,sum_ite_mem,univ_inter,← sum_div,← mul_sum,hm]
  exact mul_div_cancel_right₀ _ (hp j).ne'

theorem invariants (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (Δ : ℕ) (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j)
    (hm : ∀ j,∑ i∈P j,y i=p j) (hK : ∀ j,K j ≤ Δ) :
    ∀ a : Fin (law P y p K).length,∀ j,
      (∑ i,(law P y p K).states[a.val] j i)=K j ∧
      (∀ i,(law P y p K).states[a.val] j i ≤ Δ) ∧
      (∀ i,i∉P j → (law P y p K).states[a.val] j i=0) := by
  intro a j
  have hq : ∀ i j,0 ≤ piece P y p K i j ∧ piece P y p K i j ≤ Δ := fun i j => ⟨piece_nonnegative P y p K hy hp i j,piece_cap P y p K Δ hy hp hm hK i j⟩
  have hh := SparseBundles.invariants (piece P y p K) K Δ hq (piece_sum P y p K hp hm) a j
  refine ⟨hh.1,hh.2.1,?_⟩
  intro i hi
  exact SparseBundles.zero (piece P y p K) (piece_nonnegative P y p K hy hp) a i j
    (by simp only [piece,ite_eq_right hi])

theorem mean (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j)
    (hm : ∀ j,∑ i∈P j,y i=p j) (i : Fin n) (j : Fin t) :
    (law P y p K).moment (fun G => (G j i:ℚ))=piece P y p K i j :=
  SparseBundles.single (piece P y p K) K (piece_nonnegative P y p K hy hp)
    (piece_sum P y p K hp hm) i j

theorem pair (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j)
    (hm : ∀ j,∑ i∈P j,y i=p j) (i h : Fin n) (j k : Fin t) (hh : i≠h ∨ j≠k) :
    (law P y p K).moment (fun G => (G j i:ℚ)*(G k h:ℚ)) ≤
      piece P y p K i j*piece P y p K h k := by
  by_cases hjk : j=k
  · subst k
    exact SparseBundles.same_pair (piece P y p K) K (piece_nonnegative P y p K hy hp)
      (piece_sum P y p K hp hm) i h j (hh.resolve_right (not_not.mpr rfl))
  · exact (SparseBundles.cross_pair (piece P y p K) K (piece_nonnegative P y p K hy hp)
      (piece_sum P y p K hp hm) i h j k hjk).le

end MetricKMedian.SparseRescaledInner
end
end

end OAI
