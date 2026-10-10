import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMap
import OAI.Combinatorics.KMedian.Sparse.SparseAffineMoments
import OAI.Combinatorics.KMedian.Sparse.SparseCardinalFixed

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open Finset
open RationalWeightedStep (point)
variable {n : ℕ}

def base (q : Fin n → ℚ) (i : Fin n) : ℕ := ⌊q i⌋₊
def fraction (q : Fin n → ℚ) : Vector ℚ n := Vector.ofFn (fun i => q i-(base q i:ℚ))
def count (q : Fin n → ℚ) (p : Vector ℚ n) (i : Fin n) : ℕ :=
  base q i+if point p i=1 then 1 else 0

def law (q : Fin n → ℚ) : SparseIntegerLaw (Fin n → ℕ) :=
  (SparseCardinalRounding.round (fraction q)).map (count q)

theorem fraction_unit (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∀ i, 0 ≤ point (fraction q) i ∧ point (fraction q) i ≤ 1 := by
  intro i
  simp only [point,fraction,Vector.getElem_ofFn]
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le (hq i))
  · have hh := Nat.lt_floor_add_one (q i)
    dsimp only [base]
    linarith only [hh]

theorem base_sum_le (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) (K : ℕ)
    (hs : (∑ i, q i)=(K:ℚ)) : (∑ i, base q i) ≤ K := by
  have hh : (∑ i, (base q i:ℚ)) ≤ (K:ℚ) :=
    (sum_le_sum (fun i _ => Nat.floor_le (hq i))).trans_eq hs
  exact_mod_cast hh

theorem fraction_sum (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) (K : ℕ)
    (hs : (∑ i, q i)=(K:ℚ)) :
    (∑ i, point (fraction q) i)=(K-∑ i,base q i:ℕ) := by
  simp only [fraction,point,Vector.getElem_ofFn,sum_sub_distrib,hs,
    Nat.cast_sub (base_sum_le q hq K hs),Nat.cast_sum]

theorem count_cast (q : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, point p i=0 ∨ point p i=1) (i : Fin n) :
    (count q p i:ℚ)=(base q i:ℚ)+point p i := by
  rcases hp i with hi | hi <;> simp [count,hi]

theorem law_invariants (q : Fin n → ℚ) (K L : ℕ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ L) (hs : (∑ i, q i)=(K:ℚ)) :
    ∀ a : Fin (law q).length,
      (∑ i, (law q).states[a.val] i)=K ∧
      (∀ i, (law q).states[a.val] i ≤ L) ∧
      (∀ i, (law q).states[a.val] i=base q i ∨ (law q).states[a.val] i=base q i+1) := by
  intro a
  change Fin (SparseCardinalRounding.round (fraction q)).length at a
  have he := SparseIntegerLaw.map_states (SparseCardinalRounding.round (fraction q)) (count q) a
  change (law q).states[a.val]=_ at he
  rw [he]
  have hh := SparseCardinalRounding.round_invariants (fraction q) (fraction_unit q (fun i => (hq i).1))
    (K-∑ i,base q i) (fraction_sum q (fun i => (hq i).1) K hs) a
  refine ⟨?_,?_,?_⟩
  · have heq : (∑ i, (count q (SparseCardinalRounding.round (fraction q)).states[a.val] i:ℚ))=(K:ℚ) := by
      simp only [count_cast _ _ hh.1,sum_add_distrib,hh.2,
        Nat.cast_sub (base_sum_le q (fun i => (hq i).1) K hs),Nat.cast_sum]
      ring
    exact_mod_cast heq
  · intro i
    have hb : base q i ≤ L := by exact_mod_cast (Nat.floor_le (hq i).1).trans (hq i).2
    by_cases hi : point (SparseCardinalRounding.round (fraction q)).states[a.val] i=1
    · have hl : base q i < L := by
        by_contra hn
        have heq : base q i=L := le_antisymm hb (le_of_not_gt hn)
        have hz : point (fraction q) i=0 := by
          simp only [fraction,point,Vector.getElem_ofFn]
          have hh := Nat.floor_le (hq i).1
          change (base q i:ℚ) ≤ q i at hh
          have hh' := (hq i).2
          rw [heq] at hh ⊢
          linarith only [hh,hh']
        have hfixed := SparseCardinalRounding.zero_fixed (fraction q)
          (fraction_unit q (fun i => (hq i).1)) i hz a
        rw [hi] at hfixed
        norm_num at hfixed
      simpa only [count,ite_eq_left hi] using Nat.add_one_le_iff.mpr hl
    · simpa only [count,ite_eq_right hi,Nat.add_zero] using hb
  · intro i
    unfold count
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (Nat.add_zero _)

theorem law_mean (q : Fin n → ℚ) (K : ℕ) (hq : ∀ i, 0 ≤ q i)
    (hs : (∑ i,q i)=(K:ℚ)) (i : Fin n) :
    (law q).moment (fun c => (c i:ℚ))=q i := by
  rw [law,SparseIntegerLaw.map_moment]
  calc
    _ = (SparseCardinalRounding.round (fraction q)).moment
        (fun p => (base q i:ℚ)+point p i) := by
      apply SparseIntegerLaw.moment_congr
      intro a
      exact count_cast _ _ (SparseCardinalRounding.round_invariants (fraction q)
        (fraction_unit q hq) (K-∑ i,base q i) (fraction_sum q hq K hs) a).1 i
    _ = q i := by
      rw [SparseIntegerLaw.moment_add,SparseIntegerLaw.moment_const,SparseCardinalRounding.round_mean]
      simp only [fraction,point,Vector.getElem_ofFn,add_sub_cancel]

theorem law_pair (q : Fin n → ℚ) (K : ℕ) (hq : ∀ i, 0 ≤ q i)
    (hs : (∑ i,q i)=(K:ℚ)) (i j : Fin n) (hij : i≠j) :
    (law q).moment (fun c => (c i:ℚ)*(c j:ℚ)) ≤ q i*q j := by
  rw [law,SparseIntegerLaw.map_moment]
  calc
    _ = (SparseCardinalRounding.round (fraction q)).moment
        (fun p => ((base q i:ℚ)+point p i)*((base q j:ℚ)+point p j)) := by
      apply SparseIntegerLaw.moment_congr
      intro a
      have hh := SparseCardinalRounding.round_invariants (fraction q)
        (fraction_unit q hq) (K-∑ i,base q i) (fraction_sum q hq K hs) a
      rw [count_cast _ _ hh.1,count_cast _ _ hh.1]
    _ ≤ ((base q i:ℚ)+point (fraction q) i)*((base q j:ℚ)+point (fraction q) j) :=
      SparseIntegerLaw.moment_affine_pair_le _ _ _ _ _ _ _
        (SparseCardinalRounding.round_mean _ i) (SparseCardinalRounding.round_mean _ j)
        (SparseCardinalRounding.round_pair _ i j hij)
    _ = q i*q j := by simp only [fraction,point,Vector.getElem_ofFn,add_sub_cancel]

theorem length (q : Fin n → ℚ) : (law q).length ≤ n+n*n+1 :=
  SparseCardinalRounding.round_length (fraction q)

end MetricKMedian.SparseGridRounding
end
end

end OAI
