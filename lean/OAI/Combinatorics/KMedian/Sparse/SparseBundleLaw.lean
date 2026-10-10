import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationMoments
import OAI.Combinatorics.KMedian.Sparse.SparseRealLaw
import OAI.Combinatorics.KMedian.Sparse.SparseGridRounding
import OAI.Combinatorics.KMedian.Sparse.SparseCountRun

namespace OAI

section
section
namespace MetricKMedian.SparseBundles
open Finset
variable {n m : ℕ}

abbrev law (q : Fin n → Fin m → ℚ) : SparseIntegerLaw (SparseCounts.Table n m) :=
  SparseCounts.run (fun j => SparseGridRounding.law (fun i => q i j)) m

theorem length (q : Fin n → Fin m → ℚ) :
    (law q).length ≤ n*m+(n*m)*(n*m)+1 := SparseCounts.run_length _ _

theorem single (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ)) (i : Fin n) (j : Fin m) :
    (law q).moment (fun G => (G j i:ℚ))=q i j := by
  have hh := SparseCounts.run_single (fun j => SparseGridRounding.law (fun i => q i j)) q
    (fun i j => SparseGridRounding.law_mean (fun i => q i j) (K j) (fun i => hq i j) (hs j) i)
    m le_rfl i j
  simpa only [SparseCounts.target,SparseCounts.edge,ite_eq_left j.isLt] using hh

theorem cross_pair (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ))
    (i h : Fin n) (j k : Fin m) (hjk : j≠k) :
    (law q).moment (fun G => (G j i:ℚ)*(G k h:ℚ))=q i j*q h k := by
  have hh := SparseCounts.run_pair (fun j => SparseGridRounding.law (fun i => q i j)) q
    (fun i j => SparseGridRounding.law_mean (fun i => q i j) (K j) (fun i => hq i j) (hs j) i)
    m le_rfl i h j k hjk
  simpa only [SparseCounts.target,SparseCounts.edge,ite_eq_left j.isLt,ite_eq_left k.isLt] using hh

theorem same_pair (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ))
    (i h : Fin n) (j : Fin m) (hih : i≠h) :
    (law q).moment (fun G => (G j i:ℚ)*(G j h:ℚ)) ≤ q i j*q h j := by
  have hh := SparseCounts.run_same (fun j => SparseGridRounding.law (fun i => q i j)) m le_rfl i h j
  simp only [SparseCounts.edge,ite_eq_left j.isLt] at hh
  exact hh.trans_le (SparseGridRounding.law_pair (fun i => q i j) (K j)
    (fun i => hq i j) (hs j) i h hih)

theorem invariants (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ)) :
    ∀ a : Fin (law q).length, ∀ j,
      (∑ i,(law q).states[a.val] j i)=K j ∧
      (∀ i,(law q).states[a.val] j i ≤ L) ∧
      (∀ i,(law q).states[a.val] j i=SparseGridRounding.base (fun i => q i j) i ∨
        (law q).states[a.val] j i=SparseGridRounding.base (fun i => q i j) i+1) := by
  intro a j
  exact SparseCounts.run_columns (fun j => SparseGridRounding.law (fun i => q i j))
    (fun j S => (∑ i,S i)=K j ∧ (∀ i,S i ≤ L) ∧
      (∀ i,S i=SparseGridRounding.base (fun i => q i j) i ∨
        S i=SparseGridRounding.base (fun i => q i j) i+1))
    (fun j => SparseGridRounding.law_invariants (fun i => q i j) (K j) L (fun i => hq i j) (hs j))
    m le_rfl a j j.isLt

theorem variance (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ))
    (i : Fin n) (j : Fin m) :
    (law q).realIndex.variance (fun a => ((law q).states[a.val] j i:ℝ)) ≤ (q i j:ℝ) := by
  apply FiniteLaw.adjacent_variance _ _
    (m := SparseGridRounding.base (fun i => q i j) i) (Nat.cast_nonneg _) ?_ ?_
  · intro a _
    rcases (invariants q K L hq hs a j).2.2 i with hh | hh
    · exact Or.inl (by exact_mod_cast hh)
    · exact Or.inr (by exact_mod_cast hh)
  · have hh := (law q).realIndex_expect (fun G => (G j i:ℚ))
    simp only [Rat.cast_natCast] at hh
    rw [hh,single q K (fun i j => (hq i j).1) hs]

end MetricKMedian.SparseBundles
end
end

end OAI
