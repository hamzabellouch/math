import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseWeightedPartial
import OAI.Combinatorics.KMedian.Rounding.RationalLastFraction

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

def round (p : Vector ℚ n) : SparseIntegerLaw (Vector ℚ n) :=
  SparseWeightedPartial.run (fun _ => 1) (fun _ => by norm_num) p n

theorem integral_of_small_fractional (q : Vector ℚ n)
    (hq : ∀ i, 0 ≤ point q i ∧ point q i ≤ 1) (K : ℕ)
    (hs : (∑ i, point q i)=(K:ℚ)) (hf : (fractional q).card ≤ 1) :
    ∀ i, point q i=0 ∨ point q i=1 := by
  have has : MarginalRounding.fractional (realPoint q)=∅ := by
    by_contra h
    obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr h
    have h0 : ∀ i, 0 ≤ realPoint q i := fun i => by
      dsimp only [realPoint]; exact_mod_cast (hq i).1
    have h1 : ∀ i, realPoint q i ≤ 1 := fun i => by
      dsimp only [realPoint]; exact_mod_cast (hq i).2
    have hsum : (∑ i, realPoint q i)=(K:ℝ) := by
      dsimp only [realPoint]; exact_mod_cast hs
    obtain ⟨j,hj,hji⟩ := MarginalRounding.second_fractional h0 h1 hsum hi
    rw [real_fractional] at hi hj
    exact hji (card_le_one.mp hf j hj i hi)
  intro i
  apply RationalLastFraction.nonfractional q hq i
  rw [← real_fractional,has]
  exact notMem_empty i

theorem round_invariants (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (K : ℕ)
    (hs : (∑ i, point p i)=(K:ℚ)) :
    ∀ a : Fin (round p).length,
      (∀ i, point (round p).states[a.val] i=0 ∨ point (round p).states[a.val] i=1) ∧
      (∑ i, point (round p).states[a.val] i)=(K:ℚ) := by
  intro a
  obtain ⟨h0,h1,h2⟩ := SparseWeightedPartial.run_invariants (fun _ => 1)
    (fun _ => by norm_num) p hp n a
  simp only [one_mul] at h1
  have hsum : (∑ i, point (round p).states[a.val] i)=(K:ℚ) := h1.trans hs
  exact ⟨integral_of_small_fractional _ h0 K hsum (by simpa only [round, Nat.sub_self, max_eq_right (Nat.zero_le 1)] using h2),hsum⟩

theorem round_mean (p : Vector ℚ n) (i : Fin n) :
    (round p).moment (fun q => point q i)=point p i :=
  SparseWeightedPartial.run_mean _ _ p n i

theorem round_pair (p : Vector ℚ n) (i j : Fin n) (hij : i ≠ j) :
    (round p).moment (fun q => point q i*point q j) ≤ point p i*point p j :=
  SparseWeightedPartial.run_pair _ _ p n i j hij

theorem round_length (p : Vector ℚ n) : (round p).length ≤ n+n*n+1 :=
  SparseWeightedPartial.run_length _ _ p n

def selected (q : Vector ℚ n) : Finset (Fin n) := univ.filter (fun i => point q i=1)

theorem selected_indicator (q : Vector ℚ n)
    (hq : ∀ i, point q i=0 ∨ point q i=1) (i : Fin n) :
    (if i ∈ selected q then (1:ℚ) else 0)=point q i := by
  rcases hq i with h | h <;> simp [selected,h]

theorem selected_card (q : Vector ℚ n)
    (hq : ∀ i, point q i=0 ∨ point q i=1) (K : ℕ)
    (hs : (∑ i, point q i)=(K:ℚ)) : (selected q).card=K := by
  have he : ((selected q).card:ℚ)=(K:ℚ) := by
    calc
      _ = ∑ i, if i ∈ selected q then (1:ℚ) else 0 := by simp
      _ = ∑ i, point q i := sum_congr rfl (fun i _ => selected_indicator q hq i)
      _ = _ := hs
  exact_mod_cast he

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
