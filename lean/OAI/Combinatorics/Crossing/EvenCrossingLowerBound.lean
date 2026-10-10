import OAI.Combinatorics.Crossing.OddCrossingLowerBound
import OAI.Combinatorics.Crossing.DeletionCount

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem even_successor_crossing_lower_bound (m s : ℕ) (D : AdmissibleDrawing m ((2*s+1)+1)) :
    axisPairs m*axisPairs ((2*s+1)+1) ≤ crossingCount D := by
  by_cases hs : 0 < s
  · obtain ⟨A,hcount,hpoly,hnorm,hstraight,htrans⟩ := polygonal_no_adjacent_locally_transverse D
    have hsum : (∑ v : Fin ((2*s+1)+1), axisPairs m*axisPairs (2*s+1)) ≤
        ∑ v : Fin ((2*s+1)+1), crossingCount (deleteRightVertex A v) := by
      apply Finset.sum_le_sum
      intro v hv
      exact odd_crossing_lower_bound m s (deleteRightVertex A v)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    rw [sum_delete_crossingCount A hnorm] at hsum
    have hN : (2*s+1)+1=2*(s+1) := by omega
    have hprev : 2*s+1=2*(s+1)-1 := by omega
    have hfloor : ((2*s+1)+1)*axisPairs (2*s+1)=
        (((2*s+1)+1)-2)*axisPairs ((2*s+1)+1) := by
      rw [hN,hprev]
      exact even_deletion_floor (s+1)
    have hmul : (((2*s+1)+1)-2)*(axisPairs m*axisPairs ((2*s+1)+1)) ≤
        (((2*s+1)+1)-2)*crossingCount A := by
      calc
        _ = axisPairs m*((((2*s+1)+1)-2)*axisPairs ((2*s+1)+1)) := by ring
        _ = axisPairs m*(((2*s+1)+1)*axisPairs (2*s+1)) := by rw [← hfloor]
        _ = ((2*s+1)+1)*(axisPairs m*axisPairs (2*s+1)) := by ring
        _ ≤ _ := hsum
    exact (Nat.le_of_mul_le_mul_left hmul (by omega)).trans hcount
  · have he : s=0 := Nat.eq_zero_of_not_pos hs
    subst s
    simp [axisPairs]

theorem crossing_lower_bound (m n : ℕ) (D : AdmissibleDrawing m n) :
    axisPairs m*axisPairs n ≤ crossingCount D := by
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨s,hs⟩ := h
    cases s with
    | zero =>
      have hn : n=0 := by omega
      cases hn
      simp [axisPairs]
    | succ s =>
      have he : n=(2*s+1)+1 := by omega
      cases he
      exact even_successor_crossing_lower_bound m s D
  · obtain ⟨s,hs⟩ := h
    have hn : n=2*s+1 := by omega
    cases hn
    exact odd_crossing_lower_bound m s D

end Zarankiewicz

end

end OAI
