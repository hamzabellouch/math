import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightLabels

namespace OAI

namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction InitialCoordinatesTemplate

theorem template_current_length_le (seed : List SourceSlot) (l : ℕ) :
    (Template.current seed l).length ≤ 2^l*seed.length := by
  induction l with
  | zero => simp only [Template.current,pow_zero,one_mul]; rfl
  | succ l ih =>
    have hr : (Template.remainder (l+1) (Template.current seed l)).length ≤
        (Template.current seed l).length := List.length_filter_le _ _
    simp only [Template.current,List.length_append,pow_succ]
    nlinarith

theorem TreeSourceLabels.root_length_le {seed : List SourceSlot} {l : ℕ} {h : History l}
    (hh : TreeSourceLabels seed h) : h.root.small.length ≤ 2^l*seed.length := by
  cases h with
  | leaf a => simpa only [History.root,pow_zero,one_mul] using (Template.matches_length hh).le
  | node a p u hp hm left right =>
    exact (Template.matches_length hh.1).le.trans (template_current_length_le seed _)

theorem TreeSourceLabels.internal_length_le {seed : List SourceSlot} {l : ℕ} {h : History l}
    (hh : TreeSourceLabels seed h) : h.internalOccurrences.length ≤ l*2^l*seed.length := by
  induction h with
  | leaf a => simp only [History.internalOccurrences,List.length_nil,Nat.zero_mul]; rfl
  | @node l a p u hp hm left right il ir =>
    have hl := il hh.2.2.2.2.1
    have hr := ir hh.2.2.2.2.2
    have hu : u.length ≤ 2^l*seed.length := by
      rw [Template.matches_length hh.2.2.2.1]
      exact (List.length_filter_le _ _).trans (template_current_length_le seed l)
    simp only [History.internalOccurrences,List.length_append,pow_succ]
    nlinarith

def historyCostCoefficient (k : ℕ) : ℕ :=
  2^k*(2+(1+2*k)*2^k*(6+4*k))

theorem historyCostCoefficient_pos (k : ℕ) : 0 < historyCostCoefficient k := by
  unfold historyCostCoefficient
  positivity

theorem TreeSourceLabels.cost_le {b k l : ℕ} {h : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h) (hlk : l ≤ k) :
    2^l*(2+h.root.small.length+2*h.internalOccurrences.length) ≤
      historyCostCoefficient k*(b+1) := by
  have hr := hh.root_length_le
  have hi := hh.internal_length_le
  rw [initial_length] at hr hi
  have hpow : 2^l ≤ (2^k:ℕ) := Nat.pow_le_pow_right (by omega) hlk
  have hseed : 2*b+6+4*k ≤ (6+4*k)*(b+1) := by nlinarith
  have hroot : h.root.small.length ≤ 2^k*((6+4*k)*(b+1)) :=
    hr.trans (Nat.mul_le_mul hpow hseed)
  have hinternal : h.internalOccurrences.length ≤ k*2^k*((6+4*k)*(b+1)) :=
    hi.trans (Nat.mul_le_mul (Nat.mul_le_mul hlk hpow) hseed)
  calc
    _ ≤ 2^k*(2+2^k*((6+4*k)*(b+1))+2*(k*2^k*((6+4*k)*(b+1)))) :=
      Nat.mul_le_mul hpow (by omega)
    _ ≤ _ := by unfold historyCostCoefficient; nlinarith

end Ostmann.Arithmetic.HistorySymbolicEncoding

end OAI
