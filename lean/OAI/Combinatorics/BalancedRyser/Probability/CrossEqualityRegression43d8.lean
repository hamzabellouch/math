import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.BalancedRyser.Local.LocalTwoReuseMean

namespace OAI

namespace Balanced.Local.CrossEqualityRegression43d8
open scoped BigOperators
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def twoReusePattern : EqualityPattern 3 2 where
  classOf := ![![0, 1, 2, 3], ![0, 4, 5, 6], ![1, 7, 8, 9]]
  everyClass := by decide
  withinTuple := by decide
  pairOverlap := by decide

def crossAssignment : DirectionAssignment (ZMod 11) 3 2 :=
  (![some 4, some 7, some 10], fun c => some (c.val : ZMod 11))

theorem crossAssignment_eligible : Eligible twoReusePattern crossAssignment := by
  unfold Eligible
  decide

theorem crossAssignment_not_allTokensDistinct : ¬ AllTokensDistinct crossAssignment := by
  intro h
  have bad : (Sum.inl (0 : Fin 3) : DirectionToken 3 2) =
      Sum.inr (4 : Fin (4 * 3 - 2)) := h (by rfl)
  cases bad

open scoped Classical

theorem tokenInjection_isEmpty :
    IsEmpty (DirectionToken 3 2 ↪ Direction (ZMod 11)) := by
  refine ⟨fun e => ?_⟩
  have hc := Fintype.card_le_of_injective e e.injective
  norm_num [DirectionToken, Direction, ZMod.card] at hc

theorem allDistinct_sum_eq_zero
    (f : DirectionAssignment (ZMod 11) 3 2 → ℝ) :
    (∑ a, if AllTokensDistinct a then f a else 0) = 0 := by
  classical
  let := tokenInjection_isEmpty
  rw [TwoReuseAssembly.sum_allTokensDistinct_eq]
  simp

theorem crossAssignment_alignment_pos (bits : Bits 3) (p : Point (ZMod 11)) :
    0 < offsetProbability (Aligned twoReusePattern crossAssignment bits p) :=
  alignment_probability_pos twoReusePattern (by decide) crossAssignment
    crossAssignment_eligible bits p

theorem crossAssignment_alignment_exact (bits : Bits 3) (p : Point (ZMod 11)) :
    offsetProbability (Aligned twoReusePattern crossAssignment bits p) =
      1 / (11 : ℝ) ^ 12 := by
  simpa using alignment_probability twoReusePattern (by decide) crossAssignment
    crossAssignment_eligible bits p

theorem exceptional_alignment_sum_pos_of_witness
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {b : ℕ} (P : EqualityPattern b 2) (a : DirectionAssignment F b 2)
    (ha : Eligible P a) (hnot : ¬ AllTokensDistinct a)
    (bits : Bits b) (p : Point F) :
    0 < ∑ t : DirectionAssignment F b 2,
      if Eligible P t ∧ ¬ AllTokensDistinct t then
        offsetProbability (Aligned P t bits p) else 0 := by
  classical
  apply Finset.sum_pos'
  · intro t _
    split_ifs
    · exact KernelBridge.offsetProbability_nonneg _
    · exact le_rfl
  · refine ⟨a, Finset.mem_univ _, ?_⟩
    rw [ite_eq_left ⟨ha, hnot⟩]
    exact alignment_probability_pos P (by omega) a ha bits p

theorem noninjective_alignment_sum_pos (bits : Bits 3) (p : Point (ZMod 11)) :
    0 < ∑ a : DirectionAssignment (ZMod 11) 3 2,
      if Eligible twoReusePattern a ∧ ¬ AllTokensDistinct a then
        offsetProbability (Aligned twoReusePattern a bits p) else 0 :=
  exceptional_alignment_sum_pos_of_witness twoReusePattern crossAssignment
    crossAssignment_eligible crossAssignment_not_allTokensDistinct bits p

theorem empty_output_fixed_cross_card :
    ((Finset.univ : Finset ((Fin 1 → Fin 0) × (Fin 1 → Fin 0))).filter
      (fun a => a.1 0 = a.2 0)).card = 0 := by
  simp

theorem three_value_fixed_cross_card :
    ((Finset.univ : Finset ((Fin 2 → Fin 3) × (Fin 2 → Fin 3))).filter
      (fun a => a.1 0 = a.2 0)).card = 27 := by
  simpa using card_crossEquality (I := Fin 2) (G := Fin 2) (J := Fin 3) 0 0

end Balanced.Local.CrossEqualityRegression43d8

end OAI
