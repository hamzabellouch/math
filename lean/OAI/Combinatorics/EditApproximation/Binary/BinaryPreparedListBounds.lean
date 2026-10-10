import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalRepresentativeWork
import OAI.Combinatorics.EditApproximation.Geometry.LocalGroupBudget

namespace OAI

/-! Literal candidate counts of the three local loops, on every seed. -/

namespace EditApproximation
namespace BinaryFraction

theorem dyadicScales_length_bits (N : ℕ) : (dyadicScales N).length = max 1 N.bits.length := by
  have h := congrArg List.length (dyadicScalesWithWork_value N)
  simpa only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.length_map,
    List.length_range] using h.symm

theorem queryExponentsWithWork_length_le (N F B : ℕ) (a w : BinaryFraction)
    (hN : Nat.size N ≤ B) : (queryExponentsWithWork N F a w).1.length ≤ B + 1 := by
  change (filterWithWork _ (List.range (max 1 N.bits.length))).1.length ≤ _
  rw [filterWithWork_value]
  apply (List.length_filter_le _ _).trans
  rw [List.length_range, Nat.size_eq_bits_len]
  omega

theorem localRepresentativesWithWork_scale_bits {n : ℕ} (N P F B : ℕ) (hP : 0 < P)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction) (query : TargetInterval n)
    (hN : Nat.size N ≤ B) (br : ℕ × TargetInterval n)
    (hbr : br ∈ (localRepresentativesWithWork N P F a initial query).1) : Nat.size br.1 ≤ B + 2 := by
  rw [localRepresentativesWithWork_value N P F hP] at hbr
  have hb := (representativeList_conditions a.value (fun r => (initial r).value)
    (localRefinementRepresentatives_subset N P F a.value (fun r => (initial r).value) query br hbr)).1
  obtain ⟨e, he, hscale⟩ := List.mem_map.mp hb
  have hlen : Nat.log 2 N + 1 = max 1 N.bits.length := by
    simpa only [dyadicScales, List.length_map, List.length_range] using dyadicScales_length_bits N
  have her := List.mem_range.mp he
  rw [hlen, Nat.size_eq_bits_len] at her
  rw [← hscale, Nat.size_pow]
  omega

theorem localRepresentativesWithWork_length_le {n : ℕ} (N P F B : ℕ) (hP : 0 < P)
    (hF : 1 ≤ F) (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction)
    (query : TargetInterval n) (hN : Nat.size N ≤ B) :
    (localRepresentativesWithWork N P F a initial query).1.length ≤
      (B + 1) * (64 * F * P + 2) ^ 2 := by
  rw [localRepresentativesWithWork_value N P F hP]
  unfold localRefinementRepresentatives
  apply (list_flatMap_length_le _ _ _ ?_).trans
    (Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans (show
      (dyadicScales N).length ≤ B + 1 by rw [dyadicScales_length_bits, Nat.size_eq_bits_len]; omega)))
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hFp : (0 : ℚ) < 16 * F := by
    have : (0 : ℚ) < F := by exact_mod_cast (show 0 < F by omega)
    positivity
  have hr : ⌈(initial query).value⌉₊ ≤ (16 * F) * b := by
    apply Nat.ceil_le.mpr
    have hh := (div_le_iff₀ hFp).mp hwindow.1
    push_cast
    nlinarith only [hh]
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans (by
    simpa only [show 4 * (16 * F) * P = 64 * F * P by ring] using
      localTargetStates_length_from_scale P b ⌈(initial query).value⌉₊ (16 * F) query hP hr)

theorem preparedLocalCellGroupsWithWork_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q eM eF B : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : CellGroupDraws M F Q) (query : TargetInterval target.length)
    (hN : Nat.size N ≤ B) (hw : 0 ≤ (parentInitial query).value) :
    (preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP
      tau a parentInitial child initial current draw query).1.length ≤
      (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  have hv := congrArg List.length (preparedLocalCellGroupsWithWork_value source target parent
    N P F exponent Q eM eF hM hF hP tau a parentInitial child initial current draw query)
  rw [List.length_map] at hv
  rw [hv]
  apply (localCellGroupActions_length source target parent N P F exponent Q tau.value a.value
    (fun r => (parentInitial r).value) (fun i r => (child i r).value)
    (fun i r => (initial i r).value) (fun i r => (current i r).value) draw query
    (by rw [hF]; exact Nat.one_le_two_pow) hw).trans
  apply Nat.mul_le_mul_right
  apply (List.length_filter_le _ _).trans
  rw [dyadicScales_length_bits, Nat.size_eq_bits_len]
  omega

theorem preparedLocalOnlineActionsWithWork_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H B : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
    (hN : Nat.size N ≤ B) :
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial table t integer query).1.length ≤ B + 1 := by
  change (filterMapWithWork _ (queryExponentsWithWork N F a (parentInitial query)).1).1.length ≤ _
  rw [filterMapWithWork_value]
  exact (List.length_filterMap_le _ _).trans (queryExponentsWithWork_length_le N F B a _ hN)

end BinaryFraction
end EditApproximation

end OAI
