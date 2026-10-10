import OAI.Combinatorics.EditApproximation.Geometry.SharedGroupInputBudget
import OAI.Combinatorics.EditApproximation.Geometry.LocalGroupBudget
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Distinct current-index inputs of the bounded query loops. The cover
includes all whole-cell shared estimates, selected cell actions, and
online actions; repeated uses do not add recursive calls. -/

namespace EditApproximation

open Finset

theorem groupDyadicScales_lower {M b F : ℕ} (hM : 0 < M) (hb : 0 < b)
    (hF : 0 < F) (h : ℚ) (hh : h ∈ groupDyadicScales M b F) :
    (b : ℚ) / M ≤ h := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hh
  exact ((groupDyadicScales_mem hM hb (F : ℚ) (by exact_mod_cast hF) e).mp
    (List.mem_map.mpr ⟨e, he, rfl⟩)).1



theorem localGroupQueryKeys_scale {n N F exponent : ℕ} {a : ℚ}
    {initial : TargetInterval n → ℚ} {q : TargetInterval n} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ localGroupQueryKeys N F exponent a initial q) :
    key.1 ∈ dyadicScales N := by
  obtain ⟨b, hb, hcell⟩ := List.mem_flatMap.mp hkey
  obtain ⟨cell, _, rfl⟩ := List.mem_map.mp hcell
  exact (List.mem_filter.mp hb).1

theorem localGroupQueryKeys_length {n : ℕ} (N F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n)
    (hF : 1 ≤ F) (hw : 0 ≤ initial q) :
    (localGroupQueryKeys N F exponent a initial q).length ≤
      (dyadicQueryWindow N (initial q) a F).length *
        ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  unfold localGroupQueryKeys
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hbpos : 1 ≤ b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hb).1
    exact Nat.one_le_two_pow
  simpa only [List.length_map] using
    localTargetCells_query_length F b exponent q (initial q) hF hbpos hw hwindow.1



theorem querySharedInputCover_card {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N F exponent Q labels : ℕ) (a : ℚ)
    (initial : TargetInterval target.length → ℚ) (q : TargetInterval target.length)
    (draw : CellGroupDraws M F Q) (hM : 0 < M) (hF : 1 ≤ F) (hQ : 1 ≤ Q)
    (hlabels : ∀ b ∈ dyadicScales N, (groupDyadicScales M b F).length ≤ labels) :
    ((querySharedInputCover source target parent N F exponent Q a initial q draw).card : ℚ) ≤
      (localGroupQueryKeys N F exponent a initial q).length * labels *
        (624 * M * Q * ((2 : ℚ) ^ exponent) ^ 2) := by
  let keys := (localGroupQueryKeys N F exponent a initial q).toFinset
  let C : ℚ := 624 * M * Q * ((2 : ℚ) ^ exponent) ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hper (key : ℕ × (ℕ × ℕ)) (hk : key ∈ keys) :
      ((Finset.univ.biUnion fun scale : Fin (groupDyadicScales M key.1 F).length =>
        groupCurrentInputCover source target parent key.1 exponent Q key.2
          (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)).card : ℚ) ≤ labels * C := by
    have hb := localGroupQueryKeys_scale (List.mem_toFinset.mp hk)
    have hbpos : 0 < key.1 := by
      obtain ⟨e, _, he⟩ := List.mem_map.mp hb
      rw [← he]
      positivity
    have hcard := Finset.card_biUnion_le (s := (Finset.univ :
      Finset (Fin (groupDyadicScales M key.1 F).length)))
      (t := fun scale => groupCurrentInputCover source target parent key.1 exponent Q key.2
        (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale))
    have hcardR : ((Finset.univ.biUnion fun scale : Fin (groupDyadicScales M key.1 F).length =>
        groupCurrentInputCover source target parent key.1 exponent Q key.2
          (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)).card : ℚ) ≤
        ∑ scale : Fin (groupDyadicScales M key.1 F).length,
        ((groupCurrentInputCover source target parent key.1 exponent Q key.2
          (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)).card : ℚ) := by
      exact_mod_cast hcard
    apply hcardR.trans
    have hscale (scale : Fin (groupDyadicScales M key.1 F).length) :=
      List.get_mem (groupDyadicScales M key.1 F) scale
    calc
      _ ≤ ∑ _scale : Fin (groupDyadicScales M key.1 F).length, C := by
        apply Finset.sum_le_sum
        intro scale _
        exact groupCurrentInputCover_card source target parent exponent Q key.2 _ hM hQ hbpos
          (groupDyadicScales_pos (hscale scale))
          (groupDyadicScales_lower hM hbpos (by omega) _ (hscale scale)) _
      _ = (groupDyadicScales M key.1 F).length * C := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ labels * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hlabels key.1 hb) hC
  have hcard := Finset.card_biUnion_le (s := keys)
    (t := fun key => Finset.univ.biUnion fun scale : Fin (groupDyadicScales M key.1 F).length =>
      groupCurrentInputCover source target parent key.1 exponent Q key.2
        (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale))
  have hcardR : ((querySharedInputCover source target parent N F exponent Q a initial q draw).card : ℚ) ≤
      ∑ key ∈ keys, ((Finset.univ.biUnion fun scale : Fin (groupDyadicScales M key.1 F).length =>
        groupCurrentInputCover source target parent key.1 exponent Q key.2
          (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)).card : ℚ) := by
    exact_mod_cast hcard
  calc
    _ ≤ ∑ key ∈ keys, ((Finset.univ.biUnion fun scale : Fin (groupDyadicScales M key.1 F).length =>
        groupCurrentInputCover source target parent key.1 exponent Q key.2
          (groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)).card : ℚ) := hcardR
    _ ≤ ∑ _key ∈ keys, labels * C := Finset.sum_le_sum hper
    _ = (keys.card : ℚ) * (labels * C) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (localGroupQueryKeys N F exponent a initial q).length * (labels * C) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast List.toFinset_card_le _) (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = _ := by ring



theorem actionCurrentInputCover_card {Parent Child : Type*} [DecidableEq Child] {M : ℕ}
    (actions : List (RationalBellmanAction Parent Child M)) :
    (actionCurrentInputCover actions).card ≤ actions.length * M := by
  unfold actionCurrentInputCover
  have hindices : (List.finRange actions.length).toFinset = (Finset.univ : Finset (Fin actions.length)) := by
    ext i
    simp
  rw [hindices]
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun _ _ => Finset.card_image_le)).trans_eq
  simp only [Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

theorem actionCurrentInputCover_mem {Parent Child : Type*} [DecidableEq Child] {M : ℕ}
    (actions : List (RationalBellmanAction Parent Child M))
    (action : RationalBellmanAction Parent Child M) (ha : action ∈ actions) (i : Fin M) :
    action.childState i ∈ actionCurrentInputCover actions := by
  obtain ⟨index, hindex⟩ := List.mem_iff_get.mp ha
  apply Finset.mem_biUnion.mpr
  refine ⟨index, by simp, ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [hindex]⟩

def currentQueryInputCover {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (online : List (PhysicalRationalAction M target.length)) : Finset (Fin M × TargetInterval target.length) :=
  querySharedInputCover source target parent N F exponent Q a parentInitial q draw ∪
    actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q) ∪ actionCurrentInputCover online

theorem currentQueryInputCover_card {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q labels : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (online : List (PhysicalRationalAction M target.length))
    (hM : 0 < M) (hF : 1 ≤ F) (hQ : 1 ≤ Q)
    (hlabels : ∀ b ∈ dyadicScales N, (groupDyadicScales M b F).length ≤ labels) :
    ((currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
      child initial current draw q online).card : ℚ) ≤
      (localGroupQueryKeys N F exponent a parentInitial q).length * labels *
        (624 * M * Q * ((2 : ℚ) ^ exponent) ^ 2) +
      (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw q).length * M + online.length * M := by
  have hcard := Finset.card_union_le
    (querySharedInputCover source target parent N F exponent Q a parentInitial q draw ∪
      actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw q)) (actionCurrentInputCover online)
  have hleft := Finset.card_union_le
    (querySharedInputCover source target parent N F exponent Q a parentInitial q draw)
    (actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q))
  have hN := hcard.trans (Nat.add_le_add_right hleft _)
  have hR : ((currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
      child initial current draw q online).card : ℚ) ≤
      (querySharedInputCover source target parent N F exponent Q a parentInitial q draw).card +
      (actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw q)).card + (actionCurrentInputCover online).card := by exact_mod_cast hN
  apply hR.trans
  exact add_le_add (add_le_add
    (querySharedInputCover_card source target parent N F exponent Q labels a parentInitial q draw hM hF hQ hlabels)
    (by exact_mod_cast (actionCurrentInputCover_card
      (localCellGroupActions source target parent N P F exponent Q tau a parentInitial child initial current draw q))))
    (by exact_mod_cast (actionCurrentInputCover_card online))

end EditApproximation

end OAI
