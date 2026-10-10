import OAI.Combinatorics.EditApproximation.Geometry.CurrentQueryInputs
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Wide enumeration gathers child states before scoring its Cartesian
action list. Its recursive input count depends on the coordinate lists,
rather than the exponentially larger number of complete actions. -/

namespace EditApproximation

open Finset

theorem wideEarlierChildStateList_length_le {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hP : 0 < P) (i : Fin M) :
    (wideChildStateList parent r b P i).length ≤ (40 * P + 2) ^ 2 := by
  have hlocal := gridStateBox_length_le ny (seedGridSpacing b P) (10 * b)
    (r.lo + ((sourceChild parent i).lo - parent.lo))
    (r.lo + ((sourceChild parent i).hi - parent.lo))
    (by unfold seedGridSpacing; omega)
  apply hlocal.trans
  apply Nat.pow_le_pow_left
  simpa only [show 2 * (10 * b) = 20 * b by omega] using seedGridSpacing_radius_count b P hP



theorem wideEarlierInputCover_card {nx ny M : ℕ} (parent : TargetInterval nx) (P history : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) (hP : 0 < P) :
    (wideEarlierInputCover (M := M) parent P history representatives).card ≤
      representatives.length * M * history * (40 * P + 2) ^ 2 := by
  have hstates (br : ℕ × TargetInterval ny) (i : Fin M) (t : ℕ) :
      (((wideChildStateList parent br.2 br.1 P i).toFinset).image fun r => (i, t, r)).card ≤
        (40 * P + 2) ^ 2 :=
    (Finset.card_image_le).trans ((List.toFinset_card_le _).trans
      (wideEarlierChildStateList_length_le parent br.2 br.1 P hP i))
  have hhistory (br : ℕ × TargetInterval ny) (i : Fin M) :
      ((Finset.range history).biUnion fun t =>
        ((wideChildStateList parent br.2 br.1 P i).toFinset).image fun r => (i, t, r)).card ≤
        history * (40 * P + 2) ^ 2 := by
    exact Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum fun t _ => hstates br i t).trans_eq (by simp))
  have hchildren (br : ℕ × TargetInterval ny) :
      (Finset.univ.biUnion fun i : Fin M =>
        (Finset.range history).biUnion fun t =>
          ((wideChildStateList parent br.2 br.1 P i).toFinset).image fun r => (i, t, r)).card ≤
        M * (history * (40 * P + 2) ^ 2) := by
    exact Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum fun i _ => hhistory br i).trans_eq (by simp))
  unfold wideEarlierInputCover
  calc
    _ ≤ ∑ br ∈ representatives.toFinset, M * (history * (40 * P + 2) ^ 2) :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun br _ => hchildren br)
    _ = representatives.toFinset.card * (M * (history * (40 * P + 2) ^ 2)) := by simp
    _ ≤ representatives.length * (M * (history * (40 * P + 2) ^ 2)) :=
      Nat.mul_le_mul_right _ (List.toFinset_card_le representatives)
    _ = _ := by ring

theorem wideEarlierInputCover_mem {nx ny M : ℕ} (parent : TargetInterval nx) (P history : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) (b : ℕ) (r : TargetInterval ny)
    (hrep : (b, r) ∈ representatives) (t : ℕ) (ht : t < history)
    (action : Fin M → TargetInterval ny) (ha : action ∈ wideActionList M parent r b P)
    (i : Fin M) : (i, t, action i) ∈ wideEarlierInputCover parent P history representatives := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(b, r), List.mem_toFinset.mpr hrep, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨t, Finset.mem_range.mpr ht, Finset.mem_image.mpr ?_⟩
  exact ⟨action i, List.mem_toFinset.mpr (finiteAssignments_sound M _ action ha i), rfl⟩

theorem bandCoordinates_earlier_cover {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P history b : ℕ) (tau theta : ℚ)
    (representatives : List (ℕ × TargetInterval target.length)) (r : TargetInterval target.length)
    (hrep : (b, r) ∈ representatives) (child : Fin M → TargetInterval target.length → ℚ)
    (t : ℕ) (ht : t < history) (coordinate : Fin M × TargetInterval target.length)
    (hcoordinate : coordinate ∈ bandCoordinates
      (representativeBandActions source target parent r b P tau theta child).toFinset) :
    (coordinate.1, t, coordinate.2) ∈ wideEarlierInputCover parent P history representatives := by
  obtain ⟨action, ha, hcoordinate⟩ := Finset.mem_biUnion.mp hcoordinate
  obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hcoordinate
  obtain rfl : coordinate = (i, action i) := heq.symm
  exact wideEarlierInputCover_mem parent P history representatives b r hrep t ht action
    (representativeBandActions_wide source target parent r b P tau theta child action
      (List.mem_toFinset.mp ha)) i

theorem localRefinementRepresentatives_length {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (hP : 0 < P) (hF : 1 ≤ F) :
    (localRefinementRepresentatives N P F a initial q).length ≤
      (dyadicQueryWindow N (initial q) a F).length * (64 * F * P + 2) ^ 2 := by
  unfold localRefinementRepresentatives
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hceil : ⌈initial q⌉₊ ≤ 16 * F * b := by
    apply Nat.ceil_le.mpr
    have hFpos : (0 : ℚ) < F := Nat.cast_pos.mpr (by omega)
    have h := (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow.1
    push_cast
    nlinarith only [h]
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hcover : b ≤ 2 * P * seedGridSpacing b P := by
    have hquot : b / P ≤ seedGridSpacing b P := le_max_right _ _
    have hdiv := Nat.lt_mul_div_succ b hP
    nlinarith only [hquot, hdiv, hg]
  have hcount : 2 * ⌈initial q⌉₊ / seedGridSpacing b P + 2 ≤ 64 * F * P + 2 := by
    have hprod : 2 * ⌈initial q⌉₊ ≤ 64 * F * P * seedGridSpacing b P := by
      nlinarith only [hceil, Nat.mul_le_mul_left (32 * F) hcover]
    have hdiv := Nat.div_mul_le_self (2 * ⌈initial q⌉₊) (seedGridSpacing b P)
    have hquot : 2 * ⌈initial q⌉₊ / seedGridSpacing b P ≤ 64 * F * P := by
      nlinarith only [hprod, hdiv, hg]
    exact Nat.add_le_add_right hquot 2
  have hlocal := localTargetStates_length_le (radius := ⌈initial q⌉₊) hg q
  simpa only [List.length_map] using
    (List.length_filter_le _ _).trans (hlocal.trans (Nat.pow_le_pow_left hcount 2))

end EditApproximation

end OAI
