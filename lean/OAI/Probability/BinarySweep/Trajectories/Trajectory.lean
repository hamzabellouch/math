import Mathlib
import OAI.Probability.BinarySweep.Trajectories.PathExtension

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma trajectory_coordinates {b : ℕ} {bits : Fin b → ℕ}
    (x : Fin (b+1) → GridSlot bits)
    (hmov : ∀ (j : Fin b) (i : Fin b), i ≠ j → x j.succ i = x j.castSucc i)
    (t : Fin (b+1)) (i : Fin b) :
    x t i = if i.val < t.val then x (Fin.last b) i else x 0 i := by
  have hbefore : ∀ t : Fin (b+1), t.val ≤ i.val → x t i = x 0 i := by
    intro t
    induction t using Fin.induction with
    | zero => intro _; rfl
    | succ j ih =>
      intro ht
      have hij : i ≠ j := by intro h; subst j; simp at ht
      rw [hmov j i hij, ih]
      exact Nat.le_trans (Nat.le_succ j.val) ht
  have hafter : ∀ t : Fin (b+1), i.val < t.val → x t i = x (Fin.last b) i := by
    intro t
    induction t using Fin.reverseInduction with
    | last => intro _; rfl
    | cast j ih =>
      intro ht
      have hij : i ≠ j := by intro h; subst j; simp at ht
      rw [← hmov j i hij, ih]
      exact Nat.lt_succ_of_lt ht
  split_ifs with h
  · exact hafter t h
  · exact hbefore t (Nat.le_of_not_lt h)

lemma trajectory_unique {b : ℕ} {bits : Fin b → ℕ}
    (x y : Fin (b+1) → GridSlot bits)
    (hx : ∀ (j i : Fin b), i ≠ j → x j.succ i = x j.castSucc i)
    (hy : ∀ (j i : Fin b), i ≠ j → y j.succ i = y j.castSucc i)
    (h0 : x 0 = y 0) (hb : x (Fin.last b) = y (Fin.last b)) : x = y := by
  funext t i
  rw [trajectory_coordinates x hx, trajectory_coordinates y hy, h0, hb]

def gridPartialSweep {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits)
    (t : Fin (b+1)) : Equiv.Perm (GridSlot bits) :=
  ((List.ofFn (gridLayer bits g)).take t.val).reverse.prod

@[simp] lemma gridPartialSweep_zero {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) :
    gridPartialSweep bits g 0 = 1 := by simp [gridPartialSweep]

@[simp] lemma gridPartialSweep_last {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) :
    gridPartialSweep bits g (Fin.last b) = gridSweep bits g := by
  unfold gridPartialSweep gridSweep
  rw [List.take_of_length_le (by simp)]

lemma gridPartialSweep_succ {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) (j : Fin b) :
    gridPartialSweep bits g j.succ = gridLayer bits g j * gridPartialSweep bits g j.castSucc := by
  unfold gridPartialSweep
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [List.take_succ_eq_append_getElem (by simp)]
  simp only [List.reverse_append, List.reverse_singleton, List.prod_append,
    List.prod_singleton, List.getElem_ofFn, Fin.eta]

lemma gridLayer_other {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits)
    (j i : Fin b) (hi : i ≠ j) (x : GridSlot bits) : gridLayer bits g j x i = x i := by
  simp [gridLayer, Equiv.piSplitAt, hi]

lemma gridPartialSweep_changes {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits)
    (x : GridSlot bits) (j i : Fin b) (hi : i ≠ j) :
    gridPartialSweep bits g j.succ x i = gridPartialSweep bits g j.castSucc x i := by
  rw [gridPartialSweep_succ, Equiv.Perm.mul_apply, gridLayer_other bits g j i hi]

lemma gridPartialSweep_path {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (g : GridChoices bits) (hg : pathEvent H g)
    (t : Fin (b+1)) (i : Fin h) :
    gridPartialSweep bits g t (H.position 0 i) = H.position t i := by
  induction t using Fin.induction with
  | zero => simp
  | succ j ih => rw [gridPartialSweep_succ, Equiv.Perm.mul_apply, ih, hg j i]

lemma pathEvent_of_endpoints {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (g : GridChoices bits)
    (he : ∀ i, gridSweep bits g (H.position 0 i) = H.position (Fin.last b) i) :
    pathEvent H g := by
  have hx (i : Fin h) : (fun t => gridPartialSweep bits g t (H.position 0 i)) =
      (fun t => H.position t i) := by
    apply trajectory_unique
    · exact gridPartialSweep_changes bits g (H.position 0 i)
    · exact fun j a ha => H.changes_only_stage j i a ha
    · simp
    · simpa using he i
  intro j i
  have ha := congrFun (hx i) j.castSucc
  have hb := congrFun (hx i) j.succ
  rw [gridPartialSweep_succ, Equiv.Perm.mul_apply, ha] at hb
  exact hb

def augmentByChoice {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) : PathFamily bits (h+k) where
  position t a := gridPartialSweep bits g.val t (Fin.append (H.position 0) (fun i => (x i).val) a)
  disjoint t := (gridPartialSweep bits g.val t).injective.comp (Fin.append_injective_iff.mpr
    ⟨H.disjoint 0, Subtype.val_injective.comp x.injective, fun i j he => (x j).property ⟨i, he⟩⟩)
  changes_only_stage j _ i hi := gridPartialSweep_changes bits g.val _ j i hi

def augmentByChoice_extension {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) :
    PathExtension H (augmentByChoice H x g) where
  labels := ⟨Fin.castAdd k, Fin.castAdd_injective h k⟩
  position_eq t i := by
    change gridPartialSweep bits g.val t (Fin.append _ _ (Fin.castAdd k i)) = _
    rw [Fin.append_left, gridPartialSweep_path H g.val g.property]

lemma placementEvent_iff_augmentation {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) {k : ℕ} (x : Placement H k 0) (g g' : ConditionalChoices H) :
    placementBijection H k g' x = placementBijection H k g x ↔
      pathEvent (augmentByChoice H x g) g'.val := by
  constructor
  · intro he
    apply pathEvent_of_endpoints
    intro a
    change gridSweep bits g'.val (gridPartialSweep bits g.val 0 (Fin.append _ _ a)) =
      gridPartialSweep bits g.val (Fin.last b) (Fin.append _ _ a)
    simp only [gridPartialSweep_zero, gridPartialSweep_last, Equiv.Perm.one_apply]
    induction a using Fin.addCases with
    | left i =>
      rw [Fin.append_left, gridSweep_path H g'.val g'.property, gridSweep_path H g.val g.property]
    | right i =>
      rw [Fin.append_right]
      exact congrArg (fun y : Placement H k (Fin.last b) => (y i).val) he
  · intro he
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    change gridSweep bits g'.val (x i).val = gridSweep bits g.val (x i).val
    have hi := gridSweep_path (augmentByChoice H x g) g'.val he (Fin.natAdd h i)
    simpa only [augmentByChoice, Fin.append_right, gridPartialSweep_zero,
      gridPartialSweep_last, Equiv.Perm.one_apply] using hi

lemma placementProbability_augmentation {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) :
    placementProbability H z x (placementBijection H k g x) =
      conditionalEventWeight H z (pathEvent (augmentByChoice H x g)) := by
  unfold placementProbability conditionalEventWeight
  apply Finset.sum_congr rfl
  intro g' _
  simp only [placementEvent_iff_augmentation]

theorem placement_probability_cost {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) :
    placementProbability H z x (placementBijection H k g x) ≤
      (gridSize bits : ℝ) ^ (-(k : ℝ)) *
        Real.exp (pathCost (augmentByChoice H x g) - pathCost H + Real.log 4 * k * b) := by
  rw [placementProbability_augmentation]
  exact pathExtension_probability_bound (augmentByChoice_extension H x g) hd hz hzr

lemma placementProbability_pos_has_choice {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) :
    ∃ g : ConditionalChoices H, placementBijection H k g x = y := by
  unfold placementProbability at hp
  by_contra he
  push Not at he
  have hs : (∑ g : ConditionalChoices H,
      if placementBijection H k g x = y then conditionalChoiceWeight H z g else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro g _
    simp only [he g, ite_false]
  rw [hs] at hp
  exact (lt_irrefl _ hp)

def realizePlacement {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) : ConditionalChoices H :=
  Classical.choose (placementProbability_pos_has_choice H z x y hp)

lemma realizePlacement_spec {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) :
    placementBijection H k (realizePlacement H z x y hp) x = y :=
  Classical.choose_spec (placementProbability_pos_has_choice H z x y hp)

def placementTransitionCost {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) : ℝ :=
  if hp : 0 < placementProbability H z x y then
    pathCost (augmentByChoice H x (realizePlacement H z x y hp)) else 0

theorem placement_probability_cost_of_pos {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    {k : ℕ} (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) :
    placementProbability H z x y ≤ (gridSize bits : ℝ) ^ (-(k : ℝ)) *
      Real.exp (placementTransitionCost H z x y - pathCost H + Real.log 4 * k * b) := by
  have he := placement_probability_cost H hd hz hzr x (realizePlacement H z x y hp)
  unfold placementTransitionCost
  rw [dite_eq_left hp]
  rwa [realizePlacement_spec] at he

end BinaryCoordinateSweeps

end

end OAI
