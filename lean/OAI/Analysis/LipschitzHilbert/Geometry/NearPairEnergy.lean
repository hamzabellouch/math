import OAI.Analysis.LipschitzHilbert.Geometry.RectanglePairEnergy

namespace OAI

/-! Total near-pair energy. The previous set grows during selection, so
all near interactions are charged once to the later rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert
variable {ι : Type*} [DecidableEq ι] {n : ℕ}

omit [DecidableEq ι] in
theorem near_previous_sum (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (previous : Finset ι) (r : ι)
    (hL : ∀ j ∈ previous, (R r).long ≤ (R j).long)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      selectionDilation (by norm_num) selectionThreshold previous r) :
    (∑ j ∈ previous, nearPair R j r) ≤ volume (R r).carrier := by
  let s := previous.filter (fun j => (R r).long*dist ((R j).axes 0) ((R r).axes 0) ≤ 64*(R r).short)
  have hh := uniform_near_selected_overlap D hD R s previous (Finset.filter_subset _ _) r
    (fun j hj => hL j (Finset.mem_filter.mp hj).1)
    (fun j hj => (Finset.mem_filter.mp hj).2) hnot
  have he : (∑ j ∈ previous, nearPair R j r) =
      ∑ j ∈ s, volume ((R r).carrier ∩ (R j).carrier) := by
    dsimp [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    unfold nearPair overlapPair
    rw [inter_comm (R j).carrier]
  rwa [←he] at hh

theorem selected_near_energy (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) {previous stock : Finset ι} {selected : List ι}
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) previous stock selected)
    (hdis : Disjoint previous stock)
    (hL : ∀ i ∈ previous, ∀ j ∈ stock, (R j).long ≤ (R i).long) :
    previousPairSum (nearPair R) previous selected+orderedPairSum (nearPair R) selected ≤
      ∑ j ∈ selected.toFinset, volume (R j).carrier := by
  induction hrun with
  | stop previous => simp [previousPairSum,orderedPairSum]
  | step previous stock i tail hi hp ha htail ih =>
    have hip : i ∉ previous := by
      intro hip
      exact Finset.disjoint_left.mp hdis hip hi
    have hit : i ∉ tail := by
      intro hit
      exact (mem_rectangleRemaining _ previous stock i i).mp (htail.selected_subset i hit) |>.2.1 rfl
    have hdn : Disjoint (insert i previous)
        (rectangleRemaining (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
          selectionDilation (by norm_num) selectionThreshold) previous stock i) := by
      apply Finset.disjoint_left.mpr
      intro j hj hjr
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        exact (mem_rectangleRemaining _ previous stock i i).mp hjr |>.2.1 rfl
      · exact Finset.disjoint_left.mp hdis hj (rectangleRemaining_subset _ _ _ _ hjr)
    have hln : ∀ k ∈ insert i previous,
        ∀ j ∈ rectangleRemaining (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
          selectionDilation (by norm_num) selectionThreshold) previous stock i,
        (R j).long ≤ (R k).long := by
      intro k hk j hj
      have hjs := rectangleRemaining_subset _ _ _ _ hj
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact (hp j hjs).1
      · exact hL k hk j hjs
    have hhead := near_previous_sum D hD R previous i (fun j hj => hL j hj i hi) ha
    rw [previousPairSum_cons (nearPair R) previous i tail hip hit]
    have ih' := ih hdn hln
    have hit' : i ∉ tail.toFinset := by simpa using hit
    simpa only [List.toFinset_cons,Finset.sum_insert hit'] using add_le_add hhead ih'

end LipschitzHilbert

end

end OAI
