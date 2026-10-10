import OAI.Analysis.LipschitzHilbert.Geometry.RectanglePairEnergy

namespace OAI

/-! Total far-pair energy, charged to the earlier rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Classical
namespace LipschitzHilbert
variable {ι : Type*} [DecidableEq ι] {n : ℕ}

theorem far_outgoing_sum (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) {previous stock : Finset ι} {selected : List ι}
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) previous stock selected)
    (r : ι) (hr : r ∈ previous)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hδ : 0 < δ) (hRef : (R r).Admissible v K δ)
    (hR : ∀ j ∈ stock, (R j).Admissible v K δ)
    (hL : ∀ j ∈ selected, (R j).long ≤ (R r).long) :
    (δ : ℝ≥0∞)*(∑ j ∈ selected.toFinset, farPair R r j) ≤ 960*volume (R r).carrier := by
  let s := selected.toFinset.filter (fun j =>
    64*(R j).short < (R j).long*dist ((R r).axes 0) ((R j).axes 0) ∧
      ((R r).carrier ∩ (R j).carrier).Nonempty)
  have hs (j : ι) (hj : j ∈ s) : j ∈ selected :=
    List.mem_toFinset.mp (Finset.mem_filter.mp hj).1
  have hb := selected_far_overlap D hD R previous stock selected hrun s
    (Finset.filter_subset _ _) r hr hv hu hδ hRef
    (fun j hj => hR j (hrun.selected_subset j (hs j hj)))
    (fun j hj => hL j (hs j hj))
    (fun j hj => (Finset.mem_filter.mp hj).2.2)
    (fun j hj => (Finset.mem_filter.mp hj).2.1)
  have he : (∑ j ∈ selected.toFinset, farPair R r j) =
      ∑ j ∈ s, volume ((R j).carrier ∩ (R r).carrier) := by
    dsimp [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hf : 64*(R j).short < (R j).long*dist ((R r).axes 0) ((R j).axes 0)
    · by_cases hm : ((R r).carrier ∩ (R j).carrier).Nonempty
      · have hboth := And.intro hf hm
        simp only [farPair,ite_eq_left hf,ite_eq_left hboth,overlapPair]
        exact congrArg volume (inter_comm _ _)
      · have hz := Set.not_nonempty_iff_eq_empty.mp hm
        simp [farPair,hf,overlapPair,hz]
    · simp [farPair,hf]
  rwa [←he] at hb

theorem selected_far_energy (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) {previous stock : Finset ι} {selected : List ι}
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) previous stock selected)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hδ : 0 < δ) (hR : ∀ j ∈ stock, (R j).Admissible v K δ) :
    (δ : ℝ≥0∞)*orderedPairSum (farPair R) selected ≤
      960*(∑ j ∈ selected.toFinset, volume (R j).carrier) := by
  induction hrun with
  | stop => simp [orderedPairSum]
  | step previous stock i tail hi hp ha htail ih =>
    have hhead := far_outgoing_sum D hD R htail i (Finset.mem_insert_self _ _) hv hu hδ
      (hR i hi) (fun j hj => hR j (rectangleRemaining_subset _ _ _ _ hj))
      (fun j hj => (hp j (rectangleRemaining_subset _ _ _ _ (htail.selected_subset j hj))).1)
    have hrest := ih (fun j hj => hR j (rectangleRemaining_subset _ _ _ _ hj))
    have hit : i ∉ tail.toFinset := by
      intro hit
      have hm := htail.selected_subset i (List.mem_toFinset.mp hit)
      exact (mem_rectangleRemaining _ previous stock i i).mp hm |>.2.1 rfl
    simp only [orderedPairSum,mul_add,List.toFinset_cons,Finset.sum_insert hit]
    exact add_le_add hhead hrest

end LipschitzHilbert

end

end OAI
