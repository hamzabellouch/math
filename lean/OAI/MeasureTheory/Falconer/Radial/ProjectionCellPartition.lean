import OAI.MeasureTheory.Falconer.Measures.DyadicMeasureSplitting
import OAI.MeasureTheory.Falconer.Angular.ActualAngularTests

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem projectionTestCells_eq_image (Q : DyadicSquare) (ρ : Measure Plane)
    {p u : ℕ} (hpu : p ≤ u) {P : CellPath} (hP : P.length = p) :
    projectionTestCells Q ρ p u P =
      (occupiedAnchorPaths (Q.descendant P) ρ (u-p)).image (fun c => P++c) := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨hC,hpos,htake⟩ := Finset.mem_filter.mp hC
    have hlen := (mem_dyadicPaths _ _).mp hC
    refine Finset.mem_image.mpr ⟨C.drop p,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨(mem_dyadicPaths _ _).mpr (by simp [hlen]),?_⟩
      simpa only [← Q.descendant_append,← htake,List.take_append_drop] using hpos
    · rw [← htake,List.take_append_drop]
  · intro hmem
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨hD,hpos⟩ := Finset.mem_filter.mp hD
    have hlen := (mem_dyadicPaths _ _).mp hD
    apply Finset.mem_filter.mpr
    refine ⟨(mem_dyadicPaths _ _).mpr (by simp [hP,hlen,Nat.add_sub_of_le hpu]),?_,?_⟩
    · simpa only [Q.descendant_append] using hpos
    · simpa only [← hP] using (List.take_left : (P++D).take P.length = P)

theorem projection_measure_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) {p u : ℕ} (hpu : p ≤ u)
    {P : CellPath} (hP : P.length = p) :
    ρ.restrict (Q.descendant P).carrier =
      ∑ C ∈ projectionTestCells Q ρ p u P, ρ.restrict (Q.descendant C).carrier := by
  rw [projectionTestCells_eq_image Q ρ hpu hP]
  exact (occupied_absolute_measure_sum Q hQ ρ P (u-p)).symm

theorem ae_projection_cell (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) {p u : ℕ} (hpu : p ≤ u)
    {P : CellPath} (hP : P.length = p) :
    ∀ᵐ x ∂ρ.restrict (Q.descendant P).carrier,
      ∃ C ∈ projectionTestCells Q ρ p u P, x ∈ (Q.descendant C).carrier := by
  rw [projection_measure_split Q hQ ρ hpu hP]
  apply ae_finsetSum_measure_iff.mpr
  intro C hC
  filter_upwards [ae_restrict_mem (Q.descendant C).measurable] with x hx
  exact ⟨C,hC,hx⟩

end PlanarFalconer

end OAI
