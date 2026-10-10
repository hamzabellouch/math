import OAI.MeasureTheory.Falconer.Graphs.GraphDegrees

namespace OAI

/-!
# Parallel tests and the first unknown cell

A cap incidence supplies a witness direction. Grouping eligible cells by
their testing ancestor lets one witness control each group. The direction
perturbation is handled in the original ambient space.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

/-- The geometric counting step in `graph:degrees`. The hypotheses are the
literal parallel test at each eligible witness and the diameter of a common
ancestor. In applications there are at most `G` testing ancestors. -/
theorem parallel_count_from_witnesses {E α β : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [DecidableEq α] [DecidableEq β]
    (A : Finset α) (center : α → E) (ancestor : α → β)
    (w₀ base : E) (hw₀ : ‖w₀‖ = 1) {τ δ L W : ℝ} (hδ : 0 ≤ δ)
    {C G : ℕ} (hgroups : (A.image ancestor).card ≤ G)
    (hwidth : 2 * τ + 2 * δ * L ≤ W)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, ancestor x = ancestor y →
      ‖center x - center y‖ ≤ L)
    (hwitness : ∀ a ∈ A, ∃ w : E, ‖w‖ = 1 ∧ ‖w - w₀‖ ≤ δ ∧
      (A.filter (fun z => ancestor z = ancestor a ∧
        ‖center z - center a‖ ≤ L ∧
        ‖perpendicularPart w (center z - center a)‖ ≤ W)).card ≤ C) :
    (A.filter (fun z => ‖perpendicularPart w₀ (center z - base)‖ ≤ τ)).card ≤ C * G := by
  classical
  let S := A.filter (fun z => ‖perpendicularPart w₀ (center z - base)‖ ≤ τ)
  have hfiber (b : β) (hb : b ∈ S.image ancestor) :
      (S.filter (fun z => ancestor z = b)).card ≤ C := by
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
    obtain ⟨haA, haTube⟩ := Finset.mem_filter.mp ha
    obtain ⟨w, hw, hclose, htest⟩ := hwitness a haA
    apply le_trans (Finset.card_le_card (t := A.filter (fun z =>
      ancestor z = ancestor a ∧ ‖center z - center a‖ ≤ L ∧
        ‖perpendicularPart w (center z - center a)‖ ≤ W)) ?_) htest
    intro z hz
    obtain ⟨hzS, hzb⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzA, hzTube⟩ := Finset.mem_filter.mp hzS
    have hza : ancestor z = ancestor a := hzb.trans hab.symm
    have hsize := hdiam z hzA a haA hza
    exact Finset.mem_filter.mpr ⟨hzA, hza, hsize,
      (witness_tube_bound hw hw₀ hδ hzTube haTube hclose hsize).trans hwidth⟩
  have hcount := Finset.card_le_mul_card_image S C hfiber
  have hsub : S.image ancestor ⊆ A.image ancestor :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  exact hcount.trans (Nat.mul_le_mul_left C ((Finset.card_le_card hsub).trans hgroups))

end Falconer

end OAI
