import OAI.MeasureTheory.Falconer.Estimates.DescriptorTests

namespace OAI

/-! # A polynomial finite family containing every descriptor used at a scale -/

namespace Falconer
open PlanarFalconer (PolicyDescriptor)
attribute [local instance] Classical.propDecidable

noncomputable def validDescriptors (N : ℕ) : Finset PolicyDescriptor :=
  (((Finset.range (N+1) ×ˢ Finset.range (N+1)).image (fun p => PolicyDescriptor.parallel p.1 p.2)) ∪
    ((Finset.range (N+1) ×ˢ Finset.range (N+1)).image (fun p => PolicyDescriptor.projection p.1 p.2))).filter
      (descriptorValid N)

 theorem mem_validDescriptors (N : ℕ) (b : PolicyDescriptor) :
    b ∈ validDescriptors N ↔ descriptorValid N b := by
  constructor
  · exact fun hb => (Finset.mem_filter.mp hb).2
  · intro hb
    apply Finset.mem_filter.mpr
    refine ⟨?_,hb⟩
    cases b with
    | parallel g p =>
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨(g,p),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by
        change g ≤ p ∧ p ≤ N at hb; omega),Finset.mem_range.mpr (by
        change g ≤ p ∧ p ≤ N at hb; omega)⟩,rfl⟩
    | projection p t =>
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨(p,t),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by
        change p ≤ t ∧ t ≤ N at hb; omega),Finset.mem_range.mpr (by
        change p ≤ t ∧ t ≤ N at hb; omega)⟩,rfl⟩

 theorem validDescriptors_card (N : ℕ) : (validDescriptors N).card ≤ 2*(N+1)^2 := by
  apply (Finset.card_filter_le _ _).trans
  apply (Finset.card_union_le _ _).trans
  have hp := Finset.card_image_le (s := Finset.range (N+1) ×ˢ Finset.range (N+1))
    (f := fun p => PolicyDescriptor.parallel p.1 p.2)
  have ht := Finset.card_image_le (s := Finset.range (N+1) ×ˢ Finset.range (N+1))
    (f := fun p => PolicyDescriptor.projection p.1 p.2)
  simpa only [Finset.card_product,Finset.card_range,pow_two,two_mul] using Nat.add_le_add hp ht

end Falconer

end OAI
