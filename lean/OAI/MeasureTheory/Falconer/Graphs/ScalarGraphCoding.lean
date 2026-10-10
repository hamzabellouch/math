import OAI.MeasureTheory.Falconer.Estimates.ScalarEnergyRefinement

namespace OAI

/-! Exact graph transport under scalar quantization. The inverse is used
only on occupied cells of separated original sets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem scalar_graph_coding_pointwise {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (C : Finset ℤ)
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊a/δ⌋+⌊b/δ⌋ ∈ C) :
    ∃ d : ℤ → ℤ → Prop,
      (∑ u ∈ scalarCells δ A, ((integerNeighbors (scalarCells δ B) d u).card : ℝ)) =
        ∑ a ∈ A, ((B.filter fun b => e a b).card : ℝ) ∧
      (∀ u ∈ scalarCells δ A, ∀ v ∈ scalarCells δ B, d u v → u+v ∈ C) ∧
      ∀ a ∈ A, ∀ b ∈ B, d ⌊a/δ⌋ ⌊b/δ⌋ ↔ e a b := by
  classical
  let q : ℝ → ℤ := fun x => ⌊x/δ⌋
  let aInv := Function.invFunOn q (A : Set ℝ)
  let bInv := Function.invFunOn q (B : Set ℝ)
  let d : ℤ → ℤ → Prop := fun u v => e (aInv u) (bInv v)
  have hAi : Set.InjOn q (A : Set ℝ) := scalarCells_injective hδ hAsep
  have hBi : Set.InjOn q (B : Set ℝ) := scalarCells_injective hδ hBsep
  have haInv (a : ℝ) (ha : a ∈ A) : aInv (q a) = a := hAi.leftInvOn_invFunOn ha
  have hbInv (b : ℝ) (hb : b ∈ B) : bInv (q b) = b := hBi.leftInvOn_invFunOn hb
  have hneighbor (a : ℝ) (ha : a ∈ A) :
      integerNeighbors (scalarCells δ B) d (q a) = (B.filter fun b => e a b).image q := by
    ext v
    simp only [integerNeighbors,Finset.mem_filter]
    change (v ∈ B.image q ∧ d (q a) v) ↔ _
    simp only [Finset.mem_image,Finset.mem_filter]
    constructor
    · rintro ⟨⟨b,hb,rfl⟩,he⟩
      have he' : e a b := by
        simpa only [d,haInv a ha,hbInv b hb] using he
      exact ⟨b,⟨hb,he'⟩,rfl⟩
    · rintro ⟨b,⟨hb,he⟩,rfl⟩
      refine ⟨⟨b,hb,rfl⟩,?_⟩
      simpa only [d,haInv a ha,hbInv b hb] using he
  have hneighborCard (a : ℝ) (ha : a ∈ A) :
      (integerNeighbors (scalarCells δ B) d (q a)).card = (B.filter fun b => e a b).card := by
    rw [hneighbor a ha]
    exact Finset.card_image_of_injOn (hBi.mono (Finset.filter_subset _ _))
  have hsum : (∑ u ∈ scalarCells δ A, ((integerNeighbors (scalarCells δ B) d u).card : ℝ)) =
      ∑ a ∈ A, ((B.filter fun b => e a b).card : ℝ) := by
    change (∑ u ∈ A.image q, _) = _
    rw [Finset.sum_image hAi]
    exact Finset.sum_congr rfl (fun a ha => by rw [hneighborCard a ha])
  have hlabels' : ∀ u ∈ scalarCells δ A, ∀ v ∈ scalarCells δ B, d u v → u+v ∈ C := by
    intro u hu v hv he
    change u ∈ A.image q at hu
    change v ∈ B.image q at hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    apply hlabels a ha b hb
    simpa only [d,haInv a ha,hbInv b hb] using he
  refine ⟨d,hsum,hlabels',?_⟩
  intro a ha b hb
  change d (q a) (q b) ↔ e a b
  simp only [d,haInv a ha,hbInv b hb]

theorem scalar_graph_coding {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (C : Finset ℤ)
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊a/δ⌋+⌊b/δ⌋ ∈ C) :
    ∃ d : ℤ → ℤ → Prop,
      (∑ u ∈ scalarCells δ A, ((integerNeighbors (scalarCells δ B) d u).card : ℝ)) =
        ∑ a ∈ A, ((B.filter fun b => e a b).card : ℝ) ∧
      ∀ u ∈ scalarCells δ A, ∀ v ∈ scalarCells δ B, d u v → u+v ∈ C := by
  obtain ⟨d,hsum,hlabels',_⟩ := scalar_graph_coding_pointwise hδ A B hAsep hBsep e C hlabels
  exact ⟨d,hsum,hlabels'⟩

end Falconer

end OAI
