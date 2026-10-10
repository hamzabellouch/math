import OAI.MeasureTheory.Falconer.Graphs.ScalarGraphCoding
import OAI.MeasureTheory.Falconer.Geometry.IntegerMixedRefinement

namespace OAI

/-! The two-sided refinement for separated real sets. Large subsets of
the original sets have a small full sumset at the original scale. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

theorem scalar_mixed_refinement_with_degrees {δ ρ : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (D : Finset ℤ) (hρ : 0 < ρ)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((B.filter fun b => e a b).card : ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊(a+b)/δ⌋ ∈ D) :
    ∃ X ⊆ A, ∃ Y ⊆ B,
      ρ^2*(A.card : ℝ)/64 ≤ (X.card : ℝ) ∧
      ρ*(B.card : ℝ)/4 ≤ (Y.card : ℝ) ∧
      ((scalarCells δ (X+Y)).card : ℝ)*(ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2) ≤
        67108864*(D.card : ℝ)^5 ∧
      ∀ x ∈ X, ρ^2*(Y.card:ℝ)/64 ≤ ((Y.filter fun y => e x y).card:ℝ) := by
  classical
  let C := D ∪ D.image (fun z => z-1)
  have hC : (C.card : ℝ) ≤ 2*(D.card : ℝ) := by
    have h := (Finset.card_union_le D (D.image fun z => z-1)).trans
      (Nat.add_le_add_left (Finset.card_image_le (s := D)) D.card)
    have h' : C.card ≤ 2*D.card := by dsimp [C]; omega
    exact_mod_cast h'
  have hlabelC : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊a/δ⌋+⌊b/δ⌋ ∈ C := by
    intro a ha b hb he
    have hmem := hlabels a ha b hb he
    rw [add_div] at hmem
    rcases floor_add_carry (a/δ) (b/δ) with h | h
    · exact Finset.mem_union_left _ (h ▸ hmem)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⌊a/δ+b/δ⌋,hmem,by omega⟩)
  obtain ⟨d,hsum,hlabels',hpoint⟩ := scalar_graph_coding_pointwise hδ A B hAsep hBsep e C hlabelC
  have hAi := scalarCells_injective hδ hAsep
  have hBi := scalarCells_injective hδ hBsep
  have hAc : (scalarCells δ A).card = A.card := Finset.card_image_of_injOn hAi
  have hBc : (scalarCells δ B).card = B.card := Finset.card_image_of_injOn hBi
  have hdense' : ρ*((scalarCells δ A).card : ℝ)*((scalarCells δ B).card : ℝ) ≤
      ∑ a ∈ scalarCells δ A, ((integerNeighbors (scalarCells δ B) d a).card : ℝ) := by
    rw [hAc,hBc,hsum]
    exact hdense
  obtain ⟨S,hSA,T,hTB,hS,hT,hbound,hdegrees⟩ := integer_mixed_refinement_with_degrees
    (scalarCells δ A) (scalarCells δ B) C d
    (Finset.image_nonempty.mpr hA) (Finset.image_nonempty.mpr hB) hρ hdense' hlabels'
  obtain ⟨X,hXA,hXimage⟩ := Finset.subset_image_iff.mp hSA
  obtain ⟨Y,hYB,hYimage⟩ := Finset.subset_image_iff.mp hTB
  have hXc : X.card = S.card := by
    rw [← hXimage]
    exact (Finset.card_image_of_injOn (hAi.mono hXA)).symm
  have hYc : Y.card = T.card := by
    rw [← hYimage]
    exact (Finset.card_image_of_injOn (hBi.mono hYB)).symm
  have hsumcard := scalarCells_add_card δ X Y
  change (scalarCells δ (X+Y)).card ≤
    2*(X.image (fun x => ⌊x/δ⌋)+Y.image (fun x => ⌊x/δ⌋)).card at hsumcard
  rw [hXimage,hYimage] at hsumcard
  rw [hAc] at hS
  rw [hBc] at hT
  rw [hAc,hBc] at hbound
  refine ⟨X,hXA,Y,hYB,by simpa only [hXc] using hS,by simpa only [hYc] using hT,?_,?_⟩
  · have hsumR : ((scalarCells δ (X+Y)).card : ℝ) ≤ 2*((S+T).card : ℝ) := by
      exact_mod_cast hsumcard
    have hk : 0 ≤ ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2 := by positivity
    have hb := mul_le_mul_of_nonneg_right hsumR hk
    have hc5 : (C.card : ℝ)^5 ≤ (2*(D.card : ℝ))^5 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hC 5
    nlinarith
  · intro x hx
    have hxS : ⌊x/δ⌋ ∈ S := by
      rw [← hXimage]
      exact Finset.mem_image_of_mem _ hx
    have hd := hdegrees ⌊x/δ⌋ hxS
    have he : integerNeighbors T d ⌊x/δ⌋ =
        (Y.filter fun y => e x y).image (fun y => ⌊y/δ⌋) := by
      rw [← hYimage]
      ext v
      constructor
      · intro hv
        obtain ⟨hvT,hvd⟩ := Finset.mem_filter.mp hv
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hvT
        exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,
          (hpoint x (hXA hx) y (hYB hy)).1 hvd⟩,rfl⟩
      · intro hv
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hy,hye⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hy,
          (hpoint x (hXA hx) y (hYB hy)).2 hye⟩
    change ρ^2*(T.card:ℝ)/64 ≤ ((integerNeighbors T d ⌊x/δ⌋).card:ℝ) at hd
    rw [he,Finset.card_image_of_injOn (hBi.mono ((Finset.filter_subset _ _).trans hYB)),← hYc] at hd
    exact hd

theorem scalar_mixed_refinement {δ ρ : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (D : Finset ℤ) (hρ : 0 < ρ)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((B.filter fun b => e a b).card : ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊(a+b)/δ⌋ ∈ D) :
    ∃ X ⊆ A, ∃ Y ⊆ B,
      ρ^2*(A.card : ℝ)/64 ≤ (X.card : ℝ) ∧
      ρ*(B.card : ℝ)/4 ≤ (Y.card : ℝ) ∧
      ((scalarCells δ (X+Y)).card : ℝ)*(ρ^8*(A.card : ℝ)^2*(B.card : ℝ)^2) ≤
        67108864*(D.card : ℝ)^5 := by
  obtain ⟨X,hXA,Y,hYB,hX,hY,hbound,_⟩ :=
    scalar_mixed_refinement_with_degrees hδ A B hA hB hAsep hBsep e D hρ hdense hlabels
  exact ⟨X,hXA,Y,hYB,hX,hY,hbound⟩

end Falconer

end OAI
