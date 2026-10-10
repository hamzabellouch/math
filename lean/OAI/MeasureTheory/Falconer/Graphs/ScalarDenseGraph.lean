import OAI.MeasureTheory.Falconer.Graphs.ScalarGraphCoding

namespace OAI

/-! Dense graphs of scalar sums give large original subsets with small
quantized difference sets. The floor map is used only as an injective
coding of the separated input points. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

theorem scalar_dense_graph_refinement {δ ρ L : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (C : Finset ℤ) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hsmall : L ≤ ρ^2*(A.card : ℝ)/32)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((B.filter fun b => e a b).card : ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊a/δ⌋+⌊b/δ⌋ ∈ C) :
    ∃ G ⊆ B, ρ*(B.card : ℝ)/4 ≤ (G.card : ℝ) ∧
      ((scalarCells δ (G-G)).card : ℝ)*((ρ*(B.card : ℝ)/4)*L^2) ≤
        2*(C.card : ℝ)^4 := by
  classical
  let q : ℝ → ℤ := fun x => ⌊x/δ⌋
  have hAi : Set.InjOn q (A : Set ℝ) := scalarCells_injective hδ hAsep
  have hBi : Set.InjOn q (B : Set ℝ) := scalarCells_injective hδ hBsep
  have hAc : (scalarCells δ A).card = A.card := Finset.card_image_of_injOn hAi
  have hBc : (scalarCells δ B).card = B.card := Finset.card_image_of_injOn hBi
  obtain ⟨d,hsum,hlabels'⟩ := scalar_graph_coding hδ A B hAsep hBsep e C hlabels
  have hdense' : ρ*((scalarCells δ A).card : ℝ)*((scalarCells δ B).card : ℝ) ≤
      ∑ u ∈ scalarCells δ A, ((integerNeighbors (scalarCells δ B) d u).card : ℝ) := by
    rw [hAc,hBc,hsum]
    exact hdense
  obtain ⟨S,hSB,hSsize,hSdiff⟩ := integer_dense_small_difference
    (scalarCells δ A) (scalarCells δ B) C d
    (Finset.image_nonempty.mpr hA) (Finset.image_nonempty.mpr hB)
    hρ hL (by simpa only [hAc] using hsmall) hdense' hlabels'
  obtain ⟨G,hGB,hGimage⟩ := Finset.subset_image_iff.mp hSB
  have hGc : G.card = S.card := by
    rw [← hGimage]
    exact (Finset.card_image_of_injOn (hBi.mono hGB)).symm
  have hGdiff := scalarCells_sub_card δ G G
  change (scalarCells δ (G-G)).card ≤ 2*(G.image q-G.image q).card at hGdiff
  rw [hGimage] at hGdiff
  rw [hBc] at hSsize hSdiff
  refine ⟨G,hGB,by simpa only [hGc] using hSsize,?_⟩
  have hGdiffR : ((scalarCells δ (G-G)).card : ℝ) ≤ 2*((S-S).card : ℝ) := by
    exact_mod_cast hGdiff
  have hk : 0 ≤ (ρ*(B.card : ℝ)/4)*L^2 :=
    mul_nonneg (div_nonneg (mul_nonneg hρ.le (Nat.cast_nonneg _)) (by norm_num)) (sq_nonneg L)
  exact (mul_le_mul_of_nonneg_right hGdiffR hk).trans (by nlinarith [hSdiff])

end Falconer

end OAI
