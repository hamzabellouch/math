import OAI.MeasureTheory.Falconer.Graphs.ScalarDenseGraph

namespace OAI

/-! A small restricted scalar sumset forces additive structure in one
of the original separated sets, with explicit polynomial losses. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

theorem scalar_restricted_sum_refinement {δ ρ : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (D : Finset ℤ) (hρ : 0 < ρ)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((B.filter fun b => e a b).card : ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊(a+b)/δ⌋ ∈ D) :
    ∃ G ⊆ B, ρ*(B.card : ℝ)/4 ≤ (G.card : ℝ) ∧
      ((scalarCells δ (G-G)).card : ℝ)*(ρ^5*(B.card : ℝ)*(A.card : ℝ)^2) ≤
        131072*(D.card : ℝ)^4 := by
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
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨⌊a/δ+b/δ⌋,hmem,by omega⟩
  let L : ℝ := ρ^2*(A.card : ℝ)/32
  have hL : 0 ≤ L := div_nonneg (mul_nonneg (sq_nonneg ρ) (Nat.cast_nonneg _)) (by norm_num)
  obtain ⟨G,hGB,hGsize,hGdiff⟩ := scalar_dense_graph_refinement hδ A B hA hB
    hAsep hBsep e C hρ hL (le_refl L) hdense hlabelC
  refine ⟨G,hGB,hGsize,?_⟩
  have hc4 : (C.card : ℝ)^4 ≤ (2*(D.card : ℝ))^4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hC 4
  have hscale : (ρ*(B.card : ℝ)/4)*L^2 =
      (ρ^5*(B.card : ℝ)*(A.card : ℝ)^2)/4096 := by dsimp [L]; ring
  rw [hscale] at hGdiff
  nlinarith

end Falconer

end OAI
