import Mathlib
import OAI.RepresentationTheory.PartialPermutation.RankFillings

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

def diagonalIndices (μ : YoungDiagram) : Finset ℕ := μ.cells.image (fun x => x.1+x.2)

def diagonalRank (μ : YoungDiagram) (x : μ.cells) : diagonalIndices μ :=
  ⟨x.1.1+x.1.2, Finset.mem_image.mpr ⟨x.1,x.2,rfl⟩⟩

lemma diagonalRank_strictMono (μ : YoungDiagram) : StrictMono (diagonalRank μ) := by
  intro x y hxy
  have h1 : x.1.1 ≤ y.1.1 := hxy.le.1
  have h2 : x.1.2 ≤ y.1.2 := hxy.le.2
  have hn : x.1 ≠ y.1 := fun h => (ne_of_lt hxy) (Subtype.ext h)
  change x.1.1+x.1.2 < y.1.1+y.1.2
  by_contra h
  apply hn
  exact Prod.ext (by omega) (by omega)

lemma diagonal_factorial_lower_bound (μ : YoungDiagram) :
    (∏ k : diagonalIndices μ,
      (Fintype.card {x : μ.cells // diagonalRank μ x = k}).factorial) ≤ standardCount μ :=
  rank_factorial_le_filling_count _ _ (diagonalRank μ) (diagonalRank_strictMono μ)

lemma diagonal_power_lower_bound (μ : YoungDiagram) :
    2^(μ.cells.card - (diagonalIndices μ).card) ≤ standardCount μ := by
  simpa only [Fintype.card_coe, standardCount] using
    rank_power_le_filling_count _ _ (diagonalRank μ) (diagonalRank_strictMono μ)

lemma diagonal_count_le (μ : YoungDiagram) : (diagonalIndices μ).card ≤ 2*maxLine μ-1 := by
  apply (Finset.card_le_card (t := Finset.range (2*maxLine μ-1)) ?_).trans_eq (Finset.card_range _)
  intro k hk
  obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp hk
  have hj : j < maxLine μ := (μ.mem_iff_lt_rowLen.mp hij).trans_le
    ((μ.rowLen_anti 0 i (Nat.zero_le _)).trans (le_max_left _ _))
  have hi : i < maxLine μ := (μ.mem_iff_lt_colLen.mp hij).trans_le
    ((μ.colLen_anti 0 j (Nat.zero_le _)).trans (le_max_right _ _))
  simp only [Finset.mem_range]
  omega

lemma width_height_power_lower_bound (μ : YoungDiagram) :
    2^(μ.cells.card - (2*maxLine μ-1)) ≤ standardCount μ :=
  (Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_left (diagonal_count_le μ) _)).trans
    (diagonal_power_lower_bound μ)

end
end Tableau
end PartialPermutation
end

end OAI
