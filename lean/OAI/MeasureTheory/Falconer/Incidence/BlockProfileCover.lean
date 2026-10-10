import OAI.MeasureTheory.Falconer.Geometry.LocalPrefixCover
import OAI.MeasureTheory.Falconer.Incidence.BlockChordRegularity

namespace OAI

/-! The upper profile chord controls the actual rounded cover in a parent
chart. The covering set consists of images of the original retained points. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_local_coarse_cover {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) (Q : DyadicCube 2) (hQ : 0 < Q.side)
    {P : Finset (Space 2)} {l : Space 2 → CellPath 2}
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (himage : P.image l = classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (P.image l).image (List.take (blockDepth N B i)))
    {s A ρ Δ : ℝ} (hρ : 0 < ρ) (hΔ : 0 < Δ)
    (hscale : (Q.side/(2:ℝ)^(blockDepth N B j))/Δ ≤ ρ)
    (hprofile : let F := blockLabel L N B f K
      (N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B j)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          s*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))+A) (y c : ℝ) :
    ((((pointPrefixFiber P l (blockDepth N B i) p₀).image (localPacketPoint Δ y c)).image
      (coarsePlanarRound ρ)).card:ℝ) ≤
        49*((2:ℝ)^i*(2:ℝ)^(s*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))+A)) := by
  have hSP : pointPrefixFiber P l (blockDepth N B i) p₀ ⊆ P := Finset.filter_subset _ _
  have hb := finite_local_prefix_coarse_cover hρ hΔ y c Q hQ
    (pointPrefixFiber P l (blockDepth N B i) p₀) l
    (fun x hx => hleaf x (hSP hx)) (Nat.sub_le _ _) hscale
  rw [pointPrefixFiber_image_children,himage] at hb
  have hp₀' := hp₀
  rw [himage] at hp₀'
  have hc := blockClass_local_covering hN hL B f K p hji hi hp₀' hprofile
  exact hb.trans (mul_le_mul_of_nonneg_left hc (by norm_num))

end Falconer

end OAI
