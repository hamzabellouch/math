import OAI.MeasureTheory.Falconer.Incidence.TruncatedBlockBall
import OAI.MeasureTheory.Falconer.Geometry.LocalPrefixCover

namespace OAI

/-! Upper profile chords bound the actual rounded cover of the endpoint
center configuration used in the multiscale induction. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_truncated_local_cover {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    {s A ρ : ℝ} (hρ : 0 < ρ)
    (hscale : (1/(2:ℝ)^(blockDepth N B k))/(1/(2:ℝ)^(blockDepth N B i)) ≤ ρ)
    (hprofile : let F := blockLabel L N B f K
      (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) (y c : ℝ) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
    let P := D.image (fun q => (Q.descendant q).center)
    (((P.image (localPacketPoint (1/(2:ℝ)^(blockDepth N B i)) y c)).image
      (coarsePlanarRound ρ)).card:ℝ) ≤
        49*((2:ℝ)^i*(2:ℝ)^(s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A)) := by
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
  let P := D.image (fun q => (Q.descendant q).center)
  have hCsub : C ⊆ cubePaths 2 N := fun q hq => hL (Finset.mem_filter.mp hq).1
  have hDsub : D ⊆ cubePaths 2 (blockDepth N B j) :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hCsub (Nat.sub_le _ _))
  obtain ⟨l,hleaf,_,himage,_⟩ := planar_path_center_realization Q (by rw [hQ]; norm_num) D hDsub
  have hb := finite_local_prefix_coarse_cover hρ (by positivity : 0 < 1/(2:ℝ)^(blockDepth N B i))
    y c Q (by rw [hQ]; norm_num) P l hleaf (blockDepth_antitone N B hjk)
    (by simpa only [hQ] using hscale)
  have he : D.image (List.take (blockDepth N B k)) =
      prefixChildren C (blockDepth N B i) (blockDepth N B k) p₀ := by
    simp only [D,prefixChildren,Finset.image_image,Function.comp_def,List.take_take,
      Nat.min_eq_left (blockDepth_antitone N B hjk)]
  rw [himage,he] at hb
  have hc := blockClass_local_covering hN hL B f K p hki hi hp₀ hprofile
  exact hb.trans (mul_le_mul_of_nonneg_left hc (by norm_num))

end Falconer

end OAI
