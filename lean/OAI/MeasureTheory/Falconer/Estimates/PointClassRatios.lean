import OAI.MeasureTheory.Falconer.Incidence.PlanarLeafInjection
import OAI.MeasureTheory.Falconer.Incidence.BlockClassRatios

namespace OAI

/-! The original point Frostman bound controls ratios in the selected planar
block class. All losses remain explicit. -/
namespace Falconer
open Regularization

theorem point_block_class_ratio {δ s K A r : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    {P : Finset (Space 2)} (hball : NormalizedFiniteBallBound δ s K P)
    (Q : DyadicCube 2) (hQ : 0 < Q.side) {N : ℕ}
    {l : Space 2 → CellPath 2} (hl : Set.InjOn l (P : Set (Space 2)))
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    {B : ℕ} (hB : 0 < B) {p : CellPath 2} (hp : p ∈ P.image l)
    (hsize : ((P.image l).card : ℝ) ≤ A*(classLeaves (P.image l)
      (blockLabel (P.image l) N B (fun _ => []) (N/B+1))
      (blockLabel (P.image l) N B (fun _ => []) (N/B+1) p)).card)
    (i : ℕ) (hi : i ≤ N/B+1) (hdr : δ ≤ r) (hr1 : r ≤ 1)
    (hdiam : Real.sqrt 2*(Q.side/(2 : ℝ)^(blockDepth N B i)) ≤ r) :
    let F := blockLabel (P.image l) N B (fun _ => []) (N/B+1)
    (blockProduct (P.image l) F N B i p : ℝ)/
      (blockProduct (P.image l) F N B (N/B+1) p : ℝ) ≤ K*r^s*A*(2 : ℝ)^(N/B+1) := by
  have hL : P.image l ⊆ cubePaths 2 N := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact (hleaf x hx).1
  apply blockClass_ratio_le hL hB (fun _ => []) hp hi
    (mul_nonneg hK (Real.rpow_nonneg (hδ.le.trans hdr) s)) hA hsize
  intro q
  exact leaf_image_prefix_count_bound hδ hK hball Q hQ (Nat.sub_le _ _) hl hleaf hdr hr1 hdiam q

end Falconer

end OAI
