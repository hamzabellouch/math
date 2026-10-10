import OAI.MeasureTheory.Falconer.Incidence.TruncatedBlockCover
import OAI.MeasureTheory.Falconer.Estimates.LocalPrefixCenters
import OAI.MeasureTheory.Falconer.Recursion.ProfileChordBounds

namespace OAI

/-! Actual separated endpoint configurations for a regular profile interval.
Both the Frostman bound and the intermediate covering bound are inherited
from its chord; the two endpoint truncation losses remain explicit. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_truncated_chord_geometry {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ) (p : CellPath 2)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    {s t ε : ℝ} (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (hslope : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      s ≤ intervalSecantSlope (fun x => g ((N:ℝ)*x))
        ((blockDepth N B i:ℝ)/N) (((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N) ∧
      intervalSecantSlope (fun x => g ((N:ℝ)*x))
        ((blockDepth N B i:ℝ)/N) (((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N) ≤ t)
    (herr : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      ∀ x ∈ Icc ((blockDepth N B i:ℝ)/N) ((blockDepth N B j:ℝ)/N),
        |intervalSecantError (fun u => g ((N:ℝ)*u))
          ((blockDepth N B i:ℝ)/N) (((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N) x| ≤
            ε*(((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N)) :
    let a := blockDepth N B i
    let b := blockDepth N B j
    let A := ε*((b:ℝ)-(a:ℝ))
    let D := prefixChildren (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a b p₀
    let P := D.image (fun q => (Q.descendant q).center)
    let Z := P.image (localPacketPoint (1/(2:ℝ)^a)
      ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1))
    Z.Nonempty ∧ Z.card = D.card ∧ InBoundedLineChart Z ∧
      FiniteSeparatedAt (1/(2:ℝ)^(b-a)) Z ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(b-a)) s
        (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s) Z ∧
      ∀ k, j ≤ k → k ≤ i → ∀ ρ : ℝ, 0 < ρ →
        (1/(2:ℝ)^(blockDepth N B k))/(1/(2:ℝ)^a) ≤ ρ →
        ((Z.image (coarsePlanarRound ρ)).card:ℝ) ≤
          49*((2:ℝ)^i*(2:ℝ)^(t*((blockDepth N B k:ℝ)-(a:ℝ))+A)) := by
  dsimp only
  have hdepth : (blockDepth N B i:ℝ) ≤ (blockDepth N B j:ℝ) :=
    Nat.cast_le.mpr (blockDepth_antitone N B hji)
  have hA : 0 ≤ ε*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) :=
    mul_nonneg hε (sub_nonneg.mpr hdepth)
  have hlower : ∀ k, j ≤ k → k ≤ i →
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-
        ε*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) ≤
      (N:ℝ)*(regularizedProfile L (blockLabel L N B f K) N B K p (blockDepth N B k)-
        regularizedProfile L (blockLabel L N B f K) N B K p (blockDepth N B i)) := by
    intro k hjk hki
    apply normalized_chord_lower _ (Nat.cast_pos.mpr hN)
      ⟨Nat.cast_le.mpr (blockDepth_antitone N B hki),
        Nat.cast_le.mpr (blockDepth_antitone N B hjk)⟩ hslope.1
    intro x hx
    simpa only [neg_mul] using (abs_le.mp (herr x hx)).1
  obtain ⟨hP,_,hball⟩ := blockClass_truncated_local_ball hN hL B f K p Q hQ hji hi hp₀
    hs hA hlower ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
  have hC : classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p) ⊆ cubePaths 2 N :=
    fun q hq => hL (Finset.mem_filter.mp hq).1
  obtain ⟨hcard,hchart,hsep⟩ := local_prefix_centers_geometry Q hQ _ hC
    (blockDepth_antitone N B hji) (Nat.sub_le _ _) p₀
  refine ⟨hP.image _,hcard,hchart,hsep,hball,?_⟩
  intro k hjk hki ρ hρ hscale
  apply blockClass_truncated_local_cover hN hL B f K p Q hQ hjk hki hi hp₀ hρ hscale
  apply normalized_chord_upper _ (Nat.cast_pos.mpr hN)
    ⟨Nat.cast_le.mpr (blockDepth_antitone N B hki),
      Nat.cast_le.mpr (blockDepth_antitone N B hjk)⟩ hslope.2
  intro x hx
  exact (abs_le.mp (herr x hx)).2

end Falconer

end OAI
