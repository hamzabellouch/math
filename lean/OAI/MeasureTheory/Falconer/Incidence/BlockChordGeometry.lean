import OAI.MeasureTheory.Falconer.Incidence.BlockProfileBallBound
import OAI.MeasureTheory.Falconer.Incidence.BlockProfileCover

namespace OAI

/-! A regular profile interval gives both geometric hypotheses for the
finite-scale incidence argument, for the original points in each parent. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_chord_geometry {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {P : Finset (Space 2)} {l : Space 2 → CellPath 2}
    (hl : Set.InjOn l (P : Set (Space 2)))
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (himage : P.image l = classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (P.image l).image (List.take (blockDepth N B i)))
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
            ε*(((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N)) (y c : ℝ) :
    let a := blockDepth N B i
    let b := blockDepth N B j
    let A := ε*((b:ℝ)-(a:ℝ))
    let S := pointPrefixFiber P l a p₀
    let F := localPacketPoint (1/(2:ℝ)^a) y c
    NormalizedFiniteBallBound (1/(2:ℝ)^(b-a)) s
      (49*(((2:ℝ)^i*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s) (S.image F) ∧
    ∀ k, j ≤ k → k ≤ i → ∀ ρ : ℝ, 0 < ρ →
      ((1/(2:ℝ)^(blockDepth N B k))/(1/(2:ℝ)^a)) ≤ ρ →
      (((S.image F).image (coarsePlanarRound ρ)).card:ℝ) ≤
        49*((2:ℝ)^i*(2:ℝ)^(t*((blockDepth N B k:ℝ)-(a:ℝ))+A)) := by
  dsimp only
  have hdepth : (blockDepth N B i:ℝ) ≤ (blockDepth N B j:ℝ) :=
    Nat.cast_le.mpr (blockDepth_antitone N B hji)
  have hA : 0 ≤ ε*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) :=
    mul_nonneg hε (sub_nonneg.mpr hdepth)
  constructor
  · apply blockClass_local_ball_bound hN hL B f K p Q hQ hl hleaf himage hji hi hp₀ hs hA
    intro k hjk hki
    apply normalized_chord_lower _ (Nat.cast_pos.mpr hN)
      ⟨Nat.cast_le.mpr (blockDepth_antitone N B hki),
        Nat.cast_le.mpr (blockDepth_antitone N B hjk)⟩ hslope.1
    intro x hx
    simpa only [neg_mul] using (abs_le.mp (herr x hx)).1
  · intro k hjk hki ρ hρ hscale
    apply blockClass_local_coarse_cover hN hL B f K p Q (by rw [hQ]; norm_num)
      hleaf himage hki hi hp₀ hρ (by positivity)
      (by simpa only [hQ] using hscale)
    apply normalized_chord_upper _ (Nat.cast_pos.mpr hN)
      ⟨Nat.cast_le.mpr (blockDepth_antitone N B hki),
        Nat.cast_le.mpr (blockDepth_antitone N B hjk)⟩ hslope.2
    intro x hx
    exact (abs_le.mp (herr x hx)).2

end Falconer

end OAI
