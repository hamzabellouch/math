import OAI.MeasureTheory.Falconer.Recursion.ProfileChordBounds

namespace OAI

/-! The actual block classes inherit regularity from each selected profile
interval. All losses are retained in the exponent. -/
namespace Falconer.Regularization
open Set
variable {d : ℕ}

theorem blockClass_chord_frostman {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) (hi : i ≤ K)
    {P Q : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    (hQ : Q ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B k))) {s ε : ℝ}
    (hs : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      s ≤ intervalSecantSlope (fun t => g ((N : ℝ)*t))
        ((blockDepth N B i : ℝ)/N)
        (((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))/N))
    (herr : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      ∀ t ∈ Icc ((blockDepth N B i : ℝ)/N) ((blockDepth N B j : ℝ)/N),
        -ε*(((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))/N) ≤
          intervalSecantError (fun u => g ((N : ℝ)*u))
            ((blockDepth N B i : ℝ)/N)
            (((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))/N) t) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    ((prefixFiber C (blockDepth N B k) Q).card : ℝ)/
      ((prefixFiber C (blockDepth N B i) P).card : ℝ) ≤
      (2 : ℝ)^k*(2 : ℝ)^(ε*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))-
        s*((blockDepth N B k : ℝ)-(blockDepth N B i : ℝ))) := by
  apply blockClass_local_frostman hN hL B f K p hki hi hP hQ
  apply normalized_chord_lower _ (Nat.cast_pos.mpr hN) _ hs herr
  exact ⟨Nat.cast_le.mpr (blockDepth_antitone N B hki),
    Nat.cast_le.mpr (blockDepth_antitone N B hjk)⟩

theorem blockClass_chord_covering {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) (hi : i ≤ K)
    {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) {s ε : ℝ}
    (hs : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      intervalSecantSlope (fun t => g ((N : ℝ)*t))
        ((blockDepth N B i : ℝ)/N)
        (((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))/N) ≤ s)
    (herr : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      ∀ t ∈ Icc ((blockDepth N B i : ℝ)/N) ((blockDepth N B j : ℝ)/N),
        intervalSecantError (fun u => g ((N : ℝ)*u))
            ((blockDepth N B i : ℝ)/N)
            (((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))/N) t ≤
          ε*(((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))/N)) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    ((prefixChildren C (blockDepth N B i) (blockDepth N B k) P).card : ℝ) ≤
      (2 : ℝ)^i*(2 : ℝ)^(s*((blockDepth N B k : ℝ)-(blockDepth N B i : ℝ))+
        ε*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))) := by
  apply blockClass_local_covering hN hL B f K p hki hi hP
  apply normalized_chord_upper _ (Nat.cast_pos.mpr hN) _ hs herr
  exact ⟨Nat.cast_le.mpr (blockDepth_antitone N B hki),
    Nat.cast_le.mpr (blockDepth_antitone N B hjk)⟩

end Falconer.Regularization

end OAI
