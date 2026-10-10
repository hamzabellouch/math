import OAI.MeasureTheory.Falconer.Incidence.BlockIntervalLengths
import OAI.MeasureTheory.Falconer.Recursion.ProfileChordBounds
import OAI.MeasureTheory.Falconer.Recursion.ProfileGainAccounting

namespace OAI

/-! Transfer the rounded real profile cells and their gains to the exact
block-index pairs used by the recursive incidence estimates. -/
namespace Falconer
open Set Regularization

noncomputable def blockProfileCell (N B : ℕ) (r : ℕ × ℕ) : ℝ × ℝ :=
  ((blockDepth N B r.1:ℝ)/N,
    ((blockDepth N B r.2:ℝ)-(blockDepth N B r.1:ℝ))/N)

theorem blockProfileCell_eq_of_endpoints {N B : ℕ} {r : ℕ × ℕ} {c : ℝ × ℝ}
    (ha : c.1 = (blockDepth N B r.1:ℝ)/N)
    (hb : c.1+c.2 = (blockDepth N B r.2:ℝ)/N) : c = blockProfileCell N B r := by
  apply Prod.ext ha
  change c.2 = ((blockDepth N B r.2:ℝ)-(blockDepth N B r.1:ℝ))/N
  calc
    c.2 = (blockDepth N B r.2:ℝ)/N-(blockDepth N B r.1:ℝ)/N := by linarith only [ha,hb]
    _ = _ := by ring

theorem rounded_block_gain_sum {m B : ℕ} (S : List (ℝ × ℝ))
    (I : (ℝ × ℝ) → (ℕ × ℕ))
    (hI : ∀ c ∈ S,
      (innerProfileCell m c).1 = (blockDepth (m*B) B (I c).1:ℝ)/(m*B:ℕ) ∧
      (innerProfileCell m c).1+(innerProfileCell m c).2 =
        (blockDepth (m*B) B (I c).2:ℝ)/(m*B:ℕ))
    (g : ℝ → ℝ) (u s η a loss N : ℝ) :
    ((S.map I).map fun r => profileGainExponent g u s η a loss N (blockProfileCell (m*B) B r)).sum =
      ((S.map (innerProfileCell m)).map (profileGainExponent g u s η a loss N)).sum := by
  rw [List.map_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  dsimp only [Function.comp_apply]
  rw [blockProfileCell_eq_of_endpoints (hI c hc).1 (hI c hc).2]

theorem blockProfileCell_chord_lower (g : ℝ → ℝ) {N B i j : ℕ} (hN : 0 < N)
    {s ε : ℝ}
    (hs : s ≤ intervalSecantSlope (fun x => g ((N:ℝ)*x))
      (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2)
    (herr : ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
        ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
      -ε*(blockProfileCell N B (i,j)).2 ≤ intervalSecantError (fun u => g ((N:ℝ)*u))
        (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x) :
    ∀ k, j ≤ k → k ≤ i →
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-
        ε*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) ≤
          (N:ℝ)*(g (blockDepth N B k)-g (blockDepth N B i)) := by
  intro k hjk hki
  apply normalized_chord_lower g (Nat.cast_pos.mpr hN)
    ⟨Nat.cast_le.mpr (blockDepth_antitone N B hki),
      Nat.cast_le.mpr (blockDepth_antitone N B hjk)⟩ hs
  intro x hx
  apply herr x
  change (blockDepth N B i:ℝ)/N ≤ x ∧
    x ≤ (blockDepth N B i:ℝ)/N+((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N
  rw [show (blockDepth N B i:ℝ)/N+((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N =
    (blockDepth N B j:ℝ)/N by ring]
  exact hx

theorem blockProfileCell_chord_upper (g : ℝ → ℝ) {N B i j : ℕ} (hN : 0 < N)
    {s ε : ℝ}
    (hs : intervalSecantSlope (fun x => g ((N:ℝ)*x))
      (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 ≤ s)
    (herr : ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
        ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
      intervalSecantError (fun u => g ((N:ℝ)*u))
        (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x ≤
          ε*(blockProfileCell N B (i,j)).2) :
    ∀ k, j ≤ k → k ≤ i →
      (N:ℝ)*(g (blockDepth N B k)-g (blockDepth N B i)) ≤
        s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+
          ε*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) := by
  intro k hjk hki
  apply normalized_chord_upper g (Nat.cast_pos.mpr hN)
    ⟨Nat.cast_le.mpr (blockDepth_antitone N B hki),
      Nat.cast_le.mpr (blockDepth_antitone N B hjk)⟩ hs
  intro x hx
  apply herr x
  change (blockDepth N B i:ℝ)/N ≤ x ∧
    x ≤ (blockDepth N B i:ℝ)/N+((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N
  rw [show (blockDepth N B i:ℝ)/N+((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N =
    (blockDepth N B j:ℝ)/N by ring]
  exact hx

end Falconer

end OAI
