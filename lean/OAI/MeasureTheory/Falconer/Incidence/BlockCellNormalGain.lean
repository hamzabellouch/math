import OAI.MeasureTheory.Falconer.Incidence.BlockProfileCells
import OAI.MeasureTheory.Falconer.Recursion.ProfileGeometryPower

namespace OAI

/-! The normal estimate evaluated directly on a selected real profile cell. -/
namespace Falconer
open Set Regularization

noncomputable def profileGeometryConstant (K B : ℕ) (W A : ℝ) : ℝ :=
  100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B)

theorem profileGeometryConstant_ge {W A : ℝ} (hW : 1 ≤ W) (hA : 0 ≤ A) (K B : ℕ) :
    W ≤ profileGeometryConstant K B W A := by
  have h1 : W ≤ 100000*W := by nlinarith only [hW]
  have h2 : 100000*W ≤ 100000*W*(2:ℝ)^(6*K) :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  have h3 : 100000*W*(2:ℝ)^(6*K) ≤ 100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (by norm_num) hA)
  exact h1.trans (h2.trans (h3.trans (le_mul_of_one_le_right (by positivity)
    (one_le_pow₀ (by norm_num)))))

theorem block_cell_normal_gain {N B K : ℕ} (hN : 0 < N)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {s θ W : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hθ : 0 ≤ θ) (hW : 1 ≤ W)
    (hslope : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      s ≤ intervalSecantSlope (fun x => g ((N:ℝ)*x))
        (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2)
    (herr : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
          ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
        -θ*(blockProfileCell N B (i,j)).2 ≤ intervalSecantError (fun u => g ((N:ℝ)*u))
          (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x) :
    let A := θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))
    let E := profileGeometryConstant K B W A
    ProfileEndpointBound N B K L f p Q i j s W
      ((1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2))^(-s)/(640*E^3*((N:ℝ)+3))) := by
  let A := θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))
  have hA : 0 ≤ A := mul_nonneg hθ (sub_nonneg.mpr (Nat.cast_le.mpr (blockDepth_antitone N B hji)))
  have hWE := profileGeometryConstant_ge hW hA K B
  have hpoint := (profile_geometry_costs (B := B) hi (hji.trans hi) hs
    (hs1.trans (by norm_num)) hA hW).1
  have hprofile := blockProfileCell_chord_lower (B := B) (i := i) (j := j)
    (regularizedProfile L (blockLabel L N B f K) N B K p) hN hslope herr
  exact profileEndpointBound_normal_budget hN hL f p Q hQ hji hi hs hs1 hA hW
    (hW.trans hWE) hWE hprofile hpoint

end Falconer

end OAI
