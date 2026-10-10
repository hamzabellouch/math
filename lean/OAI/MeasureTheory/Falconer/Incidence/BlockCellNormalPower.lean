import OAI.MeasureTheory.Falconer.Incidence.BlockCellNormalGain

namespace OAI

/-! The normal cell contributes its baseline exponent, minus three times
its own chord error and the common weak loss. -/
namespace Falconer
open Set Regularization

theorem block_cell_normal_power {N B K : ℕ} (hN : 0 < N)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {s θ W q r : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hθ : 0 ≤ θ) (hW : 1 ≤ W)
    (hslope : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      s ≤ intervalSecantSlope (fun x => g ((N:ℝ)*x))
        (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2)
    (herr : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
          ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
        -θ*(blockProfileCell N B (i,j)).2 ≤ intervalSecantError (fun u => g ((N:ℝ)*u))
          (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x)
    (hgeometry : profileGeometryConstant K B W (θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) ≤
      (2:ℝ)^(q*(N:ℝ)+θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))))
    (hpoly : 640*((N:ℝ)+3) ≤ (2:ℝ)^(r*(N:ℝ))) :
    ProfileEndpointBound N B K L f p Q i j s W
      ((2:ℝ)^((s-3*θ)*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))-(3*q+r)*(N:ℝ))) := by
  let d := (blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)
  let A := θ*d
  let E := profileGeometryConstant K B W A
  let loss := (3*q+r)*(N:ℝ)+3*A
  have hE0 : 0 < E := by dsimp [E,profileGeometryConstant]; positivity
  have hcost : 640*E^3*((N:ℝ)+3) ≤ (2:ℝ)^loss := by
    calc
      _ ≤ 640*((2:ℝ)^(q*(N:ℝ)+A))^3*((N:ℝ)+3) := by gcongr
      _ ≤ _ := profile_normal_power_cost hpoly
  have hcost0 : 0 < 640*E^3*((N:ℝ)+3) := by positivity
  have hbound := block_cell_normal_gain hN hL f p Q hQ hji hi hs hs1 hθ hW hslope herr
  apply hbound.mono_value
  have hdepth : ((blockDepth N B j-blockDepth N B i+2:ℕ):ℝ) = d+2 := by
    rw [Nat.cast_add,Nat.cast_sub (blockDepth_antitone N B hji)]
    norm_num
    rfl
  calc
    _ ≤ (2:ℝ)^(s*((blockDepth N B j-blockDepth N B i+2:ℕ):ℝ)-loss) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [hdepth]
      dsimp [loss,A,d]
      nlinarith only [hs]
    _ ≤ (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2))^(-s)/(640*E^3*((N:ℝ)+3)) :=
      dyadic_power_below_normal_factor _ hcost0 hcost

end Falconer

end OAI
