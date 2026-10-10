import OAI.MeasureTheory.Falconer.Recursion.ProfileNormalBound

namespace OAI

/-! A polynomial depth loss suffices for a normal interval once its point
and pencil constants fit the common weak budget. -/
namespace Falconer
open Regularization

theorem planarCriticalConstant_le_depth {s : ℝ} (hs : s ≤ 1) {D N : ℕ} (hD : D ≤ N+2) :
    planarCriticalConstant D s ≤ 7*((N:ℝ)+3) := by
  have h2 : (2:ℝ)^s ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  have hD' : (D:ℝ) ≤ N+2 := by exact_mod_cast hD
  calc
    _ ≤ 1+2*(1+(D:ℝ)*2) := by unfold planarCriticalConstant; gcongr
    _ ≤ _ := by linarith

theorem planar_normal_cost_bound {s H W E : ℝ} {D N : ℕ}
    (hs : s ≤ 1) (hD : D ≤ N+2) (hH : 1 ≤ H) (hW : 1 ≤ W) (hE : 1 ≤ E)
    (hHE : H ≤ E) (hWE : W ≤ E) :
    W*H*80^s*(1+H*planarCriticalConstant D s) ≤ 640*E^3*((N:ℝ)+3) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 80) hs
  have hcrit := planarCriticalConstant_le_depth hs hD
  have hcrit0 : 0 ≤ planarCriticalConstant D s := by unfold planarCriticalConstant; positivity
  have hparent : 1+H*planarCriticalConstant D s ≤ 8*E*((N:ℝ)+3) := by
    have hprod : H*planarCriticalConstant D s ≤ E*(7*((N:ℝ)+3)) :=
      mul_le_mul hHE hcrit (by unfold planarCriticalConstant; positivity) hE0
    have hlarge : 1 ≤ E*((N:ℝ)+3) := one_le_mul_of_one_le_of_one_le hE
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    nlinarith only [hprod,hlarge]
  calc
    _ ≤ E*E*80*(8*E*((N:ℝ)+3)) := by gcongr
    _ = _ := by ring

theorem profileEndpointBound_normal_budget {N B K : ℕ} (hN : 0 < N)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {s A W E : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hA : 0 ≤ A) (hW : 1 ≤ W) (hE : 1 ≤ E) (hWE : W ≤ E)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i)))
    (hpoint : (max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*
      (W*(2:ℝ)^(2*i+2*j))))*4^s ≤ E) :
    ProfileEndpointBound N B K L f p Q i j s W
      ((1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2))^(-s)/(640*E^3*((N:ℝ)+3))) := by
  have hh := profileEndpointBound_normal hN hL f p Q hQ hji hi hs hA hW hprofile
  let D := blockDepth N B j-blockDepth N B i+2
  let C := (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(W*(2:ℝ)^(2*i+2*j))
  let H := max 1 (max W ((max 1 C)*4^s))
  have hH : 1 ≤ H := le_max_left _ _
  have hHE : H ≤ E := max_le hE (max_le hWE hpoint)
  have hD : D ≤ N+2 := by dsimp [D,blockDepth]; omega
  have hcost := planar_normal_cost_bound hs1 hD hH hW hE hHE hWE
  have hcrit : 0 ≤ planarCriticalConstant D s := by unfold planarCriticalConstant; positivity
  have hcost0 : 0 < W*H*80^s*(1+H*planarCriticalConstant D s) := by positivity
  exact hh.mono_value (div_le_div_of_nonneg_left (by positivity) hcost0 hcost)

end Falconer

end OAI
