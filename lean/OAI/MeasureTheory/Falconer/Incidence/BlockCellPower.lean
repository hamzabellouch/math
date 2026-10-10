import OAI.MeasureTheory.Falconer.Incidence.BlockCellNormalPower
import OAI.MeasureTheory.Falconer.Incidence.BlockCellGoodGain

namespace OAI

/-! Normal and good cells have a common additive exponent. The gain is
charged only on cells whose actual secant slope crosses the fixed threshold. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockProfileCell_gain_exponent {N B i j : ℕ} (hN : 0 < N)
    (g : ℝ → ℝ) (u s η θ loss : ℝ) :
    profileGainExponent g u s η (3*θ) loss N (blockProfileCell N B (i,j)) =
      (s-3*θ)*( (blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))+
        (if u ≤ intervalSecantSlope g (blockProfileCell N B (i,j)).1
          (blockProfileCell N B (i,j)).2
          then η*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) else 0)-loss*N := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold profileGainExponent
  split_ifs
  all_goals dsimp [blockProfileCell]
  all_goals field_simp
  all_goals ring

theorem dyadic_good_power_weaken {N D n : ℕ} {s η θ loss : ℝ}
    (hs : 0 ≤ s) (hη : 0 ≤ η) (hθ : 0 ≤ θ) (hloss : 0 ≤ loss)
    (hD : D = 2*n) :
    (2:ℝ)^((s+η-3*θ)*(D:ℝ)-loss*N) ≤ (1/(2:ℝ)^(2*n+2))^(-(s+η)) := by
  rw [dyadic_inverse_power_eq,neg_neg]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have ht : 0 ≤ 3*θ*(D:ℝ) := by positivity
  have hl : 0 ≤ loss*(N:ℝ) := by positivity
  rw [hD] at ht ⊢
  push_cast
  push_cast at ht
  nlinarith only [ht,hl,hs,hη]

theorem block_cell_power {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+3 → ∀ s W θ q r : ℝ,
      κ ≤ s → s ≤ 1-8*κ → 1 ≤ W → 0 ≤ θ → 0 ≤ 3*q+r →
    ∀ N B K : ℕ, 0 < N → ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 N →
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
    ∀ i j : ℕ, j ≤ i → i ≤ K → blockDepth N B j-blockDepth N B i = 2*n →
      (let g := fun x => regularizedProfile L (blockLabel L N B f K) N B K p ((N:ℝ)*x);
        s ≤ intervalSecantSlope g (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 ∧
        intervalSecantSlope g (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 ≤ 2 ∧
        (∀ x ∈ Icc (blockProfileCell N B (i,j)).1
            ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
          -θ*(blockProfileCell N B (i,j)).2 ≤ intervalSecantError g
            (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x) ∧
        (s+2*κ ≤ intervalSecantSlope g (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 →
          ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
              ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
            |intervalSecantError g (blockProfileCell N B (i,j)).1
              (blockProfileCell N B (i,j)).2 x| ≤ θ*(blockProfileCell N B (i,j)).2)) →
      profileGeometryConstant K B W (θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) ≤
        (2:ℝ)^(q*(N:ℝ)+θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) →
      q*(N:ℝ)+θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) ≤ ε*((n+3:ℕ):ℝ) →
      640*((N:ℝ)+3) ≤ (2:ℝ)^(r*(N:ℝ)) →
      ProfileEndpointBound N B K L f p Q i j s W
        ((2:ℝ)^(profileGainExponent
          (fun x => regularizedProfile L (blockLabel L N B f K) N B K p ((N:ℝ)*x))
          (s+2*κ) s η (3*θ) (3*q+r) N (blockProfileCell N B (i,j)))) := by
  obtain ⟨ε,η,N0,hε,hε1,hη,hN0,hgood⟩ := block_cell_good_gain hκ hκ1
  refine ⟨ε,η,N0,hε,hε1,hη,hN0,?_⟩
  intro n hn s W θ q r hs hs1 hW hθ hloss N B K hN L hL f p Q hQ i j hji hi hlen
    hprofile hgeometry hscale hpoly
  obtain ⟨hslope,ht,hlo,hlinear⟩ := hprofile
  let g := fun x => regularizedProfile L (blockLabel L N B f K) N B K p ((N:ℝ)*x)
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hs1' : s ≤ 1 := by linarith
  have hcast : ((blockDepth N B j-blockDepth N B i:ℕ):ℝ) =
      (blockDepth N B j:ℝ)-(blockDepth N B i:ℝ) :=
    Nat.cast_sub (blockDepth_antitone N B hji)
  rw [blockProfileCell_gain_exponent hN]
  by_cases hh : s+2*κ ≤ intervalSecantSlope g (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2
  · rw [ite_eq_left hh]
    have hbudget : profileGeometryConstant K B W (θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) ≤
        Real.exp (ε*((n+3:ℕ):ℝ)*Real.log 2) := by
      calc
        _ ≤ (2:ℝ)^(q*(N:ℝ)+θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) := hgeometry
        _ ≤ (2:ℝ)^(ε*((n+3:ℕ):ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hscale
        _ = _ := by rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; congr 1; ring
    have hb := hgood n hn s (intervalSecantSlope g (blockProfileCell N B (i,j)).1
      (blockProfileCell N B (i,j)).2) W θ hs hs1 (by linarith only [hh]) ht hW hθ
      N B K hN L hL f p Q hQ i j hji hi hlen rfl (hlinear hh) hbudget
    apply hb.mono_value
    convert dyadic_good_power_weaken (N := N) hs0 hη.le hθ hloss hlen using 1
    rw [hcast]
    congr 1
    ring
  · rw [ite_eq_right hh,add_zero]
    exact block_cell_normal_power hN hL f p Q hQ hji hi hs0 hs1' hθ hW hslope hlo hgeometry hpoly

end Falconer

end OAI
