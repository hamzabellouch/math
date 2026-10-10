import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeShootingData
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoupledLargePower

namespace OAI

/-! Numerical data for the actual inner profiles at every sufficiently large odd power. -/

open Set Filter
namespace DefocusingNLS

theorem exists_radialInnerShootingData :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ w : RadialShootingDisk,
      ∃ P : RadialInnerData, P.p=2*n+1 ∧ P.R=innerBoundaryRadius ∧
        P.lo=‖(radialFreeInnerJet w innerBoundaryRadius).1‖ ∧
        P.c=6-1/(n : ℝ) ∧ P.b=radialShootingB w := by
  obtain ⟨P₁,_,hP₁⟩ := scalar_boundary_power_small (1-3*(1/10000 : ℝ)^2/20)
    (by norm_num) (by norm_num)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 999/1000) (by norm_num : (999/1000 : ℝ) < 1)
  obtain ⟨P₂,hP₂⟩ := eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/5)))
  refine ⟨max 200 (max P₁ P₂),?_⟩
  intro n hn w
  have hn200 : 200 ≤ n := (le_max_left _ _).trans hn
  have hnP₁ : P₁ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnP₂ : P₂ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  let lo := ‖(radialFreeInnerJet w innerBoundaryRadius).1‖
  have hlo := (radialFreeInnerJet_spec w).2.2.2.2
  have hlo0 : 0 ≤ lo := norm_nonneg _
  have hsmall : lo^((2*n+1)-1) ≤ (3/10 : ℝ) :=
    hP₁ (2*n+1) (by omega) lo hlo0 (by dsimp [lo]; linarith [hlo.2])
  have hleft : (999/1000 : ℝ)^(2*n) ≤ (1/5 : ℝ) := (hP₂ (2*n) (by omega)).le
  have htarg : (1/5 : ℝ) ∈ Icc ((999/1000 : ℝ)^(2*n)) ((1 : ℝ)^(2*n)) :=
    ⟨hleft,by norm_num⟩
  obtain ⟨m,hm,hmp⟩ := intermediate_value_Icc (by norm_num : (999/1000 : ℝ) ≤ 1)
    (continuous_id.pow (2*n)).continuousOn htarg
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hinv : 1/(n : ℝ) ≤ (1/100 : ℝ) := (div_le_iff₀ hnpos).mpr (by
    have hh : (200 : ℝ) ≤ n := by exact_mod_cast hn200
    linarith)
  let c : ℝ := 6-1/(n : ℝ)
  refine ⟨({ p := 2*n+1
             R := innerBoundaryRadius
             lo := lo
             c := c
             b := radialShootingB w
             m := m
             hp := by omega
             hR := innerBoundaryRadius_bounds.1
             hR2 := innerBoundaryRadius_bounds.2
             hlo := by dsimp [lo]; linarith [hlo.1]
             hlo1 := by dsimp [lo]; linarith [hlo.2]
             hSmall := hsmall
             hm := hm.1
             hm1 := hm.2
             hmp := by simpa using hmp
             hc := ⟨by dsimp [c]; linarith,by
               dsimp [c]
               have := one_div_nonneg.mpr hnpos.le
               linarith⟩
             hb := (radialShooting_geometry w).1 } : RadialInnerData),rfl,rfl,rfl,rfl,rfl⟩

end DefocusingNLS

end OAI
