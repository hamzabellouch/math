import OAI.MeasureTheory.Falconer.Estimates.ScalarCompressedBunching

namespace OAI

/-! Quantitative radius-to-gap estimates for a trimmed porous bunch. -/
namespace Falconer

 theorem scalar_dyadic_gap_ratio {n s H : ℕ} (hs : n+H ≤ s) :
    5*(1/2:ℝ)^s/(4*(1/2:ℝ)^n) ≤ (5/4:ℝ)*(1/2:ℝ)^H := by
  have hpow : (1/2:ℝ)^s ≤ (1/2:ℝ)^n*(1/2:ℝ)^H := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  apply (div_le_iff₀ (by positivity : 0 < 4*(1/2:ℝ)^n)).2
  nlinarith

 theorem scalar_dyadic_gap_geometry {n s N : ℕ} (hn : n+2 ≤ s) (hs : s ≤ N) :
    15*(1/2:ℝ)^s < 4*(1/2:ℝ)^n ∧
      (1/2:ℝ)^N ≤ 5*(1/2:ℝ)^s/(4*(1/2:ℝ)^n) := by
  have hpow : (1/2:ℝ)^s ≤ (1/2:ℝ)^n/4 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) hn
    rw [pow_add] at hh
    norm_num at hh
    linarith
  have hpos : 0 < (1/2:ℝ)^n := by positivity
  have hle : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hNs : (1/2:ℝ)^N ≤ (1/2:ℝ)^s :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  constructor
  · linarith
  · apply hNs.trans
    apply (le_div_iff₀ (by positivity : 0 < 4*(1/2:ℝ)^n)).2
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) s]

 theorem scalar_dyadic_bunch_small {n s H M : ℕ} {K κ : ℝ}
    (hs : n+H ≤ s) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hsmall : 16*(M:ℝ)^4*K*((5/4:ℝ)*(1/2:ℝ)^H)^κ ≤ 1/4) :
    16*(M:ℝ)^4*K*(5*(1/2:ℝ)^s/(4*(1/2:ℝ)^n))^κ ≤ 1/4 := by
  apply le_trans _ hsmall
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (by positivity) (scalar_dyadic_gap_ratio hs) hκ

 theorem scalarPathCenter_unit (p : List (Fin 1 → Bool)) :
    0 ≤ scalarPathCenter p ∧ scalarPathCenter p ≤ 1 := by
  have hh := (⟨0,1⟩ : DyadicCube 1).descendant_subset p
    (((⟨0,1⟩ : DyadicCube 1).descendant p).center_mem
      ((⟨0,1⟩ : DyadicCube 1).descendant_side_pos (by norm_num) p))
  have hcoord := hh 0
  change 0 ≤ scalarPathCenter p ∧ scalarPathCenter p < 0+1 at hcoord
  exact ⟨hcoord.1,by linarith [hcoord.2]⟩

end Falconer

end OAI
