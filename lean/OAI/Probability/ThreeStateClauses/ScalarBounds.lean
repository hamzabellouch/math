import Mathlib

namespace OAI

/-! Scalar Bounds. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
namespace ThreeState.TreeClauses.Positive

def cLower (lam : ℝ) : ℝ := (37/27)*(1+2*lam/3)
def scalarT (lam mu s : ℝ) : ℝ :=
  (1-lam^2)/(2*s)+3/(2*(1+2*mu/3))+(17*lam*mu)/(25*s)

lemma cLower_pos {lam : ℝ} (hl : 0 ≤ lam) : 0 < cLower lam := by
  dsimp [cLower]; positivity

lemma small_polynomial {lam : ℝ} (h₀ : 0 ≤ lam) (h₁ : lam ≤ 3/10) :
    (2/5-lam^2/2)*cLower lam^2 > (2/3)*(11/10+lam^2/2) := by
  let u := (10/3)*lam
  have hu₀ : 0 ≤ u := by dsimp [u]; positivity
  have hu₁ : u ≤ 1 := by dsimp [u]; linarith
  have heq : (2/5-lam^2/2)*cLower lam^2-(2/3)*(11/10+lam^2/2) =
      (65000*(1-u)^4+1355200*u*(1-u)^3+3367745*u^2*(1-u)^2+
        2806680*u^3*(1-u)+716814*u^4)/3645000 := by dsimp [u, cLower]; ring
  have hp : 0 < (2/5-lam^2/2)*cLower lam^2-(2/3)*(11/10+lam^2/2) := by
    rw [heq]
    rcases lt_or_eq_of_le hu₁ with h | h
    · have : 0 < 1-u := sub_pos.mpr h
      positivity
    · rw [h]; norm_num
  linarith

lemma middle_polynomial {lam : ℝ} (h₀ : 3/10 ≤ lam) (h₁ : lam ≤ 71/100) :
    (2/5-lam^2/2)*cLower lam^2 > 1-17*lam/25 := by
  let u := (100/41)*(lam-3/10)
  have hu₀ : 0 ≤ u := by dsimp [u]; positivity
  have hu₁ : u ≤ 1 := by dsimp [u]; linarith
  have heq : (2/5-lam^2/2)*cLower lam^2-(1-17*lam/25) =
      (53796960000*(1-u)^4+340999128000*u*(1-u)^3+592285169900*u^2*(1-u)^2+
        337132599220*u^3*(1-u)+28181130511*u^4)/328050000000 := by dsimp [u, cLower]; ring
  have hp : 0 < (2/5-lam^2/2)*cLower lam^2-(1-17*lam/25) := by
    rw [heq]
    rcases lt_or_eq_of_le hu₁ with h | h
    · have : 0 < 1-u := sub_pos.mpr h
      positivity
    · rw [h]; norm_num
  linarith

lemma large_polynomial {lam : ℝ} (h : 7/10 ≤ lam) :
    (3/20)*cLower lam^2 > 1-17*lam/25 := by
  have heq : (3/20)*cLower lam^2-(1-17*lam/25) =
      44801/546750+(67297/54675)*(lam-7/10)+(1369/10935)*(lam-7/10)^2 := by
    dsimp [cLower]; ring
  have hpos : 0 < (3/20)*cLower lam^2-(1-17*lam/25) := by
    rw [heq]; positivity
  linarith

lemma substitute_moment_region {C B D mu : ℝ} (hC : 0 < C) (hD : 0 ≤ D)
    (hmu : mu*C^2 ≤ 1) (hBD : D < B*C^2) : D*mu < B := by
  have h := mul_le_mul_of_nonneg_left hmu hD
  have hprod : (D*mu)*C^2 < B*C^2 := by nlinarith
  exact (mul_lt_mul_iff_left₀ (sq_pos_of_pos hC)).mp hprod

lemma reciprocal_lower {mu : ℝ} (hmu : 0 ≤ mu) :
    3/2-mu ≤ 3/(2*(1+2*mu/3)) := by
  apply (le_div_iff₀ (by positivity : 0 < 2*(1+2*mu/3))).2
  nlinarith [sq_nonneg mu]

theorem scalar_strict {lam mu s : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (hmu : 0 ≤ mu) (hs₀ : 0 < s) (hs₁ : s ≤ 1) (hregion : mu*cLower lam^2 ≤ s)
    (hmodel : lam^2 ≤ 1/2 ∨ s ≤ 2*(1-lam^2)) : 8/5 < scalarT lam mu s := by
  have hC := cLower_pos hl₀.le
  have hmuC : mu*cLower lam^2 ≤ 1 := hregion.trans hs₁
  have hlam : 0 < 1-lam^2 := by nlinarith [mul_pos (sub_pos.mpr hl₁) (by linarith : 0 < 1+lam)]
  have hfirst : (1-lam^2)/2 ≤ (1-lam^2)/(2*s) :=
    div_le_div_of_nonneg_left hlam.le (by positivity) (by nlinarith)
  have hlast : 17*lam*mu/25 ≤ 17*lam*mu/(25*s) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have hrecip := reciprocal_lower hmu
  by_cases hsmall : lam ≤ 3/10
  · have hp := small_polynomial hl₀.le hsmall
    have hD : 0 ≤ (2/3)*(11/10+lam^2/2) := by positivity
    have hsub := substitute_moment_region hC hD hmuC hp
    have hden : 0 < 2*(1+2*mu/3) := by positivity
    have hfrac : 11/10+lam^2/2 < 3/(2*(1+2*mu/3)) := by
      apply (lt_div_iff₀ hden).2
      nlinarith
    dsimp [scalarT]
    have : 0 ≤ 17*lam*mu/25 := by positivity
    linarith
  · have hlow : 3/10 ≤ lam := le_of_not_ge hsmall
    have hD : 0 ≤ 1-17*lam/25 := by linarith
    rcases le_or_gt (lam^2) (1/2) with hmid | hbig
    · have hhigh : lam ≤ 71/100 := by nlinarith
      have hp := middle_polynomial hlow hhigh
      have hsub := substitute_moment_region hC hD hmuC hp
      dsimp [scalarT]
      nlinarith
    · have hsurvive : s ≤ 2*(1-lam^2) := hmodel.resolve_left (not_le.mpr hbig)
      have hquarter : 1/4 ≤ (1-lam^2)/(2*s) := by
        apply (le_div_iff₀ (by positivity : 0 < 2*s)).2
        linarith
      have hlarge : 7/10 ≤ lam := by nlinarith
      have hp := large_polynomial hlarge
      have hsub := substitute_moment_region hC hD hmuC hp
      dsimp [scalarT]
      nlinarith

end ThreeState.TreeClauses.Positive

end

end OAI
