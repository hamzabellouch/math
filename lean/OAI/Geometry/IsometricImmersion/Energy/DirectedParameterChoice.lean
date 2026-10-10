import OAI.Geometry.IsometricImmersion.Darboux.ModelPrincipal
import OAI.Geometry.IsometricImmersion.Energy.DirectedFarNegative

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Model

theorem exists_directed_parameters (ell : ℕ)
    {kappa cG rhoMax MG MI MB Mr MA MAs MAt MG1 D : ℝ}
    (hk : 0 < kappa) (hcG : 0 < cG) (hrho : 0 < rhoMax)
    (hMG : 0 ≤ MG) (hMI : 0 ≤ MI) (hMB : 0 ≤ MB) (hMr : 0 ≤ Mr)
    (hMA : 0 ≤ MA) (hMAs : 0 ≤ MAs) (hMAt : 0 ≤ MAt) (hMG1 : 0 ≤ MG1) (hD : 0 ≤ D) :
    ∃ epsilon lambda c1 : ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧
      epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax ∧
      2 * (MI + epsilon + epsilon * 2 * MB) ≤ lambda ∧
      (MI + 1 + 2 * MB) / 2 + Mr ≤ lambda / 8 ∧
      4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2 * MA ≤ 1 / 8 ∧
      (4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2) / lambda ≤
        modelCoercivityMargin cG kappa rhoMax epsilon ell / 8 ∧
      directedPrincipalBound ell epsilon 2 MAs MAt + modelCoercivityMargin cG kappa rhoMax epsilon ell / 2 ≤
        lambda * (cG * modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell) / 4 ∧
      c1 * D ≤ modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell ∧
      MG1 * c1 * (lambda * D + 8) ≤ modelCoercivityMargin cG kappa rhoMax epsilon ell / 6 := by
  let Cj := 2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)
  let L := 4 * Cj^2
  have hCj : 0 ≤ Cj := by dsimp [Cj]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbeta : 0 < ((ell : ℝ) + 1 / 2) / rhoMax := by positivity
  have hden : 0 < 8 * L * MA + 1 := by positivity
  let epsilon := min 1 (min (((ell : ℝ) + 1 / 2) / rhoMax) (1 / (8 * L * MA + 1)))
  have heps : 0 < epsilon := by dsimp [epsilon]; positivity
  have heps1 : epsilon ≤ 1 := min_le_left _ _
  have hepsbeta : epsilon ≤ ((ell : ℝ) + 1 / 2) / rhoMax :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hepsden : epsilon ≤ 1 / (8 * L * MA + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hcross : L * epsilon^2 * MA ≤ 1 / 8 := by
    have hm := (le_div_iff₀ hden).mp hepsden
    have hsquare : epsilon^2 ≤ epsilon := by nlinarith only [heps.le, heps1]
    have hprod := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hL hMA)
    nlinarith only [hm, hprod, heps.le]
  have hqbudget : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax := by
    have hh : epsilon * 2 * ((1 : ℝ) / 100) ≤ epsilon := by linarith only [heps.le]
    exact hh.trans hepsbeta
  let margin := modelCoercivityMargin cG kappa rhoMax epsilon ell
  let delta := modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell
  let alpha := cG * delta
  have hmargin : 0 < margin := modelCoercivityMargin_pos ell hcG hk hrho heps
  have hdelta : 0 < delta := modelPrincipalRadius_pos ell hcG hk hrho heps (by norm_num) hMG
  have halpha : 0 < alpha := mul_pos hcG hdelta
  let T0 := 2 * (MI + 1 + 2 * MB)
  let E0 := (MI + 1 + 2 * MB) / 2 + Mr
  let P0 := ((ell : ℝ) + 1 / 2) * MAs + MAt
  have hT0 : 0 ≤ T0 := by dsimp [T0]; positivity
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have hP0 : 0 ≤ P0 := by dsimp [P0]; positivity
  let lambda := 1 + T0 + 8 * E0 + 8 * L * epsilon^2 / margin + 4 * (P0 + margin / 2) / alpha
  have hLterm : 0 ≤ 8 * L * epsilon^2 / margin := by positivity
  have hFterm : 0 ≤ 4 * (P0 + margin / 2) / alpha := by positivity
  have hlambda : 0 < lambda := by dsimp [lambda]; linarith only [hT0, hE0, hLterm, hFterm]
  have hTlambda : T0 ≤ lambda := by dsimp [lambda]; linarith only [hE0, hLterm, hFterm]
  have hElambda : 8 * E0 ≤ lambda := by dsimp [lambda]; linarith only [hT0, hLterm, hFterm]
  have hLlambda : 8 * L * epsilon^2 / margin ≤ lambda := by dsimp [lambda]; linarith only [hT0, hE0, hFterm]
  have hFlambda : 4 * (P0 + margin / 2) / alpha ≤ lambda := by dsimp [lambda]; linarith only [hT0, hE0, hLterm]
  have hTbudget : 2 * (MI + epsilon + epsilon * 2 * MB) ≤ lambda := by
    have hp := mul_le_mul_of_nonneg_right heps1 (show 0 ≤ 2 * MB by positivity)
    have hh : 2 * (MI + epsilon + epsilon * 2 * MB) ≤ T0 := by dsimp [T0]; nlinarith only [hp, heps1]
    exact hh.trans hTlambda
  have hEbudget : E0 ≤ lambda / 8 := by linarith only [hElambda]
  have hloss : L * epsilon^2 / lambda ≤ margin / 8 := by
    have hh := (div_le_iff₀ hmargin).mp hLlambda
    apply (div_le_iff₀ hlambda).mpr
    nlinarith only [hh]
  have hprincipal : directedPrincipalBound ell epsilon 2 MAs MAt ≤ P0 := by
    have hh := mul_le_mul_of_nonneg_right heps1 hMAt
    dsimp [directedPrincipalBound, P0]
    nlinarith only [hh]
  have hfar : directedPrincipalBound ell epsilon 2 MAs MAt + margin / 2 ≤ lambda * alpha / 4 := by
    have hh := (div_le_iff₀ halpha).mp hFlambda
    nlinarith only [hh, hprincipal]
  have hD1 : 0 < D + 1 := by linarith only [hD]
  have hstripden : 0 < 6 * (MG1 + 1) * (lambda * D + 8) := by positivity
  let c1 := min (delta / (D + 1)) (margin / (6 * (MG1 + 1) * (lambda * D + 8)))
  have hc1 : 0 < c1 := by dsimp [c1]; positivity
  have hc1delta : c1 ≤ delta / (D + 1) := min_le_left _ _
  have hc1strip : c1 ≤ margin / (6 * (MG1 + 1) * (lambda * D + 8)) := min_le_right _ _
  have hnearstrip : c1 * D ≤ delta := by
    have hh := (le_div_iff₀ hD1).mp hc1delta
    nlinarith only [hh, hc1.le]
  have hstrip : MG1 * c1 * (lambda * D + 8) ≤ margin / 6 := by
    have hh := (le_div_iff₀ hstripden).mp hc1strip
    have hfac : 0 ≤ c1 * (lambda * D + 8) := by positivity
    have hbase : MG1 * c1 * (lambda * D + 8) ≤ (MG1 + 1) * c1 * (lambda * D + 8) := by
      nlinarith only [hfac]
    have hfull : (MG1 + 1) * c1 * (lambda * D + 8) ≤ margin / 6 := by nlinarith only [hh]
    exact hbase.trans hfull
  exact ⟨epsilon, lambda, c1, heps, heps1, hlambda, hc1, hqbudget, hTbudget,
    hEbudget, hcross, hloss, hfar, hnearstrip, hstrip⟩

end SmoothLocal.Weighted

end

end OAI
