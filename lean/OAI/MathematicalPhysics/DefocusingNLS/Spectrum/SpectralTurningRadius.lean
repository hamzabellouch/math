import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningGeometry

namespace OAI

/-! Turning radii escape in both high-parameter cases used in the paper. -/

open Filter
namespace DefocusingNLS

theorem spectralTurning_radius_bound (h b eta omega r : ℝ)
    (hh : |h|≤1) (hb : b≤1) (homega : 0≤omega) (hr : 0<r)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r=0) :
    eta/(1+omega)≤r^4/16+r^2 := by
  have hr2 : 0<r^2 := sq_pos_of_pos hr
  have hden : 0<1+omega := by linarith
  have he : eta+99/4=r^4/16+(b-h*omega)*r^2 := by
    dsimp only [homogeneousSpectralLocalizationFrequency] at hz
    have hprod := congrArg (fun x : ℝ => x*r^2) hz
    field_simp at hprod
    nlinarith
  have hhw : -omega≤h*omega := by nlinarith [abs_le.mp hh]
  have hlow : eta≤r^4/16+(1+omega)*r^2 := by
    have hm := mul_le_mul_of_nonneg_right (show b-h*omega≤1+omega by linarith) hr2.le
    nlinarith
  apply (div_le_iff₀ hden).mpr
  have hrest : 0≤omega*(r^4/16) := by positivity
  nlinarith

theorem spectralTurning_radius_escape_caseI
    (h : ℝ) (hh : |h|≤1) (b eta omega r : ℕ → ℝ)
    (hescape : Tendsto (fun n => eta n/(1+omega n)) atTop atTop)
    (hdata : ∀ᶠ n in atTop, b n≤1 ∧ 0≤eta n ∧ 0≤omega n ∧ 0<r n ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r n)=0) :
    Tendsto r atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let C := max B 1
  have hC : 0≤C := le_trans (by norm_num : (0 : ℝ)≤1) (le_max_right _ _)
  filter_upwards [hdata,hescape.eventually (eventually_gt_atTop (C^4/16+C^2))] with n hn he
  have hb := spectralTurning_radius_bound h (b n) (eta n) (omega n) (r n)
    hh hn.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2
  by_contra hrB
  have hrC : r n≤C := (le_of_not_ge hrB).trans (le_max_left _ _)
  have h2 := pow_le_pow_left₀ hn.2.2.2.1.le hrC 2
  have h4 := pow_le_pow_left₀ hn.2.2.2.1.le hrC 4
  linarith

theorem spectralTurning_positive_radius_bound (b eta omega r : ℝ)
    (hb : b≤1) (heta : 0≤eta) (hr : 0<r)
    (hz : homogeneousSpectralLocalizationFrequency 1 b eta omega r=0) :
    16*(omega-1)≤r^2 := by
  have hp : 0≤(eta+99/4)/r^2 := by positivity
  dsimp only [homogeneousSpectralLocalizationFrequency] at hz
  norm_num only [one_mul] at hz
  linarith

theorem spectralTurning_radius_escape_caseII (b eta omega r : ℕ → ℝ)
    (hescape : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, b n≤1 ∧ 0≤eta n ∧ 0<r n ∧
      homogeneousSpectralLocalizationFrequency 1 (b n) (eta n) (omega n) (r n)=0) :
    Tendsto r atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let C := max B 1
  have hC : 0≤C := le_trans (by norm_num : (0 : ℝ)≤1) (le_max_right _ _)
  filter_upwards [hdata,hescape.eventually (eventually_gt_atTop (1+C^2/16))] with n hn he
  have hb := spectralTurning_positive_radius_bound (b n) (eta n) (omega n) (r n)
    hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
  by_contra hrB
  have hrC : r n≤C := (le_of_not_ge hrB).trans (le_max_left _ _)
  have h2 := pow_le_pow_left₀ hn.2.2.1.le hrC 2
  linarith

end DefocusingNLS

end OAI
