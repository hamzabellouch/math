import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidualOrder
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnRadiusOrder
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnResidual
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnRemote
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleOscillatoryBounds

namespace OAI

/-! Uniform scalar transfer on the whole interval in the no-turn channel. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralNoTurn_uniform_inner_transfer
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (C R B : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (_hRB : R ≤ B) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    ∀ᶠ n in atTop, ∀ L ∈ Icc R B, ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc L (E n)) →
      (∀ t ∈ Ioo L (E n), HasDerivAt q (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+
          Complex.I*(gamma n : ℂ)) (q t)) t) →
      ∀ r ∈ Icc L (E n), ∀ t ∈ Icc L (E n), r ≤ t →
        let k := fun s => Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) s‖
        spectralShellNorm (k t) (q t) ≤ (25*Real.exp (256+25/4))*spectralShellNorm (k r) (q r) ∧
        spectralShellNorm (k r) (q r) ≤ (25*Real.exp (256+25/4))*spectralShellNorm (k t) (q t) := by
  let eta := fun n => (ell n : ℝ)*(ell n+10)
  have hgeom : ∀ᶠ n in atTop, R ≤ E n ∧ E n ≤ 32*Real.sqrt (omega n/2) := by
    filter_upwards [hdata,hw.eventually (eventually_ge_atTop (C+2)),
      hw.eventually (eventually_ge_atTop (R^2))] with n hn hcn hrn
    exact spectralNoTurn_remote (ell n) (omega n) C R (E n) hC hcn hR hrn hn.2.2.2.1 hn.2.2.1 hn.2.2.2.2
  have hd : ∀ᶠ n in atTop, 0 ≤ b n ∧ 0 ≤ eta n ∧ R ≤ E n ∧ eta n+99/4 ≤ C*omega n := by
    filter_upwards [hdata,hgeom] with n hn hg
    exact ⟨hn.1,by dsimp only [eta]; positivity,hg.1,hn.2.2.2.1⟩
  have hres := spectralNoTurn_residual_tendsto b eta omega gamma E C R hC hR hCR hw hd
  have hroot : Tendsto (fun n => Real.sqrt (omega n/2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (hw.atTop_div_const (by norm_num))
  have hE := (spectralNoTurn_eventual_data ell b omega gamma E C R hC hR hw hdata).1
  filter_upwards [hdata,hgeom,hres.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hroot.eventually (eventually_ge_atTop ((2/R+4*C/R^3)/2)),
    hw.eventually (eventually_gt_atTop (0 : ℝ)),
    hE.eventually (eventually_ge_atTop B)] with n hn hg hj hk hwn hBE
  have hF (t : ℝ) (ht : t ∈ Icc R (E n)) :
      0 < homogeneousSpectralLocalizationFrequency (-1) (b n) (eta n) (omega n) t :=
    lt_of_lt_of_le (by positivity) (spectralNoTurn_frequency_lower (b n) (eta n) (omega n) C R t
      hn.1 hwn hR ht.1 hn.2.2.2.1 hCR)
  have hsmall (t : ℝ) (ht : t ∈ Icc R (E n)) :=
    spectralNoTurn_derivative_small (b n) (eta n) (omega n) (gamma n) C R t hn.1
      (by dsimp only [eta]; positivity) hwn hC hR ht.1 hn.2.2.2.1 hCR (by linarith)
  intro L hL q hq hqD r hr t ht hrt
  have hL0 : 0 < L := hR.trans_le hL.1
  have hLE : L ≤ E n := hL.2.trans hBE
  have hCL : 2*C ≤ L^2 := hCR.trans (pow_le_pow_left₀ hR.le hL.1 2)
  have hphaseL := spectralNoTurn_phase_bound (b n) (eta n) (omega n) C L (E n) 32
    hn.1 hwn hL0 hLE hn.2.2.2.1 hCL hg.2
  have hjL := (spectralLiouvilleResidual_unscaled_mono 1 (-1) (b n) (eta n)
    (omega n) (gamma n) R L (E n) (by norm_num) hR hL.1 hLE
    (by simpa only [one_mul] using hF)).trans hj.le
  have hb := spectralLiouville_oscillatory_subinterval (-1) (b n) (eta n) (omega n) (gamma n)
    L (E n) 32 1 hL0 hLE
      (fun x hx => hF x ⟨hL.1.trans hx.1,hx.2⟩)
      (fun x hx => hsmall x ⟨hL.1.trans hx.1,hx.2⟩) hphaseL hjL r t hr ht hrt q hq hqD
  have hNr := spectralShellNorm_nonneg (Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n)
    (eta n) (omega n) (gamma n) r‖) (Real.sqrt_nonneg _) (q r)
  have hNt := spectralShellNorm_nonneg (Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n)
    (eta n) (omega n) (gamma n) t‖) (Real.sqrt_nonneg _) (q t)
  have he : Real.exp (|gamma n| *32+(25/4)*1) ≤ Real.exp (256+25/4) :=
    Real.exp_le_exp.mpr (by linarith [hn.2.1])
  have hc : 2*((25/4 : ℝ)*Real.exp (|gamma n| *32+(25/4)*1)) ≤ 25*Real.exp (256+25/4) := by
    nlinarith [Real.exp_pos (256+(25/4 : ℝ))]
  have hc' : (25/4 : ℝ)*Real.exp (|gamma n| *32+(25/4)*1) ≤ 25*Real.exp (256+25/4) := by
    nlinarith [Real.exp_pos (|gamma n| *32+(25/4)*1)]
  exact ⟨hb.1.trans (mul_le_mul_of_nonneg_right hc' hNr),hb.2.trans (mul_le_mul_of_nonneg_right hc hNt)⟩

end DefocusingNLS

end OAI
