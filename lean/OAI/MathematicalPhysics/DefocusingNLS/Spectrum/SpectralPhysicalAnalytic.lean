import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalCoupling
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! The physical coordinate change preserves holomorphic dependence on the spectral parameter. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalPair_analyticAt (νp νm : ℂ → ℂ) (Y : ℂ → ℝ → E₄)
    (z : ℂ) (r : ℝ) (hp : AnalyticAt ℂ νp z) (hm : AnalyticAt ℂ νm z)
    (hY : AnalyticAt ℂ (fun lam => Y lam (Real.log r)) z) :
    AnalyticAt ℂ (fun lam => spectralPhysicalPair (νp lam) (νm lam) (Y lam) r) z := by
  have h1 : AnalyticAt ℂ (fun lam => (Y lam (Real.log r)).1) z := by
    convert! ((ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ)).analyticAt _).comp hY
  have h2 : AnalyticAt ℂ (fun lam => (Y lam (Real.log r)).2) z := by
    convert! ((ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)).analyticAt _).comp hY
  have h11 : AnalyticAt ℂ (fun lam => (Y lam (Real.log r)).1.1) z := by
    convert! ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp h1
  have h12 : AnalyticAt ℂ (fun lam => (Y lam (Real.log r)).1.2) z := by
    convert! ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _).comp h1
  have h21 : AnalyticAt ℂ (fun lam => (Y lam (Real.log r)).2.1) z := by
    convert! ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp h2
  have h22 : AnalyticAt ℂ (fun lam => (Y lam (Real.log r)).2.2) z := by
    convert! ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _).comp h2
  have hAp : AnalyticAt ℂ (fun lam => Complex.exp (νp lam*(Real.log r : ℂ))) z :=
    (hp.mul analyticAt_const).cexp'
  have hAm : AnalyticAt ℂ (fun lam => Complex.exp (νm lam*(Real.log r : ℂ))) z :=
    (hm.mul analyticAt_const).cexp'
  exact ((hAp.mul h11).prod (hAp.div_const.mul ((hp.mul h11).add h12))).prod
    ((hAm.mul h21).prod (hAm.div_const.mul ((hm.mul h21).add h22)))

end DefocusingNLS

end OAI
