import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularPhysical

namespace OAI

/-! Holomorphy is preserved when restoring the angular radial factor. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralAngularPair_analyticAt (ell : ℕ) (Y : ℂ → ℝ → E₄)
    (z : ℂ) (r : ℝ) (hY : AnalyticAt ℂ (fun lam => Y lam r) z) :
    AnalyticAt ℂ (fun lam => spectralAngularPair ell (Y lam) r) z := by
  have h1 : AnalyticAt ℂ (fun lam => (Y lam r).1) z := by
    convert! ((ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ)).analyticAt _).comp hY
  have h2 : AnalyticAt ℂ (fun lam => (Y lam r).2) z := by
    convert! ((ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)).analyticAt _).comp hY
  have h11 : AnalyticAt ℂ (fun lam => (Y lam r).1.1) z := by
    convert! ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp h1
  have h12 : AnalyticAt ℂ (fun lam => (Y lam r).1.2) z := by
    convert! ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _).comp h1
  have h21 : AnalyticAt ℂ (fun lam => (Y lam r).2.1) z := by
    convert! ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp h2
  have h22 : AnalyticAt ℂ (fun lam => (Y lam r).2.2) z := by
    convert! ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _).comp h2
  exact ((analyticAt_const.mul h11).prod
    (analyticAt_const.mul ((analyticAt_const.mul h11).add h12))).prod
    ((analyticAt_const.mul h21).prod
      (analyticAt_const.mul ((analyticAt_const.mul h21).add h22)))

end DefocusingNLS

end OAI
