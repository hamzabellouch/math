import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeCoreBoundary

namespace OAI

/-! The two free core conditions form a fixed continuous complex linear map. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralFreeCoreBoundaryCLM (ell : ℕ) (r : ℝ) : E₄ →L[ℂ] (Fin 2 → ℂ) :=
  let p := ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ)
  let n := ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)
  let v := ContinuousLinearMap.fst ℂ ℂ ℂ
  let d := ContinuousLinearMap.snd ℂ ℂ ℂ
  ContinuousLinearMap.pi (fun i => if i = 0 then v.comp p + v.comp n else
    d.comp p - d.comp n - ((ell : ℂ)/(r : ℂ)) • (v.comp p-v.comp n))

theorem spectralFreeCoreBoundaryCLM_apply (ell : ℕ) (r : ℝ) (U : E₄) :
    spectralFreeCoreBoundaryCLM ell r U = spectralFreeCoreBoundary ell r U := by
  funext i
  fin_cases i <;>
    simp [spectralFreeCoreBoundaryCLM,spectralFreeCoreBoundary]

theorem spectralFreeCoreBoundary_hasDerivAt (ell : ℕ) (r : ℝ) (U : ℂ → E₄)
    (D : E₄) (z : ℂ) (hU : HasDerivAt U D z) :
    HasDerivAt (fun lam => spectralFreeCoreBoundary ell r (U lam))
      (spectralFreeCoreBoundary ell r D) z := by
  simpa only [Function.comp_def,spectralFreeCoreBoundaryCLM_apply] using
    (spectralFreeCoreBoundaryCLM ell r).hasFDerivAt.comp_hasDerivAt z hU

theorem spectralFreeCoreBoundary_analyticAt (ell : ℕ) (r : ℝ) (U : ℂ → E₄)
    (z : ℂ) (hU : AnalyticAt ℂ U z) :
    AnalyticAt ℂ (fun lam => spectralFreeCoreBoundary ell r (U lam)) z := by
  simpa only [Function.comp_def,spectralFreeCoreBoundaryCLM_apply] using
    ((spectralFreeCoreBoundaryCLM ell r).analyticAt (U z)).comp hU

end DefocusingNLS

end OAI
