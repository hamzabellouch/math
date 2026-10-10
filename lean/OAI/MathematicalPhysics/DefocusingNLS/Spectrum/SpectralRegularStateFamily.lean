import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularStateAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularFamily
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularRank

namespace OAI

/-! A holomorphic regular basis with its rank proved at the matching radius. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_regular_state_family (d : ℕ) (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) :
    ∃ W : (ℂ × ℂ) → ℂ → ℝ → E₄,
      (∀ c lam, W c lam 0=((c.1,0),(c.2,0)) ∧ Continuous (W c lam)) ∧
      (∀ c lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R,
        HasDerivAt (W c lam)
          (spectralRegularField d (A r) (B r) (cp+Complex.I*lam)
            (cm-Complex.I*lam) r (W c lam r)) r) ∧
      (∀ lam, ‖lam‖ ≤ L → LinearIndependent ℂ ![W (1,0) lam R,W (0,1) lam R]) ∧
      (∀ c z, ‖z‖ ≤ L → ∀ r, 0 ≤ r → AnalyticAt ℂ (fun lam => W c lam r) z) := by
  let α := spectralRegularSourceBound A B cp cm+2*L+1
  have hC := spectralRegularSourceBound_nonneg A B cp cm
  have hα : 0 < α := by dsimp only [α]; linarith
  have hgap (lam : ℂ) (hlam : ‖lam‖ ≤ L) :
      spectralRegularSourceBound A B (cp+Complex.I*lam) (cm-Complex.I*lam)<2*α := by
    have h := spectralRegularSourceBound_parameter A B cp cm lam
    dsimp only [α]
    linarith
  let W := fun c lam => spectralRegularState d α c
    (spectralRegularSolutionSource d R α hR.le hα A B cp cm c lam)
  have hinit (c : ℂ × ℂ) (lam : ℂ) :
      W c lam 0=((c.1,0),(c.2,0)) ∧ Continuous (W c lam) :=
    ⟨spectralRegularState_initial d α c _,spectralRegularState_continuous d α c _⟩
  have hODE (c : ℂ × ℂ) (lam : ℂ) (hlam : ‖lam‖ ≤ L) (r : ℝ) (hr : r ∈ Ioc 0 R) :
      HasDerivAt (W c lam) (spectralRegularField d (A r) (B r)
        (cp+Complex.I*lam) (cm-Complex.I*lam) r (W c lam r)) r :=
    spectralRegularState_hasDerivAt d R α hR.le hα A B _ _ c _ _
      (spectralRegularVector_equation d R α hR.le hα A B cp cm c lam (hgap lam hlam))
      rfl r hr
  refine ⟨W,hinit,hODE,?_,?_⟩
  · intro lam hlam
    exact spectralRegular_at_linearIndependent d A B _ _ (W (1,0) lam) (W (0,1) lam) R hR
      (hinit _ _).2 (hinit _ _).2 (hODE _ _ hlam) (hODE _ _ hlam)
      (hinit _ _).1 (hinit _ _).1
  · intro c z hz r hr
    exact spectralRegularState_analyticAt d α hα c _ z r hr
      (spectralRegularSolutionSource_analyticAt d R α hR.le hα A B cp cm c z (hgap z hz))

end DefocusingNLS

end OAI
