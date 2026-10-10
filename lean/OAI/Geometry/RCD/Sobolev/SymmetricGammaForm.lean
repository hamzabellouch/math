import OAI.Geometry.RCD.Coordinates.GammaCoordinateForm

namespace OAI

/-! # A pointwise symmetric Gram form for a finite Sobolev family -/

open Filter MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

def symmetricGammaForm (U : Euclidean m →L[ℝ] SobolevSpace μ hQ) (x : X) :
    Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ :=
  (1/2:ℝ) • (gammaCoordinateForm μ hQ U U x+(gammaCoordinateForm μ hQ U U x).flip)

omit [ProperSpace X] in
theorem symmetricGammaForm_symmetric (U : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (x : X) (a b : Euclidean m) : symmetricGammaForm μ hQ U x a b=symmetricGammaForm μ hQ U x b a := by
  change (1/2:ℝ)*(gammaCoordinateForm μ hQ U U x a b+gammaCoordinateForm μ hQ U U x b a)=
    (1/2:ℝ)*(gammaCoordinateForm μ hQ U U x b a+gammaCoordinateForm μ hQ U U x a b)
  ring

theorem symmetricGammaForm_rep (U : Euclidean m →L[ℝ] SobolevSpace μ hQ) (a b : Euclidean m) :
    localGamma μ hQ (U a) (U b) =ᵐ[μ] fun x => symmetricGammaForm μ hQ U x a b := by
  filter_upwards [gammaCoordinateForm_rep μ hQ U U a b,gammaCoordinateForm_rep μ hQ U U b a,
    localGamma_comm μ hQ (U b) (U a)] with x ha hb hc
  change localGamma μ hQ (U a) (U b) x=
    (1/2:ℝ)*(gammaCoordinateForm μ hQ U U x a b+gammaCoordinateForm μ hQ U U x b a)
  rw [← ha,← hb,hc]
  ring

theorem symmetricGammaForm_nonneg (U : Euclidean m →L[ℝ] SobolevSpace μ hQ) (a : Euclidean m) :
    ∀ᵐ x ∂μ, 0 ≤ symmetricGammaForm μ hQ U x a a := by
  filter_upwards [symmetricGammaForm_rep μ hQ U a a,localGamma_self μ hQ (U a)] with x he hs
  rw [← he,hs]
  positivity

end RegularPointCoordinates

end

end OAI
