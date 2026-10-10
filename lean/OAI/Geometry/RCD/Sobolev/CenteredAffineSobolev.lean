import OAI.Geometry.RCD.Coordinates.AffineFitPerturbation

namespace OAI

/-! # Sobolev representatives of the centered radial affine fits -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def centeredAffineSobolev {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (η : SobolevSpace μ hQ) (v a : Euclidean n) : SobolevSpace μ hQ :=
  (-⟪v, a⟫_ℝ) • η + sobolevColumnMap μ hQ u a

theorem centeredAffineSobolev_harmonic {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (η : SobolevSpace μ hQ) (v a : Euclidean n) (s : Set X)
    (hu : ∀ i, IsSobolevHarmonicOn μ hQ s (u i)) (hη : IsSobolevHarmonicOn μ hQ s η) :
    IsSobolevHarmonicOn μ hQ s (centeredAffineSobolev μ hQ u η v a) :=
  (hη.smul μ hQ (-⟪v, a⟫_ℝ)).add μ hQ (IsSobolevHarmonicOn.linearCombination μ hQ hu a)

theorem centeredAffineSobolev_restrict {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (η : SobolevSpace μ hQ) (v a : Euclidean n) (s : Set X) (hs : μ s ≠ ∞)
    (hη : SobolevSpace.restrictLp μ hQ s η = restrictedOne μ s hs) :
    SobolevSpace.restrictLp μ hQ s (centeredAffineSobolev μ hQ u η v a) =
      affineCoordinateMap μ hQ u s hs (-⟪v, a⟫_ℝ, a) := by
  rw [centeredAffineSobolev, map_add, map_smul, hη, affineCoordinateMap_apply]

end RegularPointCoordinates

end

end OAI
