import OAI.Geometry.RCD.Coordinates.SplittingApproximation

namespace OAI

/-! # Actual Sobolev columns under a coordinate transformation -/

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The coefficient map is the adjoint of the map acting on pointwise
coordinate values. -/
def transformedColumn {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (A : Euclidean n →L[ℝ] Euclidean n) : Fin n → SobolevSpace μ hQ :=
  fun i => sobolevColumnMap μ hQ u (A (EuclideanSpace.single i 1))

omit [BorelSpace X] [ProperSpace X] in
theorem sobolevColumnMap_transformed {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (A : Euclidean n →L[ℝ] Euclidean n) :
    sobolevColumnMap μ hQ (transformedColumn μ hQ u A) =
      (sobolevColumnMap μ hQ u).comp A := by
  classical
  ext v
  rw [sobolevColumnMap_apply]
  have he : (∑ i : Fin n, v i • EuclideanSpace.single i 1) = v := by
    ext j
    simp [Pi.single_apply]
  have h := congrArg ((sobolevColumnMap μ hQ u).comp A) he
  simpa only [map_sum, map_smul, ContinuousLinearMap.comp_apply, transformedColumn] using h

omit [BorelSpace X] [ProperSpace X] in
/-- Harmonicity of the transformed scalar components follows from actual
linearity in the Sobolev space. -/
theorem transformedColumn_harmonic {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (A : Euclidean n →L[ℝ] Euclidean n) (Ω : Set X)
    (hu : ∀ i, IsSobolevHarmonicOn μ hQ Ω (u i)) :
    ∀ i, IsSobolevHarmonicOn μ hQ Ω (transformedColumn μ hQ u A i) := by
  intro i
  exact IsSobolevHarmonicOn.linearCombination μ hQ hu (A (EuclideanSpace.single i 1))

/-- The exact normalization identity is the mean Gram identity for the
transformed components themselves. -/
theorem meanGram_transformed_eq_id {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (A : Euclidean n ≃L[ℝ] Euclidean n) (s : Set X) (hs : MeasurableSet s)
    (hA : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u) s hs A) :
    sobolevMeanGram μ hQ (sobolevColumnMap μ hQ (transformedColumn μ hQ u A)) s hs =
      ContinuousLinearMap.id ℝ (Euclidean n) := by
  rw [sobolevColumnMap_transformed]
  exact hA

end RegularPointCoordinates

end

end OAI
