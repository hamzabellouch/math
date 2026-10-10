import OAI.Geometry.RCD.Harmonic.AffineChange
import OAI.Geometry.RCD.Harmonic.TransformedColumns

namespace OAI

/-! # Actual Sobolev columns after a linear change and local recentering -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A continuous linear Sobolev family is recovered from its finite
standard coordinate columns. -/
theorem sobolevColumnMap_of_linear {n : ℕ}
    (U : Euclidean n →L[ℝ] SobolevSpace μ hQ) :
    sobolevColumnMap μ hQ (fun i => U (EuclideanSpace.single i 1)) = U := by
  classical
  ext v
  rw [sobolevColumnMap_apply]
  have he : (∑ i : Fin n, v i • EuclideanSpace.single i 1) = v := by
    ext j
    simp [Pi.single_apply]
  simpa only [map_sum, map_smul] using congrArg U he

/-- The local constant is supplied by a genuine compact Sobolev cutoff. -/
def affineChangedColumn {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (B : Euclidean n →L[ℝ] Euclidean n) (b : Euclidean n →L[ℝ] ℝ)
    (η : SobolevSpace μ hQ) : Fin n → SobolevSpace μ hQ :=
  fun i => sobolevColumnMap μ hQ u (B (EuclideanSpace.single i 1)) +
    b (EuclideanSpace.single i 1) • η

theorem sobolevColumnMap_affineChanged {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (B : Euclidean n →L[ℝ] Euclidean n) (b : Euclidean n →L[ℝ] ℝ)
    (η : SobolevSpace μ hQ) :
    sobolevColumnMap μ hQ (affineChangedColumn μ hQ u B b η) =
      (sobolevColumnMap μ hQ u).comp B + b.smulRight η := by
  exact sobolevColumnMap_of_linear μ hQ ((sobolevColumnMap μ hQ u).comp B + b.smulRight η)

/-- Recentring and normalizing the actual Sobolev columns preserves their
least-squares residual on every set where the cutoff equals one. -/
theorem affineChangedColumn_residual_eq {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (B : Euclidean n ≃L[ℝ] Euclidean n) (b : Euclidean n →L[ℝ] ℝ)
    (η : SobolevSpace μ hQ) (s : Set X) (hfin : μ s ≠ ∞)
    (hη : SobolevSpace.restrictLp μ hQ s η = restrictedOne μ s hfin) :
    affineResidual μ hQ (affineChangedColumn μ hQ u B b η) s hfin =
      affineResidual μ hQ u s hfin := by
  apply affineResidual_eq_of_change μ hQ u _ s hfin B b
  intro v
  rw [sobolevColumnMap_affineChanged]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearEquiv.coe_coe, map_add, map_smul, hη]

/-- A local pointwise representative equal to one identifies the
restriction with the constant generator of the affine space. -/
theorem restrictLp_eq_one_of_representative (η : SobolevSpace μ hQ)
    (s : Set X) (hfin : μ s ≠ ∞)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict s] fun _ => (1 : ℝ)) :
    SobolevSpace.restrictLp μ hQ s η = restrictedOne μ s hfin := by
  apply Lp.ext
  have hone : restrictedOne μ s hfin =ᵐ[μ.restrict s] fun _ => (1 : ℝ) := by
    simpa only [restrictedOne, indicator_univ] using
      (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ.restrict s)
        (hs := MeasurableSet.univ) (hμs := by simpa only [Measure.restrict_apply_univ] using hfin)
        (c := (1 : ℝ)))
  exact (SobolevSpace.restrictLp_coe μ hQ s η).trans (hη.trans hone.symm)

end RegularPointCoordinates

end

end OAI
