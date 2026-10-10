import OAI.Geometry.EinsteinFour.CurvatureForm
import OAI.Geometry.EinsteinFour.RiemannianVolume

namespace OAI

/-! Spherical disintegration of the actual frame-curvature energies.

The explicit published input `BrinKarcherAveraging` is the specialization of
the Riemannian-base times Stiefel probability measure in Brin--Karcher (1984),
Section 1, p.275, to functions depending only on the first frame direction.
It is a generic integration statement and contains no curvature estimate.
The angular curvature identities used below are proved separately. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

local instance : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup

def DirectionInvariant {g : SmoothMetric M} (F : FrameBundle g → ℝ) : Prop :=
  ∀ e f, e.base = f.base → e.frame.vector 0 = f.frame.vector 0 → F e = F f

/-- Generic spherical disintegration, parameterized by the frame measure. -/
structure BrinKarcherAveraging (g : SmoothMetric M) (μ : Measure (FrameBundle g)) : Prop where
  probability : IsProbabilityMeasure μ
  fiberFormula : ∀ (F : FrameBundle g → ℝ) (A : M → ℝ),
    Integrable F μ → Integrable A (normalizedVolume g) → DirectionInvariant F →
    (∀ c (e : OrthonormalFrame g c), (∫ q, F (frameTurn e q) ∂sphereMeasure) = A c) →
    (∫ e, F e ∂μ) = ∫ c, A c ∂normalizedVolume g

/-- Derive the time-zero curvature energy from the published disintegration
and the proved frame transformation and angular contraction. -/
theorem frameCurvatureField_mean_square
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)} (hμ : BrinKarcherAveraging g μ)
    (h : FollandMoments) (S : M → ℝ)
    (hCi : Integrable (fun e => ‖frameCurvatureField g e‖ ^ 2) μ)
    (hSi : Integrable S (normalizedVolume g))
    (hInv : DirectionInvariant (fun e => ‖frameCurvatureField g e‖ ^ 2))
    (hdec : ∀ c (e : OrthonormalFrame g c), frameCurvature g c e =
      einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e))
    (htr : ∀ c (e : OrthonormalFrame g c),
      (plusWeyl g c e).trace = 0 ∧ (minusWeyl g c e).trace = 0)
    (hS : ∀ c (e : OrthonormalFrame g c),
      normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2 = S c) :
    (∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ) =
      (3 / 2) * (∫ c, S c ∂normalizedVolume g) := by
  rw [hμ.fiberFormula _ (fun c => (3 / 2) * S c) hCi (hSi.const_mul _) hInv]
  · exact integral_const_mul _ _
  · intro c e
    simp_rw [frameCurvatureField_turn]
    rw [normalCurvatureDeviation_mean_frobenius h g c e (hdec c e)
      (htr c e).1 (htr c e).2, hS]

/-- The same disintegration yields the exact derivative energy. The gradient
sum is a base scalar; its independence of orthonormal frame is explicit. -/
theorem frameCurvatureDerivative_mean_square
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)} (hμ : BrinKarcherAveraging g μ)
    (h : FollandMoments) (E : M → ℝ)
    (hHi : Integrable (fun e => ‖frameCurvatureDerivative g e‖ ^ 2) μ)
    (hEi : Integrable E (normalizedVolume g))
    (hInv : DirectionInvariant (fun e => ‖frameCurvatureDerivative g e‖ ^ 2))
    (hturn : ∀ c (e : OrthonormalFrame g c) q,
      frameCurvatureDerivative g (frameTurn e q) = normalCurvatureDerivative g c e q)
    (hsym : ∀ c (e : OrthonormalFrame g c) a,
      (plusWeylGradient g c e a)ᵀ = plusWeylGradient g c e a)
    (htr : ∀ c (e : OrthonormalFrame g c) a, (plusWeylGradient g c e a).trace = 0)
    (hE : ∀ c (e : OrthonormalFrame g c),
      gradientSquareNorm (plusWeylGradient g c e) +
        gradientSquareNorm (minusWeylGradient g c e) = E c) :
    (∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ) =
      (∫ c, E c ∂normalizedVolume g) / 16 := by
  rw [hμ.fiberFormula _ (fun c => E c / 16) hHi (hEi.div_const _) hInv]
  · exact integral_div _ _
  · intro c e
    simp_rw [hturn, ← squareNorm_eq_frobenius_norm_sq]
    rw [normalCurvatureDerivative_mean_square h g c e (hsym c e) (htr c e), hE]

end

end PositiveEinsteinFour.Geometry

end OAI
