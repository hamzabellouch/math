import Mathlib
import OAI.Geometry.SmoothYau.Estimates.CutoffPullbackSobolevBound

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cutoffPullbackLinear (η : E → ℂ) (hηc : HasCompactSupport η) (hη : ContDiff ℝ ∞ η)
    (φ : E → E) (hφ : ContDiff ℝ ∞ φ) : 𝓢(E, ℂ) →ₗ[ℂ] 𝓢(E, ℂ) where
  toFun := cutoffPullback η hηc hη φ hφ
  map_add' f g := by ext x; simp [cutoffPullback, mul_add]
  map_smul' c f := by ext x; simp [cutoffPullback, mul_left_comm]

def sobolevCutoffPullback (η : E → ℂ) (hηc : HasCompactSupport η) (hη : ContDiff ℝ ∞ η)
    (φ : E → E) (hφ : ContDiff ℝ ∞ φ) (k : ℕ) :
    FourierSobolevSpace E ℂ (2 * (k : ℝ)) →L[ℂ] FourierSobolevSpace E ℂ (2 * (k : ℝ)) :=
  ((schwartzToSobolev (2 * (k : ℝ))).toLinearMap.comp
    (cutoffPullbackLinear η hηc hη φ hφ)).extendOfNorm
    (schwartzToSobolev (2 * (k : ℝ))).toLinearMap

lemma sobolevCutoffPullback_schwartz (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (φ : E → E) (hφ : ContDiff ℝ ∞ φ)
    (hinj : Set.InjOn φ (tsupport η)) (J : ℝ≥0)
    (hJ : ∀ x ∈ tsupport η, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det|)
    (k : ℕ) (f : 𝓢(E, ℂ)) :
    sobolevCutoffPullback η hηc hη φ hφ k (schwartzToSobolev (2 * (k : ℝ)) f) =
      schwartzToSobolev (2 * (k : ℝ)) (cutoffPullback η hηc hη φ hφ f) := by
  obtain ⟨C, _, hC⟩ := cutoffPullback_sobolev_bound η hηc hη φ hφ hinj J hJ k
  exact LinearMap.extendOfNorm_eq (denseRange_schwartzToSobolev _)
    ⟨C, hC⟩ f

theorem sobolevRepresentative_cutoffPullback (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (φ : E → E) (hφ : ContDiff ℝ ∞ φ)
    (hinj : Set.InjOn φ (tsupport η)) (J : ℝ≥0)
    (hJ : ∀ x ∈ tsupport η, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det|)
    (k : ℕ) (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (u : FourierSobolevSpace E ℂ (2 * (k : ℝ))) (x : E) :
    sobolevRepresentative hs (sobolevCutoffPullback η hηc hη φ hφ k u) x =
      η x * sobolevRepresentative hs u (φ x) := by
  refine (denseRange_schwartzToSobolev (E := E) (2 * (k : ℝ))).induction_on u ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro f
    rw [sobolevCutoffPullback_schwartz η hηc hη φ hφ hinj J hJ,
      sobolevRepresentative_schwartz, sobolevRepresentative_schwartz]
    rfl

end YauCounterexamples

open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap

end

end OAI
