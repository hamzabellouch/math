import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.LpNormTwoBounds

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
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem cutoffPullback_sobolev_bound (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (φ : E → E) (hφ : ContDiff ℝ ∞ φ)
    (hinj : Set.InjOn φ (tsupport η)) (J : ℝ≥0)
    (hJ : ∀ x ∈ tsupport η, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det|)
    (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(E, ℂ),
      ‖schwartzToSobolev (2 * (k : ℝ)) (cutoffPullback η hηc hη φ hφ f)‖ ≤
        C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖ := by
  obtain ⟨C, hC, hc⟩ := cutoffPullback_derivative_L2 η hηc hη φ hφ hinj J hJ (2 * k)
  let A : ℝ := (1 + ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * Module.finrank ℝ E) ^ k
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A * C, mul_pos hA hC, fun f => ?_⟩
  have hb : SchwartzWordBound (2 * k) (cutoffPullback η hηc hη φ hφ f)
      (C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖) := by
    intro j hj w
    let g := cutoffPullback η hηc hη φ hφ f
    have hh : eLpNorm ((∂^{fun a => stdOrthonormalBasis ℝ E (w a)} g : 𝓢(E, ℂ)) : E → ℂ)
        2 volume ≤ ENNReal.ofReal (C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖) := by
      refine (eLpNorm_mono_real (g := fun x => ‖iteratedFDeriv ℝ j g x‖)
        ((∂^{fun a => stdOrthonormalBasis ℝ E (w a)} g : 𝓢(E, ℂ)).continuous.aestronglyMeasurable)
        ?_).trans ?_
      · intro x
        rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
        simpa only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one] using
          (iteratedFDeriv ℝ j g x).le_opNorm (fun a => stdOrthonormalBasis ℝ E (w a))
      · rw [eLpNorm_norm (iteratedFDeriv ℝ j g) ((g.smooth ⊤).continuous_iteratedFDeriv
          (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).aestronglyMeasurable]
        exact hc (2 * (k : ℝ)) (by norm_num) f j hj
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    simpa only [g, SchwartzMap.norm_toLp, ENNReal.toReal_ofReal (mul_nonneg hC.le (norm_nonneg _))] using h
  simpa only [A, mul_assoc] using sobolev_even_le_word_bound k
    (cutoffPullback η hηc hη φ hφ f) (C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖) hb

end YauCounterexamples

end

end OAI
