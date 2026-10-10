import OAI.Combinatorics.Progressions.Linear.ProductOneSiteProjectionCap

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem oneSiteDensity_tested_error {X I K F : Type*} [Fintype X] [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η τ B C : ℝ} (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (prob : FiniteProbabilityWeights X) (b : X → Option K → I → ℝ) (w : X → ℂ)
    (hD : ∀ x, prob.weight x ≠ 0 → Integrable (fun z => D (coefficientFiberMap U t
      (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm (b x))) z)) μ)
    (hw : prob.mean (fun x => ‖w x‖) ≤ B) (hc : (∑ a, ‖c a‖) ≤ C)
    (hdiscard : ∀ a, ¬affineCubeModeFactors U t difference (frequency a) →
      ‖prob.complexMean (fun x => w x * layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d s => (frequency a j d s : ℝ)))) p (b x))‖ ≤ τ) :
    ‖prob.complexMean (fun x => w x * (D (affineSampleCoefficientTorus U p hm (b x)) : ℂ)) -
      prob.complexMean (fun x => w x * ((coefficientFiberAverage U μ t D
        (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm (b x))) : ℝ) : ℂ))‖ ≤
      2 * B * η + C * τ := by
  apply prob.weighted_projection_tested_error w _ _ c
    (fun a x => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d s => (frequency a j d s : ℝ)))) p (b x))
    (fun a => affineCubeModeFactors U t difference (frequency a)) hη hτ hw hc
  · intro x _hx
    rw [norm_sub_rev]
    simpa only [coefficientTorusFourierSum, coefficientTorusCharacter_sample U _ p hp hm] using
      happrox (affineSampleCoefficientTorus U p hm (b x))
  · intro x hx
    exact affineCubeFourierProjection_approx U t difference frequency c μ D happrox p hp hm (b x) (hD x hx)
  · exact hdiscard

end Erdos3.BooleanCubeKernel

end

end OAI
