import OAI.Probability.InvariantIsing.Fields.FieldTiltedFamilyDerivative

namespace OAI

/-! Covariance form of the derivative of an actual normalized average.
This is the two-coordinate formula used by the finite scalar recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_tilted_integral_normalize {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure ℝ) (U : ℝ → ℝ)
    (B : ℝ → E) (ζ : ℝ) :
    (∫ u, B u ∂μ.tilted (fun u => ζ * U u)) =
      (∫ u, Real.exp (ζ * U u) ∂μ)⁻¹ •
        (∫ u, Real.exp (ζ * U u) • B u ∂μ) := by
  rw [integral_tilted, ← integral_smul]
  congr 1
  funext u
  rw [smul_smul]
  congr 1
  ring

lemma field_tiltedFamily_covariance_hasFDerivAt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U A : (ℝ × ℝ) → ℝ → ℝ)
    (DU DA : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    {p : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hS : S ∈ 𝓝 p) (ζ : ℝ)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) μ) (hDA : AEStronglyMeasurable (DA p) μ)
    (hE : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u) μ)
    (MD MN : ℝ → ℝ) (hMD : Integrable MD μ) (hMN : Integrable MN μ)
    (hDen : ∀ q ∈ S, ∀ u, ‖fieldWeightDifferential U DU ζ q u‖ ≤ MD u)
    (hNum : ∀ q ∈ S, ∀ u, ‖fieldObservableDifferential U A DU DA ζ q u‖ ≤ MN u)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    HasFDerivAt (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u))
      ((∫ u, DA p u + (ζ * A p u) • DU p u
          ∂μ.tilted (fun u => ζ * U p u)) -
        (∫ u, A p u ∂μ.tilted (fun u => ζ * U p u)) •
          (∫ u, ζ • DU p u ∂μ.tilted (fun u => ζ * U p u))) p := by
  have h := field_tiltedFamily_hasFDerivAt μ U A DU DA hS ζ hU hA hDU hDA
    hE hEA MD MN hMD hMN hDen hNum dU dA
  convert h using 1
  rw [field_tilted_integral_normalize, field_tilted_integral_normalize,
    field_tilted_integral_normalize]
  simp only [smul_eq_mul, fieldObservableDifferential, fieldWeightDifferential,
    pow_two, smul_smul]
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply, smul_eq_mul]
  ring

end InvariantIsing

end

end OAI
