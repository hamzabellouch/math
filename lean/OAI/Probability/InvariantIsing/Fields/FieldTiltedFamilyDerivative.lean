import OAI.Probability.InvariantIsing.Fields.FieldGaussianFamilyEnvelope
import OAI.Probability.InvariantIsing.Fields.FieldGaussianTiltMoments

namespace OAI

/-! Differentiating a normalized scalar Gaussian average with a varying
observable. The local envelopes allow the affine-noise quadratic terms
needed in the second derivative of the finite Ising recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

/-- Derivative of the unnormalized Gaussian weight. -/
def fieldWeightDifferential (U : (ℝ × ℝ) → ℝ → ℝ)
    (DU : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (ζ : ℝ)
    (p : ℝ × ℝ) (u : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  Real.exp (ζ * U p u) • (ζ • DU p u)

/-- Derivative of the weighted observable. -/
def fieldObservableDifferential (U A : (ℝ × ℝ) → ℝ → ℝ)
    (DU DA : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (ζ : ℝ)
    (p : ℝ × ℝ) (u : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  Real.exp (ζ * U p u) • (DA p u + (ζ * A p u) • DU p u)

lemma field_tiltedFamily_hasFDerivAt
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
    let Z := ∫ u, Real.exp (ζ * U p u) ∂μ
    let N := ∫ u, Real.exp (ζ * U p u) * A p u ∂μ
    HasFDerivAt (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u))
      (Z⁻¹ • (∫ u, fieldObservableDifferential U A DU DA ζ p u ∂μ) -
        (N * (Z ^ 2)⁻¹) • (∫ u, fieldWeightDifferential U DU ζ p u ∂μ)) p := by
  let Z := ∫ u, Real.exp (ζ * U p u) ∂μ
  let N := ∫ u, Real.exp (ζ * U p u) * A p u ∂μ
  let DZ := ∫ u, fieldWeightDifferential U DU ζ p u ∂μ
  let DN := ∫ u, fieldObservableDifferential U A DU DA ζ p u ∂μ
  have hZD : HasFDerivAt (fun q => ∫ u, Real.exp (ζ * U q u) ∂μ) DZ p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => ((hU q).const_mul ζ).exp.aestronglyMeasurable)
      hE (((hU p).const_mul ζ).exp.aestronglyMeasurable.smul (hDU.const_smul ζ))
      (ae_of_all _ fun u q hq => hDen q hq u) hMD
    exact ae_of_all _ fun u q hq => ((dU q hq u).const_mul ζ).exp
  have hND : HasFDerivAt (fun q => ∫ u, Real.exp (ζ * U q u) * A q u ∂μ) DN p := by
    have hDM : AEStronglyMeasurable (fieldObservableDifferential U A DU DA ζ p) μ :=
      ((hU p).const_mul ζ).exp.aestronglyMeasurable.smul
        (hDA.add (((hA p).const_mul ζ).aestronglyMeasurable.smul hDU))
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => (((hU q).const_mul ζ).exp.mul (hA q)).aestronglyMeasurable)
      hEA hDM (ae_of_all _ fun u q hq => hNum q hq u) hMN
    refine ae_of_all _ fun u q hq => ?_
    convert (((dU q hq u).const_mul ζ).exp).mul (dA q hq u) using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [fieldObservableDifferential, smul_apply,
      add_apply, smul_eq_mul]
    ring
  have hZ : Z ≠ 0 := (integral_exp_pos μ (U p) hE).ne'
  have hInv : HasFDerivAt (fun q => (∫ u, Real.exp (ζ * U q u) ∂μ)⁻¹)
      (-(Z ^ 2)⁻¹ • DZ) p := by
    convert (hasDerivAt_inv hZ).hasFDerivAt.comp p hZD using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        smul_eq_mul]
      change -(Z ^ 2)⁻¹ * DZ v = DZ v * -(Z ^ 2)⁻¹
      ring
  have hquot := hND.mul hInv
  have he : (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u)) =
      fun q => (∫ u, Real.exp (ζ * U q u) * A q u ∂μ) *
        (∫ u, Real.exp (ζ * U q u) ∂μ)⁻¹ := by
    funext q
    rw [integral_tilted_eq_div, div_eq_mul_inv]
  rw [he]
  convert hquot using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [sub_apply, smul_apply,
    add_apply, smul_eq_mul]
  change Z⁻¹ * DN v - N * (Z ^ 2)⁻¹ * DZ v =
    N * (-(Z ^ 2)⁻¹ * DZ v) + Z⁻¹ * DN v
  ring

end InvariantIsing

end

end OAI
