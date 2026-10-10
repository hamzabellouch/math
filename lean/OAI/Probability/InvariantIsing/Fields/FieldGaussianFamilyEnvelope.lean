import OAI.Probability.InvariantIsing.Fields.FieldGaussianVarianceDerivative

namespace OAI

/-! A local exponential envelope for the two-parameter scalar Gaussian
recursion. This is used with parameter and spatial coordinate together. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology NNReal

namespace InvariantIsing

lemma field_average_hasFDerivAt_of_envelope
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U : (ℝ × ℝ) → ℝ → ℝ) (D : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    {p : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hS : S ∈ 𝓝 p)
    (hU : ∀ q, Measurable (U q)) (hD : AEStronglyMeasurable (D p) μ)
    (hi : Integrable (U p) μ) (ζ : ℝ)
    (hExp : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (B E : ℝ → ℝ) (hBi : Integrable B μ)
    (hEBi : Integrable (fun u => E u * B u) μ)
    (hB : ∀ q ∈ S, ∀ u, ‖D q u‖ ≤ B u)
    (hE : ∀ q ∈ S, ∀ u, Real.exp (ζ * U q u) ≤ E u)
    (hd : ∀ q ∈ S, ∀ u, HasFDerivAt (fun s => U s u) (D q u) q) :
    HasFDerivAt (fun q => if ζ = 0 then ∫ u, U q u ∂μ
        else Real.log (∫ u, Real.exp (ζ * U q u) ∂μ) / ζ)
      (∫ u, D p u ∂μ.tilted (fun u => ζ * U p u)) p := by
  by_cases hζ : ζ = 0
  · subst ζ
    simp only [ite_true, zero_mul, tilted_const]
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => (hU q).aestronglyMeasurable) hi hD
      (ae_of_all _ fun u q hq => hB q hq u) hBi
      (ae_of_all _ fun u q hq => hd q hq u)
  · have hexp := hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (F := fun q u => Real.exp (ζ * U q u))
      (F' := fun q u => Real.exp (ζ * U q u) • (ζ • D q u))
      (Eventually.of_forall fun q => ((hU q).const_mul ζ).exp.aestronglyMeasurable)
      hExp (((hU p).const_mul ζ).exp.aestronglyMeasurable.smul (hD.const_smul ζ))
      (bound := fun u => |ζ| * (E u * B u))
      (ae_of_all _ fun u q hq => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          norm_smul, Real.norm_eq_abs]
        calc
          _ = |ζ| * (Real.exp (ζ * U q u) * ‖D q u‖) := by ring
          _ ≤ |ζ| * (E u * B u) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (hE q hq u) (hB q hq u) (norm_nonneg _)
                ((Real.exp_pos _).le.trans (hE q hq u))) (abs_nonneg ζ))
      (hEBi.const_mul |ζ|)
      (ae_of_all _ fun u q hq => ((hd q hq u).const_mul ζ).exp)
    have hp := IsingPerceptron.integral_exp_pos μ (U p) hExp
    have hraw : (∫ u, D p u ∂μ.tilted (fun u => ζ * U p u)) =
        (∫ u, Real.exp (ζ * U p u) ∂μ)⁻¹ •
          (∫ u, Real.exp (ζ * U p u) • D p u ∂μ) := by
      rw [integral_tilted, ← integral_smul]
      congr 1
      funext u
      rw [smul_smul]
      congr 1
      ring
    have hfactor : (∫ u, Real.exp (ζ * U p u) • (ζ • D p u) ∂μ) =
        ζ • (∫ u, Real.exp (ζ * U p u) • D p u ∂μ) := by
      rw [← integral_smul]
      congr 1
      funext u
      rw [smul_smul, smul_smul]
      congr 1
      ring
    convert (hexp.log hp.ne').const_mul ζ⁻¹ using 1
    · funext q
      simp only [hζ, ite_false]
      ring
    · rw [hraw, hfactor]
      simp only [smul_smul]
      congr 1
      field_simp

end InvariantIsing

end

end OAI
