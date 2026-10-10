import OAI.MeasureTheory.Falconer.Fourier.SpatialSymbols
import OAI.MeasureTheory.Falconer.Fourier.OscillatoryExpansion

namespace OAI

/-! # Endpoint factorization of the integer spatial inverse powers -/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate
variable {d : ℕ}

theorem spatial_endpoint_pair (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (M P s : ℝ) (ξ : Space d)
    (b c : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform μ M (fun x w => spatialFourierPhase s ξ x*b x w) r w *
      star (endpointTransform ν P (fun x w => spatialFourierPhase s ξ x*c x w) r w) =
    (M⁻¹*P⁻¹) • ∫ z : Space d × Space d,
      spatialPairPhase s ξ z *
        (Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
          (b z.1 w*star (c z.2 w))) ∂μ.prod ν := by
  rw [endpointTransform_mul_star]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  simp only [star_mul,spatialPairPhase,starRingEnd_apply]
  ring

theorem spatial_inverse_endpoint_separation
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ L)
    (M P : ℝ) (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (hcC : ∀ x w, ‖c x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    (M⁻¹*P⁻¹) • ∫ z : Space d × Space d,
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        (Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
          (b z.1 w*star (c z.2 w))) ∂μ.prod ν =
    ∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
      (endpointTransform μ M (fun x w => spatialFourierPhase s ξ x*b x w) r w *
        star (endpointTransform ν P (fun x w => spatialFourierPhase s ξ x*c x w) r w)) := by
  let A : Space d × Space d → ℂ := fun z =>
    Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
      (b z.1 w*star (c z.2 w))
  have hA : Measurable A := by
    apply Measurable.mul
    · fun_prop
    · exact (hb.comp (measurable_fst.prodMk measurable_const)).mul
        (Complex.continuous_conj.measurable.comp (hc.comp (measurable_snd.prodMk measurable_const)))
  have hbound : ∀ z, ‖A z‖ ≤ B*C := by
    intro z
    have hphase : ‖Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))‖ = 1 := by
      simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
    simp only [A,norm_mul,norm_star,hphase,one_mul]
    exact mul_le_mul (hbB _ _) (hcC _ _) (norm_nonneg _) hB
  change (M⁻¹*P⁻¹) • (∫ z, (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ)*A z ∂μ.prod ν) = _
  rw [spatialInverseDistance_integral_separation δ L hδ hL j hs (μ.prod ν) hsep A hA hbound,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [spatial_endpoint_pair]
  simp only [Complex.real_smul]
  ring

end Falconer

end OAI
