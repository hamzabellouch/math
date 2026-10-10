import OAI.MeasureTheory.Falconer.Estimates.EnergyOriginalKernel
import OAI.MeasureTheory.Falconer.Angular.CapCrossIntegral

namespace OAI

/-! # The original four-point kernel for a mixed endpoint cross term -/

namespace Falconer
open Set MeasureTheory

theorem endpoint_cross_original_kernel {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B) :
    (∫ z, (endpointTransform μ M b z.1 z.2.1 * endpointTransform ν P c z.1 z.2.2) *
      star (endpointTransform μ' M b z.1 z.2.1 * endpointTransform ν' P c z.1 z.2.2)
      ∂angularProductMeasure d v Ψ) =
    ((M⁻¹*M⁻¹)*(P⁻¹*P⁻¹)) •
      ∫ z : (Space d × Space d) × (Space d × Space d), ∫ r,
        (∫ w, sphereOscillator r (z.1.1-z.1.2) w*(b z.1.1 w*star (b z.1.2 w))
          ∂sphereMeasure d)*
        (∫ w, sphereOscillator r (z.2.1-z.2.2) w*(c z.2.1 w*star (c z.2.2 w))
          ∂sphereMeasure d)
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ ∂(μ.prod μ').prod (ν.prod ν') := by
  have he := endpointCapCrossTerm_product_integral μ μ' ν ν' M M P P v Ψ
    hM hM hP hP b b c c hb hb hc hc (fun _ => 1) (fun _ => 1)
    measurable_const measurable_const (by intro; norm_num) (by intro; norm_num)
    hB hbB hbB hcB hcB
  simp only [Complex.ofReal_one,one_mul] at he
  rw [← he,endpointCapCrossTerm_four_point]
  let b₁ : ((Space d × Space d) × (Space d × Space d)) →
      Sphere d → ℂ := fun z w => b z.1.1 w*star (b z.1.2 w)
  let b₂ : ((Space d × Space d) × (Space d × Space d)) →
      Sphere d → ℂ := fun z w => c z.2.1 w*star (c z.2.2 w)
  have hb₁ : Measurable (Function.uncurry b₁) :=
    (hb.comp (measurable_fst.fst.fst.prodMk measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp
        (hb.comp (measurable_fst.fst.snd.prodMk measurable_snd)))
  have hb₂ : Measurable (Function.uncurry b₂) :=
    (hc.comp (measurable_fst.snd.fst.prodMk measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp
        (hc.comp (measurable_fst.snd.snd.prodMk measurable_snd)))
  have hbound₁ (z) (w) : ‖b₁ z w‖ ≤ B^2 := by
    simpa only [b₁,norm_mul,norm_star,pow_two] using
      mul_le_mul (hbB z.1.1 w) (hbB z.1.2 w) (norm_nonneg _) hB
  have hbound₂ (z) (w) : ‖b₂ z w‖ ≤ B^2 := by
    simpa only [b₂,norm_mul,norm_star,pow_two] using
      mul_le_mul (hcB z.2.1 w) (hcB z.2.2 w) (norm_nonneg _) hB
  have h₁ : (fun z w => capPairAmplitude (fun _ => 1) b b z.1 w) = b₁ := by
    funext z w; simp only [capPairAmplitude,Complex.ofReal_one,one_mul,b₁]
  have h₂ : (fun z w => capPairAmplitude (fun _ => 1) c c z.2 w) = b₂ := by
    funext z w; simp only [capPairAmplitude,Complex.ofReal_one,one_mul,b₂]
  rw [h₁,h₂,expandedCapTerm_spatial_kernel _ v Ψ _ _ (by fun_prop) (by fun_prop)
    b₁ b₂ hb₁ hb₂ (sq_nonneg _) (sq_nonneg _) hbound₁ hbound₂]


end Falconer

end OAI
