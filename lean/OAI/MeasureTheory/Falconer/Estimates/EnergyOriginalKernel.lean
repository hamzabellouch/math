import OAI.MeasureTheory.Falconer.Angular.OriginalAngularKernel

namespace OAI

/-! # Angular energy as a kernel on the original four-point law -/

namespace Falconer
open Set MeasureTheory

theorem independentAngularEnergy_four_point {d : ℕ}
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M P a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C) :
    (independentAngularEnergy a v Ψ
      (fun z => endpointTransform μ M b z.1 z.2)
      (fun z => endpointTransform ν P c z.1 z.2) : ℂ) =
    ((2:ℝ)^((d:ℝ)*(v-a))*((M⁻¹*M⁻¹)*(P⁻¹*P⁻¹))) •
      ∫ z : (Space d × Space d) × (Space d × Space d), ∫ r,
        (∫ w, sphereOscillator r (z.1.1-z.1.2) w*(b z.1.1 w*star (b z.1.2 w))
          ∂sphereMeasure d)*
        (∫ w, sphereOscillator r (z.2.1-z.2.2) w*(c z.2.1 w*star (c z.2.2 w))
          ∂sphereMeasure d)
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ ∂(μ.prod μ).prod (ν.prod ν) := by
  let b₁ : ((Space d × Space d) × (Space d × Space d)) → Sphere d → ℂ :=
    fun z w => b z.1.1 w*star (b z.1.2 w)
  let b₂ : ((Space d × Space d) × (Space d × Space d)) → Sphere d → ℂ :=
    fun z w => c z.2.1 w*star (c z.2.2 w)
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
  have hbound₂ (z) (w) : ‖b₂ z w‖ ≤ C^2 := by
    simpa only [b₂,norm_mul,norm_star,pow_two] using
      mul_le_mul (hcC z.2.1 w) (hcC z.2.2 w) (norm_nonneg _) hC
  rw [independentAngularEnergy_eq_capCrossTerm,endpointCapCrossTerm_four_point]
  have he : (fun z w => capPairAmplitude (fun _ => 1) b b z.1 w) = b₁ := by
    funext z w
    simp only [capPairAmplitude,Complex.ofReal_one,one_mul,b₁]
  have hf : (fun z w => capPairAmplitude (fun _ => 1) c c z.2 w) = b₂ := by
    funext z w
    simp only [capPairAmplitude,Complex.ofReal_one,one_mul,b₂]
  rw [he,hf,expandedCapTerm_spatial_kernel _ v Ψ _ _ (by fun_prop) (by fun_prop)
    b₁ b₂ hb₁ hb₂ (sq_nonneg _) (sq_nonneg _) hbound₁ hbound₂,smul_smul]

end Falconer

end OAI
