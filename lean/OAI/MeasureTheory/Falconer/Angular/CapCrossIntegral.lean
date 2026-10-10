import OAI.MeasureTheory.Falconer.Angular.FourPointCaps
import OAI.MeasureTheory.Falconer.Estimates.EnergySplitting

namespace OAI

/-!
# The original cap cross term as one product-measure integral

This is the bridge between the radial/angular nonstationary estimates
and the finite graph expansion. Its integrability follows from bounded
endpoint symbols and the finite radial shell law.
-/

namespace Falconer
open Set MeasureTheory

theorem weighted_endpoint_cross_integrable {d : ℕ} (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (η θ : Sphere d → ℝ) (U U' V V' : ℝ × Sphere d → ℂ)
    (hη : Measurable η) (hθ : Measurable θ)
    (hU : Measurable U) (hU' : Measurable U') (hV : Measurable V) (hV' : Measurable V')
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B₁ B₂ B₃ B₄ : ℝ} (hB₁ : ∀ z, ‖U z‖ ≤ B₁) (hB₂ : ∀ z, ‖U' z‖ ≤ B₂)
    (hB₃ : ∀ z, ‖V z‖ ≤ B₃) (hB₄ : ∀ z, ‖V' z‖ ≤ B₄) :
    Integrable (fun z : ℝ × (Sphere d × Sphere d) =>
      ((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
        ((U (z.1,z.2.1)*V (z.1,z.2.2))*star (U' (z.1,z.2.1)*V' (z.1,z.2.2))))
      (angularProductMeasure d v Ψ) := by
  have hp₁ : Measurable (fun z : ℝ × (Sphere d × Sphere d) => (z.1,z.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hp₂ : Measurable (fun z : ℝ × (Sphere d × Sphere d) => (z.1,z.2.2)) :=
    measurable_fst.prodMk measurable_snd.snd
  have hUV := (hU.comp hp₁).mul (hV.comp hp₂)
  have hUV' := (hU'.comp hp₁).mul (hV'.comp hp₂)
  have hweight : Measurable (fun z : ℝ × (Sphere d × Sphere d) =>
      (η z.2.1 : ℂ)*(θ z.2.2 : ℂ)) :=
    (Complex.measurable_ofReal.comp (hη.comp measurable_snd.fst)).mul
      (Complex.measurable_ofReal.comp (hθ.comp measurable_snd.snd))
  apply Integrable.of_bound (hweight.mul
    (hUV.mul (Complex.continuous_conj.measurable.comp hUV'))).aestronglyMeasurable
    ((B₁*B₃)*(B₂*B₄))
  filter_upwards with z
  change ‖((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
    ((U (z.1,z.2.1)*V (z.1,z.2.2))*star (U' (z.1,z.2.1)*V' (z.1,z.2.2)))‖ ≤ _
  have hw : |η z.2.1| * |θ z.2.2| ≤ 1 :=
    (mul_le_mul (hηnorm _) (hθnorm _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hp : ‖U (z.1,z.2.1)‖*‖V (z.1,z.2.2)‖ ≤ B₁*B₃ :=
    mul_le_mul (hB₁ (z.1,z.2.1)) (hB₃ (z.1,z.2.2)) (norm_nonneg _)
      ((norm_nonneg (U (z.1,z.2.1))).trans (hB₁ (z.1,z.2.1)))
  have hp' : ‖U' (z.1,z.2.1)‖*‖V' (z.1,z.2.2)‖ ≤ B₂*B₄ :=
    mul_le_mul (hB₂ (z.1,z.2.1)) (hB₄ (z.1,z.2.2)) (norm_nonneg _)
      ((norm_nonneg (U' (z.1,z.2.1))).trans (hB₂ (z.1,z.2.1)))
  have hpp := mul_le_mul hp hp' (by positivity : 0 ≤ ‖U' (z.1,z.2.1)‖*‖V' (z.1,z.2.2)‖)
    ((by positivity : 0 ≤ ‖U (z.1,z.2.1)‖*‖V (z.1,z.2.2)‖).trans hp)
  simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul hw hpp (by positivity) zero_le_one).trans_eq (one_mul _)

theorem endpointCapCrossTerm_integrable {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM : 0 < M) (hM' : 0 < M') (hP : 0 < P) (hP' : 0 < P')
    (b b' c c' : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hb' : Measurable (Function.uncurry b'))
    (hc : Measurable (Function.uncurry c)) (hc' : Measurable (Function.uncurry c'))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (_hB : 0 ≤ B)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hb'B : ∀ x w, ‖b' x w‖ ≤ B)
    (hcB : ∀ x w, ‖c x w‖ ≤ B) (hc'B : ∀ x w, ‖c' x w‖ ≤ B) :
    Integrable (fun z : ℝ × (Sphere d × Sphere d) => ((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
        ((endpointTransform μ M b z.1 z.2.1*endpointTransform ν P c z.1 z.2.2)*
          star (endpointTransform μ' M' b' z.1 z.2.1*endpointTransform ν' P' c' z.1 z.2.2))
) (angularProductMeasure d v Ψ) := by
  exact weighted_endpoint_cross_integrable v Ψ η θ
    (fun z => endpointTransform μ M b z.1 z.2)
    (fun z => endpointTransform μ' M' b' z.1 z.2)
    (fun z => endpointTransform ν P c z.1 z.2)
    (fun z => endpointTransform ν' P' c' z.1 z.2)
    hη hθ (measurable_endpointTransform μ M b hb)
    (measurable_endpointTransform μ' M' b' hb')
    (measurable_endpointTransform ν P c hc)
    (measurable_endpointTransform ν' P' c' hc') hηnorm hθnorm
    (fun z => endpointTransform_norm_le μ hM b hbB z.1 z.2)
    (fun z => endpointTransform_norm_le μ' hM' b' hb'B z.1 z.2)
    (fun z => endpointTransform_norm_le ν hP c hcB z.1 z.2)
    (fun z => endpointTransform_norm_le ν' hP' c' hc'B z.1 z.2)

theorem endpointCapCrossTerm_product_integral {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM : 0 < M) (hM' : 0 < M') (hP : 0 < P) (hP' : 0 < P')
    (b b' c c' : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hb' : Measurable (Function.uncurry b'))
    (hc : Measurable (Function.uncurry c)) (hc' : Measurable (Function.uncurry c'))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hb'B : ∀ x w, ‖b' x w‖ ≤ B)
    (hcB : ∀ x w, ‖c x w‖ ≤ B) (hc'B : ∀ x w, ‖c' x w‖ ≤ B) :
    endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ =
      ∫ z, ((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
        ((endpointTransform μ M b z.1 z.2.1*endpointTransform ν P c z.1 z.2.2)*
          star (endpointTransform μ' M' b' z.1 z.2.1*endpointTransform ν' P' c' z.1 z.2.2))
        ∂angularProductMeasure d v Ψ := by
  exact (integral_prod _ (endpointCapCrossTerm_integrable μ μ' ν ν' M M' P P' v Ψ
    hM hM' hP hP' b b' c c' hb hb' hc hc' η θ hη hθ hηnorm hθnorm
    hB hbB hb'B hcB hc'B)).symm

end Falconer

end OAI
