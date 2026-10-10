import OAI.MeasureTheory.Falconer.Fourier.DyadicTransforms
import OAI.MeasureTheory.Falconer.Fourier.OscillatoryExpansion

namespace OAI

/-!
# Exact independent-energy expansion on the original dyadic cells

The two endpoint laws and their symbols are unchanged when passing to
occupied descendants. The identity keeps every complex cross term inside
the angular--radial integral, where nonstationary localization is applied.
-/

namespace Falconer
open MeasureTheory

noncomputable abbrev angularProductMeasure (d : ℕ) (v : ℝ) (Ψ : ℝ → ℝ) :=
  (PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
    ((sphereMeasure d).prod (sphereMeasure d))

theorem complex_sum_square {ι : Type*} (S : Finset ι) (F : ι → ℂ) :
    ((‖∑ i ∈ S, F i‖^2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, F i * star (F j) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem integral_cross_sum_norm {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (F : ι → X → ℂ) :
    ‖∫ x, ∑ i ∈ S, ∑ j ∈ S, F i x * star (F j x) ∂μ‖ =
      ∫ x, ‖∑ i ∈ S, F i x‖^2 ∂μ := by
  have he : (∫ x, ∑ i ∈ S, ∑ j ∈ S, F i x * star (F j x) ∂μ) =
      ((∫ x, ‖∑ i ∈ S, F i x‖^2 ∂μ : ℝ) : ℂ) := by
    simp_rw [← complex_sum_square]
    exact integral_ofReal
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]

noncomputable def dyadicPairTransform {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) (M₁ M₂ : ℝ)
    (b c : Space d → Sphere d → ℂ)
    (p : List (Fin d → Bool) × List (Fin d → Bool))
    (z : ℝ × (Sphere d × Sphere d)) : ℂ :=
  endpointTransform (μ.restrict (Q₁.descendant p.1).carrier) M₁ b z.1 z.2.1 *
    endpointTransform (ν.restrict (Q₂.descendant p.2).carrier) M₂ c z.1 z.2.2

theorem dyadicPairTransform_sum {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (n : ℕ) (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C)
    (z : ℝ × (Sphere d × Sphere d)) :
    endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2.1 *
      endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2.2 =
    ((Mp₁ / Ma₁) * (Mp₂ / Ma₂)) •
      ∑ p ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c p z := by
  rw [Q₁.endpointTransform_split μ n Ma₁ Mp₁ hMp₁ b hb hbB,
    Q₂.endpointTransform_split ν n Ma₂ Mp₂ hMp₂ c hc hcC,
    smul_mul_smul_comm, Finset.sum_product]
  congr 1
  simp only [dyadicPairTransform, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Exact expansion before any cross term is discarded or replaced by
its absolute value. The child masses are the chosen model masses. -/
theorem independentAngularEnergy_dyadic_expansion {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (n : ℕ) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2)
      (fun z => endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2) =
    (2 : ℝ)^((d : ℝ)*(v-a)) * ((Mp₁/Ma₁)*(Mp₂/Ma₂))^2 *
      ‖∫ z, ∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        ∑ col ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
          dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c row z *
            star (dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c col z)
        ∂angularProductMeasure d v Ψ‖ := by
  rw [independentAngularEnergy_product_integral a v Ψ _ _
    (measurable_endpointTransform _ _ b hb) (measurable_endpointTransform _ _ c hc)
    (show 0 ≤ B * (μ.restrict Q₁.carrier).real Set.univ / Ma₁ by positivity)
    (show 0 ≤ C * (ν.restrict Q₂.carrier).real Set.univ / Ma₂ by positivity)
    (fun z => endpointTransform_norm_le _ hMa₁ b hbB z.1 z.2)
    (fun z => endpointTransform_norm_le _ hMa₂ c hcC z.1 z.2)]
  simp_rw [dyadicPairTransform_sum Q₁ Q₂ μ ν n Ma₁ Ma₂ Mp₁ Mp₂ hMp₁ hMp₂ b c hb hc hbB hcC,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, integral_cross_sum_norm]
  ring

end Falconer

end OAI
