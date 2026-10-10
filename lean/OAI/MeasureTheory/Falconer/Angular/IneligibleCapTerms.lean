import OAI.MeasureTheory.Falconer.Angular.DyadicCapTerms
import OAI.MeasureTheory.Falconer.Estimates.EligibilityExcision

namespace OAI

/-!
# Vanishing of individual ineligible original cap terms

One null set is chosen before frequency. This permits arbitrary whole-cell
edge decisions in the finite graph without introducing angular cutoffs.
-/

namespace Falconer
open Set MeasureTheory MeasureTheory.Measure

theorem DyadicCube.ineligible_transform_ae_zero {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (j : ℕ) (M : ℝ)
    (η : Sphere d → ℝ) (hηm : Measurable η) (hη : ∀ w, 0 ≤ η w)
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {B : ℝ} (hB : 0 ≤ B) (hηB : ∀ w, η w ≤ 1) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (p : List (Fin d → Bool)) (hp : p ∈ Q.occupiedPaths μ j)
    (he : p ∉ Q.eligiblePaths μ j η b) :
    ∀ᵐ w ∂sphereMeasure d, ∀ r, η w ≠ 0 →
      endpointTransform (μ.restrict (Q.descendant p).carrier) M b r w = 0 := by
  have hz : capIncidence (μ.restrict (Q.descendant p).carrier) η b = 0 := by
    apply le_antisymm _ (capIncidence_nonneg _ η b hη)
    apply le_of_not_gt
    intro hpos
    exact he (Finset.mem_filter.mpr ⟨hp,hpos⟩)
  have hzero := capIncidence_zero_transform (μ.restrict (Q.descendant p).carrier)
    η hηm hη b hb zero_le_one hB hηB hbB hz M
  filter_upwards [hzero] with w hw
  intro r hne
  exact hw (lt_of_le_of_ne (hη w) (Ne.symm hne)) r

theorem angularProduct_ae_first {d : ℕ} {v : ℝ} {Ψ : ℝ → ℝ}
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    {p : Sphere d → Prop} (hp : ∀ᵐ w ∂sphereMeasure d, p w) :
    ∀ᵐ z ∂angularProductMeasure d v Ψ, p z.2.1 :=
  quasiMeasurePreserving_snd.ae (quasiMeasurePreserving_fst.ae hp)

theorem angularProduct_ae_second {d : ℕ} {v : ℝ} {Ψ : ℝ → ℝ}
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    {p : Sphere d → Prop} (hp : ∀ᵐ w ∂sphereMeasure d, p w) :
    ∀ᵐ z ∂angularProductMeasure d v Ψ, p z.2.2 :=
  quasiMeasurePreserving_snd.ae (quasiMeasurePreserving_snd.ae hp)

theorem dyadicCapIntegrand_star {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) (M₁ M₂ : ℝ) (b c : Space d → Sphere d → ℂ)
    (η θ : Sphere d → ℝ) (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (z : ℝ × (Sphere d × Sphere d)) :
    star (dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col z) =
      dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ col row z := by
  simp only [dyadicCapIntegrand,star_smul,star_mul,star_star]
  congr 1
  exact mul_comm _ _

theorem dyadicCapIntegrand_row_ineligible {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (j : ℕ) (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η θ : Sphere d → ℝ) (hηm : Measurable η) (hθm : Measurable θ)
    (hη : ∀ w, 0 ≤ η w) (hθ : ∀ w, 0 ≤ θ w)
    (hηB : ∀ w, η w ≤ 1) (hθB : ∀ w, θ w ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (hrow : row ∈ Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j)
    (he : row ∉ Q₁.eligiblePaths μ j η b ×ˢ Q₂.eligiblePaths ν j θ c) :
    dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col =ᵐ[angularProductMeasure d v Ψ] 0 := by
  classical
  rw [Finset.mem_product,not_and_or] at he
  rcases he with hfirst | hsecond
  · have hz := angularProduct_ae_first (v := v) (Ψ := Ψ)
      (Q₁.ineligible_transform_ae_zero μ j M₁ η hηm hη b hb hB hηB hbB row.1
        (Finset.mem_product.mp hrow).1 hfirst)
    filter_upwards [hz] with z hz
    by_cases hzero : η z.2.1 = 0
    · simp [dyadicCapIntegrand,hzero]
    · simp [dyadicCapIntegrand,dyadicPairTransform,hz z.1 hzero]
  · have hz := angularProduct_ae_second (v := v) (Ψ := Ψ)
      (Q₂.ineligible_transform_ae_zero ν j M₂ θ hθm hθ c hc hB hθB hcB row.2
        (Finset.mem_product.mp hrow).2 hsecond)
    filter_upwards [hz] with z hz
    by_cases hzero : θ z.2.2 = 0
    · simp [dyadicCapIntegrand,hzero]
    · simp [dyadicCapIntegrand,dyadicPairTransform,hz z.1 hzero]

theorem dyadicCapIntegrand_col_ineligible {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (j : ℕ) (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η θ : Sphere d → ℝ) (hηm : Measurable η) (hθm : Measurable θ)
    (hη : ∀ w, 0 ≤ η w) (hθ : ∀ w, 0 ≤ θ w)
    (hηB : ∀ w, η w ≤ 1) (hθB : ∀ w, θ w ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (hcol : col ∈ Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j)
    (he : col ∉ Q₁.eligiblePaths μ j η b ×ˢ Q₂.eligiblePaths ν j θ c) :
    dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col =ᵐ[angularProductMeasure d v Ψ] 0 := by
  have hz := dyadicCapIntegrand_row_ineligible Q₁ Q₂ μ ν j M₁ M₂ v Ψ b c hb hc
    η θ hηm hθm hη hθ hηB hθB hB hbB hcB col row hcol he
  filter_upwards [hz] with z hz
  rw [← dyadicCapIntegrand_star,hz]
  exact star_zero _

end Falconer

end OAI
