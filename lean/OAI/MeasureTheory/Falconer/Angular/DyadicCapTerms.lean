import OAI.MeasureTheory.Falconer.Angular.CapCrossIntegral

namespace OAI

/-!
# Cap terms on the original dyadic descendants

The finite graph expansion and the analytic endpoint cross terms use the
same restricted laws and model masses. These identities connect them
without changing the spatial labels or taking an absolute value early.
-/

namespace Falconer
open Set MeasureTheory

noncomputable def dyadicCapIntegrand {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) (M₁ M₂ : ℝ)
    (b c : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (z : ℝ × (Sphere d × Sphere d)) : ℂ :=
  (η z.2.1*θ z.2.2) • (dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c row z *
    star (dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c col z))

theorem dyadicCapIntegrand_integrable {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    Integrable (dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col)
      (angularProductMeasure d v Ψ) := by
  unfold dyadicCapIntegrand
  simpa only [dyadicCapIntegrand,dyadicPairTransform,Complex.real_smul,Complex.ofReal_mul] using
    endpointCapCrossTerm_integrable (μ.restrict (Q₁.descendant row.1).carrier)
      (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
      (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ
      hM₁ hM₁ hM₂ hM₂ b b c c hb hb hc hc η θ hη hθ hηnorm hθnorm hB hbB hbB hcB hcB

theorem integral_dyadicCapIntegrand {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    (∫ z, dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col z
      ∂angularProductMeasure d v Ψ) =
    endpointCapCrossTerm (μ.restrict (Q₁.descendant row.1).carrier)
      (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
      (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ b b c c η θ := by
  simpa only [dyadicCapIntegrand,dyadicPairTransform,Complex.real_smul,Complex.ofReal_mul] using
    (endpointCapCrossTerm_product_integral (μ.restrict (Q₁.descendant row.1).carrier)
      (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
      (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ
      hM₁ hM₁ hM₂ hM₂ b b c c hb hb hc hc η θ hη hθ hηnorm hθnorm hB hbB hbB hcB hcB).symm

end Falconer

end OAI
