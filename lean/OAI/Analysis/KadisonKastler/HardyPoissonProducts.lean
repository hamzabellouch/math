import OAI.Analysis.KadisonKastler.PublishedHardyEvaluation
import OAI.Analysis.KadisonKastler.FourierConstant
import OAI.Analysis.KadisonKastler.PoissonProductEstimates

namespace OAI

/-! # Poisson products from the published Hardy evaluation

The boundary multiplication operators and their positive-frequency algebra
are concrete. Multiplicativity is obtained by applying the precisely cited
published evaluation homomorphism, including for constant middle factors.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem RepresentsOperatorField.mul
    {B S : ℝ → H →L[ℂ] H}
    {T V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hB : RepresentsOperatorField volume B T) (hS : RepresentsOperatorField volume S V) :
    RepresentsOperatorField volume (fun t => B t * S t) (T * V) := by
  intro f
  filter_upwards [hB (V f), hS f] with t h₁ h₂
  change (T (V f)) t = B t (S t (f t))
  rw [h₁, h₂]

theorem RepresentsOperatorField.mem_positiveFrequencyAlgebra
    {B : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hB : ∀ x, AEStronglyMeasurable (fun t => B t x) volume)
    {C : ℝ} (hC : ∀ᵐ t, ‖B t‖ ≤ C)
    (hBT : RepresentsOperatorField volume B T)
    (hT : PreservesProjectionNest regularFrequencyNest T) :
    T ∈ positiveFrequencyAlgebra (H := H) := by
  have he := RepresentsOperatorField.unique hBT (regularFieldOperator_represents volume B hB C hC)
  rw [he] at hT ⊢
  exact regularFieldOperator_mem_positiveFrequencyAlgebra B hB C hC hT

private theorem poisson_constant (x : H →L[ℂ] H) (t r : ℝ) (hr : 0 < r) :
    measurablePoissonAverage (fun _ => x) (fun _ => aestronglyMeasurable_const)
      ‖x‖ (Filter.Eventually.of_forall fun _ => le_rfl) t r hr = x := by
  apply ContinuousLinearMap.ext
  intro ξ
  change (∫ _, x ξ ∂ProbabilityTheory.cauchyMeasure t (NNReal.mk r hr.le)) = x ξ
  rw [integral_const, probReal_univ, one_smul]

variable [TopologicalSpace.SeparableSpace H]

/-- Exact multiplication of Poisson extensions of positive-frequency
preserving, bounded measurable multiplication operators. -/
theorem measurablePoissonAverage_mul_of_hardy
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (B S : ℝ → H →L[ℂ] H)
    (hB : ∀ x, AEStronglyMeasurable (fun t => B t x) volume)
    (hS : ∀ x, AEStronglyMeasurable (fun t => S t x) volume)
    (CB CS : ℝ) (hb : ∀ᵐ t, ‖B t‖ ≤ CB) (hs : ∀ᵐ t, ‖S t‖ ≤ CS)
    (hBS : ∀ᵐ t, ‖B t * S t‖ ≤ CB * CS)
    (T V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hBT : RepresentsOperatorField volume B T) (hSV : RepresentsOperatorField volume S V)
    (hT : PreservesProjectionNest regularFrequencyNest T)
    (hV : PreservesProjectionNest regularFrequencyNest V)
    (t r : ℝ) (hr : 0 < r) :
    measurablePoissonAverage B hB CB hb t r hr *
        measurablePoissonAverage S hS CS hs t r hr =
      measurablePoissonAverage (fun s => B s * S s)
        (operator_product_vector_measurable B S hB hS) (CB * CS) hBS t r hr := by
  let A : positiveFrequencyAlgebra (H := H) :=
    ⟨T, hBT.mem_positiveFrequencyAlgebra hB hb hT⟩
  let D : positiveFrequencyAlgebra (H := H) :=
    ⟨V, hSV.mem_positiveFrequencyAlgebra hS hs hV⟩
  obtain ⟨ev, he⟩ := hHardy H t r hr
  rw [← he B hB CB hb A hBT hr, ← he S hS CS hs D hSV hr,
    ← he _ (operator_product_vector_measurable B S hB hS) _ hBS (A * D) (hBT.mul hSV) hr]
  exact (ev.map_mul A D).symm

/-- The same identity with an arbitrary constant operator in the middle.
Only the two boundary multipliers need to preserve the frequency nest. -/
theorem measurablePoissonAverage_sandwich_of_hardy
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (B S : ℝ → H →L[ℂ] H)
    (hB : ∀ ξ, AEStronglyMeasurable (fun t => B t ξ) volume)
    (hS : ∀ ξ, AEStronglyMeasurable (fun t => S t ξ) volume)
    (CB CS : ℝ) (hb : ∀ᵐ t, ‖B t‖ ≤ CB) (hs : ∀ᵐ t, ‖S t‖ ≤ CS)
    (T V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hBT : RepresentsOperatorField volume B T) (hSV : RepresentsOperatorField volume S V)
    (hT : PreservesProjectionNest regularFrequencyNest T)
    (hV : PreservesProjectionNest regularFrequencyNest V)
    (x : H →L[ℂ] H)
    (hBxS : ∀ ξ, AEStronglyMeasurable (fun t => (B t * x * S t) ξ) volume)
    (C : ℝ) (hC : ∀ᵐ t, ‖B t * x * S t‖ ≤ C)
    (t r : ℝ) (hr : 0 < r) :
    measurablePoissonAverage B hB CB hb t r hr * x *
        measurablePoissonAverage S hS CS hs t r hr =
      measurablePoissonAverage (fun s => B s * x * S s) hBxS C hC t r hr := by
  let A : positiveFrequencyAlgebra (H := H) :=
    ⟨T, hBT.mem_positiveFrequencyAlgebra hB hb hT⟩
  let D : positiveFrequencyAlgebra (H := H) :=
    ⟨V, hSV.mem_positiveFrequencyAlgebra hS hs hV⟩
  let X : positiveFrequencyAlgebra (H := H) :=
    ⟨regularConstantOperator volume x, regularConstantOperator_mem_positiveFrequencyAlgebra x⟩
  have hX : RepresentsOperatorField volume (fun _ => x) X.val :=
    regularConstantOperator_apply_ae volume x
  obtain ⟨ev, he⟩ := hHardy H t r hr
  have hex : ev X = x := (he _ (fun _ => aestronglyMeasurable_const) ‖x‖
    (Filter.Eventually.of_forall fun _ => le_rfl) X hX hr).trans (poisson_constant x t r hr)
  rw [← he B hB CB hb A hBT hr, ← he S hS CS hs D hSV hr]
  conv_lhs => rw [← hex]
  rw [← he _ hBxS C hC (A * X * D) ((hBT.mul hX).mul hSV) hr]
  simp only [map_mul]

end

end KadisonKastler

end OAI
