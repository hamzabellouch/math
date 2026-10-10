import OAI.InformationTheory.Entanglement.PhysicalRawPrefix

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory ProbabilityTheory Filter
namespace SecretKey
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {ι κ υ S X : Type*} [MeasurableSpace S] [MeasurableSpace X]

theorem physical_right_raw_prefix (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (J : S→TraceInstrument b c X)
    (G : S→TraceInstrument (tensorHilbertBasis d b) (tensorHilbertBasis d c) X)
    (hG : ∀ h s, MeasurableSet s → IsRightTraceAction b c d ((J h).event s) ((G h).event s))
    (ρ : S→DensityOperator b) (σ : S→DensityOperator d)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (hm : ∀ V, MeasurableSet V → Measurable (fun h => (J h).outcome (ρ h) V))
    (U : ∀ h, (J h).ConditionalUpdate (ρ h))
    (hp : ∀ x y, Measurable (fun p : S×X => inner ℂ x
      ((densityTensor d c (σ p.1) ((U p.1).state p.2)).val.val y)))
    (W : PositiveHilbertMeasure (S×X) (HilbertTensor L K) (tensorHilbertBasis d c))
    [IsProbabilityMeasure W.traceMeasure]
    (hEvent : ∀ A B, MeasurableSet A → MeasurableSet B → ∀ x y,
      W.coeff x y (A ×ˢ B)=∫ h in A,
        inner ℂ x (((G h).event B (densityTensor d b (σ h) (ρ h)).val).val y) ∂μ) :
    W.traceMeasure=μ ⊗ₘ TraceInstrument.historyKernel J ρ hm ∧
    ∀ Z, MeasurableSet Z → ∀ x y, W.coeff x y Z=
      ∫ p in Z, inner ℂ x ((densityTensor d c (σ p.1) ((U p.1).state p.2)).val.val y)
        ∂(μ ⊗ₘ TraceInstrument.historyKernel J ρ hm) := by
  let ν := μ ⊗ₘ TraceInstrument.historyKernel J ρ hm
  let f := fun p : S×X => densityTensor d c (σ p.1) ((U p.1).state p.2)
  have hd (Z : Set (S×X)) (hZ : MeasurableSet Z) (x y : HilbertTensor L K) :
      W.coeff x y Z=∫ p in Z, inner ℂ x ((f p).val.val y) ∂ν := by
    have hi := density_coefficient_integrable (tensorHilbertBasis d c) ν f hp x y
    have he : W.coeff x y=ν.withDensityᵥ (fun p => inner ℂ x ((f p).val.val y)) := by
      apply complexMeasure_ext_rectangles
      intro A B hA hB
      rw [withDensityᵥ_apply hi (hA.prod hB)]
      change W.coeff x y (A ×ˢ B)=(∫ p in A ×ˢ B, inner ℂ x ((f p).val.val y)
        ∂(μ ⊗ₘ TraceInstrument.historyKernel J ρ hm))
      rw [Measure.setIntegral_compProd hA hB hi.integrableOn,hEvent A B hA hB x y]
      apply setIntegral_congr_fun hA
      intro h hh
      exact physical_right_disintegration_all b c d (J h) (ρ h) (σ h) (U h) hB
        ((G h).event B) (hG h B hB) x y
    rw [he,withDensityᵥ_apply hi hZ]
  exact ⟨weak_density_trace_eq (tensorHilbertBasis d c) W ν f hp hd,hd⟩

end SecretKey

end

end OAI
