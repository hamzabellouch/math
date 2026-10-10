import OAI.InformationTheory.Entanglement.PhysicalVersion

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

theorem physical_history_kernel_eq (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (J : S→TraceInstrument b c X)
    (G : S→TraceInstrument (tensorHilbertBasis b d) (tensorHilbertBasis c d) X)
    (hG : ∀ h s, MeasurableSet s → IsLeftTraceAction b c d ((J h).event s) ((G h).event s))
    (ρ : S→DensityOperator b) (σ : S→DensityOperator d)
    (R : S→DensityOperator (tensorHilbertBasis b d))
    (μ : Measure S)
    (hR : R=ᵐ[μ](fun h => densityTensor b d (ρ h) (σ h)))
    (hm : ∀ V, MeasurableSet V → Measurable (fun h => (J h).outcome (ρ h) V))
    (hmg : ∀ V, MeasurableSet V → Measurable (fun h => (G h).outcome (R h) V)) :
    TraceInstrument.historyKernel G R hmg=ᵐ[μ]TraceInstrument.historyKernel J ρ hm := by
  filter_upwards [hR] with h hh
  change (G h).outcome (R h)=(J h).outcome (ρ h)
  rw [hh]
  exact physical_product_outcome b c d (J h) (G h) (hG h) (ρ h) (σ h)

theorem physical_adaptive_prefix (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (d : HilbertBasis υ ℂ L) (J : S→TraceInstrument b c X)
    (G : S→TraceInstrument (tensorHilbertBasis b d) (tensorHilbertBasis c d) X)
    (hG : ∀ h s, MeasurableSet s → IsLeftTraceAction b c d ((J h).event s) ((G h).event s))
    (ρ : S→DensityOperator b) (σ : S→DensityOperator d)
    (R : S→DensityOperator (tensorHilbertBasis b d))
    (μ : Measure S) [IsProbabilityMeasure μ]
    (hR : R=ᵐ[μ](fun h => densityTensor b d (ρ h) (σ h)))
    (hm : ∀ V, MeasurableSet V → Measurable (fun h => (J h).outcome (ρ h) V))
    (hmg : ∀ V, MeasurableSet V → Measurable (fun h => (G h).outcome (R h) V))
    (U : ∀ h, (G h).ConditionalUpdate (R h))
    (V : ∀ h, (J h).ConditionalUpdate (ρ h))
    (hf : ∀ x y, Measurable (fun p : S×X => inner ℂ x (((U p.1).state p.2).val.val y)))
    (hp : ∀ x y, Measurable (fun p : S×X => inner ℂ x
      ((densityTensor c d ((V p.1).state p.2) (σ p.1)).val.val y)))
    (T : DensityOperator (tensorHilbertBasis c d))
    (hmean : ∀ x y, inner ℂ x (T.val.val y)=∫ p, inner ℂ x (((U p.1).state p.2).val.val y)
      ∂(μ ⊗ₘ TraceInstrument.historyKernel G R hmg)) :
    (μ ⊗ₘ TraceInstrument.historyKernel G R hmg)=
        (μ ⊗ₘ TraceInstrument.historyKernel J ρ hm) ∧
    (fun p : S×X => (U p.1).state p.2)=ᵐ[μ ⊗ₘ TraceInstrument.historyKernel G R hmg]
       (fun p => densityTensor c d ((V p.1).state p.2) (σ p.1)) := by
  have hk := physical_history_kernel_eq b c d J G hG ρ σ R μ hR hm hmg
  have hμ := Measure.compProd_congr hk
  refine ⟨hμ,?_⟩
  rw [hμ] at hmean ⊢
  let ν := μ ⊗ₘ TraceInstrument.historyKernel J ρ hm
  let f := fun p : S×X => (U p.1).state p.2
  let q := fun p : S×X => densityTensor c d ((V p.1).state p.2) (σ p.1)
  apply weak_density_ae_unique (tensorHilbertBasis c d) ν f q T hf hp hmean
  intro Z hZ x y
  have hfi := density_coefficient_integrable (tensorHilbertBasis c d) ν f hf x y
  have hqi := density_coefficient_integrable (tensorHilbertBasis c d) ν q hp x y
  have he : ν.withDensityᵥ (fun p => inner ℂ x ((f p).val.val y))=
      ν.withDensityᵥ (fun p => inner ℂ x ((q p).val.val y)) := by
    apply complexMeasure_ext_rectangles
    intro A B hA hB
    rw [withDensityᵥ_apply hfi (hA.prod hB),withDensityᵥ_apply hqi (hA.prod hB)]
    change (∫ p in A ×ˢ B, inner ℂ x ((f p).val.val y) ∂(μ ⊗ₘ TraceInstrument.historyKernel J ρ hm))=_
    rw [Measure.setIntegral_compProd hA hB hfi.integrableOn,
      Measure.setIntegral_compProd hA hB hqi.integrableOn]
    apply setIntegral_congr_ae hA
    filter_upwards [hR] with h hh
    intro _
    change (∫ z in B, inner ℂ x (((U h).state z).val.val y) ∂(J h).outcome (ρ h))=_
    have hlaw : (G h).outcome (R h)=(J h).outcome (ρ h) := by
      rw [hh]
      exact physical_product_outcome b c d (J h) (G h) (hG h) (ρ h) (σ h)
    rw [← hlaw,← (U h).disintegration B hB x y,hh]
    exact physical_disintegration_all b c d (J h) (ρ h) (σ h) (V h) hB ((G h).event B) (hG h B hB) x y
  have hh := congrArg (fun M : ComplexMeasure (S×X) => M Z) he
  simpa only [withDensityᵥ_apply hfi hZ,withDensityᵥ_apply hqi hZ] using hh

end SecretKey

end

end OAI
