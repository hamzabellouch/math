import OAI.InformationTheory.Entanglement.PhysicalPublicPrefix

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory ProbabilityTheory Filter
namespace SecretKey
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι κ S X : Type*} [MeasurableSpace S] [MeasurableSpace X]

def IsRawInstrumentTransition (b : HilbertBasis ι ℂ H)
    (W : PositiveHilbertMeasure S H b) (V : PositiveHilbertMeasure (S×X) H b)
    (G : S→TraceInstrument b b X) : Prop :=
  ∀ R : S→DensityOperator b,
    (∀ x y, Measurable (fun h => inner ℂ x ((R h).val.val y))) →
    IsWeakDensity b W W.traceMeasure R →
    ∀ A B, MeasurableSet A → MeasurableSet B → ∀ x y,
      V.coeff x y (A ×ˢ B)=∫ h in A, inner ℂ x (((G h).event B (R h).val).val y) ∂W.traceMeasure

def IsRawPublicTransition (b : HilbertBasis ι ℂ H)
    (W : PositiveHilbertMeasure S H b) (V : PositiveHilbertMeasure (S×X) H b)
    (P : Kernel S X) : Prop :=
  ∀ R : S→DensityOperator b,
    (∀ x y, Measurable (fun h => inner ℂ x ((R h).val.val y))) →
    IsWeakDensity b W W.traceMeasure R →
    ∀ A B, MeasurableSet A → MeasurableSet B → ∀ x y,
      V.coeff x y (A ×ˢ B)=∫ h in A, ((P h).real B : ℂ)*inner ℂ x ((R h).val.val y) ∂W.traceMeasure

inductive PhysicalExecutionStep (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)
    (W : PositiveHilbertMeasure S (HilbertTensor H K) (tensorHilbertBasis b d))
    (V : PositiveHilbertMeasure (S×X) (HilbertTensor H K) (tensorHilbertBasis b d))
    (ρ : S→DensityOperator b) (σ : S→DensityOperator d)
    (ρ' : S×X→DensityOperator b) (σ' : S×X→DensityOperator d) (P : Kernel S X) : Prop
  | left
      (J : S→TraceInstrument b b X)
      (G : S→TraceInstrument (tensorHilbertBasis b d) (tensorHilbertBasis b d) X)
      (hG : ∀ h s, MeasurableSet s → IsLeftTraceAction b b d ((J h).event s) ((G h).event s))
      (hm : ∀ s, MeasurableSet s → Measurable (fun h => (J h).outcome (ρ h) s))
      (U : ∀ h, (J h).ConditionalUpdate (ρ h))
      (hraw : IsRawInstrumentTransition (tensorHilbertBasis b d) W V G)
      (hstateA : ρ'=fun p => (U p.1).state p.2)
      (hstateB : σ'=σ ∘ Prod.fst)
      (hkernel : P=TraceInstrument.historyKernel J ρ hm) :
      PhysicalExecutionStep b d W V ρ σ ρ' σ' P
  | right
      (J : S→TraceInstrument d d X)
      (G : S→TraceInstrument (tensorHilbertBasis b d) (tensorHilbertBasis b d) X)
      (hG : ∀ h s, MeasurableSet s → IsRightTraceAction d d b ((J h).event s) ((G h).event s))
      (hm : ∀ s, MeasurableSet s → Measurable (fun h => (J h).outcome (σ h) s))
      (U : ∀ h, (J h).ConditionalUpdate (σ h))
      (hraw : IsRawInstrumentTransition (tensorHilbertBasis b d) W V G)
      (hstateA : ρ'=ρ ∘ Prod.fst)
      (hstateB : σ'=fun p => (U p.1).state p.2)
      (hkernel : P=TraceInstrument.historyKernel J σ hm) :
      PhysicalExecutionStep b d W V ρ σ ρ' σ' P
  | publicDraw
      (hraw : IsRawPublicTransition (tensorHilbertBasis b d) W V P)
      (hstateA : ρ'=ρ ∘ Prod.fst) (hstateB : σ'=σ ∘ Prod.fst) :
      PhysicalExecutionStep b d W V ρ σ ρ' σ' P
variable (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)

theorem physical_execution_step
    (W : PositiveHilbertMeasure S (HilbertTensor H K) (tensorHilbertBasis b d))
    (V : PositiveHilbertMeasure (S×X) (HilbertTensor H K) (tensorHilbertBasis b d))
    [IsProbabilityMeasure W.traceMeasure] [IsProbabilityMeasure V.traceMeasure]
    (ρ : S→DensityOperator b) (σ : S→DensityOperator d)
    (ρ' : S×X→DensityOperator b) (σ' : S×X→DensityOperator d) (P : Kernel S X) [IsMarkovKernel P]
    (hR : ∀ x y, Measurable (fun h => inner ℂ x ((densityTensor b d (ρ h) (σ h)).val.val y)))
    (hR' : ∀ x y, Measurable (fun p => inner ℂ x ((densityTensor b d (ρ' p) (σ' p)).val.val y)))
    (hd : IsWeakDensity (tensorHilbertBasis b d) W W.traceMeasure (fun h => densityTensor b d (ρ h) (σ h)))
    (hstep : PhysicalExecutionStep b d W V ρ σ ρ' σ' P) :
    V.traceMeasure=W.traceMeasure ⊗ₘ P ∧
    IsWeakDensity (tensorHilbertBasis b d) V (W.traceMeasure ⊗ₘ P)
      (fun p => densityTensor b d (ρ' p) (σ' p)) := by
  cases hstep with
  | left J G hG hm U hraw ha hb hk =>
    subst ρ'; subst σ'; subst P
    exact physical_raw_prefix b b d J G hG ρ σ W.traceMeasure hm U hR' V
      (hraw _ hR hd)
  | right J G hG hm U hraw ha hb hk =>
    subst ρ'; subst σ'; subst P
    exact physical_right_raw_prefix d d b J G hG σ ρ W.traceMeasure hm U hR' V
      (hraw _ hR hd)
  | publicDraw hraw ha hb =>
    subst ρ'; subst σ'
    exact physical_public_raw_prefix (tensorHilbertBasis b d) W.traceMeasure P
      (fun h => densityTensor b d (ρ h) (σ h)) hR V (hraw _ hR hd)

end SecretKey

end

end OAI
