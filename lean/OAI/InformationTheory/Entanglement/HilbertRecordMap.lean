import OAI.InformationTheory.Entanglement.WeakLawTrace
import OAI.InformationTheory.Entanglement.SequentialSampling

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory ProbabilityTheory Filter
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
namespace PositiveHilbertMeasure
variable {b : HilbertBasis ι ℂ H} (W : PositiveHilbertMeasure X H b)

def mapRecord (f : X→Y) (hf : Measurable f) : PositiveHilbertMeasure Y H b where
  value s := W.value (f ⁻¹' s)
  coeff x y := (W.coeff x y).map f
  coeff_value x y s hs := by rw [VectorMeasure.map_apply _ hf hs,W.coeff_value _ _ _ (hf hs)]
  positive s hs := W.positive _ (hf hs)
  traceMeasure := W.traceMeasure.map f
  traceFinite := inferInstance
  trace_value s hs := by rw [Measure.real,Measure.map_apply hf hs]; exact W.trace_value _ (hf hs)
@[simp] lemma mapRecord_trace (f : X→Y) (hf : Measurable f) :
    (W.mapRecord f hf).traceMeasure=W.traceMeasure.map f := rfl
instance mapRecord_probability [IsProbabilityMeasure W.traceMeasure]
    (f : X→Y) (hf : Measurable f) : IsProbabilityMeasure (W.mapRecord f hf).traceMeasure := by
  change IsProbabilityMeasure (W.traceMeasure.map f)
  infer_instance
end PositiveHilbertMeasure

def IsWeakDensity (b : HilbertBasis ι ℂ H) (W : PositiveHilbertMeasure X H b)
    (μ : Measure X) (ρ : X→DensityOperator b) : Prop :=
  ∀ s, MeasurableSet s → ∀ x y, W.coeff x y s=∫ z in s, inner ℂ x ((ρ z).val.val y) ∂μ
lemma weakDensity_mapRecord (b : HilbertBasis ι ℂ H) (W : PositiveHilbertMeasure X H b)
    (μ : Measure X) (ρ : X→DensityOperator b)
    (hm : ∀ x y, Measurable (fun z => inner ℂ x ((ρ z).val.val y)))
    (hd : IsWeakDensity b W μ ρ) (e : X ≃ᵐ Y) :
    IsWeakDensity b (W.mapRecord e e.measurable) (μ.map e) (ρ ∘ e.symm) := by
  intro s hs x y
  change (W.coeff x y).map e s=_
  rw [VectorMeasure.map_apply _ e.measurable hs,hd _ (e.measurable hs)]
  erw [setIntegral_map hs ((hm x y).comp e.symm.measurable).aestronglyMeasurable e.measurable.aemeasurable]
  simp only [Function.comp_apply,e.symm_apply_apply]

def historyStepEquiv (X : Type*) [MeasurableSpace X] (k : ℕ) :
    (Fin (k+1)→X) ≃ᵐ ((Fin k→X)×X) where
  toFun x := (fun i => x i.castSucc,x (Fin.last k))
  invFun p := Fin.snoc p.1 p.2
  left_inv x := by funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by ext i <;> simp
  measurable_toFun := by
    change Measurable (fun x : Fin (k+1)→X => (fun i : Fin k => x i.castSucc,x (Fin.last k)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : (Fin k→X)×X => Fin.snoc (α := fun _ : Fin (k+1) => X) p.1 p.2)
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (fun p : (Fin k→X)×X => p.2))
    · simpa only [Fin.snoc_castSucc,Function.comp_def] using
        (measurable_pi_apply j).comp (measurable_fst : Measurable (fun p : (Fin k→X)×X => p.1))
lemma weakDensity_of_step {steps : ℕ} (b : HilbertBasis ι ℂ H)
    (W : PositiveHilbertMeasure (Fin (steps+1)→X) H b) (μ : Measure (Fin (steps+1)→X))
    (ρ : (Fin (steps+1)→X)→DensityOperator b)
    (hm : ∀ x y, Measurable (fun z => inner ℂ x ((ρ z).val.val y)))
    (hd : IsWeakDensity b (W.mapRecord (historyStepEquiv X steps) (historyStepEquiv X steps).measurable)
      (μ.map (historyStepEquiv X steps)) (ρ ∘ (historyStepEquiv X steps).symm)) :
    IsWeakDensity b W μ ρ := by
  intro s hs x y
  let e := historyStepEquiv X steps
  have he := hd (e.symm ⁻¹' s) (e.symm.measurable hs) x y
  change (W.coeff x y).map e (e.symm ⁻¹' s)=_ at he
  rw [VectorMeasure.map_apply _ e.measurable (e.symm.measurable hs)] at he
  erw [setIntegral_map (e.symm.measurable hs)
    ((hm x y).comp e.symm.measurable).aestronglyMeasurable e.measurable.aemeasurable] at he
  simpa only [Function.comp_apply,e.symm_apply_apply,Set.preimage_preimage,
    e.symm_comp_self,Set.preimage_id'] using he

end SecretKey

end

end OAI
