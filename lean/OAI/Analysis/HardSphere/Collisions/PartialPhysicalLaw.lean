import Mathlib
import OAI.Analysis.HardSphere.Geometry.AuxiliaryChecks
import OAI.Analysis.HardSphere.Conditioning.ConditionedCommon

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I E : Type*} [DecidableEq I] [Fintype E]
  {V : I → Type*} [∀i,MeasurableSpace (V i)]
  (checks : E → LocalCheck V)
  (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]

def insertionFiberEvent (s o : Finset I) : Set ((∀i,V i)×(∀i : s,V i)) :=
  {p | Function.updateFinset p.1 s p.2∈retainedEvent checks (s∪o)}

lemma insertionFiberEvent_measurable (s o : Finset I) :
    MeasurableSet (insertionFiberEvent checks s o) :=
  (measurableSet_retainedEvent checks (s∪o)).preimage measurable_updateFinset'

omit [∀i,IsProbabilityMeasure (μ i)] in
lemma insertionFiberEvent_mass (s o : Finset I) (x : ∀i,V i) :
    (Measure.pi (fun i : s ↦ μ i)) {y | (x,y)∈insertionFiberEvent checks s o}=
      partialNormalizer checks μ s o x := by
  change _=∫⁻y,checkWeight checks (s∪o) (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i)
  have he : (fun y : ∀i : s,V i ↦ checkWeight checks (s∪o) (Function.updateFinset x s y))=
      {y | (x,y)∈insertionFiberEvent checks s o}.indicator (fun _ ↦ (1:ℝ≥0∞)) := rfl
  have hs : MeasurableSet {y : ∀i : s,V i | (x,y)∈insertionFiberEvent checks s o} :=
    (insertionFiberEvent_measurable checks s o).preimage (measurable_const.prodMk measurable_id)
  rw [he,lintegral_indicator_const hs,one_mul]

def insertedLaw (s o : Finset I) (ξ : Measure (∀i,V i)) [SFinite ξ] :
    Measure ((∀i,V i)×(∀i : s,V i)) :=
  ξ.compProd (fiberNormalize (Kernel.const _ (Measure.pi (fun i : s ↦ μ i)))
    (insertionFiberEvent checks s o))

lemma insertedLaw_positive (s o : Finset I) (hso : Disjoint s o)
    {a : ℝ≥0∞} (ha : 0<a) (hcompat : UniformInsertionOn checks μ a s)
    (x : ∀i,V i) (hx : x∈retainedEvent checks o) :
    0<(Measure.pi (fun i : s ↦ μ i)) {y | (x,y)∈insertionFiberEvent checks s o} := by
  rw [insertionFiberEvent_mass]
  exact partialNormalizer_pos checks ha hcompat hso x hx

lemma insertedLaw_environment (s o : Finset I) (hso : Disjoint s o)
    {a : ℝ≥0∞} (ha : 0<a) (hcompat : UniformInsertionOn checks μ a s)
    (ξ : Measure (∀i,V i)) [SFinite ξ] (hξ : ∀ᵐx ∂ξ,x∈retainedEvent checks o) :
    (insertedLaw checks μ s o ξ).map Prod.fst=ξ := by
  apply fiberNormalize_fst ξ _ (insertionFiberEvent_measurable checks s o)
  exact hξ.mono (fun x hx ↦ insertedLaw_positive checks μ s o hso ha hcompat x hx)

lemma insertedLaw_probability (s o : Finset I) (hso : Disjoint s o)
    {a : ℝ≥0∞} (ha : 0<a) (hcompat : UniformInsertionOn checks μ a s)
    (ξ : Measure (∀i,V i)) [IsProbabilityMeasure ξ] (hξ : ∀ᵐx ∂ξ,x∈retainedEvent checks o) :
    IsProbabilityMeasure (insertedLaw checks μ s o ξ) := by
  constructor
  apply fiberNormalize_compProd_mass ξ _ (insertionFiberEvent_measurable checks s o)
  exact hξ.mono (fun x hx ↦ insertedLaw_positive checks μ s o hso ha hcompat x hx)

lemma insertedLaw_supported (s o : Finset I) (ξ : Measure (∀i,V i)) [SFinite ξ] :
    ∀ᵐp ∂insertedLaw checks μ s o ξ,Function.updateFinset p.1 s p.2∈retainedEvent checks (s∪o) := by
  change ∀ᵐp ∂ξ.compProd _,p∈insertionFiberEvent checks s o
  apply (Measure.ae_compProd_iff (insertionFiberEvent_measurable checks s o)).mpr
  exact ae_of_all _ (fiberNormalize_supported _ (insertionFiberEvent_measurable checks s o))

lemma insertedLaw_factorSupport (s o : Finset I) (ξ : Measure (∀i,V i)) [SFinite ξ]
    (A : ∀i : s,Set (V i)) (hA : ∀i,MeasurableSet (A i))
    (hμ : ∀i,∀ᵐv ∂μ i,v∈A i) :
    ∀ᵐp ∂insertedLaw checks μ s o ξ,∀i : s,p.2 i∈A i := by
  have hm : ∀ᵐy ∂Measure.pi (fun i : s ↦ μ i),∀i : s,y i∈A i := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun j : s ↦ μ j) i).quasiMeasurePreserving.ae (hμ i)
  change ∀ᵐp : (∀i,V i)×(∀i : s,V i) ∂ξ.compProd _,∀i : s,p.2 i∈A i
  have hs : MeasurableSet {p : (∀i,V i)×(∀i : s,V i) | ∀i : s,p.2 i∈A i} := by
    have hh := MeasurableSet.iInter (fun i ↦ (hA i).preimage ((measurable_pi_apply i).comp
      (measurable_snd : Measurable (Prod.snd : (∀i,V i)×(∀i : s,V i) → (∀i : s,V i)))))
    convert hh using 1
    ext p
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Set.mem_preimage,Function.comp_apply]
  apply (Measure.ae_compProd_iff hs).mpr
  exact ae_of_all _ (fun x ↦ (fiberNormalize_ac _ (insertionFiberEvent_measurable checks s o) x).ae_le hm)

end HardSphere.Comparison

end
end

end

end OAI
