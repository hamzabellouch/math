import OAI.NumberTheory.Jacobsthal.Probability.RawMarkedWords
import OAI.NumberTheory.Jacobsthal.Probability.SourceMarkedWords

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.RegenerationTails

lemma rawReturnInputCost_ae (a : ℕ) (h : RawHistory a) :
    ∀ᵐ r ∂rawReturnTraceKernel a h, rawReturnInputCost a r=(rawLast a h).2 := by
  have hm : MeasurableSet {r : RawReturnTrace a | rawReturnInputCost a r=(rawLast a h).2} :=
    measurableSet_eq_fun (rawReturnInputCost_measurable a) measurable_const
  rw [rawReturnTraceKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.map_apply _ (rawReturnTrace_mk_measurable a n)]
  apply (ae_map_iff (rawReturnTrace_mk_measurable a n).aemeasurable hm).mpr
  filter_upwards [firstReturnHistory_retains_past a n h] with y hy
  have he := congrFun hy (⟨a,by simp⟩ : Finset.Iic a)
  exact congrArg (fun s : CostState => s.2) he

lemma rawBranchReturnInputCost_ae (a : ℕ) (b : Bool) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) : ∀ᵐ r ∂rawBranchReturnKernel a b h, rawReturnInputCost a r=z.2 := by
  rw [rawBranchReturnKernel,Kernel.restrict_apply]
  filter_upwards [ae_restrict_of_ae (rawReturnInputCost_ae a h)] with r hr
  simpa only [hz,embedOdd] using hr

theorem rawBranchReturn_input_signature (a : ℕ) (b : Bool) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    (rawBranchReturnKernel a b h).map (rawReturnInputSignature a) =
      (sourceBranchWitnessKernel b z).map (sourceCycleInputSignature z) := by
  have he : rawReturnInputSignature a =ᵐ[rawBranchReturnKernel a b h]
      fun r => (z.2,rawReturnSignature a r) := by
    filter_upwards [rawBranchReturnInputCost_ae a b h z hz] with r hr
    exact Prod.ext hr rfl
  calc
    _ = (rawBranchReturnKernel a b h).map (fun r => (z.2,rawReturnSignature a r)) := Measure.map_congr he
    _ = ((rawBranchReturnKernel a b h).map (rawReturnSignature a)).map (fun s => (z.2,s)) := by
      rw [Measure.map_map (g := fun s : ReturnSignature => (z.2,s))
        (measurable_const.prodMk measurable_id) (rawReturnSignature_measurable a)]
      rfl
    _ = ((sourceBranchWitnessKernel b z).map (sourceReturnSignature z)).map (fun s => (z.2,s)) := by
      rw [rawBranchReturn_signature a b h z hz]
    _ = _ := by
      rw [Measure.map_map (g := fun s : ReturnSignature => (z.2,s))
        (measurable_const.prodMk measurable_id) (sourceReturnSignature_measurable z)]
      rfl

def decodeReturnedOdd (s : CostState) : OddCost :=
  (Sum.elim (fun _ => regenerationState) id s.1,s.2)

lemma decodeReturnedOdd_measurable : Measurable decodeReturnedOdd :=
  ((measurable_const.sumElim measurable_id).comp measurable_fst).prodMk measurable_snd

lemma decodeReturnedOdd_embed (z : OddCost) : decodeReturnedOdd (embedOdd z)=z := rfl

lemma embed_decodeReturnedOdd_of_regeneration (s : CostState) (hs : s ∈ regenerationSet) :
    embedOdd (decodeReturnedOdd s)=s := by
  rcases s with ⟨s,T⟩
  cases s with
  | inl s => exact False.elim (regeneration_even s T hs)
  | inr s => rfl

lemma decode_source_signature (z : OddCost) (w : SourceCycleWitness) :
    decodeReturnedOdd (sourceReturnSignature z w).2.2=w.2.2 := rfl

lemma rawBranchReturn_endpoint_supported (a : ℕ) (b : Bool) (h : RawHistory a) :
    ∀ᵐ r ∂rawBranchReturnKernel a b h,
      rawLast (a+2*(r.1+1)) r.2 = embedOdd (decodeReturnedOdd (rawReturnSignature a r).2.2) := by
  filter_upwards [rawBranchReturn_ae_regeneration a b h] with r hr
  exact (embed_decodeReturnedOdd_of_regeneration _ hr).symm

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
