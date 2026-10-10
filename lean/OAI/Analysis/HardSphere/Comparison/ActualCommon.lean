import Mathlib
import OAI.Analysis.HardSphere.Conditioning.ReferenceResample
import OAI.Analysis.HardSphere.Conditioning.PermutationObserved

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C E W : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  [MeasurableSpace E] [MeasurableEq E] [MeasurableSpace W]
  {X Z : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Z i)]

lemma proposal_factorSupport (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s o : Finset I) (z : ∀i,Z i) (ξ : Measure (∀i,X i)) [SFinite ξ]
    (A : ∀i:s,Set (X i×Z i)) (hA : ∀i,MeasurableSet (A i))
    (hμ : ∀i:s,∀ᵐp ∂(μ i).compProd (κ i),p∈A i) :
    ∀ᵐp ∂ξ.compProd (proposalKernel checks μ κ s o z),∀i:s,p.2 i∈A i := by
  have hm : ∀ᵐy ∂Measure.pi (fun i:s ↦ (μ i).compProd (κ i)),∀i:s,y i∈A i := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun j:s ↦ (μ j).compProd (κ j)) i).ae (hμ i)
  have hs : MeasurableSet {p : (∀i,X i)×(∀i:s,X i×Z i) | ∀i:s,p.2 i∈A i} := by
    have hh := MeasurableSet.iInter (fun i ↦ (hA i).preimage ((measurable_pi_apply i).comp
      (measurable_snd : Measurable (Prod.snd : (∀i,X i)×(∀i:s,X i×Z i)→_))))
    convert hh using 1
    ext p
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Set.mem_preimage,Function.comp_apply]
  apply (Measure.ae_compProd_iff hs).mpr
  exact ae_of_all _ (fun x ↦ (fiberNormalize_ac _ (measurable_proposalEvent checks s o z) x).ae_le hm)

def actualPairedPositions (σ : Equiv.Perm I) (s : Finset I) (mid : ∀i,X i→E)
    (out : (∀i,X i)→W) (z : ∀i,X (σ.symm i))
    (p : (∀i,X i)×(∀i:s,X i×X (σ.symm i))) : (I→E)×(I→E)×W :=
  let v := Function.updateFinset (fun i ↦ (p.1 i,z i)) s p.2
  (fun i ↦ mid i (v i).1,secondPositions σ s mid v,out p.1)

omit [Fintype I] [MeasurableEq E] in
lemma actualPairedPositions_measurable (σ : Equiv.Perm I) (s : Finset I) (mid : ∀i,X i→E)
    (hm : ∀i,Measurable (mid i)) (out : (∀i,X i)→W) (ho : Measurable out)
    (z : ∀i,X (σ.symm i)) : Measurable (actualPairedPositions σ s mid out z) := by
  have hu : Measurable (fun p : (∀i,X i)×(∀i:s,X i×X (σ.symm i)) ↦
      Function.updateFinset (fun i ↦ (p.1 i,z i)) s p.2) := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i∈s
    · simpa only [Function.updateFinset,dite_eq_left hi,Function.comp_def] using
        (measurable_pi_apply (⟨i,hi⟩:s)).comp measurable_snd
    · simpa only [Function.updateFinset,dite_eq_right hi,Function.comp_def] using
        (((measurable_pi_apply i).comp (measurable_fst : Measurable (Prod.fst : (∀i,X i)×(∀i:s,X i×X (σ.symm i))→_))).prodMk measurable_const)
  exact ((Measurable.of_eval (fun i ↦ (hm i).comp (measurable_fst.comp (measurable_pi_apply i)))).comp hu).prodMk
    (((secondPositions_measurable σ s mid hm).comp hu).prodMk (ho.comp measurable_fst))

lemma actual_common_observed (σ : Equiv.Perm I) (s o : Finset I)
    (hf : ∀i,i∉s→σ i=i)
    (checks : C→LocalCheck (fun i ↦ X i×X (σ.symm i)))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (ξ : Measure (∀i,X i)) [SFinite ξ] (z : ∀i,X (σ.symm i))
    (mid : ∀i,X i→E) (hm : ∀i,Measurable (mid i))
    (hmid : ∀i:s,∀ᵐp ∂(μ i).compProd (κ i),mid i p.1=mid (σ.symm i) p.2)
    (out : (∀i,X i)→W) (ho : Measurable out)
    (star a b : I) (hs : σ star=a) (hb : σ b=star) :
    ((ξ.compProd (proposalKernel checks μ κ s o z)).map (actualPairedPositions σ s mid out z)).map
      (permutedFirstObservation σ star a b)=
    ((ξ.compProd (proposalKernel checks μ κ s o z)).map (actualPairedPositions σ s mid out z)).map
      (secondPermutationObservation star b) := by
  apply permutation_observedMeasures_eq σ star a b hs hb
  apply (ae_map_iff (actualPairedPositions_measurable σ s mid hm out ho z).aemeasurable (by measurability)).mpr
  have h := proposal_factorSupport checks μ κ s o z ξ
    (fun i ↦ {p | mid i p.1=mid (σ.symm i) p.2})
    (fun i ↦ measurableSet_eq_fun ((hm i).comp measurable_fst) ((hm _).comp measurable_snd)) hmid
  filter_upwards [h] with p hp
  intro j
  apply secondPositions_eq σ s hf mid
  intro i hi
  simpa only [Function.updateFinset,dite_eq_left hi,Function.comp_def] using hp (⟨i,hi⟩:s)

end HardSphere.Comparison

end
end

end

end OAI
