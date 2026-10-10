import Mathlib
import OAI.Analysis.HardSphere.Collisions.PartialPhysicalLaw
import OAI.Analysis.HardSphere.Bridges.PhysicalSparse

namespace OAI

section

section
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace HardSphere.Comparison
variable {I E W : Type*} [DecidableEq I] [MeasurableSpace E] [MeasurableSpace W]

def bathPermutation (σ : Equiv.Perm I) (star a b : I)
    (hs : σ star=a) (hb : σ b=star) :
    {i : I // i≠star ∧ i≠b} ≃ {i : I // i≠a ∧ i≠star} :=
  σ.subtypeEquiv (by
    intro i
    constructor
    · rintro ⟨hi,hj⟩
      exact ⟨fun h ↦ hi (σ.injective (h.trans hs.symm)),
        fun h ↦ hj (σ.injective (h.trans hb.symm))⟩
    · rintro ⟨hi,hj⟩
      exact ⟨fun h ↦ hi (h ▸ hs),fun h ↦ hj (h ▸ hb)⟩)

omit [DecidableEq I] in
lemma bathPermutation_apply (σ : Equiv.Perm I) (star a b : I)
    (hs : σ star=a) (hb : σ b=star) (i : {i : I // i≠star ∧ i≠b}) :
    (bathPermutation σ star a b hs hb i).val=σ i := rfl

def permutedFirstObservation (σ : Equiv.Perm I) (star a b : I)
    (p : (I→E)×(I→E)×W) : E×E×({i : I // i≠star ∧ i≠b}→E)×W :=
  (p.1 a,p.1 star,fun i ↦ p.1 (σ i),p.2.2)
def secondPermutationObservation (star b : I)
    (p : (I→E)×(I→E)×W) : E×E×({i : I // i≠star ∧ i≠b}→E)×W :=
  (p.2.1 star,p.2.1 b,fun i ↦ p.2.1 i,p.2.2)

omit [DecidableEq I] in
lemma permutedFirstObservation_measurable (σ : Equiv.Perm I) (star a b : I) :
    Measurable (permutedFirstObservation (E:=E) (W:=W) σ star a b) := by
  unfold permutedFirstObservation
  fun_prop
omit [DecidableEq I] in
lemma secondPermutationObservation_measurable (star b : I) :
    Measurable (secondPermutationObservation (E:=E) (W:=W) star b) := by
  unfold secondPermutationObservation
  fun_prop

omit [DecidableEq I] [MeasurableSpace E] [MeasurableSpace W] in
lemma permutation_observations_eq (σ : Equiv.Perm I) (star a b : I)
    (hs : σ star=a) (hb : σ b=star) (p : (I→E)×(I→E)×W)
    (hp : ∀i,p.2.1 i=p.1 (σ i)) :
    permutedFirstObservation σ star a b p=secondPermutationObservation star b p := by
  unfold permutedFirstObservation secondPermutationObservation
  simp only [hp,hs,hb]

omit [DecidableEq I] in
lemma permutation_observedMeasures_eq (σ : Equiv.Perm I) (star a b : I)
    (hs : σ star=a) (hb : σ b=star) (μ : Measure ((I→E)×(I→E)×W))
    (h : ∀ᵐ p ∂μ,∀i,p.2.1 i=p.1 (σ i)) :
    μ.map (permutedFirstObservation σ star a b)=μ.map (secondPermutationObservation star b) := by
  apply Measure.map_congr
  filter_upwards [h] with p hp
  exact permutation_observations_eq σ star a b hs hb p hp

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C E W : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  [MeasurableSpace E] [MeasurableEq E] [MeasurableSpace W]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

def secondPositions (σ : Equiv.Perm I) (s : Finset I) (mid : ∀i,X i→E)
    (p : ∀i,X i×X (σ.symm i)) (j : I) : E :=
  if j∈s then mid (σ.symm (σ j)) (p (σ j)).2 else mid j (p j).1

omit [Fintype I] [MeasurableEq E] in
lemma secondPositions_measurable (σ : Equiv.Perm I) (s : Finset I) (mid : ∀i,X i→E)
    (hm : ∀i,Measurable (mid i)) : Measurable (secondPositions σ s mid) := by
  apply Measurable.of_eval
  intro j
  unfold secondPositions
  split_ifs
  · exact (hm _).comp (measurable_snd.comp (measurable_pi_apply _))
  · exact (hm _).comp (measurable_fst.comp (measurable_pi_apply _))

omit [Fintype I] [MeasurableSpace E] [MeasurableEq E] [∀i,MeasurableSpace (X i)] in
lemma secondPositions_eq (σ : Equiv.Perm I) (s : Finset I)
    (hfix : ∀i,i∉s → σ i=i) (mid : ∀i,X i→E)
    (p : ∀i,X i×X (σ.symm i))
    (hp : ∀i∈s,mid i (p i).1=mid (σ.symm i) (p i).2) (j : I) :
    secondPositions σ s mid p j=mid (σ j) (p (σ j)).1 := by
  unfold secondPositions
  split_ifs with hj
  · exact (hp (σ j) ((Bridge.move_mem_iff σ s hfix j).mpr hj)).symm
  · rw [hfix j hj]

def pairedPositions (σ : Equiv.Perm I) (s : Finset I) (mid : ∀i,X i→E)
    (out : (∀i,X i×X (σ.symm i))→W)
    (p : (∀i,X i×X (σ.symm i))×(∀i:s,X i×X (σ.symm i))) :
    (I→E)×(I→E)×W :=
  let v := Function.updateFinset p.1 s p.2
  (fun i ↦ mid i (v i).1, secondPositions σ s mid v, out p.1)

omit [Fintype I] [MeasurableEq E] in
lemma pairedPositions_measurable (σ : Equiv.Perm I) (s : Finset I) (mid : ∀i,X i→E)
    (hm : ∀i,Measurable (mid i)) (out : (∀i,X i×X (σ.symm i))→W) (ho : Measurable out) :
    Measurable (pairedPositions σ s mid out) := by
  have hu : Measurable (fun p : (∀i,X i×X (σ.symm i))×(∀i:s,X i×X (σ.symm i)) ↦
      Function.updateFinset p.1 s p.2) := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i∈s
    · simpa only [Function.updateFinset,dite_eq_left hi,Function.comp_def] using
        (measurable_pi_apply (⟨i,hi⟩:s)).comp measurable_snd
    · simpa only [Function.updateFinset,dite_eq_right hi,Function.comp_def] using
        (measurable_pi_apply i).comp measurable_fst
  exact ((Measurable.of_eval (fun i ↦ (hm i).comp (measurable_fst.comp (measurable_pi_apply i)))).comp hu).prodMk
    (((secondPositions_measurable σ s mid hm).comp hu).prodMk (ho.comp measurable_fst))

lemma inserted_common_observed (σ : Equiv.Perm I) (s o : Finset I)
    (hfix : ∀i,i∉s → σ i=i)
    (checks : C→LocalCheck (fun i ↦ X i×X (σ.symm i)))
    (μ : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsProbabilityMeasure (μ i)]
    (ξ : Measure (∀i,X i×X (σ.symm i))) [SFinite ξ]
    (mid : ∀i,X i→E) (hm : ∀i,Measurable (mid i))
    (hmid : ∀i : s,∀ᵐp ∂μ i,mid i p.1=mid (σ.symm i) p.2)
    (out : (∀i,X i×X (σ.symm i))→W) (ho : Measurable out)
    (star a b : I) (hs : σ star=a) (hb : σ b=star) :
    ((insertedLaw checks μ s o ξ).map (pairedPositions σ s mid out)).map
      (permutedFirstObservation σ star a b)=
    ((insertedLaw checks μ s o ξ).map (pairedPositions σ s mid out)).map
      (secondPermutationObservation star b) := by
  apply permutation_observedMeasures_eq σ star a b hs hb
  apply (ae_map_iff (pairedPositions_measurable σ s mid hm out ho).aemeasurable (by measurability)).mpr
  have h := insertedLaw_factorSupport checks μ s o ξ
    (fun i ↦ {p | mid i p.1=mid (σ.symm i) p.2})
    (fun i ↦ measurableSet_eq_fun ((hm i).comp measurable_fst) ((hm _).comp measurable_snd)) hmid
  filter_upwards [h] with p hp
  intro j
  apply secondPositions_eq σ s hfix mid
  intro i hi
  simpa only [Function.updateFinset,dite_eq_left hi,Function.comp_def] using hp (⟨i,hi⟩:s)

end HardSphere.Comparison

end
end

end

end OAI
