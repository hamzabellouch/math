import Mathlib
import OAI.Analysis.HardSphere.Bridges.ActualReverse
import OAI.Analysis.HardSphere.Comparison.ActualCommon

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison
variable {I E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace E]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] [MeasurableSpace E] in
lemma mid_fiberEquiv (mid : ∀i,X i→E) {i j : I} (h : i=j) (x : X i) :
    mid j (fiberEquiv h x)=mid i x := by cases h; rfl

omit [Fintype I] [MeasurableSpace E] in
lemma secondPositions_reverseSelected (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (mid : ∀i,X i→E) (x : ∀i,X i)
    (z : ∀i,X (σ.symm i)) (p : ∀i:s,X i×X (σ.symm i)) (j : I) :
    secondPositions σ s mid (Function.updateFinset (fun i ↦ (x i,z i)) s p) j=
      mid j (Function.updateFinset x s (fun i ↦ (reverseSelected σ s hf p i).1) j) := by
  by_cases hj : j∈s
  · have hσj := (move_mem_iff σ s hf j).mpr hj
    simp only [secondPositions,ite_eq_left hj,Function.updateFinset,dite_eq_left hj,dite_eq_left hσj,
      reverseSelected_apply,mid_fiberEquiv]
    rfl
  · simp only [secondPositions,ite_eq_right hj,Function.updateFinset,dite_eq_right hj]

def primaryFirstObservation (σ : Equiv.Perm I) (star a b : I) (mid : ∀i,X i→E)
    (x : ∀i,X i) : E×E×({i : I // i≠star ∧ i≠b}→E) :=
  (mid a (x a),mid star (x star),fun i ↦ mid (σ i) (x (σ i)))

def primarySecondObservation (star b : I) (mid : ∀i,X i→E)
    (x : ∀i,X i) : E×E×({i : I // i≠star ∧ i≠b}→E) :=
  (mid star (x star),mid b (x b),fun i ↦ mid i (x i))

omit [Fintype I] [DecidableEq I] in
lemma primaryFirstObservation_measurable (σ : Equiv.Perm I) (star a b : I)
    (mid : ∀i,X i→E) (hm : ∀i,Measurable (mid i)) :
    Measurable (primaryFirstObservation σ star a b mid) := by
  exact ((hm a).comp (measurable_pi_apply a)).prodMk
    (((hm star).comp (measurable_pi_apply star)).prodMk
      (Measurable.of_eval (fun i ↦ (hm (σ i)).comp (measurable_pi_apply (σ i)))))
omit [Fintype I] [DecidableEq I] in
lemma primarySecondObservation_measurable (star b : I)
    (mid : ∀i,X i→E) (hm : ∀i,Measurable (mid i)) :
    Measurable (primarySecondObservation star b mid) := by
  exact ((hm star).comp (measurable_pi_apply star)).prodMk
    (((hm b).comp (measurable_pi_apply b)).prodMk
      (Measurable.of_eval (fun i ↦ (hm i).comp (measurable_pi_apply i.val))))

omit [Fintype I] [MeasurableSpace E] in
lemma primary_observations_eq (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (mid : ∀i,X i→E)
    (x : ∀i,X i) (p : ∀i:s,X i×X (σ.symm i))
    (hp : ∀i:s,mid i (p i).1=mid (σ.symm i) (p i).2)
    (star a b : I) (hs : σ star=a) (hb : σ b=star) :
    primaryFirstObservation σ star a b mid (Function.updateFinset x s (fun i ↦ (p i).1))=
    primarySecondObservation star b mid
      (Function.updateFinset x s (fun i ↦ (reverseSelected σ s hf p i).1)) := by
  have h (j : I) : mid j (Function.updateFinset x s (fun i ↦ (reverseSelected σ s hf p i).1) j)=
      mid (σ j) (Function.updateFinset x s (fun i ↦ (p i).1) (σ j)) := by
    by_cases hj : j∈s
    · have hσj := (move_mem_iff σ s hf j).mpr hj
      simp only [Function.updateFinset,dite_eq_left hj,dite_eq_left hσj,reverseSelected_apply,mid_fiberEquiv]
      exact (hp (selectedPerm σ s hf ⟨j,hj⟩)).symm
    · have he : σ j∉s := by simpa only [hf j hj] using hj
      simp only [Function.updateFinset,dite_eq_right hj,dite_eq_right he]
      exact congrArg (fun i ↦ mid i (x i)) (hf j hj).symm
  simp only [primaryFirstObservation,primarySecondObservation,h]
  let F : I→E := fun i ↦ mid i (Function.updateFinset x s (fun i ↦ (p i).1) i)
  change (F a,F star,fun i : {i : I // i≠star ∧ i≠b} ↦ F (σ i))=
    (F (σ star),F (σ b),fun i : {i : I // i≠star ∧ i≠b} ↦ F (σ i))
  rw [hs,hb]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]
lemma actual_observed_likelihoods {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (star : I) (hstar : ∀j,label j≠star) (hs : star∈s)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (heq : ∀i,i≠star→μ i=ν i)
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i))
    {E : Type*} [MeasurableSpace E] [MeasurableEq E]
    (mid : ∀i,X i→E) (hm : ∀i,Measurable (mid i))
    (hmid : ∀i:s,∀ᵐp ∂(μ i).compProd (κ i),mid i p.1=mid (σ.symm i) p.2)
    (a b : I) (hsa : σ star=a) (hbs : σ b=star) :
    let R := primaryChecks r anchor allowed label get hg
    let C := routeChecks σ s hf r anchor allowed label get hg
    let C' := routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg
    let P := conditionedMeasure (Measure.pi μ) (retainedEvent R Finset.univ)
    let Q := conditionedMeasure (Measure.pi ν) (retainedEvent R Finset.univ)
    (P.withDensity (fun x ↦ conditionalLikelihood R C μ κ s (Finset.univ\s) x z)).map
      (primaryFirstObservation σ star a b mid)=
    (Q.withDensity (fun x ↦ conditionalLikelihood R C' ν η s (Finset.univ\s) x w)).map
      (primarySecondObservation star b mid) := by
  dsimp only
  obtain ⟨h₁,h₂⟩ := actual_two_primary_laws σ s hf r anchor allowed label get hg star hstar hs μ ν heq κ η he z w
  let upd : ((∀i,X i)×(∀i:s,X i×X (σ.symm i)))→(∀i,X i) :=
    fun p ↦ Function.updateFinset p.1 s (fun i ↦ (p.2 i).1)
  let rev : ((∀i,X i)×(∀i:s,X i×X (σ.symm i)))→(∀i,X i) :=
    fun p ↦ Function.updateFinset p.1 s (fun i ↦ (reverseSelected σ s hf p.2 i).1)
  let π : (∀i:s,X i×X (σ.symm i))→(∀i:s,X i) := fun p i ↦ (p i).1
  have hπ : Measurable π := Measurable.of_eval (fun i ↦ measurable_fst.comp (measurable_pi_apply i))
  have hu : Measurable upd := measurable_updateFinset'.comp
    (measurable_fst.prodMk (hπ.comp measurable_snd))
  have hv : Measurable rev := measurable_updateFinset'.comp
    (measurable_fst.prodMk (Measurable.of_eval (fun i ↦ measurable_fst.comp
      ((measurable_pi_apply i).comp ((reverseSelected σ s hf).measurable.comp measurable_snd)))))
  rw [←h₁,←h₂,Measure.map_map (primaryFirstObservation_measurable σ star a b mid hm) hu,
    Measure.map_map (primarySecondObservation_measurable star b mid hm) hv]
  apply Measure.map_congr
  have h := proposal_factorSupport
    (routeChecks σ s hf r anchor allowed label get hg) μ κ s (Finset.univ\s) z
    (conditionedMeasure (Measure.pi μ) (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ))
    (fun i ↦ {p | mid i p.1=mid (σ.symm i) p.2})
    (fun i ↦ measurableSet_eq_fun ((hm i).comp measurable_fst) ((hm _).comp measurable_snd)) hmid
  filter_upwards [h] with p hp
  exact primary_observations_eq σ s hf mid p.1 p.2 hp star a b hsa hbs

end HardSphere.Bridge

end
end

end

end OAI
