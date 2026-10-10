import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalPairedRoute

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {I J E : Type*} [DecidableEq I] [DecidableEq J]

def optionParticle (particle : J↪I) : Option J↪Option I where
  toFun := Option.map particle
  inj' := by
    intro i j h
    cases i <;> cases j <;> simp_all only [Option.map_none,Option.map_some,Option.some.injEq,
      reduceCtorEq]
    exact particle.injective h

omit [DecidableEq I] [DecidableEq J] in
lemma routeEmbedding_natural {d : ℕ} (particle : J↪I) (labels : Fin d↪J) (k : Fin (d+1)) :
    routeEmbedding (labels.trans particle) k=optionParticle particle (routeEmbedding labels k) := by
  change (if h : k.val<d then some (particle (labels ⟨k.val,h⟩)) else none)=
    Option.map particle (if h : k.val<d then some (labels ⟨k.val,h⟩) else none)
  by_cases hk : k.val<d <;> simp only [hk,↓reduceDIte,Option.map_some,Option.map_none]

omit [DecidableEq I] in
lemma routePermutation_natural {d : ℕ} (particle : J↪I) (labels : Fin d↪J) (i : Option J) :
    routePermutation (labels.trans particle) (optionParticle particle i)=
      optionParticle particle (routePermutation labels i) := by
  by_cases hi : i∈routeSlots labels
  · obtain ⟨k,_,hk⟩ := Finset.mem_map.mp hi
    subst i
    rw [←routeEmbedding_natural]
    change (finRotate (d+1)).viaEmbedding _ _=optionParticle particle ((finRotate (d+1)).viaEmbedding _ _)
    rw [Equiv.Perm.viaEmbedding_apply,Equiv.Perm.viaEmbedding_apply,routeEmbedding_natural]
  · have hni : optionParticle particle i∉routeSlots (labels.trans particle) := by
      rintro hj
      obtain ⟨k,_,hk⟩ := Finset.mem_map.mp hj
      apply hi
      refine Finset.mem_map.mpr ⟨k,Finset.mem_univ _,?_⟩
      apply (optionParticle particle).injective
      rwa [←routeEmbedding_natural]
    rw [routePermutation_fixed _ _ hni,routePermutation_fixed _ _ hi]

omit [DecidableEq I] [DecidableEq J] in
lemma fullRoute_fixed_outside {d : ℕ} (particle : J↪I) (labels : Fin d↪J) (i : Option I)
    (hi : i∉Set.range (optionParticle particle)) : routePermutation (labels.trans particle) i=i := by
  apply routePermutation_fixed
  intro h
  obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp h
  exact hi ⟨routeEmbedding labels k,(routeEmbedding_natural particle labels k).symm⟩

def fillGroup (particle : J↪I) (H : Option I→E) (F : Option J→E) : Option I→E :=
  Function.extend (optionParticle particle) F H

omit [DecidableEq I] [DecidableEq J] in
lemma fillGroup_selected (particle : J↪I) (H : Option I→E) (F : Option J→E) (i : Option J) :
    fillGroup particle H F (optionParticle particle i)=F i :=
  (optionParticle particle).injective.extend_apply F H i

omit [DecidableEq I] in
lemma fillGroup_permutation {d : ℕ} (particle : J↪I) (labels : Fin d↪J)
    (H : Option I→E) (F G : Option J→E) (hFG : ∀i,G i=F (routePermutation labels i)) :
    ∀i,fillGroup particle H G i=fillGroup particle H F (routePermutation (labels.trans particle) i) := by
  intro i
  by_cases hi : i∈Set.range (optionParticle particle)
  · obtain ⟨j,rfl⟩ := hi
    rw [routePermutation_natural,fillGroup_selected,fillGroup_selected,hFG]
  · rw [fullRoute_fixed_outside particle labels i hi]
    exact (Function.extend_apply' G H i hi).trans (Function.extend_apply' F H i hi).symm

omit [DecidableEq I] [DecidableEq J] in
lemma fillGroup_measurable [MeasurableSpace E] (particle : J↪I) :
    Measurable (fun z : (Option I→E)×(Option J→E) ↦ fillGroup particle z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈Set.range (optionParticle particle)
  · obtain ⟨j,rfl⟩ := hi
    simpa only [fillGroup_selected,Function.comp_def] using (measurable_pi_apply j).comp measurable_snd
  · have he : (fun z : (Option I→E)×(Option J→E) ↦ fillGroup particle z.1 z.2 i)=fun z ↦ z.1 i := by
      funext z; exact Function.extend_apply' z.2 z.1 i hi
    rw [he]
    exact (measurable_pi_apply i).comp measurable_fst

lemma ambient_midpoint_permutation [Fintype I] [MeasurableSpace E]
    {V : I→Type*} [∀i,MeasurableSpace (V i)] (σ : Equiv.Perm I) (s : Finset I)
    (hσ : ∀i,i∉s→σ i=i) (mid : ∀i,V i→E)
    (z : (∀i,V i)×(∀i:s,V i×V (σ.symm i)))
    (hz : ∀i:s,mid i (z.2 i).1=mid (σ.symm i) (z.2 i).2) :
    ∀i,mid i (ambientSecond s σ hσ z i)=mid (σ i) (ambientFirst s σ z (σ i)) := by
  intro i
  by_cases hi : i∈s
  · have hσi := (Bridge.move_mem_iff σ s hσ i).mpr hi
    simp only [ambientFirst,ambientSecond,Function.updateFinset,dite_eq_left hi,dite_eq_left hσi,
      Bridge.reverseSelected_apply,Bridge.mid_fiberEquiv]
    exact (hz (Bridge.selectedPerm σ s hσ ⟨i,hi⟩)).symm
  · have hσi : σ i∉s := by simpa only [hσ i hi] using hi
    simp only [ambientFirst,ambientSecond,Function.updateFinset,dite_eq_right hi,dite_eq_right hσi]
    exact congrArg (fun j ↦ mid j (z.1 j)) (hσ i hi).symm

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma projectPoint_continuous (L : Length) : Continuous (projectPoint L) :=
  continuous_pi (fun j ↦ (AddCircle.continuous_mk' L.val).comp (continuous_apply j))

def physicalFullMidpoint {N K M G : ℕ} {L : Length} (particle : J↪Fin N)
    (z : PhysicalDatum N K M G L×(Option J→C(Time,Point))) : Option (Fin N)→Torus L :=
  fillGroup particle (fun i ↦ i.elim 0 (fun j ↦ z.1.2.2.2.2 j midpointTime 0))
    (fun i ↦ projectPoint L (z.2 i midpointTime))

omit [Fintype J] [DecidableEq J] in
lemma physicalFullMidpoint_measurable {N K M G : ℕ} {L : Length} (particle : J↪Fin N) :
    Measurable (physicalFullMidpoint (K:=K) (M:=M) (G:=G) (L:=L) particle) := by
  unfold physicalFullMidpoint
  refine (fillGroup_measurable (E:=Torus L) particle).comp (f:=fun z : PhysicalDatum N K M G L×(Option J→C(Time,Point)) ↦
    ((fun i : Option (Fin N) ↦ i.elim 0 (fun j ↦ z.1.2.2.2.2 j midpointTime 0)),
     (fun i : Option J ↦ projectPoint L (z.2 i midpointTime)))) ?_
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    cases i with
    | none => exact measurable_const
    | some i =>
      exact (measurable_pi_apply 0).comp ((continuous_eval_const midpointTime).measurable.comp
        ((datumFrozen_measurable i).comp measurable_fst))
  · apply Measurable.of_eval
    intro i
    exact (projectPoint_continuous L).measurable.comp ((continuous_eval_const midpointTime).measurable.comp
      ((measurable_pi_apply i).comp measurable_snd))

theorem physicalPairedRoute_midpoint {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d) :
    ∀ᵐz ∂physicalPairedRoute hL g m t r R C S u particle labels v steps d,
      ∀i,physicalFullMidpoint particle (d,z.2) i=
        physicalFullMidpoint particle (d,z.1) (routePermutation (labels.trans particle) i) := by
  have h := ambientSharedKernel_support (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels)
    (physicalPrimaryReference hL g m t r R C S u particle (v (Fin.last (n+1))))
    (physicalSelectedFactor hL g m t r R C S u particle labels v steps)
    (Prod.snd ⁻¹' physicalSlotMutual (L:=L) (J:=J) r)
    ((physicalSlotMutual_measurable r).preimage measurable_snd) d
    (fun _ ↦ {p : C(Time,Point)×C(Time,Point) | projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)})
    (fun _ ↦ measurableSet_eq_fun ((projectPoint_continuous L).measurable.comp ((continuous_eval_const midpointTime).measurable.comp measurable_fst))
      ((projectPoint_continuous L).measurable.comp ((continuous_eval_const midpointTime).measurable.comp measurable_snd)))
    (fun i ↦ (physicalSelectedFactor_physical hL g m t r R C S ht u particle labels v steps hc d hhome haccess i).2.2.2.2.2)
  rw [physicalPairedRoute,Kernel.map_apply _ ((ambientFirst_measurable _ _).prodMk (ambientSecond_measurable _ _ _))]
  rw [ae_map_iff ((ambientFirst_measurable _ _).prodMk (ambientSecond_measurable _ _ _)).aemeasurable (by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_eq_fun
      ((measurable_pi_apply i).comp ((physicalFullMidpoint_measurable particle).comp (measurable_const.prodMk measurable_snd)))
      ((measurable_pi_apply _).comp ((physicalFullMidpoint_measurable particle).comp (measurable_const.prodMk measurable_fst))))]
  filter_upwards [h] with z hz
  exact fillGroup_permutation particle labels _ _ _ (ambient_midpoint_permutation _ _ _
    (fun _ p ↦ projectPoint L (p midpointTime)) z hz)

end HardSphere.Groups
end
end

end OAI
