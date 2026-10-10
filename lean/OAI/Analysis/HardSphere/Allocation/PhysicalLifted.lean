import Mathlib
import OAI.Analysis.HardSphere.Geometry.SharedIdentities
import OAI.Analysis.HardSphere.Allocation.PhysicalSupported
import OAI.Analysis.HardSphere.Geometry.SharedFixed

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

instance physicalSelectedOn_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) (i : routeSlots labels) :
    IsFiniteMeasure (physicalSelectedOn hL g m t r R C S u particle labels v steps d i) := by
  unfold physicalSelectedOn supportedPair
  infer_instance

def physicalOnChecks {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) :=
  primaryChecks (X:=fun i : Option J ↦ physicalSlotAllowed hL g m r R C S u particle d i)
    r (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
    (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j))
    some (fun _ f ↦ f) (fun _ ↦ measurable_id)

def physicalOnPrimary {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :=
  conditionedMeasure (Measure.pi (physicalSlotOn hL g m t r R C S u particle v d))
    (retainedEvent (physicalOnChecks hL g m r R C S u particle d) Finset.univ)

instance physicalOnPrimary_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    IsFiniteMeasure (physicalOnPrimary hL g m t r R C S u particle v d) := by
  unfold physicalOnPrimary; infer_instance

def physicalSharedOn {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) :=
  ambientSharedKernel (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels)
    (Kernel.const Unit (physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d))
    (fun i ↦ Kernel.const Unit (physicalSelectedOn hL g m t r R C S u particle labels v steps d i))
    (Prod.snd ⁻¹' retainedEvent (physicalOnChecks hL g m r R C S u particle d) Finset.univ) ()

theorem physicalSharedOn_map {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d) :
    (physicalSharedOn hL g m t r R C S u particle labels v steps d).map
      (routePairedMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))
        (routeSlots labels) (routePermutation labels))=
      physicalSharedRoute hL g m t r R C S u particle labels v steps d := by
  let f := fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→C(Time,Point))
  let s := routeSlots labels
  let σ := routePermutation labels
  let P := physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let ρ := physicalSelectedOn hL g m t r R C S u particle labels v steps d
  have hf : ∀i,Measurable (f i) := fun _ ↦ measurable_subtype_coe
  have hP : P.map (routeConfigMap f)=
      physicalPrimaryReference hL g m t r R C S u particle (v (Fin.last (n+1))) d :=
    physicalPrimary_on_map hL g m t r R C S hr u particle _ d
  have hρ : ∀i,(ρ i).map (Prod.map (f i) (f (σ.symm i)))=
      physicalSelectedFactor hL g m t r R C S u particle labels v steps i d :=
    fun i ↦ (physicalSelectedOn_physical hL g m t r R C S ht u particle labels v steps hc d hhome haccess i).2.2.2.2.2
  have hE : (fun p : Unit×(∀i,physicalSlotAllowed hL g m r R C S u particle d i) ↦
      (p.1,routeConfigMap f p.2)) ⁻¹' (Prod.snd ⁻¹' physicalSlotMutual (L:=L) r)=
      Prod.snd ⁻¹' retainedEvent (physicalOnChecks hL g m r R C S u particle d) Finset.univ := by
    change Prod.snd ⁻¹' ((routeConfigMap f) ⁻¹' physicalSlotMutual (L:=L) r)=_
    exact congrArg (fun event ↦ Prod.snd ⁻¹' event)
      (physicalAllowed_checks hL g m r R C S hr u particle d)
  have H := ambientShared_map f hf s σ (routePermutation_fixed labels)
    (Kernel.const Unit P) (fun i ↦ Kernel.const Unit (ρ i))
    (Prod.snd ⁻¹' physicalSlotMutual (L:=L) r) ((physicalSlotMutual_measurable r).preimage measurable_snd) ()
  rw [hE] at H
  change (physicalSharedOn hL g m t r R C S u particle labels v steps d).map
    (routePairedMap f s σ)=_ at H
  refine H.trans ?_
  have HP : ((Kernel.const Unit P).map (routeConfigMap f)) ()=
      physicalPrimaryReference hL g m t r R C S u particle (v (Fin.last (n+1))) d := by
    rw [Kernel.map_apply _ (routeConfigMap_measurable f hf),Kernel.const_apply,hP]
  have HR : ∀i,((Kernel.const Unit (ρ i)).map (Prod.map (f i) (f (σ.symm i)))) ()=
      physicalSelectedFactor hL g m t r R C S u particle labels v steps i d := by
    intro i
    rw [Kernel.map_apply _ ((hf i).prodMap (hf _)),Kernel.const_apply,hρ]
  rw [ambientShared_constant_of s σ (routePermutation_fixed labels) _ _ _
    ((physicalSlotMutual_measurable r).preimage measurable_snd) () _ _ _ HP HR rfl]
  exact (ambientShared_constant s σ (routePermutation_fixed labels) _ _ _
    ((physicalSlotMutual_measurable r).preimage measurable_snd) d).symm

end HardSphere.Groups
end
end

end OAI
