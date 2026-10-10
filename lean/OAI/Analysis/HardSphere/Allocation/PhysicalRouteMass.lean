import Mathlib
import OAI.Analysis.HardSphere.Bridges.RouteInsertion
import OAI.Analysis.HardSphere.Bridges.RouteMass
import OAI.Analysis.HardSphere.Allocation.RouteCenters
import OAI.Analysis.HardSphere.Allocation.PhysicalLikelihood
import OAI.Analysis.HardSphere.Collisions.PhysicalCollisionReference

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
lemma physical_owner_centers {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (particle : J→Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (hneigh : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1) :
    ∀b j,torusDistance L (projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (gridCenter L (slotCenter (fun j ↦ datumHome hL d (particle j)) (v (Fin.last (n+1)))
        (routeOwner (routePermutation labels) some b j)))≤1 := by
  intro b j
  cases b
  · change torusDistance L (gridCenter L (datumHome hL d (particle j)))
      (gridCenter L (datumHome hL d (particle j)))≤1
    simp [torusDistance]
  · exact (route_two_center_bounds (fun j ↦ datumHome hL d (particle j)) labels v hhome hneigh).1 j

omit [Fintype J] [DecidableEq J] in
lemma physical_reverse_owner_centers {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (particle : J→Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (hneigh : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1) :
    ∀b j,torusDistance L (projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (gridCenter L (slotCenter (fun j ↦ datumHome hL d (particle j)) (v 0)
        (routeOwner (routePermutation labels).symm some b j)))≤1 := by
  intro b j
  cases b
  · change torusDistance L (gridCenter L (datumHome hL d (particle j)))
      (gridCenter L (datumHome hL d (particle j)))≤1
    simp [torusDistance]
  · exact (route_two_center_bounds (fun j ↦ datumHome hL d (particle j)) labels v hhome hneigh).2 j

lemma physical_forward_insertion {N K M G n : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (hneigh : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1)
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (ν : ∀i,Measure (physicalSlotAllowed hL g m r R C S u particle d i ×
      physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)))
    [∀i,IsProbabilityMeasure (ν i)] (q a : ℝ≥0∞)
    (hd : ∀b j,routeOwner (routePermutation labels) some b j∈routeSlots labels→
      (ν (routeOwner (routePermutation labels) some b j)).map
        (routePath (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) (routePermutation labels) (routeSlots labels) (routePermutation_fixed labels)
          (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) b j)≤
        routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
    UniformInsertionOn (routeChecks (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) (routePermutation labels) (routeSlots labels) (routePermutation_fixed labels)
      r (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id))
      ν a (routeSlots labels) := by
  exact route_insertion (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i) hL r _ (slotCenter (fun j ↦ datumHome hL d (particle j)) (v (Fin.last (n+1)))) (M+1)
    (slotCenter_fiber _ _ M hm) _ some (Option.some_injective _) (fun _ f ↦ f) (fun _ ↦ measurable_id)
    _ _ (routePermutation_fixed labels) (physical_owner_centers hL particle labels v d hhome hneigh) ν
    (physicalCollisionReference hL g m t r R C S u particle d) (routeDensityBound t) q a hd hq hsmall

lemma physicalSharedOn_mass_of {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (ν : ∀i,Measure (physicalSlotAllowed hL g m r R C S u particle d i ×
      physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)))
    [∀i,IsProbabilityMeasure (ν i)]
    (he : ∀i:routeSlots labels,ν i=physicalSelectedOn hL g m t r R C S u particle labels v steps d i)
    (a : ℝ≥0∞) (ha : 0<a)
    (hi : UniformInsertionOn (routeChecks (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
      (routePermutation labels) (routeSlots labels) (routePermutation_fixed labels)
      r (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id))
      ν a (routeSlots labels)) :
    physicalSharedOn hL g m t r R C S u particle labels v steps d univ=
      physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d univ := by
  let X : Option J→Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let σ := routePermutation labels
  let s := routeSlots labels
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  let z : ∀i,X (σ.symm i) := fun i ↦ Classical.choice (nonempty_of_isProbabilityMeasure (μ (σ.symm i)))
  have H := route_shared_mass (X:=X) σ s (routePermutation_fixed labels) r
    (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
    (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some
    (fun _ f ↦ f) (fun _ ↦ measurable_id) μ ν a ha hi z
  have hρ : (fun i:s ↦ Kernel.const Unit (ν i))=
      (fun i:s ↦ Kernel.const Unit (physicalSelectedOn hL g m t r R C S u particle labels v steps d i)) := by
    funext i
    rw [he i]
  dsimp only at H
  simp only [hρ] at H
  exact H

theorem physicalSharedOn_mass {N K M G n : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (hneigh : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1)
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q a : ℝ≥0∞) (ha : 0<a)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
    physicalSharedOn hL g m t r R C S u particle labels v steps d univ=
      physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d univ := by
  let X : Option J→Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let σ := routePermutation labels
  let s := routeSlots labels
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let anchor := fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j)))
  let allowed := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  obtain ⟨κ,η,hκf,hηf,he,hr,hκb,hηb,hκm,hηm⟩ := physical_auxiliary_exists
    hL g m t r R C S ht u particle labels v steps hc d hhome haccess hp
  have : ∀i,IsFiniteKernel (κ i) := hκf
  have : ∀i,IsFiniteKernel (η i) := hηf
  let ν := fun i ↦ (μ i).compProd (κ i)
  have : ∀i,IsProbabilityMeasure (ν i) := fun i ↦ ⟨by
    rw [Measure.compProd_apply MeasurableSet.univ]
    simpa using hκm i⟩
  have hd := (physical_auxiliary_collision_bounds hL g m t r R C S ht u
    particle labels v steps hc d hhome haccess κ η he (fun i ↦ hr i)).1
  have hi := physical_forward_insertion hL g m t r R C S u particle labels v d hhome hneigh hm ν q a hd hq hsmall
  exact physicalSharedOn_mass_of hL g m t r R C S u particle labels v steps d hp ν he a ha hi

end HardSphere.Groups
end
end

end OAI
