import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalRouteMass
import OAI.Analysis.HardSphere.Bridges.RouteSecondMoment

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L)

structure PhysicalRouteAux where
  forward : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
    (physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i))
  backward : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
    (physicalSlotAllowed hL g m r R C S u particle d (routePermutation labels i))
  forward_finite : ∀i,IsFiniteKernel (forward i)
  backward_finite : ∀i,IsFiniteKernel (backward i)
  selected : ∀i:routeSlots labels,
    (physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d i).compProd (forward i)=
      physicalSelectedOn hL g m t r R C S u particle labels v steps d i
  reverse : ∀i,((physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d (routePermutation labels i)).compProd
    (forward (routePermutation labels i))).map (reverseFactor (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
      (routePermutation labels) i)=(physicalSlotOn hL g m t r R C S u particle (v 0) d i).compProd (backward i)
  forward_bound : ∀i x,forward i x univ≤routeDensityBound t
  backward_bound : ∀i x,backward i x univ≤routeDensityBound t
  forward_mass : ∀i,∫⁻x,forward i x univ ∂physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d i=1
  backward_mass : ∀i,∫⁻x,backward i x univ ∂physicalSlotOn hL g m t r R C S u particle (v 0) d i=1
  firstSeed : ∀i,physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)
  secondSeed : ∀i,physicalSlotAllowed hL g m r R C S u particle d (routePermutation labels i)

attribute [instance] PhysicalRouteAux.forward_finite PhysicalRouteAux.backward_finite

omit [Fintype J] in
lemma physicalRouteAux_nonempty (ht : 0<t)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    Nonempty (PhysicalRouteAux hL g m t r R C S u particle labels v steps d) := by
  have : ∀i,IsProbabilityMeasure (physicalSlotOn hL g m t r R C S u particle (v 0) d i) :=
    physicalOn_probability hL g m t r R C S u particle _ d hp
  obtain ⟨κ,η,hκf,hηf,he,hr,hκb,hηb,hκm,hηm⟩ := physical_auxiliary_exists
    hL g m t r R C S ht u particle labels v steps hc d hhome haccess hp
  exact ⟨⟨κ,η,hκf,hηf,he,hr,hκb,hηb,hκm,hηm,
    (fun i ↦ Classical.choice (nonempty_of_isProbabilityMeasure
      (physicalSlotOn hL g m t r R C S u particle (v 0) d ((routePermutation labels).symm i)))),
    (fun i ↦ Classical.choice (nonempty_of_isProbabilityMeasure
      (physicalSlotOn hL g m t r R C S u particle (v 0) d (routePermutation labels i))))⟩⟩

variable {hL g m t r R C S u particle labels v steps d}

def PhysicalRouteAux.firstDensity (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d) :
    (∀i,physicalSlotAllowed hL g m r R C S u particle d i)→ℝ≥0∞ :=
  fun x ↦ conditionalLikelihood (physicalOnChecks hL g m r R C S u particle d)
    (routeChecks (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
      (routePermutation labels) (routeSlots labels) (routePermutation_fixed labels) r
      (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id))
    (physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d) A.forward
    (routeSlots labels) (Finset.univ\routeSlots labels) x A.firstSeed

def PhysicalRouteAux.secondDensity (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d) :
    (∀i,physicalSlotAllowed hL g m r R C S u particle d i)→ℝ≥0∞ :=
  fun x ↦ conditionalLikelihood (physicalOnChecks hL g m r R C S u particle d)
    (routeChecks (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
      (routePermutation labels).symm (routeSlots labels) (reverse_fix _ _ (routePermutation_fixed labels)) r
      (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id))
    (physicalSlotOn hL g m t r R C S u particle (v 0) d) A.backward
    (routeSlots labels) (Finset.univ\routeSlots labels) x A.secondSeed

lemma PhysicalRouteAux.laws (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    (physicalSharedOn hL g m t r R C S u particle labels v steps d).map
      (ambientFirst (routeSlots labels) (routePermutation labels))=
      (physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d).withDensity A.firstDensity ∧
    (physicalSharedOn hL g m t r R C S u particle labels v steps d).map
      (ambientSecond (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels))=
      (physicalOnPrimary hL g m t r R C S u particle (v 0) d).withDensity A.secondDensity := by
  exact physical_two_likelihoods hL g m t r R C S u particle labels v steps d hp
    A.forward A.backward A.selected (fun i ↦ A.reverse i) A.firstSeed A.secondSeed

omit [Fintype J] in
lemma PhysicalRouteAux.path_bounds (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
    (ht : 0<t)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d) :
    let X : Option J→Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
    let σ := routePermutation labels
    let s := routeSlots labels
    let allowed := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
    let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
    let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
    (∀b j,routeOwner σ some b j∈s→
      ((μ (routeOwner σ some b j)).compProd (A.forward (routeOwner σ some b j))).map
        (routePath (X:=X) σ s (routePermutation_fixed labels) allowed some (fun _ f ↦ f) b j)≤
          routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j) ∧
    (∀b j,routeOwner σ.symm some b j∈s→
      ((ν (routeOwner σ.symm some b j)).compProd (A.backward (routeOwner σ.symm some b j))).map
        (routePath (X:=X) σ.symm s (reverse_fix σ s (routePermutation_fixed labels)) allowed some (fun _ f ↦ f) b j)≤
          routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j) := by
  exact physical_auxiliary_collision_bounds hL g m t r R C S ht u particle labels v steps hc d hhome haccess
    A.forward A.backward A.selected (fun i ↦ A.reverse i)

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physical_first_likelihood_moment {N K M G n l : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N)
    (f : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K)) (steps : Fin (n+1)→Fin 7)
    (f' : Fin (l+1)↪J) (v' : Fin (l+2)→(Fin 3→Fin K)) (steps' : Fin (l+1)→Fin 7)
    (d : PhysicalDatum N K M G L)
    (A : PhysicalRouteAux hL g m t r R C S u particle f v steps d)
    (B : PhysicalRouteAux hL g m t r R C S u particle f' v' steps' d)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (hc' : ∀k,projectPoint L (routeCellPeriod (v' k.succ) (v' k.castSucc) (steps' k))=0)
    (hh : ∀k,datumHome hL d (particle (f k))=v k.castSucc)
    (hh' : ∀k,datumHome hL d (particle (f' k))=v' k.castSucc)
    (ha : ∀k,datumAccessible hL g m t r R C S u (particle (f k)) d)
    (ha' : ∀k,datumAccessible hL g m t r R C S u (particle (f' k)) d)
    (hn : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1)
    (hn' : ∀k : Fin (l+1),torusDistance L (gridCenter L (v' k.castSucc)) (gridCenter L (v' k.succ))≤1)
    (hend : v' (Fin.last (l+1))=v (Fin.last (n+1)))
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q a : ℝ≥0∞) (ha0 : 0<a)
    (hq : ∀ j k, j ≠ k → ∀p : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p' | TrialCollision r (projectCurve L p.val) p'.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
    let c := fun i ↦ gridSite (slotCenter (fun j ↦ datumHome hL d (particle j)) (v (Fin.last (n+1))) i)
    let ns := nearSlots (torusNear K 30) c (routeSlots f) (routeSlots f')
    let nt := nearSlots (torusNear K 30) c (routeSlots f') (routeSlots f)
    (∫⁻x,A.firstDensity x*B.firstDensity x
      ∂physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d)≤
      (routeDensityBound t)^(routeSlots f∩routeSlots f').card/a^(2*(ns.card+nt.card)) := by
  let X : Option J→Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let anchor := fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j)))
  let allowed := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
  let center := slotCenter (fun j ↦ datumHome hL d (particle j)) (v (Fin.last (n+1)))
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have hdom : ∀j,some j∈routeSlots f∪routeSlots f'→(μ (some j)).map (fun p ↦ p)≤
      routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j := by
    intro j hj
    apply physical_primary_domination
    rcases Finset.mem_union.mp hj with hj|hj
    · exact route_selected_accessible hL g m t r R C S u particle f d ha j hj
    · exact route_selected_accessible hL g m t r R C S u particle f' d ha' j hj
  have h0 : ∀j,torusDistance L (anchor j) (gridCenter L (center (some j)))≤1 := by
    intro j
    change torusDistance L (gridCenter L (datumHome hL d (particle j)))
      (gridCenter L (datumHome hL d (particle j)))≤1
    simp [torusDistance]
  have hB := (B.path_bounds ht hc' hh' ha').1
  have hmB := B.forward_mass
  have hcB := physical_owner_centers hL particle f' v' d hh' hn' true
  simp only [hend] at hB hmB hcB
  have H := physical_route_encounter_moment (X:=X) hL r anchor center (M+1)
    (slotCenter_fiber _ _ M hm) allowed some (Option.some_injective _) (fun _ p ↦ p) (fun _ ↦ measurable_id)
    (routePermutation f) (routePermutation f') (routeSlots f) (routeSlots f')
    (routePermutation_fixed f) (routePermutation_fixed f') h0
    (physical_owner_centers hL particle f v d hh hn true) hcB μ A.forward B.forward
    (physicalCollisionReference hL g m t r R C S u particle d) (routeDensityBound t) q a ha0
    ((le_add_right le_rfl).trans hsmall) A.forward_bound A.forward_mass hmB hdom
    (A.path_bounds ht hc hh ha).1 hB hq hsmall (routeDensityBound_ne_top ht) A.firstSeed B.firstSeed
  simpa only [PhysicalRouteAux.firstDensity,hend,physicalOnPrimary,physicalOnChecks,X,μ,anchor,allowed,center] using H

theorem physical_second_likelihood_moment {N K M G n l : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N)
    (f : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K)) (steps : Fin (n+1)→Fin 7)
    (f' : Fin (l+1)↪J) (v' : Fin (l+2)→(Fin 3→Fin K)) (steps' : Fin (l+1)→Fin 7)
    (d : PhysicalDatum N K M G L)
    (A : PhysicalRouteAux hL g m t r R C S u particle f v steps d)
    (B : PhysicalRouteAux hL g m t r R C S u particle f' v' steps' d)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (hc' : ∀k,projectPoint L (routeCellPeriod (v' k.succ) (v' k.castSucc) (steps' k))=0)
    (hh : ∀k,datumHome hL d (particle (f k))=v k.castSucc)
    (hh' : ∀k,datumHome hL d (particle (f' k))=v' k.castSucc)
    (ha : ∀k,datumAccessible hL g m t r R C S u (particle (f k)) d)
    (ha' : ∀k,datumAccessible hL g m t r R C S u (particle (f' k)) d)
    (hn : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1)
    (hn' : ∀k : Fin (l+1),torusDistance L (gridCenter L (v' k.castSucc)) (gridCenter L (v' k.succ))≤1)
    (hstart : v' 0=v 0)
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q a : ℝ≥0∞) (ha0 : 0<a)
    (hq : ∀ j k, j ≠ k → ∀p : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p' | TrialCollision r (projectCurve L p.val) p'.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
    let c := fun i ↦ gridSite (slotCenter (fun j ↦ datumHome hL d (particle j)) (v 0) i)
    let ns := nearSlots (torusNear K 30) c (routeSlots f) (routeSlots f')
    let nt := nearSlots (torusNear K 30) c (routeSlots f') (routeSlots f)
    (∫⁻x,A.secondDensity x*B.secondDensity x
      ∂physicalOnPrimary hL g m t r R C S u particle (v 0) d)≤
      (routeDensityBound t)^(routeSlots f∩routeSlots f').card/a^(2*(ns.card+nt.card)) := by
  let X : Option J→Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let μ := physicalSlotOn hL g m t r R C S u particle (v 0) d
  let anchor := fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j)))
  let allowed := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
  let center := slotCenter (fun j ↦ datumHome hL d (particle j)) (v 0)
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have hdom : ∀j,some j∈routeSlots f∪routeSlots f'→(μ (some j)).map (fun p ↦ p)≤
      routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j := by
    intro j hj
    apply physical_primary_domination
    rcases Finset.mem_union.mp hj with hj|hj
    · exact route_selected_accessible hL g m t r R C S u particle f d ha j hj
    · exact route_selected_accessible hL g m t r R C S u particle f' d ha' j hj
  have h0 : ∀j,torusDistance L (anchor j) (gridCenter L (center (some j)))≤1 := by
    intro j
    change torusDistance L (gridCenter L (datumHome hL d (particle j)))
      (gridCenter L (datumHome hL d (particle j)))≤1
    simp [torusDistance]
  have hB := (B.path_bounds ht hc' hh' ha').2
  have hmB := B.backward_mass
  have hcB := physical_reverse_owner_centers hL particle f' v' d hh' hn' true
  simp only [hstart] at hB hmB hcB
  have : ∀i,IsFiniteKernel (A.backward i) := A.backward_finite
  have : ∀i,IsFiniteKernel (B.backward i) := B.backward_finite
  have H := physical_route_encounter_moment (X:=X) hL r anchor center (M+1)
    (slotCenter_fiber _ _ M hm) allowed some (Option.some_injective _) (fun _ p ↦ p) (fun _ ↦ measurable_id)
    (routePermutation f).symm (routePermutation f').symm (routeSlots f) (routeSlots f')
    (reverse_fix _ _ (routePermutation_fixed f)) (reverse_fix _ _ (routePermutation_fixed f')) h0
    (physical_reverse_owner_centers hL particle f v d hh hn true) hcB μ A.backward B.backward
    (physicalCollisionReference hL g m t r R C S u particle d) (routeDensityBound t) q a ha0
    ((le_add_right le_rfl).trans hsmall) A.backward_bound A.backward_mass hmB hdom
    (A.path_bounds ht hc hh ha).2 hB hq hsmall (routeDensityBound_ne_top ht) A.secondSeed B.secondSeed
  simpa only [PhysicalRouteAux.secondDensity,hstart,physicalOnPrimary,physicalOnChecks,X,μ,anchor,allowed,center] using H

end HardSphere.Groups
end
end

end OAI
