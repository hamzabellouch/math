import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalPairedRoute
import OAI.Analysis.HardSphere.Comparison.RouteRN

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
  (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
  (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→Fin 3→Fin K)
  (steps : Fin (n+1)→Fin 7)
  (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
  (d : PhysicalDatum N K M G L)
  (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
  (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)

include ht hr hc hhome haccess

lemma physicalPairedRoute_marginals :
    (physicalPairedRoute hL g m t r R C S u particle labels v steps d).map Prod.fst=
      ((physicalSharedOn hL g m t r R C S u particle labels v steps d).map
        (ambientFirst (routeSlots labels) (routePermutation labels))).map
          (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) ∧
    (physicalPairedRoute hL g m t r R C S u particle labels v steps d).map Prod.snd=
      ((physicalSharedOn hL g m t r R C S u particle labels v steps d).map
        (ambientSecond (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels))).map
          (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) := by
  let f := fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→C(Time,Point))
  have hf : ∀i,Measurable (f i) := fun _ ↦ measurable_subtype_coe
  have H := physicalSharedOn_map hL g m t r R C S ht hr u particle labels v steps hc d hhome haccess
  have hF := ambientFirst_measurable (X:=fun _ : Option J ↦ C(Time,Point)) (routeSlots labels) (routePermutation labels)
  have hS := ambientSecond_measurable (X:=fun _ : Option J ↦ C(Time,Point)) (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels)
  rw [physicalPairedRoute,Kernel.map_apply _ (hF.prodMk hS)]
  constructor
  · rw [Measure.map_map measurable_fst (hF.prodMk hS)]
    change (physicalSharedRoute hL g m t r R C S u particle labels v steps d).map
      (ambientFirst (routeSlots labels) (routePermutation labels))=_
    rw [←H,Measure.map_map hF (routePairedMap_measurable f hf _ _),
      Measure.map_map (routeConfigMap_measurable f hf) (ambientFirst_measurable _ _)]
    congr 1
    funext p
    exact ambientFirst_natural f _ _ p
  · rw [Measure.map_map measurable_snd (hF.prodMk hS)]
    change (physicalSharedRoute hL g m t r R C S u particle labels v steps d).map
      (ambientSecond (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels))=_
    rw [←H,Measure.map_map hS (routePairedMap_measurable f hf _ _),
      Measure.map_map (routeConfigMap_measurable f hf) (ambientSecond_measurable _ _ _)]
    congr 1
    funext p
    exact ambientSecond_natural f _ _ _ p

lemma physicalPairedRoute_densities
    (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    (physicalPairedRoute hL g m t r R C S u particle labels v steps d).map Prod.fst=
      ((physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d).withDensity A.firstDensity).map
        (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) ∧
    (physicalPairedRoute hL g m t r R C S u particle labels v steps d).map Prod.snd=
      ((physicalOnPrimary hL g m t r R C S u particle (v 0) d).withDensity A.secondDensity).map
        (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) := by
  have H := physicalPairedRoute_marginals hL g m t r R C S ht hr u particle labels v steps hc d hhome haccess
  rw [(A.laws hp).1] at H
  rw [(A.laws hp).2] at H
  exact H

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

instance physicalSharedOn_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→Fin 3→Fin K)
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) :
    IsFiniteMeasure (physicalSharedOn hL g m t r R C S u particle labels v steps d) := by
  unfold physicalSharedOn
  infer_instance

variable {N K M G n l : ℕ} {L : Length} (hL : L.val=(K:ℝ))
  (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
  (particle : J↪Fin N)
  (f : Fin (n+1)↪J) (v : Fin (n+2)→Fin 3→Fin K) (steps : Fin (n+1)→Fin 7)
  (f' : Fin (l+1)↪J) (v' : Fin (l+2)→Fin 3→Fin K) (steps' : Fin (l+1)→Fin 7)
  (d : PhysicalDatum N K M G L)
  (A : PhysicalRouteAux hL g m t r R C S u particle f v steps d)
  (B : PhysicalRouteAux hL g m t r R C S u particle f' v' steps' d)
  (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
  (hc' : ∀k,projectPoint L (routeCellPeriod (v' k.succ) (v' k.castSucc) (steps' k))=0)
  (hh : ∀k,datumHome hL d (particle (f k))=v k.castSucc)
  (hh' : ∀k,datumHome hL d (particle (f' k))=v' k.castSucc)
  (ha : ∀k,datumAccessible hL g m t r R C S u (particle (f k)) d)
  (ha' : ∀k,datumAccessible hL g m t r R C S u (particle (f' k)) d)
  (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
include ht hr hc hc' hh hh' ha ha' hp

lemma physical_first_RN_cross (he : v' (Fin.last (l+1))=v (Fin.last (n+1))) :
    let P := physicalPrimaryReference hL g m t r R C S u particle (v (Fin.last (n+1))) d
    (∫⁻z,((physicalPairedRoute hL g m t r R C S u particle f v steps d).map Prod.fst).rnDeriv P z *
      ((physicalPairedRoute hL g m t r R C S u particle f' v' steps' d).map Prod.fst).rnDeriv P z ∂P)=
    ∫⁻z,A.firstDensity z*B.firstDensity z
      ∂physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d := by
  dsimp only
  rw [(physicalPairedRoute_marginals hL g m t r R C S ht hr u particle f v steps hc d hh ha).1,
    (physicalPairedRoute_marginals hL g m t r R C S ht hr u particle f' v' steps' hc' d hh' ha').1,
    ←physicalPrimary_on_map hL g m t r R C S hr u particle _ d]
  apply mapped_likelihood_cross
    (physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d) _ _
    A.firstDensity B.firstDensity (A.firstDensity_measurable hp) (B.firstDensity_measurable hp)
    (A.laws hp).1 _ _ (physicalConfig_embedding hL g m r R C S u particle d)
  simpa only [he] using (B.laws hp).1

lemma physical_second_RN_cross (he : v' 0=v 0) :
    let P := physicalPrimaryReference hL g m t r R C S u particle (v 0) d
    (∫⁻z,((physicalPairedRoute hL g m t r R C S u particle f v steps d).map Prod.snd).rnDeriv P z *
      ((physicalPairedRoute hL g m t r R C S u particle f' v' steps' d).map Prod.snd).rnDeriv P z ∂P)=
    ∫⁻z,A.secondDensity z*B.secondDensity z
      ∂physicalOnPrimary hL g m t r R C S u particle (v 0) d := by
  dsimp only
  rw [(physicalPairedRoute_marginals hL g m t r R C S ht hr u particle f v steps hc d hh ha).2,
    (physicalPairedRoute_marginals hL g m t r R C S ht hr u particle f' v' steps' hc' d hh' ha').2,
    ←physicalPrimary_on_map hL g m t r R C S hr u particle _ d]
  apply mapped_likelihood_cross
    (physicalOnPrimary hL g m t r R C S u particle (v 0) d) _ _
    A.secondDensity B.secondDensity (A.secondDensity_measurable hp) (B.secondDensity_measurable hp)
    (A.laws hp).2 _ _ (physicalConfig_embedding hL g m r R C S u particle d)
  simpa only [he] using (B.laws hp).2

end HardSphere.Groups
end
end

end OAI
