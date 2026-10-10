import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalAmbientRN
import OAI.Analysis.HardSphere.Allocation.PhysicalFamilyLikelihood

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [NeZero K] in
lemma simpleEncounter_comm (R : ℕ) (p q : SimplePath x y) :
    simpleEncounter R p q=simpleEncounter R q p := by
  unfold simpleEncounter
  apply Finset.card_bij (fun z _ ↦ z.swap)
  · intro z hz
    obtain ⟨hp,hq,hn⟩ := (mem_encounterSet _ _ _ _ _).mp hz
    exact (mem_encounterSet _ _ _ _ _).mpr ⟨hq,hp,torusNear_symm hn⟩
  · intro z _ w _ he
    exact Prod.swap_injective he
  · intro z hz
    obtain ⟨hp,hq,hn⟩ := (mem_encounterSet _ _ _ _ _).mp hz
    exact ⟨z.swap,(mem_encounterSet _ _ _ _ _).mpr ⟨hq,hp,torusNear_symm hn⟩,rfl⟩

theorem physicalCoded_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L) (hxy : x≠y)
    (p p' : SimplePath x y) (z z' : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (hz' : ∀v,z' v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (ha' : ∀i : Fin p'.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p' i.castSucc) d).Nonempty)
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q a : ℝ≥0∞) (ha0 : 0<a)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) (b : Bool) :
    (∫⁻w,physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p,z)) w *
      physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p',z')) w
      ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d)≤
      (routeDensityBound t)^(1+(fieldLabelImage p z∩fieldLabelImage p' z').card)*
        (a⁻¹)^(8*simpleEncounter 30 p p') := by
  have hv := routeFieldValid_of_supported hL g m t r R C S u particle d p z hz ha
  have hv' := routeFieldValid_of_supported hL g m t r R C S u particle d p' z' hz' ha'
  let f := fieldRouteLabels hxy p z hv
  let f' := fieldRouteLabels hxy p' z' hv'
  let v := simpleRouteVertices p (p.val.length-1)
  let v' := simpleRouteVertices p' (p'.val.length-1)
  let steps := simpleRouteSteps hL p _ (simpleRouteLength_eq hxy p)
  let steps' := simpleRouteSteps hL p' _ (simpleRouteLength_eq hxy p')
  have hc := simpleRouteSteps_period hL p _ (simpleRouteLength_eq hxy p)
  have hc' := simpleRouteSteps_period hL p' _ (simpleRouteLength_eq hxy p')
  have hh := fieldRouteLabels_physical hL g m t r R C S u particle d hxy p z hz ha hv
  have hh' := fieldRouteLabels_physical hL g m t r R C S u particle d hxy p' z' hz' ha' hv'
  let A := Classical.choice (physicalRouteAux_nonempty hL g m t r R C S u particle f v steps d ht hc
    (fun i ↦ (hh i).1) (fun i ↦ (hh i).2) hp)
  let B := Classical.choice (physicalRouteAux_nonempty hL g m t r R C S u particle f' v' steps' d ht hc'
    (fun i ↦ (hh' i).1) (fun i ↦ (hh' i).2) hp)
  have hn := simpleRouteVertices_distance hL p _ (simpleRouteLength_eq hxy p)
  have hn' := simpleRouteVertices_distance hL p' _ (simpleRouteLength_eq hxy p')
  have ha1 : 1≤a⁻¹ := ENNReal.one_le_inv.mpr ((le_add_right le_rfl).trans hsmall)
  have hover : (routeSlots f∩routeSlots f').card=1+(fieldLabelImage p z∩fieldLabelImage p' z').card :=
    fieldRoute_overlap hxy p p' z z' hv hv'
  have he0 : v 0=siteIndex x := simpleRouteVertices_zero p _
  have he0' : v' 0=siteIndex x := simpleRouteVertices_zero p' _
  have he1 : v (Fin.last (p.val.length-1+1))=siteIndex y := simpleRouteVertices_last p _ (simpleRouteLength_eq hxy p)
  have he1' : v' (Fin.last (p'.val.length-1+1))=siteIndex y := simpleRouteVertices_last p' _ (simpleRouteLength_eq hxy p')
  have HL := lintegral_congr_ae ((physicalRouteLikelihood_measure hL g m t r R C S u particle hxy b d (p,z)).mul
    (physicalRouteLikelihood_measure hL g m t r R C S u particle hxy b d (p',z')))
  simp only [Pi.mul_apply] at HL
  rw [HL]
  simp only [physicalCodedRoute,dite_eq_left hv,dite_eq_left hv']
  cases b with
  | true =>
    simp only [ite_true]
    have H := physical_first_likelihood_moment hL g m t r R C S ht u particle f v steps f' v' steps' d A B
      hc hc' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) (fun i ↦ (hh i).2) (fun i ↦ (hh' i).2)
      hn hn' (he1'.trans he1.symm) hm hp q a ha0 hq hsmall
    have Hrn := physical_first_RN_cross hL g m t r R C S ht hr u particle f v steps f' v' steps' d A B
      hc hc' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) (fun i ↦ (hh i).2) (fun i ↦ (hh' i).2) hp (he1'.trans he1.symm)
    rw [he1] at Hrn H
    rw [Hrn]
    apply H.trans
    rw [div_eq_mul_inv,ENNReal.inv_pow,hover]
    apply mul_le_mul' le_rfl
    apply pow_le_pow_right₀ ha1
    have h1 := simpleRoute_near_first p p' (simpleRouteLength_eq hxy p) (simpleRouteLength_eq hxy p')
      (fun j ↦ datumHome hL d (particle j)) f f' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) 30
    have h2 := simpleRoute_near_first p' p (simpleRouteLength_eq hxy p') (simpleRouteLength_eq hxy p)
      (fun j ↦ datumHome hL d (particle j)) f' f (fun i ↦ (hh' i).1) (fun i ↦ (hh i).1) 30
    rw [simpleEncounter_comm 30 p' p] at h2
    omega
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    have H := physical_second_likelihood_moment hL g m t r R C S ht u particle f v steps f' v' steps' d A B
      hc hc' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) (fun i ↦ (hh i).2) (fun i ↦ (hh' i).2)
      hn hn' (he0'.trans he0.symm) hm hp q a ha0 hq hsmall
    have Hrn := physical_second_RN_cross hL g m t r R C S ht hr u particle f v steps f' v' steps' d A B
      hc hc' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) (fun i ↦ (hh i).2) (fun i ↦ (hh' i).2) hp (he0'.trans he0.symm)
    rw [he0] at Hrn H
    rw [Hrn]
    apply H.trans
    rw [div_eq_mul_inv,ENNReal.inv_pow,hover]
    apply mul_le_mul' le_rfl
    apply pow_le_pow_right₀ ha1
    have h1 := simpleRoute_near_second p p' (simpleRouteLength_eq hxy p) (simpleRouteLength_eq hxy p')
      (fun j ↦ datumHome hL d (particle j)) f f' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) 30
    have h2 := simpleRoute_near_second p' p (simpleRouteLength_eq hxy p') (simpleRouteLength_eq hxy p)
      (fun j ↦ datumHome hL d (particle j)) f' f (fun i ↦ (hh' i).1) (fun i ↦ (hh i).1) 30
    rw [simpleEncounter_comm 30 p' p] at h2
    omega

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
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physicalCoded_density {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L) (hxy : x≠y)
    (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (b : Bool) :
    (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d).withDensity
      (physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p,z))) =
    (physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d).map
      (if b then Prod.fst else Prod.snd) := by
  have hv := routeFieldValid_of_supported hL g m t r R C S u particle d p z hz ha
  let f := fieldRouteLabels hxy p z hv
  let v := simpleRouteVertices p (p.val.length-1)
  let steps := simpleRouteSteps hL p _ (simpleRouteLength_eq hxy p)
  have hc := simpleRouteSteps_period hL p _ (simpleRouteLength_eq hxy p)
  have hh := fieldRouteLabels_physical hL g m t r R C S u particle d hxy p z hz ha hv
  let A := Classical.choice (physicalRouteAux_nonempty hL g m t r R C S u particle f v steps d ht hc
    (fun i ↦ (hh i).1) (fun i ↦ (hh i).2) hp)
  have hd := physicalPairedRoute_densities hL g m t r R C S ht hr u particle f v steps hc d
    (fun i ↦ (hh i).1) (fun i ↦ (hh i).2) A hp
  rw [withDensity_congr_ae (physicalRouteLikelihood_measure hL g m t r R C S u particle hxy b d (p,z))]
  have : IsFiniteMeasure (physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d) :=
    IsFiniteKernel.isFiniteMeasure (κ:=physicalCodedRoute hL g m t r R C S u particle hxy (p,z)) d
  have : IsFiniteMeasure (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d) :=
    IsFiniteKernel.isFiniteMeasure (κ:=physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x))) d
  have : IsFiniteMeasure ((physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d).map
      (if b then Prod.fst else Prod.snd)) := Measure.isFiniteMeasure_map _ _
  have := Measure.haveLebesgueDecomposition_of_sigmaFinite
    (μ:=(physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d).map (if b then Prod.fst else Prod.snd))
    (ν:=physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d)
  apply Measure.withDensity_rnDeriv_eq
  simp only [physicalCodedRoute,dite_eq_left hv]
  have hf : Measurable (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) :=
    routeConfigMap_measurable _ (fun _ ↦ measurable_subtype_coe)
  cases b with
  | true =>
    simp only [ite_true]
    rw [hd.1,←simpleRouteVertices_last p _ (simpleRouteLength_eq hxy p),
      ←physicalPrimary_on_map hL g m t r R C S hr u particle _ d]
    exact (withDensity_absolutelyContinuous _ _).map hf
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    rw [hd.2,←simpleRouteVertices_zero p _,←physicalPrimary_on_map hL g m t r R C S hr u particle _ d]
    exact (withDensity_absolutelyContinuous _ _).map hf

end HardSphere.Groups
end
end

end OAI
