import Mathlib
import OAI.Analysis.HardSphere.Comparison.ConditionalTagDensity
import OAI.Analysis.HardSphere.Allocation.PhysicalMixedObservation
import OAI.Analysis.HardSphere.Allocation.PhysicalAverageMoment

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def physicalTaggedMixture {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) (E : Set (PhysicalDatum (N+1) K M G L)) :=
  (((μ.restrict E).compProd ((ν.prod (physicalLabels hL g m t r R C S u particle))⊗ₖ
    physicalRouteView hL g m t r R C S u particle hxy b)).map
      (fun z ↦ (physicalCodeTag particle hxy b z.2.1,(z.1,z.2.2))))

def physicalTagLikelihood {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y))
    (E : Set (PhysicalDatum (N+1) K M G L)) :=
  conditionalTagLikelihood (ν.prod (physicalLabels hL g m t r R C S u particle))
    (physicalCodeTag particle hxy b)
    (fun z ↦ physicalRouteLikelihood hL g m t r R C S u particle hxy b z.1 z.2) E

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalTagLikelihood_measurable {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsSFiniteKernel ν]
    (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E) (i : Fin (N+1)) :
    Measurable (physicalTagLikelihood hL g m t r R C S u particle hxy b ν E i) :=
  conditionalTagLikelihood_measurable _ _ (measurable_of_countable _) _
    (physicalRouteLikelihood_measurable hL g m t r R C S u particle hxy b) E hE i

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalTagLikelihood_sum {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y))
    (E : Set (PhysicalDatum (N+1) K M G L))
    (z : PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point))) :
    (∑i,physicalTagLikelihood hL g m t r R C S u particle hxy b ν E i z)=
      physicalGoodLikelihood hL g m t r R C S u particle hxy b ν E z := by
  exact conditionalTagLikelihood_sum _ _ (measurable_of_countable _) _
    (physicalRouteLikelihood_measurable hL g m t r R C S u particle hxy b) E z

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
theorem physicalTaggedMixture_density_support {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [SFinite μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (hdata : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀i : Fin p.val.length,
        (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)))
    (b : Bool) :
    physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E =
      (Measure.count.prod (μ.compProd (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x))))).withDensity
        (fun z ↦ physicalTagLikelihood hL g m t r R C S u particle hxy b ν E z.1 z.2) ∧
    (∀ᵐz ∂physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E,
      z.2∈physicalTagEvent particle (siteIndex (if b then x else y)) z.1) := by
  have hb : Measurable (if b then (Prod.fst : ((Option J→C(Time,Point))×(Option J→C(Time,Point)))→_) else Prod.snd) := by
    cases b <;> simp <;> fun_prop
  have hd : ∀ᵐd ∂μ.restrict E,∀ᵐc ∂(ν.prod (physicalLabels hL g m t r R C S u particle)) d,
      physicalRouteView hL g m t r R C S u particle hxy b (d,c)=
        (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d).withDensity
          (physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,c)) := by
    filter_upwards [hdata] with d hd
    rw [Kernel.prod_apply]
    apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
    filter_upwards [hd.1] with p hp
    filter_upwards [physicalLabels_supported hL g m t r R C S u particle d] with z hz
    simpa only [physicalRouteView,Kernel.map_apply _ hb,physicalRouteFamily,Kernel.coe_mk] using
      (physicalCoded_density hL g m t r R C S ht hr u particle d hxy p z hz hp hd.2 b).symm
  constructor
  · exact conditionalTagged_density μ _ _ _ _ (measurable_of_countable _) _
      (physicalRouteLikelihood_measurable hL g m t r R C S u particle hxy b) E hE hd
  · apply conditionalTagged_support μ _ _ _ (measurable_of_countable _) E _
      (physicalTagEvent_measurable particle (siteIndex (if b then x else y)))
    filter_upwards [hdata] with d hd
    rw [Kernel.prod_apply]
    apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
    filter_upwards [hd.1] with p hp
    filter_upwards [physicalLabels_supported hL g m t r R C S u particle d] with z hz
    simp only [physicalRouteView,Kernel.map_apply _ hb,physicalRouteFamily,Kernel.coe_mk]
    rw [ae_map_iff hb.aemeasurable ((physicalTagEvent_measurable particle _ _).preimage measurable_prodMk_left)]
    have H := physicalCodedRoute_tag_support hL g m t r R C S ht hr u particle d hxy p z hz hp hd.2 b
    cases b <;> simpa using H

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def physicalTaggedReference {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (b : Bool) (μ : Measure (PhysicalDatum (N+1) K M G L)) :=
  taggedReference (μ.compProd (physicalPrimaryReference hL g m t r R C S u particle
    (siteIndex (if b then y else x)))) (physicalTagEvent particle (siteIndex (if b then x else y)))

theorem physicalTagged_observed_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (hM : 0<M) (q : ℝ≥0∞) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1≤B) (hCpath : 0≤Cpath)
    (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
    (hdata : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀v∈departureSites p,(M:ℝ)≤2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ)) ∧
      (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
      (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
        physicalCollisionReference hL g m t r R C S u particle d j
          {p | TrialCollision r (projectCurve L f.val) p.val}≤q))
    (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ)≤ENNReal.ofReal Cpath)
    (b : Bool) {Y : Type*} [MeasurableSpace Y]
    (obs : Kernel (Fin (N+1)×(PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point)))) Y)
    [IsMarkovKernel obs] :
    Integrable (fun z ↦ ((((physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E).compProd obs).map Prod.snd).rnDeriv
      (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) z).toReal^2)
      (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) ∧
    (∫z,((((physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E).compProd obs).map Prod.snd).rnDeriv
      (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) z).toReal^2
      ∂((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd)≤B*Cpath := by
  have ha : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀i : Fin p.val.length,
        (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) := by
    filter_upwards [hdata] with d hd
    refine ⟨?_,hd.2.2.1⟩
    filter_upwards [hd.1] with p hp
    intro i
    apply Finset.card_pos.mp
    have H := hp _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    have hM' : (0:ℝ)<M := by exact_mod_cast hM
    have H' : (0:ℝ)<(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).card := by linarith
    exact_mod_cast H'
  have hd := physicalTaggedMixture_density_support hL g m t r R C S ht hr u particle hxy ν μ E hE ha b
  apply tagged_observed_of_density _ _ _ (physicalTagEvent_measurable particle _)
    _ (physicalTagLikelihood_measurable hL g m t r R C S u particle hxy b ν E hE)
    hd.1 hd.2 obs (B*Cpath) (mul_nonneg (le_trans zero_le_one hB) hCpath)
  simp_rw [physicalTagLikelihood_sum]
  rw [ENNReal.ofReal_mul (le_trans zero_le_one hB)]
  exact physicalGoodLikelihood_moment hL g m t r R C S ht hr u particle hxy ν μ E hE
    hM q δ B κ Cpath hδ hB hBt hκ hsmall hdata henc b

end HardSphere.Groups
end
end

end OAI
