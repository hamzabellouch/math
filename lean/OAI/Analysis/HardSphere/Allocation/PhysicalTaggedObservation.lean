import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalTaggedDensity
import OAI.Analysis.HardSphere.Allocation.PhysicalObservedMixture
import OAI.Analysis.HardSphere.Conditioning.RetainedObservation

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def retainedTaggedPhysicalBath {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1)) (b : Bool) :=
  (Kernel.deterministic (fun z : Fin (N+1)×(PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point))) ↦ z.2.1)
    measurable_snd.fst) ×ₖ taggedPhysicalBathKernel particle b
instance retainedTaggedPhysicalBath_markov {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1)) (b : Bool) :
    IsMarkovKernel (retainedTaggedPhysicalBath (K:=K) (M:=M) (G:=G) (L:=L) particle b) := by
  unfold retainedTaggedPhysicalBath; infer_instance
instance physicalTaggedMixture_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) :
    IsFiniteMeasure (physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E) := by
  unfold physicalTaggedMixture; infer_instance

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
theorem physicalTaggedMixture_observation {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [SFinite μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) :
    (retainedTaggedPhysicalBath particle b) ∘ₘ
      physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E =
    (μ.restrict E).compProd (physicalObservedMixture hL g m t r R C S u particle hxy ν b) := by
  unfold physicalTaggedMixture retainedTaggedPhysicalBath
  rw [conditional_tag_observation _ _ _ _ (measurable_of_countable _) _]
  unfold physicalRouteView
  rw [conditional_observation_map _ _ _ (by cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]; exact measurable_snd; exact measurable_fst) _ (measurable_of_countable _) _]
  cases b <;> rfl

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
theorem physicalTaggedMixture_same {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [SFinite μ]
    (E : Set (PhysicalDatum (N+1) K M G L))
    (ha : ∀ᵐd ∂μ.restrict E,∀ᵐp ∂ν d,∀i : Fin p.val.length,
      (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) :
    (retainedTaggedPhysicalBath particle true) ∘ₘ
      physicalTaggedMixture hL g m t r R C S u particle hxy true ν μ E =
    (retainedTaggedPhysicalBath particle false) ∘ₘ
      physicalTaggedMixture hL g m t r R C S u particle hxy false ν μ E := by
  rw [physicalTaggedMixture_observation,physicalTaggedMixture_observation]
  exact physicalObservedMixture_same_joint hL g m t r R C S ht u particle hxy ν μ E ha

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
theorem physicalTagged_observed_ac {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (hdata : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀i : Fin p.val.length,
        (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)))
    (b : Bool) {Y : Type*} [MeasurableSpace Y]
    (obs : Kernel (Fin (N+1)×(PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point)))) Y) :
    obs ∘ₘ physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E ≪
      obs ∘ₘ physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ := by
  have H := physicalTaggedMixture_density_support hL g m t r R C S ht hr u particle hxy ν μ E hE hdata b
  have hd := tagged_density_of_ae_support _ _ _ (physicalTagEvent_measurable particle _)
    _ H.1 H.2
  have ha : physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E ≪
      physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ := by
    rw [hd]
    exact withDensity_absolutelyContinuous _ _
  exact ha.comp_right obs

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [NeZero K] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalOnPrimary_mass {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (hr : r≤1) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    physicalOnPrimary hL g m t r R C S u particle v d univ=
      physicalPrimaryReference hL g m t r R C S u particle v d univ := by
  rw [←physicalPrimary_on_map hL g m t r R C S hr u particle v d]
  rw [Measure.map_apply (routeConfigMap_measurable _ (fun _ ↦ measurable_subtype_coe)) MeasurableSet.univ]
  rfl

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
theorem physicalCodedRoute_mass {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L) (hxy : x≠y)
    (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q a : ℝ≥0∞) (ha0 : 0<a)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
    physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d univ=
      physicalPrimaryReference hL g m t r R C S u particle (siteIndex y) d univ := by
  have hv := routeFieldValid_of_supported hL g m t r R C S u particle d p z hz ha
  have hphys := fieldRouteLabels_physical hL g m t r R C S u particle d hxy p z hz ha hv
  rw [physicalCodedRoute,dite_eq_left hv,
    physicalPairedRoute_mass_from_allowed hL g m t r R C S ht hr u particle _ _ _
      (simpleRouteSteps_period hL p _ (simpleRouteLength_eq hxy p)) d (fun i ↦ (hphys i).1) (fun i ↦ (hphys i).2)]
  rw [physicalSharedOn_mass hL g m t r R C S ht u particle _ _ _
    (simpleRouteSteps_period hL p _ (simpleRouteLength_eq hxy p)) d (fun i ↦ (hphys i).1) (fun i ↦ (hphys i).2)
    (simpleRouteVertices_distance hL p _ (simpleRouteLength_eq hxy p)) hm hp q a ha0 hq hsmall]
  rw [physicalOnPrimary_mass hL g m t r R C S hr u,
    simpleRouteVertices_last p _ (simpleRouteLength_eq hxy p)]

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
theorem physicalMixedRoutes_mass {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (ha : ∀ᵐp ∂ν d,∀i : Fin p.val.length,
      (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q a : ℝ≥0∞) (ha0 : 0<a)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
    physicalMixedRoutes hL g m t r R C S u particle hxy ν d univ=
      physicalPrimaryReference hL g m t r R C S u particle (siteIndex y) d univ := by
  rw [physicalMixedRoutes,Kernel.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  have hae : ∀ᵐc ∂(ν.prod (physicalLabels hL g m t r R C S u particle)) d,
      physicalRouteFamily hL g m t r R C S u particle hxy (d,c) univ=
        physicalPrimaryReference hL g m t r R C S u particle (siteIndex y) d univ := by
    rw [Kernel.prod_apply]
    apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
    filter_upwards [ha] with p hpPath
    filter_upwards [physicalLabels_supported hL g m t r R C S u particle d] with z hz
    exact physicalCodedRoute_mass hL g m t r R C S ht hr u particle d hxy p z hz hpPath hm hp q a ha0 hq hsmall
  rw [lintegral_congr_ae hae]
  simp

end HardSphere.Groups
end
end

end OAI
