import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.PhysicalScaleData
import OAI.Analysis.HardSphere.Allocation.PhysicalTaggedObservation

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

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalObservedMixture_mass_eq {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (b : Bool) (d : PhysicalDatum (N+1) K M G L) :
    physicalObservedMixture hL g m t r R C S u particle hxy ν b d univ=
      physicalMixedRoutes hL g m t r R C S u particle hxy ν d univ := by
  simp only [physicalObservedMixture,Kernel.snd_apply' _ _ MeasurableSet.univ,preimage_univ,
    Kernel.compProd_apply_univ]

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
theorem physicalObservedMixture_mass {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [SFinite μ] (E : Set (PhysicalDatum (N+1) K M G L))
    (q a : ℝ≥0∞) (ha0 : 0<a)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
    (hdata : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀i : Fin p.val.length,
        (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) ∧
      (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
      (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
        physicalCollisionReference hL g m t r R C S u particle d j
          {p | TrialCollision r (projectCurve L f.val) p.val}≤q) ∧
      IsProbabilityMeasure (physicalPrimaryReference hL g m t r R C S u particle (siteIndex y) d))
    (b : Bool) :
    ((μ.restrict E).compProd (physicalObservedMixture hL g m t r R C S u particle hxy ν b)) univ=μ E := by
  rw [Measure.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  have hh : ∀ᵐd ∂μ.restrict E,physicalObservedMixture hL g m t r R C S u particle hxy ν b d univ=1 := by
    filter_upwards [hdata] with d hd
    rw [physicalObservedMixture_mass_eq,physicalMixedRoutes_mass hL g m t r R C S ht hr u
      particle d hxy ν hd.1 hd.2.1 hd.2.2.1 q a ha0 hd.2.2.2.1 hsmall]
    let := hd.2.2.2.2
    exact measure_univ
  rw [lintegral_congr_ae hh]
  simp

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

instance physicalTaggedReference_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (b : Bool) (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ) := by
  unfold physicalTaggedReference taggedReference
  infer_instance

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalTaggedMixture_unretained {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [SFinite μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) :
    taggedPhysicalBathKernel particle b ∘ₘ physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E =
      physicalObservedMixture hL g m t r R C S u particle hxy ν b ∘ₘ μ.restrict E := by
  have H := congrArg (fun ρ ↦ ρ.map Prod.snd)
    (physicalTaggedMixture_observation hL g m t r R C S u particle hxy b ν μ E)
  rw [Measure.map_comp _ _ measurable_snd,←Measure.snd,Measure.snd_compProd] at H
  have he : (retainedTaggedPhysicalBath (K:=K) (M:=M) (G:=G) (L:=L) particle b).map Prod.snd=
      taggedPhysicalBathKernel particle b := by
    rw [←Kernel.snd_eq]
    unfold retainedTaggedPhysicalBath
    rw [Kernel.snd_prod]
  rw [he] at H
  exact H

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def physicalCommonObserved {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) (E : Set (PhysicalDatum (N+1) K M G L)) :=
  taggedPhysicalBathKernel particle false ∘ₘ physicalTaggedMixture hL g m t r R C S u particle hxy false ν μ E
instance physicalCommonObserved_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ] (E : Set (PhysicalDatum (N+1) K M G L)) :
    IsFiniteMeasure (physicalCommonObserved hL g m t r R C S u particle hxy ν μ E) := by
  unfold physicalCommonObserved; infer_instance

def physicalObservedReference {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (b : Bool) (μ : Measure (PhysicalDatum (N+1) K M G L)) :=
  taggedPhysicalBathKernel particle b ∘ₘ physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ
instance physicalObservedReference_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (b : Bool) (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (physicalObservedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ) := by
  unfold physicalObservedReference; infer_instance

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalCommonObserved_eq {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [SFinite μ] (E : Set (PhysicalDatum (N+1) K M G L))
    (ha : ∀ᵐd ∂μ.restrict E,∀ᵐp ∂ν d,∀i : Fin p.val.length,
      (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (b : Bool) :
    physicalCommonObserved hL g m t r R C S u particle hxy ν μ E=
      taggedPhysicalBathKernel particle b ∘ₘ physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E := by
  cases b
  · rfl
  · have H := congrArg (fun ρ ↦ ρ.map Prod.snd)
      (physicalTaggedMixture_same hL g m t r R C S ht u particle hxy ν μ E ha)
    have he (b : Bool) : (retainedTaggedPhysicalBath (K:=K) (M:=M) (G:=G) (L:=L) particle b).map Prod.snd=
        taggedPhysicalBathKernel particle b := by
      rw [←Kernel.snd_eq]; unfold retainedTaggedPhysicalBath; rw [Kernel.snd_prod]
    rw [Measure.map_comp _ _ measurable_snd,Measure.map_comp _ _ measurable_snd,he,he] at H
    exact H.symm

theorem physical_common_observed_estimates {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (hM : 0<M) (q : ℝ≥0∞) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1≤B) (hCpath : 0≤Cpath)
    (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
    (hdata : ∀ᵐd ∂μ.restrict E,PhysicalMomentData hL g m t r R C S u particle ν q d)
    (hprimary : ∀ᵐd ∂μ.restrict E,IsProbabilityMeasure (physicalPrimaryReference hL g m t r R C S u particle (siteIndex y) d))
    (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ)≤ENNReal.ofReal Cpath) :
    let σ := physicalCommonObserved hL g m t r R C S u particle hxy ν μ E
    σ univ=μ E ∧ ∀b,
      let P := physicalObservedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ
      σ≪P ∧ Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P ∧
        (∫z,(σ.rnDeriv P z).toReal^2 ∂P)≤B*Cpath := by
  dsimp only
  have ha : ∀ᵐd ∂μ.restrict E,∀ᵐp ∂ν d,∀i : Fin p.val.length,
      (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty :=
    hdata.mono (fun d hd ↦ hd.accessible hM)
  constructor
  · have H := physicalObservedMixture_mass hL g m t r R C S ht hr u particle hxy ν μ E q
      (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) hsmall
      (by filter_upwards [hdata,hprimary] with d hd hp; exact ⟨hd.accessible hM,hd.2.1,hd.2.2.1,hd.2.2.2,hp⟩) false
    rw [←physicalTaggedMixture_observation,Measure.comp_apply_univ] at H
    simpa only [physicalCommonObserved,Measure.comp_apply_univ] using H
  · intro b
    rw [physicalCommonObserved_eq hL g m t r R C S ht u particle hxy ν μ E ha b]
    refine ⟨physicalTagged_observed_ac hL g m t r R C S ht hr u particle hxy ν μ E hE
      (by filter_upwards [hdata] with d hd; exact ⟨hd.accessible hM,hd.2.2.1⟩) b (taggedPhysicalBathKernel particle b),?_⟩
    have H := physicalTagged_observed_moment hL g m t r R C S ht hr u particle hxy ν μ E hE hM
      q δ B κ Cpath hδ hB hCpath hBt hκ hsmall hdata henc b (taggedPhysicalBathKernel particle b)
    rw [←Measure.snd,Measure.snd_compProd,←Measure.snd,Measure.snd_compProd] at H
    exact H

end HardSphere.Groups
end
end

end OAI
