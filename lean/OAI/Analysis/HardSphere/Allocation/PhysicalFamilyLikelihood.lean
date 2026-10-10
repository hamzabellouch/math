import Mathlib
import OAI.Analysis.HardSphere.Conditioning.RouteMatches
import OAI.Analysis.HardSphere.Allocation.RouteFields

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalRouteView {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) :=
  (physicalRouteFamily (M:=M) hL g m t r R C S u particle hxy).map
    (if b then Prod.fst else Prod.snd)
instance physicalRouteView_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) :
    IsFiniteKernel (physicalRouteView (M:=M) hL g m t r R C S u particle hxy b) := by
  unfold physicalRouteView; infer_instance

def physicalFamilyReference {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N) (b : Bool) :
    Kernel (PhysicalDatum N K M G L×PhysicalRouteCode x y J) (Option J→C(Time,Point)) :=
  (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x))).comap
    Prod.fst measurable_fst
instance physicalFamilyReference_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N) (b : Bool) :
    IsFiniteKernel (physicalFamilyReference (M:=M) (x:=x) (y:=y) hL g m t r R C S u particle b) := by
  unfold physicalFamilyReference; infer_instance

def physicalRouteLikelihood {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) :=
  Kernel.rnDeriv (physicalRouteView (M:=M) hL g m t r R C S u particle hxy b)
    (physicalFamilyReference hL g m t r R C S u particle b)
lemma physicalRouteLikelihood_measurable {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) :
    Measurable (fun z : (PhysicalDatum N K M G L×PhysicalRouteCode x y J)×(Option J→C(Time,Point)) ↦ physicalRouteLikelihood (M:=M) hL g m t r R C S u particle hxy b z.1 z.2) :=
  Kernel.measurable_rnDeriv _ _
lemma physicalRouteLikelihood_measure {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (d : PhysicalDatum N K M G L) (c : PhysicalRouteCode x y J) :
    physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,c)=ᵐ[
      physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d]
      ((physicalCodedRoute hL g m t r R C S u particle hxy c d).map
        (if b then Prod.fst else Prod.snd)).rnDeriv
      (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d) := by
  have hb : Measurable (if b then (Prod.fst : (Option J→C(Time,Point))×(Option J→C(Time,Point))→_) else Prod.snd) := by
    cases b
    · exact measurable_snd
    · exact measurable_fst
  have H := Kernel.rnDeriv_eq_rnDeriv_measure
    (κ:=physicalRouteView (M:=M) hL g m t r R C S u particle hxy b)
    (η:=physicalFamilyReference hL g m t r R C S u particle b) (a:=(d,c))
  simpa only [physicalRouteLikelihood,physicalRouteView,physicalFamilyReference,
    Kernel.comap_apply,Kernel.map_apply _ hb,physicalRouteFamily,Kernel.coe_mk] using H

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Comparison HardSphere.Lattice
attribute [local instance] Classical.propDecidable

lemma uniformFinset_subtype {J : Type*} [Fintype J] [DecidableEq J]
    [MeasurableSpace J] [MeasurableSingletonClass J] (s : Finset J) (hs : s.Nonempty) :
    have : Nonempty s := hs.to_subtype
    ((PMF.uniformOfFintype s).toMeasure).map (Subtype.val : s→J)=
      (PMF.uniformOfFinset s hs).toMeasure := by
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton j),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j)]
  by_cases hj : j∈s
  · have he : (Subtype.val : s→J) ⁻¹' {j}={⟨j,hj⟩} := by ext a; simp [Subtype.ext_iff]
    rw [he,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp only [PMF.uniformOfFintype_apply,PMF.uniformOfFinset_apply,hj,ite_true,Fintype.card_coe]
  · have he : (Subtype.val : s→J) ⁻¹' {j}=∅ := by
      ext a
      simp only [mem_preimage,mem_singleton_iff,mem_empty_iff_false,iff_false]
      intro h
      exact hj (h ▸ a.property)
    rw [he,measure_empty]
    simp only [PMF.uniformOfFinset_apply,hj,ite_false]

lemma paddedLabels_card {J : Type*} [DecidableEq J] (s : Finset J) (hs : s.Nonempty) :
    (paddedLabels s).card=s.card := by
  rw [paddedLabels,ite_eq_left hs,Finset.card_image_of_injective _ (Option.some_injective _)]

lemma label_pair_transport {V J : Type*} [Fintype V] [Fintype J] [DecidableEq J]
    [MeasurableSpace J] [MeasurableSingletonClass J] (s : V→Finset J) :
    let A := fun v ↦ paddedLabels (s v)
    have : ∀v,Nonempty (A v) := fun v ↦ (paddedLabels_nonempty (s v)).to_subtype
    MeasurePreserving (fun z : ∀v,A v×A v ↦ (fun v ↦ (z v).1.val,fun v ↦ (z v).2.val))
      (Measure.pi fun v ↦ (PMF.uniformOfFintype (A v)).toMeasure.prod
        (PMF.uniformOfFintype (A v)).toMeasure)
      ((Measure.pi fun v ↦ uniformLabels (s v)).prod (Measure.pi fun v ↦ uniformLabels (s v))) := by
  dsimp only
  let A := fun v ↦ paddedLabels (s v)
  have : ∀v,Nonempty (A v) := fun v ↦ (paddedLabels_nonempty (s v)).to_subtype
  have hp (v : V) : MeasurePreserving (Subtype.val : A v→Option J)
      (PMF.uniformOfFintype (A v)).toMeasure (uniformLabels (s v)) :=
    ⟨measurable_subtype_coe,uniformFinset_subtype (A v) (paddedLabels_nonempty (s v))⟩
  exact (measurePreserving_arrowProdEquivProdArrow (Option J) (Option J) V
      (fun v ↦ uniformLabels (s v)) (fun v ↦ uniformLabels (s v))).comp
    (measurePreserving_pi _ _ (fun v ↦ (hp v).prod (hp v)))

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Comparison HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def fieldLabelImage (p : SimplePath x y) (z : DiscreteTorus K→Option J) : Finset (Option J) :=
  Finset.univ.image (fun i : Fin p.val.length ↦ z (pathVertexEmbedding p i.castSucc))

lemma padded_label_overlap (p q : SimplePath x y) (s : DiscreteTorus K→Finset J)
    (home : J→DiscreteTorus K)
    (hn : ∀v∈departureSites p∪departureSites q,(s v).Nonempty)
    (hh : ∀v∈departureSites p∪departureSites q,∀j∈s v,home j=v)
    (G M : ℝ) (hG : 1≤G) (hM : 0<M)
    (hm : ∀v∈departureSites p∩departureSites q,M≤2*((s v).card:ℝ)) :
    (∫z : (DiscreteTorus K→Option J)×(DiscreteTorus K→Option J),
      G^(1+(fieldLabelImage p z.1∩fieldLabelImage q z.2).card)
      ∂(Measure.pi (fun v ↦ uniformLabels (s v))).prod (Measure.pi (fun v ↦ uniformLabels (s v))))≤
      G*Real.exp ((2*(G-1)/M)*((departureSites p∩departureSites q).card:ℝ)) := by
  let A := fun v ↦ paddedLabels (s v)
  have : ∀v,Nonempty (A v) := fun v ↦ (paddedLabels_nonempty (s v)).to_subtype
  have ha : ∀v∈departureSites p∪departureSites q,∀a : A v,
      a.val.elim x home=v := by
    intro v hv a
    have h := a.property
    change a.val∈paddedLabels (s v) at h
    rw [paddedLabels,ite_eq_left (hn v hv)] at h
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
    rw [←he]
    exact hh v hv j hj
  have hc : ∀v∈departureSites p∩departureSites q,M≤2*(Fintype.card (A v):ℝ) := by
    intro v hv
    rw [Fintype.card_coe]
    change M≤2*((paddedLabels (s v)).card:ℝ)
    rw [paddedLabels_card _ (hn v (Finset.mem_union_left _ (Finset.mem_inter.mp hv).1))]
    exact hm v hv
  have H := route_label_integral p q (fun o : Option J ↦ o.elim x home) (fun v ↦ (A v : Type _)) (fun _ a ↦ a.val)
    (fun _ _ ↦ Subtype.val_injective) ha G M hG hM hc
  have hmap := (label_pair_transport s).map_eq
  rw [←hmap,integral_map (label_pair_transport s).measurable.aemeasurable
    ((measurable_of_countable _ : Measurable (fun z : (DiscreteTorus K→Option J)×(DiscreteTorus K→Option J) ↦
      G^(1+(fieldLabelImage p z.1∩fieldLabelImage q z.2).card))).aestronglyMeasurable)]
  exact H

omit [NeZero K] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma fieldLabelImage_eq (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : RouteFieldValid p z) :
    fieldLabelImage p z=(Finset.univ.image (fieldLabels p z hz)).image some := by
  simp only [fieldLabelImage,fieldLabels_spec p z hz,Finset.image_image,Function.comp_def]

omit [NeZero K] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma fieldRoute_overlap (hxy : x≠y) (p q : SimplePath x y)
    (z w : DiscreteTorus K→Option J) (hz : RouteFieldValid p z) (hw : RouteFieldValid q w) :
    (routeSlots (fieldRouteLabels hxy p z hz)∩routeSlots (fieldRouteLabels hxy q w hw)).card=
      1+(fieldLabelImage p z∩fieldLabelImage q w).card := by
  rw [fieldRouteLabels,fieldRouteLabels,routeSlots_reparam,routeSlots_reparam,
    routeSlots_inter_card,fieldLabelImage_eq p z hz,fieldLabelImage_eq q w hw,
    ←Finset.image_inter _ _ (Option.some_injective J),
    Finset.card_image_of_injective _ (Option.some_injective J)]

end HardSphere.Groups
end
end

end OAI
