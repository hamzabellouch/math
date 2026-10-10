import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalCodedMoment
import OAI.Analysis.HardSphere.Comparison.PhysicalObservedLaw

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalCodeTag {N : ℕ} (particle : J↪Fin (N+1)) (hxy : x≠y)
    (b : Bool) (c : PhysicalRouteCode x y J) : Fin (N+1) :=
  if h : RouteFieldValid c.1 c.2 then
    particle (fieldRouteLabels hxy c.1 c.2 h (if b then 0 else Fin.last (c.1.val.length-1)))
  else 0

def taggedPhysicalBathKernel {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1)) (b : Bool) :
    Kernel (Fin (N+1)×(PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point))))
      (Torus L×Torus L×(Fin N→Torus L)) where
  toFun z := primaryBathKernel b z.1 (physicalFullMidpoint particle z.2)
  measurable' := measurable_from_prod_countable_right fun i ↦
    (primaryBathKernel b i).measurable.comp (physicalFullMidpoint_measurable particle)
instance taggedPhysicalBathKernel_markov {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1)) (b : Bool) :
    IsMarkovKernel (taggedPhysicalBathKernel (K:=K) (M:=M) (G:=G) (L:=L) particle b) :=
  ⟨fun z ↦ inferInstanceAs (IsProbabilityMeasure (primaryBathKernel b z.1 (physicalFullMidpoint particle z.2)))⟩

def physicalCodeObserver {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool) :
    Kernel (PhysicalDatum (N+1) K M G L×(PhysicalRouteCode x y J×((Option J→C(Time,Point))×(Option J→C(Time,Point)))))
      (Torus L×Torus L×(Fin N→Torus L)) :=
  (taggedPhysicalBathKernel particle b).comap
    (fun z ↦ (physicalCodeTag particle hxy b z.2.1,(z.1,if b then z.2.2.1 else z.2.2.2)))
    (by
      apply Measurable.prodMk
      · exact (measurable_of_countable (physicalCodeTag particle hxy b)).comp measurable_snd.fst
      · cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> exact measurable_fst.prodMk (by fun_prop))
instance physicalCodeObserver_markov {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool) :
    IsMarkovKernel (physicalCodeObserver (M:=M) (G:=G) (L:=L) particle hxy b) := by
  unfold physicalCodeObserver; infer_instance

theorem physicalCodedRoute_same_observed {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin (N+1)) (d : PhysicalDatum (N+1) K M G L) (hxy : x≠y)
    (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) :
    ((physicalCodeObserver particle hxy true).comap (fun w ↦ (d,((p,z),w)))
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))) ∘ₘ
        physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d =
    ((physicalCodeObserver particle hxy false).comap (fun w ↦ (d,((p,z),w)))
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))) ∘ₘ
        physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d := by
  have hv := routeFieldValid_of_supported hL g m t r R C S u particle d p z hz ha
  have hh := fieldRouteLabels_physical hL g m t r R C S u particle d hxy p z hz ha hv
  have H := physicalPairedRoute_same_observed hL g m t r R C S ht u particle
    (fieldRouteLabels hxy p z hv) (simpleRouteVertices p (p.val.length-1))
    (simpleRouteSteps hL p _ (simpleRouteLength_eq hxy p))
    (simpleRouteSteps_period hL p _ (simpleRouteLength_eq hxy p)) d
    (fun i ↦ (hh i).1) (fun i ↦ (hh i).2)
  simp only [physicalCodedRoute,dite_eq_left hv]
  convert H using 2 <;>
    (funext w
     simp only [physicalCodeObserver,Kernel.comap_apply,taggedPhysicalBathKernel,Kernel.coe_mk,
       physicalCodeTag,dite_eq_left hv,ite_true,Bool.false_eq_true,ite_false,physicalBathKernel])

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
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [NeZero K] in
lemma unitTarget_project {L : Length} (hL : 1≤L.val) (v : Fin 3→Fin K) (z : Point)
    (hz : z∈unitTarget (anchorPoint v)) : projectPoint L z∈centeredCell L (gridCenter L v) := by
  rw [centeredCell_image hL]
  intro j
  have hj := hz j (mem_univ j)
  refine ⟨z j-(v j:ℝ),⟨?_,?_⟩,?_⟩
  · change (v j:ℝ)-1/2≤z j ∧ z j<(v j:ℝ)+1/2 at hj
    linarith [hj.1]
  · change (v j:ℝ)-1/2≤z j ∧ z j<(v j:ℝ)+1/2 at hj
    linarith [hj.2]
  · change ((z j-(v j:ℝ):ℝ):AddCircle L.val)=((z j:ℝ):AddCircle L.val)-((v j:ℝ):AddCircle L.val)
    exact QuotientAddGroup.mk_sub _ _ _

omit [NeZero K] in
lemma cellPathReference_support {L : Length} (hL : 1≤L.val) (v : Fin 3→Fin K) :
    ∀ᵐp ∂cellPathReference v,projectPoint L (p midpointTime)∈centeredCell L (gridCenter L v) := by
  have hm : Measurable (fun p : C(Time,Point) ↦ projectPoint L (p midpointTime)) :=
    (projectPoint_continuous L).measurable.comp (continuous_eval_const midpointTime).measurable
  rw [cellPathReference,ae_map_iff pointAsPath_measurable.aemeasurable ((centeredCell_measurable L _).preimage hm)]
  unfold targetUniform
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem (unitTarget_measurable (anchorPoint v))] with z hz
  exact unitTarget_project hL v z hz

omit [DecidableEq J] in
lemma physicalPrimary_extra {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    ∀ᵐw ∂physicalPrimaryReference hL g m t r R C S u particle v d,
      physicalFullMidpoint particle (d,w) none∈centeredCell L (gridCenter L v) := by
  have hL1 : 1≤L.val := by rw [hL]; exact_mod_cast NeZero.pos K
  have hextra := (Measure.quasiMeasurePreserving_eval
    (fun i ↦ physicalSlotReference hL g m t r R C S u particle v i d) none).ae (cellPathReference_support hL1 v)
  rw [physicalPrimaryReference_apply,conditionedMeasure]
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_of_ae hextra] with w hw
  change fillGroup particle _ _ (optionParticle particle none)∈_
  rw [fillGroup_selected]
  exact hw

def physicalTagEvent {N M G : ℕ} {L : Length} (particle : J↪Fin N)
    (v : Fin 3→Fin K) (i : Fin N) : Set (PhysicalDatum N K M G L×(Option J→C(Time,Point))) :=
  {z | i∈Set.range particle ∧ physicalFullMidpoint particle z (some i)∈centeredCell L (gridCenter L v)}
omit [NeZero K] [DecidableEq J] in
lemma physicalTagEvent_measurable {N M G : ℕ} {L : Length} (particle : J↪Fin N)
    (v : Fin 3→Fin K) (i : Fin N) : MeasurableSet (physicalTagEvent (M:=M) (G:=G) (L:=L) particle v i) :=
  .inter (show MeasurableSet {z : PhysicalDatum N K M G L×(Option J→C(Time,Point)) | i∈Set.range particle} from by
    by_cases h : i∈Set.range particle <;> simp [h]) ((centeredCell_measurable L _).preimage
    ((measurable_pi_apply (some i)).comp (physicalFullMidpoint_measurable particle)))

theorem physicalCodedRoute_tag_support {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (d : PhysicalDatum (N+1) K M G L) (hxy : x≠y)
    (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) (b : Bool) :
    ∀ᵐw ∂physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d,
      (d,if b then w.1 else w.2)∈physicalTagEvent particle (siteIndex (if b then x else y))
        (physicalCodeTag particle hxy b (p,z)) := by
  have he (b : Bool) : ∀ᵐw ∂physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d,
      physicalFullMidpoint particle (d,if b then w.1 else w.2) none∈
        centeredCell L (gridCenter L (siteIndex (if b then y else x))) := by
    have hd := physicalCoded_density hL g m t r R C S ht hr u particle d hxy p z hz ha hp b
    have h := (withDensity_absolutelyContinuous _ (physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p,z)))).ae_le (physicalPrimary_extra hL g m t r R C S u particle (siteIndex (if b then y else x)) d)
    rw [hd] at h
    have hf : Measurable (if b then (Prod.fst : ((Option J→C(Time,Point))×(Option J→C(Time,Point)))→_) else Prod.snd) := by cases b <;> simp <;> fun_prop
    have hm : Measurable (fun w : Option J→C(Time,Point) ↦ physicalFullMidpoint particle (d,w) none) :=
      (measurable_pi_apply none).comp ((physicalFullMidpoint_measurable particle).comp measurable_prodMk_left)
    have h' := (ae_map_iff hf.aemeasurable ((centeredCell_measurable L _).preimage hm)).mp h
    cases b <;> simpa using h'
  have hv := routeFieldValid_of_supported hL g m t r R C S u particle d p z hz ha
  have hh := fieldRouteLabels_physical hL g m t r R C S u particle d hxy p z hz ha hv
  have hmid := physicalPairedRoute_midpoint hL g m t r R C S ht u particle
    (fieldRouteLabels hxy p z hv) (simpleRouteVertices p (p.val.length-1))
    (simpleRouteSteps hL p _ (simpleRouteLength_eq hxy p))
    (simpleRouteSteps_period hL p _ (simpleRouteLength_eq hxy p)) d
    (fun i ↦ (hh i).1) (fun i ↦ (hh i).2)
  have hmid' : ∀ᵐw ∂physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d,
      ∀i,physicalFullMidpoint particle (d,w.2) i=physicalFullMidpoint particle (d,w.1)
        (routePermutation ((fieldRouteLabels hxy p z hv).trans particle) i) := by
    simpa only [physicalCodedRoute,dite_eq_left hv] using hmid
  filter_upwards [he true,he false,hmid'] with w h1 h2 hm
  cases b with
  | true =>
    simp only [physicalTagEvent,mem_ofPred_eq,physicalCodeTag,dite_eq_left hv,ite_true]
    refine ⟨⟨_,rfl⟩,?_⟩
    have H := hm none
    rw [routePermutation_star] at H
    simp only [Function.Embedding.trans_apply] at H
    change physicalFullMidpoint particle (d,w.1) (some (particle (fieldRouteLabels hxy p z hv 0)))∈_
    rw [←H]
    exact h2
  | false =>
    simp only [physicalTagEvent,mem_ofPred_eq,physicalCodeTag,dite_eq_left hv,Bool.false_eq_true,ite_false]
    refine ⟨⟨_,rfl⟩,?_⟩
    have H := hm (some (particle (fieldRouteLabels hxy p z hv (Fin.last (p.val.length-1)))))
    change physicalFullMidpoint particle (d,w.2) (some (((fieldRouteLabels hxy p z hv).trans particle) (Fin.last (p.val.length-1)))) = physicalFullMidpoint particle (d,w.1) (routePermutation ((fieldRouteLabels hxy p z hv).trans particle) (some (((fieldRouteLabels hxy p z hv).trans particle) (Fin.last (p.val.length-1))))) at H
    rw [routePermutation_lastLabel] at H
    simp only [Function.Embedding.trans_apply] at H
    rw [H]
    exact h1

end HardSphere.Groups
end
end

end OAI
