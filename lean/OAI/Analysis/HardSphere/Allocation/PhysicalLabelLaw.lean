import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalRouteGeometry
import OAI.Analysis.HardSphere.Allocation.PhysicalBranchLaw
import OAI.Analysis.HardSphere.Geometry.PhysicalGeometry

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
instance labelOptionSpace (J : Type*) : MeasurableSpace (Option J) := ⊤
instance labelOptionSingletons (J : Type*) : MeasurableSingletonClass (Option J) := ⟨fun _ ↦ trivial⟩

variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def paddedLabels (s : Finset J) : Finset (Option J) :=
  if s.Nonempty then s.image some else {none}
omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma paddedLabels_nonempty (s : Finset J) : (paddedLabels s).Nonempty := by
  by_cases h : s.Nonempty
  · simpa only [paddedLabels,ite_eq_left h] using h.image some
  · simp [paddedLabels,h]

def uniformLabels (s : Finset J) : Measure (Option J) :=
  (PMF.uniformOfFinset (paddedLabels s) (paddedLabels_nonempty s)).toMeasure
instance uniformLabels_probability (s : Finset J) : IsProbabilityMeasure (uniformLabels s) := by
  unfold uniformLabels; infer_instance

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma uniformLabels_supported (s : Finset J) : ∀ᵐ i ∂uniformLabels s,i∈paddedLabels s := by
  rw [ae_iff]
  change uniformLabels s ((↑(paddedLabels s) : Set (Option J))ᶜ)=0
  unfold uniformLabels
  rw [PMF.toMeasure_uniformOfFinset_apply _ _ (Set.to_countable _).measurableSet]
  simp

def branchAccessible {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (v : DiscreteTorus K) (d : PhysicalDatum N K M G L) : Finset J :=
  Finset.univ.filter fun j ↦ particle j∈datumAccessibleLabels hL g m t r R C S u (siteIndex v) d

omit [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma branchAccessible_measurable {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (v : DiscreteTorus K) : Measurable (branchAccessible (M:=M) hL g m t r R C S u particle v) := by
  exact (measurable_of_countable (f:=fun s : Finset (Fin N) ↦
    Finset.univ.filter fun j ↦ particle j∈s)).comp (datumAccessibleLabels_measurable hL g m t r R C S u _)

def physicalLabelAt {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (v : DiscreteTorus K) : Kernel (PhysicalDatum N K M G L) (Option J) where
  toFun d := uniformLabels (branchAccessible hL g m t r R C S u particle v d)
  measurable' := (measurable_of_countable (f:=uniformLabels (J:=J))).comp
    (branchAccessible_measurable hL g m t r R C S u particle v)

instance physicalLabelAt_markov {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (v : DiscreteTorus K) : IsMarkovKernel (physicalLabelAt (M:=M) hL g m t r R C S u particle v) :=
  ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (uniformLabels _))⟩

def physicalLabels {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N) :
    Kernel (PhysicalDatum N K M G L) (DiscreteTorus K→Option J) :=
  finiteKernelPi (physicalLabelAt hL g m t r R C S u particle)
instance physicalLabels_markov {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N) :
    IsMarkovKernel (physicalLabels (M:=M) hL g m t r R C S u particle) := by
  constructor
  intro d
  rw [physicalLabels,finiteKernelPi_apply]
  infer_instance

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalLabels_supported {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (d : PhysicalDatum N K M G L) :
    ∀ᵐ z ∂physicalLabels hL g m t r R C S u particle d,
      ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d) := by
  rw [physicalLabels,finiteKernelPi_apply]
  apply ae_all_iff.mpr
  intro v
  exact (measurePreserving_eval (fun v ↦ physicalLabelAt hL g m t r R C S u particle v d) v).quasiMeasurePreserving.ae
    (uniformLabels_supported _)

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
attribute [local irreducible] datumHome datumSelected groupUnion datumStart datumEnd anchorPoint

lemma physicalBranchLaw_ae {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time)
    (P : PhysicalDatum N K M G L→Prop) (hPm : MeasurableSet {d | P d})
    (hP : ∀ω : ConfigurationPath N L,
      (∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support) →
      P (physicalDatum g m r R C S s₀ u (ω,a))) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ T u,P d := by
  rw [physicalBranchLaw_raw]
  have hm : Measurable (fun z : BridgeEndpoints N L×(Fin N→Bridge.Noise) ↦
      physicalDatum g m r R C S s₀ u (labelBridgePath N L T z,a)) :=
    (physicalDatum_measurable g m r R C S s₀ u).comp
      ((labelBridgePath_measurable N L T).prodMk measurable_const)
  apply (ae_map_iff hm.aemeasurable hPm).mpr
  have hB := (labelInteraction_measurable N L r T).inter
    (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable (K:=K) m r R C S s₀ T u i) b)
  have hs := allocationBase_ae_support μ (gridAllocationKernel hL (G*M)) b a
    (fun e a' ↦ ∀v,a' v∈(allocationPMF (recordedList hL v (e,b)) (G*M)).support)
    (fun e ↦ gridAllocation_support_ae hL (G*M) (e,b))
  filter_upwards [ae_restrict_of_ae (Measure.quasiMeasurePreserving_fst.ae hs),
    ae_restrict_of_ae (label_endpoints_ae T (allocationBase μ (gridAllocationKernel hL (G*M)) b a)),
    ae_restrict_mem hB] with z hz hz01 hzB
  apply hP _
  intro v
  have hb : (fun i ↦ eligibilityFlag (K:=K) m r R C S s₀ T u i (z.1,z.2 i))=b := funext hzB.2
  have he := recordedList_eq hL hK m r R C S s₀ T u v z.1 z.2 hz01.1 hz01.2
  rw [hb] at he
  simpa only [←he] using hz v

lemma physicalBranchLaw_allocation {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ T u,d.2.2.2.1=a := by
  apply (ae_map_iff (physicalBranchDatum_measurable g b a T).aemeasurable
    (measurableSet_eq_fun measurable_snd.snd.snd.fst measurable_const)).mpr
  exact ae_of_all _ fun _ ↦ rfl

lemma physicalBranchLaw_multiplicity {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ T u, ∀v,
      (Finset.univ.filter (fun i : {i // i∈groupUnion g a} ↦ datumHome hL d i=v)).card≤M := by
  apply physicalBranchLaw_ae hL hK μ g b a m r R C S s₀ T u _ ?_
    (fun ω hω v ↦ physicalDatum_group_multiplicity hL hK g m r R C S s₀ u ω a hω v)
  have hf : Measurable (fun d : PhysicalDatum N K M G L ↦ fun i : {i // i∈groupUnion g a} ↦ datumHome hL d i.val) :=
    Measurable.of_eval (fun i ↦ datumHome_measurable hL i.val)
  exact hf ((Set.to_countable {f : {i // i∈groupUnion g a}→(Fin 3→Fin K) |
      ∀v,(Finset.univ.filter (fun i ↦ f i=v)).card≤M}).measurableSet)

lemma datum_norm_geometry_measurableSet {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (i : Fin N) :
    MeasurableSet {d : PhysicalDatum N K M G L |
      ‖datumStart hL d i-anchorPoint (datumHome hL d i)‖≤3 ∧
      ‖datumEnd hL d i-anchorPoint (datumHome hL d i)‖≤3} := by
  have hs := datumStart_measurable (N:=N) (K:=K) (M:=M) (G:=G) hL i
  have he := datumEnd_measurable (N:=N) (K:=K) (M:=M) (G:=G) hL i
  have hc := datumAnchor_measurable (N:=N) (K:=K) (M:=M) (G:=G) hL i
  exact (measurableSet_le (hs.sub hc).norm measurable_const).inter
    (measurableSet_le (he.sub hc).norm measurable_const)

lemma datum_sep_geometry_measurableSet {N K M G : ℕ} {L : Length} (s₀ : ℝ) (i j : Fin N) :
    MeasurableSet {d : PhysicalDatum N K M G L |
      s₀<torusDistance L (d.1 i) (d.1 j) ∧ s₀<torusDistance L (d.2.1 i) (d.2.1 j)} := by
  have h₀ : Measurable (fun d : PhysicalDatum N K M G L ↦ (d.1 i,d.1 j)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_fst)
  have h₁ : Measurable (fun d : PhysicalDatum N K M G L ↦ (d.2.1 i,d.2.1 j)) :=
    ((measurable_pi_apply i).comp measurable_snd.fst).prodMk ((measurable_pi_apply j).comp measurable_snd.fst)
  exact (measurableSet_lt measurable_const ((torusDistance_continuous_pair L).measurable.comp h₀)).inter
    (measurableSet_lt measurable_const ((torusDistance_continuous_pair L).measurable.comp h₁))

lemma datum_geometry_measurableSet {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (s₀ : ℝ) (s : Finset (Fin N)) :
    MeasurableSet {d : PhysicalDatum N K M G L | ∀i : {i // i∈s},
      ‖datumStart hL d i-anchorPoint (datumHome hL d i)‖≤3 ∧
      ‖datumEnd hL d i-anchorPoint (datumHome hL d i)‖≤3 ∧
      ∀j : Fin N,j≠i→s₀<torusDistance L (projectPoint L (datumStart hL d i)) (projectPoint L (datumStart hL d j)) ∧
        s₀<torusDistance L (projectPoint L (datumEnd hL d i)) (projectPoint L (datumEnd hL d j))} := by
  have hsep (i : Fin N) : MeasurableSet {d : PhysicalDatum N K M G L | ∀j : Fin N,j≠i→
      s₀<torusDistance L (projectPoint L (datumStart hL d i)) (projectPoint L (datumStart hL d j)) ∧
      s₀<torusDistance L (projectPoint L (datumEnd hL d i)) (projectPoint L (datumEnd hL d j))} := by
    simp only [datumStart,datumEnd,nearestLift_project,Set.ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦ datum_sep_geometry_measurableSet s₀ i j
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have h := (datum_norm_geometry_measurableSet (M:=M) (G:=G) hL i.val).inter (hsep i.val)
  convert h using 1
  ext d
  exact and_assoc.symm

lemma physicalBranchLaw_geometry {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ T u, ∀i : {i // i∈groupUnion g a},
      ‖datumStart hL d i-anchorPoint (datumHome hL d i)‖≤3 ∧
      ‖datumEnd hL d i-anchorPoint (datumHome hL d i)‖≤3 ∧
      ∀j : Fin N,j≠i→s₀<torusDistance L (projectPoint L (datumStart hL d i)) (projectPoint L (datumStart hL d j)) ∧
        s₀<torusDistance L (projectPoint L (datumEnd hL d i)) (projectPoint L (datumEnd hL d j)) := by
  exact physicalBranchLaw_ae hL hK μ g b a m r R C S s₀ T u _
    (datum_geometry_measurableSet hL s₀ (groupUnion g a))
    (fun ω hω (i : {i // i∈groupUnion g a}) ↦ physicalDatum_selected_geometry hL hK g m r R C S s₀ u ω a hω i.val i.property)

lemma branchAccessible_card {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M)) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (v : HardSphere.Lattice.DiscreteTorus K) (d : PhysicalDatum N K M G L) (hd : d.2.2.2.1=a) :
    (branchAccessible hL g m t r R C S u (fun i : {i // i∈groupUnion g a} ↦ i.val) v d).card=
      (datumAccessibleLabels hL g m t r R C S u (siteIndex v) d).card := by
  let s := branchAccessible hL g m t r R C S u (fun i : {i // i∈groupUnion g a} ↦ i.val) v d
  have he : s.image Subtype.val=datumAccessibleLabels hL g m t r R C S u (siteIndex v) d := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      have hsel : i∈groupUnion g a := by
        have h := (Finset.mem_filter.mp hi).1
        simpa only [datumSelected,hd] using h
      exact Finset.mem_image.mpr ⟨⟨i,hsel⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  rw [←he,Finset.card_image_of_injective _ Subtype.val_injective]

lemma branchAccessible_supply {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M)) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (v : HardSphere.Lattice.DiscreteTorus K) (d : PhysicalDatum N K M G L) (hd : d.2.2.2.1=a)
    (hv : siteIndex v∉datumBad hL g m t r R C S u d) :
    (M:ℝ)≤2*((branchAccessible hL g m t r R C S u (fun i : {i // i∈groupUnion g a} ↦ i.val) v d).card:ℝ) := by
  rw [branchAccessible_card hL g a m t r R C S u v d hd]
  have hh : M≤2*(datumAccessibleLabels hL g m t r R C S u (siteIndex v) d).card := by
    simpa only [datumBad,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hv
  exact_mod_cast hh

end HardSphere.Groups
end
end

end OAI
