import Mathlib
import OAI.Analysis.HardSphere.Allocation.CoarsePhysical

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma label_endpoints_ae {N : ℕ} {L : Length} (T : ℝ)
    (μ : Measure (BridgeEndpoints N L)) :
    ∀ᵐ z ∂μ.prod (Measure.pi fun _ : Fin N ↦ Bridge.law),
      labelBridgePath N L T z 0=z.1.2 ∧
      labelBridgePath N L T z 1=bridgeEnd N L T z.1 := by
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_eq_fun ((continuous_eval_const (0:Time)).measurable.comp
        (labelBridgePath_measurable N L T)) measurable_fst.snd).inter
      (measurableSet_eq_fun ((continuous_eval_const (1:Time)).measurable.comp
        (labelBridgePath_measurable N L T))
        ((bridgeEnd_continuous N L T).measurable.comp measurable_fst)))).mpr
  exact ae_of_all _ (exposed_endpoints T)

lemma physicalDatum_branch_of {N K M G : ℕ} {L : Length}
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time)
    (z : BridgeEndpoints N L × (Fin N→Bridge.Noise))
    (h0 : labelBridgePath N L T z 0=z.1.2)
    (h1 : labelBridgePath N L T z 1=bridgeEnd N L T z.1)
    (hb : z∈flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b) :
    physicalDatum g m r R C S s₀ u (labelBridgePath N L T z,a)=
      physicalBranchDatum g b a T (blockExpose (fun i ↦ i∈groupUnion g a) z) := by
  have hf : (fun i ↦ decide (∃v : Fin 3→Fin K,
      Eligible m r R C S s₀ u v i (labelBridgePath N L T z)))=b := by
    funext i
    have hi := hb i
    simpa only [eligibilityFlag,ownEligible,Eligible,h0,h1,ownPath_eq] using hi
  simp only [physicalDatum,physicalBranchDatum,h0,h1,hf,blockExpose]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_)))
  funext i
  by_cases hi : i∈groupUnion g a
  · simp only [ite_eq_left hi,dite_eq_left hi]
  · simp only [ite_eq_right hi,dite_eq_right hi]
    rw [labelBridgePath_lift]
    rfl

theorem actual_physical_branch_joint {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) :
    let p := fun i ↦ i∈groupUnion g a
    let B := labelInteraction N L r (2*t)∩
      flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b
    let ν := exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p B
    (ν.compProd (fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law))
      (blockEvent p B))).map (fun z ↦
        (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) (blockGlue p z),a),
          selectedPhysicalPath (L:=L) (2*t) p z)) =
    (ν.map (physicalBranchDatum g b a (2*t))).compProd
      (datumPhysicalReference hL g a m r R C S t u) := by
  dsimp only
  let p := fun i ↦ i∈groupUnion g a
  let B := labelInteraction N L r (2*t)∩
    flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b
  let μ₀ := allocationBase μ (gridAllocationKernel hL (G*M)) b a
  let ν := exposedLaw μ₀ (fun _ : Fin N ↦ Bridge.law) p B
  let κ := fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law)) (blockEvent p B)
  have hB : MeasurableSet B := (labelInteraction_measurable N L r (2*t)).inter
    (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b)
  have : SFinite ν := by dsimp [ν,exposedLaw]; infer_instance
  have hr := exposed_block_reconstruct μ₀ (fun _ : Fin N ↦ Bridge.law) p hB
  have he : ∀ᵐ z ∂((μ₀.prod (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict B),
      physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a)=
        physicalBranchDatum g b a (2*t) (blockExpose p z) := by
    filter_upwards [ae_restrict_of_ae (label_endpoints_ae (2*t) μ₀),ae_restrict_mem hB] with z hz hzB
    exact physicalDatum_branch_of g b a m r R C S s₀ (2*t) u z hz.1 hz.2 hzB.2
  have he' : ∀ᵐ z ∂ν.compProd κ,
      physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) (blockGlue p z),a)=
        physicalBranchDatum g b a (2*t) z.1 := by
    rw [←hr] at he
    have ht := ae_of_ae_map (blockGlue_measurable p).aemeasurable he
    have ht' := ht.mono (fun z hz ↦ show
        physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) (blockGlue p z),a)=
          physicalBranchDatum g b a (2*t) z.1 from by
      have hzg := congrFun (blockExpose_glue (E:=BridgeEndpoints N L)
        (X:=fun _ : Fin N ↦ Bridge.Noise) p) z
      simpa only [Function.comp_apply] using hz.trans (congrArg (physicalBranchDatum g b a (2*t)) hzg))
    dsimp only [ν,κ]
    convert ht' using 1
    congr 20
    all_goals try exact Subsingleton.elim _ _
  trans (ν.compProd κ).map (fun z ↦
    (physicalBranchDatum g b a (2*t) z.1,selectedPhysicalPath (L:=L) (2*t) p z))
  · apply Measure.map_congr
    filter_upwards [he'] with z hz
    exact Prod.ext hz rfl
  · exact coarse_joint_reference ν κ _ _ (physicalBranchDatum_measurable g b a (2*t))
      _ (selectedPhysicalPath_measurable (2*t) p)
      (actual_allocated_physical_coarse_fiber hL hK h50 μ m r R C S s₀ t u g b a)

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma individualReference_probability_of_nonzero (t : ℝ) (y z : Point)
    (E : Set C(Time,Point)) (h : individualReference t y z E≠0) :
    IsProbabilityMeasure (individualReference t y z E) := by
  have : IsProbabilityMeasure (law.map (leg (2*t) y z)) :=
    (Measure.isProbabilityMeasure_map_iff
      (leg_continuous (2*t) y z).measurable.aemeasurable).mpr inferInstance
  apply conditioned_probability
  intro hz
  apply h
  simp only [individualReference,Measure.restrict_eq_zero.mpr hz,smul_zero]

lemma datum_group_probability_factors {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) (d : PhysicalDatum N K M G L)
    (hmass : datumGroupReference hL g a m r R C S t u d univ=1) :
    ∀i : {i // i∈groupUnion g a},
      IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u i d) := by
  let μ := fun i : {i // i∈groupUnion g a} ↦ datumIndividualReference hL g m r R C S t u i d
  have : ∀i,IsFiniteMeasure (μ i) := fun _ ↦ inferInstance
  have hcond : conditionedMeasure (Measure.pi μ) (physicalMutual (L:=L) r) univ=1 := by
    simpa only [μ,datumGroupReference_apply,datumIndividualReference_apply] using hmass
  have hprod : (Measure.pi μ) univ≠0 := by
    intro hz
    have he : (Measure.pi μ) (physicalMutual (L:=L) r)=0 := measure_mono_null (subset_univ _) hz
    simp only [conditionedMeasure,Measure.restrict_eq_zero.mpr he,smul_zero,Measure.coe_zero,Pi.zero_apply] at hcond
    exact zero_ne_one hcond
  intro i
  rw [datumIndividualReference_apply]
  apply individualReference_probability_of_nonzero
  intro hz
  have hi : μ i=0 := by simpa only [μ,datumIndividualReference_apply] using hz
  apply hprod
  rw [Measure.pi_univ]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; rfl)

lemma exposed_fiber_mass {E I : Type*} [MeasurableSpace E] [Fintype I]
    {X : I→Type*} [∀i,MeasurableSpace (X i)]
    (μ : Measure E) [SFinite μ] (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I→Prop) [DecidablePred p] {B : Set (E×(∀i,X i))} (hB : MeasurableSet B) :
    ∀ᵐw ∂exposedLaw μ ν p B,
      fiberNormalize (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i))
        (blockGlue p ⁻¹' B) w univ=1 := by
  filter_upwards [exposed_block_positive μ ν p hB] with w hw
  exact fiberNormalize_mass (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i))
    (hB.preimage (blockGlue_measurable p)) hw

theorem actual_branch_normalized {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) :
    let p := fun i ↦ i∈groupUnion g a
    ∀ᵐw ∂exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      IsProbabilityMeasure (datumGroupReference hL g a m r R C S t u
        (physicalBranchDatum g b a (2*t) w)) ∧
      ∀i : {i // i∈groupUnion g a},IsProbabilityMeasure
        (datumIndividualReference hL g m r R C S t u i (physicalBranchDatum g b a (2*t) w)) := by
  dsimp only
  let p := fun i ↦ i∈groupUnion g a
  let B := labelInteraction N L r (2*t)∩
    flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b
  have hB : MeasurableSet B := (labelInteraction_measurable N L r (2*t)).inter
    (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b)
  have hpos := exposed_fiber_mass (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
    (fun _ : Fin N ↦ Bridge.law) p hB
  filter_upwards [actual_allocated_physical_coarse_fiber hL hK h50 μ m r R C S s₀ t u g b a,
    hpos] with w hw hp
  change (_ : ℝ≥0∞)=1 at hp
  have hh := congrArg (fun ν ↦ ν univ) hw
  rw [Measure.map_apply (by exact (selectedPhysicalPath_measurable (L:=L) (2*t) (fun i ↦ i∈groupUnion g a)).comp (measurable_const.prodMk measurable_id)) MeasurableSet.univ,preimage_univ] at hh
  change (fiberNormalize _ (blockGlue p ⁻¹' B) w) univ = _ at hh
  have hh' : (datumPhysicalReference hL g a m r R C S t u
      (physicalBranchDatum g b a (2*t) w)) univ=1 :=
    hh.symm.trans (by
      convert hp using 1
      congr
      exact Subsingleton.elim _ _)
  have hmass : datumGroupReference hL g a m r R C S t u (physicalBranchDatum g b a (2*t) w) univ=1 := by
    rw [datumPhysicalReference,Kernel.map_apply _ projectGroup_measurable,
      Measure.map_apply projectGroup_measurable MeasurableSet.univ,preimage_univ] at hh'
    exact hh'
  exact ⟨⟨hmass⟩,datum_group_probability_factors hL g a m r R C S t u _ hmass⟩

end HardSphere.Groups
end
end

end OAI
