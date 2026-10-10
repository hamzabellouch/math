import Mathlib
import OAI.Analysis.HardSphere.Conditioning.GlobalExposure
import OAI.Analysis.HardSphere.Allocation.NearLift

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Comparison

lemma coarse_joint_reference {W D X Y : Type*} [MeasurableSpace W]
    [MeasurableSpace D] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure W) [SFinite μ] (κ : Kernel W X) [IsSFiniteKernel κ]
    (R : Kernel D Y) [IsSFiniteKernel R] (d : W→D) (hd : Measurable d)
    (f : W×X→Y) (hf : Measurable f)
    (h : ∀ᵐw ∂μ,(κ w).map (fun x ↦ f (w,x))=R (d w)) :
    (μ.compProd κ).map (fun p ↦ (d p.1,f p))=(μ.map d).compProd R := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hm : Measurable (fun p : W×X ↦ (d p.1,f p)) :=
    (hd.comp measurable_fst).prodMk hf
  rw [lintegral_map hF hm]
  have hFm : Measurable (fun p : W×X ↦ F (d p.1,f p)) := hF.comp hm
  rw [Measure.lintegral_compProd hFm,Measure.lintegral_compProd hF,
    lintegral_map (hF.lintegral_kernel_prod_right' (κ:=R)) hd]
  apply lintegral_congr_ae
  filter_upwards [h] with w hw
  rw [←hw]
  exact (lintegral_map (μ:=κ w)
    (show Measurable (fun y ↦ F (d w,y)) from hF.comp measurable_prodMk_left)
    (show Measurable (fun x ↦ f (w,x)) from hf.comp measurable_prodMk_left)).symm

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def physicalBranchDatum {N K M G : ℕ} {L : Length} (g : Fin G)
    (b : Fin N→Bool) (a : GridAllocation N K (G*M)) (T : ℝ)
    (w : BridgeEndpoints N L × ({i // i∉groupUnion g a}→Bridge.Noise)) :
    PhysicalDatum N K M G L :=
  (w.1.2,bridgeEnd N L T w.1,b,a,fun i ↦ if hi : i∈groupUnion g a then 0 else
    frozenPaths T w.1 (fun j ↦ j∈groupUnion g a) w.2 ⟨i,hi⟩)

lemma frozenPaths_joint_measurable {N : ℕ} {L : Length} (T : ℝ)
    (p : Fin N→Prop) (j : {i // ¬p i}) :
    Measurable (fun w : BridgeEndpoints N L × ({i // ¬p i}→Bridge.Noise) ↦
      frozenPaths T w.1 p w.2 j) := by
  have hp : Measurable (fun w : BridgeEndpoints N L × ({i // ¬p i}→Bridge.Noise) ↦
      (w.1,fillOutside p (fun _ ↦ (0 : Bridge.Noise)) w.2)) :=
    measurable_fst.prodMk ((fillOutside_measurable p (fun _ ↦ (0 : Bridge.Noise))).comp measurable_snd)
  have hω := (labelBridgePath_measurable N L T).comp hp
  have hm : Measurable (fun w : BridgeEndpoints N L × ({i // ¬p i}→Bridge.Noise) ↦
      onePathAt j (labelBridgePath N L T (w.1,fillOutside p (fun _ ↦ 0) w.2))) :=
    (onePathAt_continuous (j : Fin N)).measurable.comp hω
  simpa only [labelBridgePath_lift,fillOutside,dite_eq_right j.property,frozenPaths] using hm

lemma physicalBranchDatum_measurable {N K M G : ℕ} {L : Length} (g : Fin G)
    (b : Fin N→Bool) (a : GridAllocation N K (G*M)) (T : ℝ) :
    Measurable (physicalBranchDatum (L:=L) g b a T) := by
  unfold physicalBranchDatum
  apply measurable_fst.snd.prodMk
  apply ((bridgeEnd_continuous N L T).measurable.comp measurable_fst).prodMk
  apply measurable_const.prodMk
  apply measurable_const.prodMk
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈groupUnion g a
  · simpa only [dite_eq_left hi] using (measurable_const : Measurable
      (fun _ : BridgeEndpoints N L × ({i // i∉groupUnion g a}→Bridge.Noise) ↦
        (0 : ConfigurationPath 1 L)))
  · simpa only [dite_eq_right hi] using frozenPaths_joint_measurable (L:=L) T
      (fun j ↦ j∈groupUnion g a) (⟨i,hi⟩ : {i // i∉groupUnion g a})

lemma datumPermitted_branch {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S T : ℝ) (u : Time)
    (w : BridgeEndpoints N L × ({i // i∉groupUnion g a}→Bridge.Noise)) (i : Fin N) :
    Prod.mk (physicalBranchDatum g b a T w) ⁻¹' datumPermitted hL g m r R C S u i =
      permittedPath m r R C S u
        (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (w.1.2 i))
        (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (bridgeEnd N L T w.1 i))
        (anchorPoint (gridHome hL (w.1.2 i)))
        (frozenPaths T w.1 (fun j ↦ j∈groupUnion g a) w.2) := by
  ext f
  simp only [mem_preimage,datumPermitted,mem_ofPred_eq,physicalBranchDatum,
    datumStart,datumEnd,datumHome,datumSelected,permittedPath]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h j
    simpa only [dite_eq_right j.property] using h j j.property
  · intro h j hj
    simpa only [dite_eq_right hj] using h ⟨j,hj⟩

def datumIndividualReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S t : ℝ) (u : Time) (i : Fin N) :
    Kernel (PhysicalDatum N K M G L) C(Time,Point) :=
  parameterIndividualReference t (fun d ↦ datumStart hL d i) (fun d ↦ datumEnd hL d i)
    (datumStart_measurable hL i) (datumEnd_measurable hL i)
    (datumPermitted hL g m r R C S u i) (datumPermitted_measurable hL g m r R C S u i)

instance datumIndividualReference_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S t : ℝ) (u : Time) (i : Fin N) :
    IsFiniteKernel (datumIndividualReference (M:=M) hL g m r R C S t u i) :=
  inferInstanceAs (IsFiniteKernel (parameterIndividualReference ..))

lemma datumIndividualReference_apply {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S t : ℝ) (u : Time) (i : Fin N)
    (d : PhysicalDatum N K M G L) :
    datumIndividualReference hL g m r R C S t u i d=
      individualReference t (datumStart hL d i) (datumEnd hL d i)
        (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u i) :=
  parameterIndividualReference_apply ..

def datumGroupReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) :
    Kernel (PhysicalDatum N K M G L) ({i // i∈groupUnion g a}→C(Time,Point)) :=
  fiberNormalize (finiteKernelPi (fun i : {i // i∈groupUnion g a} ↦
    datumIndividualReference hL g m r R C S t u i))
    (Prod.snd ⁻¹' physicalMutual (L:=L) r)

instance datumGroupReference_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) :
    IsFiniteKernel (datumGroupReference hL g a m r R C S t u) :=
  inferInstanceAs (IsFiniteKernel (fiberNormalize ..))

lemma datumGroupReference_apply {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) (d : PhysicalDatum N K M G L) :
    datumGroupReference hL g a m r R C S t u d=
      conditionedMeasure (Measure.pi fun i : {i // i∈groupUnion g a} ↦
        individualReference t (datumStart hL d i) (datumEnd hL d i)
          (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u i)) (physicalMutual (L:=L) r) := by
  unfold datumGroupReference
  change (fiberRestrict _ _ d univ)⁻¹ • fiberRestrict _ _ d=_
  rw [fiberRestrict_apply _ ((physicalMutual_measurable r).preimage measurable_snd)]
  simp only [Measure.restrict_apply_univ,finiteKernelPi_apply,datumIndividualReference_apply]
  rfl

end HardSphere.Groups

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def projectGroup {I : Type*} {L : Length} (f : I→C(Time,Point)) :
    I→ ConfigurationPath 1 L := fun i ↦ projectCurve L (f i)
lemma projectGroup_measurable {I : Type*} {L : Length} :
    Measurable (projectGroup (I:=I) (L:=L)) :=
  Measurable.of_eval fun i ↦ (projectCurve_continuous L).measurable.comp (measurable_pi_apply i)

def selectedPhysicalPath {N : ℕ} {L : Length} (T : ℝ) (p : Fin N→Prop)
    (v : (BridgeEndpoints N L × ({i // ¬p i}→Bridge.Noise)) × ({i // p i}→Bridge.Noise)) :
    {i // p i}→ ConfigurationPath 1 L :=
  fun i ↦ onePathAt i (labelBridgePath N L T (blockGlue p v))
lemma selectedPhysicalPath_measurable {N : ℕ} {L : Length} (T : ℝ) (p : Fin N→Prop) :
    Measurable (selectedPhysicalPath (L:=L) T p) := by
  apply Measurable.of_eval
  intro i
  exact (onePathAt_continuous (i : Fin N)).measurable.comp
    ((labelBridgePath_measurable N L T).comp (blockGlue_measurable p))

lemma selectedPhysicalPath_apply {N : ℕ} {L : Length} (T : ℝ) (p : Fin N→Prop)
    (w : BridgeEndpoints N L × ({i // ¬p i}→Bridge.Noise))
    (β : {i // p i}→Bridge.Noise) (i : {i // p i}) :
    selectedPhysicalPath T p (w,β) i=
      projectCurve L (leg T (labelStartLift w.1 i) (labelEndLift T w.1 i) (β i)) := by
  unfold selectedPhysicalPath
  rw [labelBridgePath_lift,blockGlue_fst,blockGlue_inside]

def datumPhysicalReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) :
    Kernel (PhysicalDatum N K M G L) ({i // i∈groupUnion g a}→ ConfigurationPath 1 L) :=
  (datumGroupReference hL g a m r R C S t u).map projectGroup
instance datumPhysicalReference_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) :
    IsFiniteKernel (datumPhysicalReference hL g a m r R C S t u) := by
  unfold datumPhysicalReference
  infer_instance

theorem actual_allocated_physical_coarse_fiber {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) :
    let p := fun i ↦ i∈groupUnion g a
    ∀ᵐw ∂exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ((fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law))
        (blockEvent p (labelInteraction N L r (2*t)∩
          flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b))) w).map
        (fun β ↦ selectedPhysicalPath (L:=L) (2*t) p (w,β)) =
      datumPhysicalReference hL g a m r R C S t u (physicalBranchDatum g b a (2*t) w) := by
  dsimp only
  filter_upwards [actual_allocated_canonical_reference hL hK h50 μ m r R C S s₀ t u g b a] with w hw
  rw [datumPhysicalReference,Kernel.map_apply _ projectGroup_measurable,
    datumGroupReference_apply]
  simp only [datumPermitted_branch]
  simp only [datumStart,datumEnd,datumHome,physicalBranchDatum]
  have hh := congrArg (fun ν ↦ ν.map (projectGroup (L:=L))) hw
  have hm : Measurable (fun β : {i // i ∈ groupUnion g a} → Bridge.Noise ↦
      fun i : {i // i ∈ groupUnion g a} ↦ Bridge.shiftPath (canonicalShift hL w.1 i)
        (leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) (β i))) :=
    Measurable.of_eval fun i ↦
      (Bridge.shiftPath_continuous _).measurable.comp
        ((leg_continuous _ _ _).measurable.comp (measurable_pi_apply i))
  rw [Measure.map_map projectGroup_measurable hm] at hh
  rw [←hh]
  apply congrArg (Measure.map · _)
  funext β i
  simp only [Function.comp_apply,projectGroup,selectedPhysicalPath_apply,
    project_shift _ (canonicalShift_period hL w.1 i)]

end HardSphere.Groups
end
end

end OAI
