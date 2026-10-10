import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalDisintegration

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma measurable_probability_kernel {D W : Type*} [MeasurableSpace D] [MeasurableSpace W]
    (κ : Kernel D W) : MeasurableSet {d | IsProbabilityMeasure (κ d)} := by
  simp only [isProbabilityMeasure_iff]
  exact measurableSet_eq_fun (κ.measurable_coe MeasurableSet.univ) measurable_const

attribute [local irreducible] datumGroupReference datumIndividualReference

def physicalBranchLaw {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) : Measure (PhysicalDatum N K M G L) :=
  (exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
    (fun _ : Fin N ↦ Bridge.law) (fun i ↦ i∈groupUnion g a)
    (labelInteraction N L r T∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b)).map
      (physicalBranchDatum g b a T)
instance physicalBranchLaw_sfinite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    SFinite (physicalBranchLaw hL μ g b a m r R C S s₀ T u) := by
  unfold physicalBranchLaw exposedLaw; infer_instance

lemma physicalBranchLaw_raw {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    physicalBranchLaw hL μ g b a m r R C S s₀ T u =
    (((allocationBase μ (gridAllocationKernel hL (G*M)) b a).prod
      (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict
      (labelInteraction N L r T∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b)).map
        (fun z ↦ physicalDatum g m r R C S s₀ u (labelBridgePath N L T z,a)) := by
  have hB := (labelInteraction_measurable N L r T).inter
    (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable (K:=K) m r R C S s₀ T u i) b)
  rw [physicalBranchLaw,exposedLaw_marginal _ _ _ hB,
    Measure.map_map (physicalBranchDatum_measurable g b a T) (blockExpose_measurable _)]
  apply Measure.map_congr
  filter_upwards [ae_restrict_of_ae (label_endpoints_ae T
    (allocationBase μ (gridAllocationKernel hL (G*M)) b a)),ae_restrict_mem hB] with z hz hb
  exact (physicalDatum_branch_of g b a m r R C S s₀ T u z hz.1 hz.2 hb.2).symm

lemma genuine_ground_allocated_raw {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (ψ : Jet N L)
    (m q : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    (∑b,∑a : GridAllocation N K q,
      (((allocationBase (endpointWeightedBase ψ T) (gridAllocationKernel hL q) b a).prod
        (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict
        (labelInteraction N L r T∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b)).map
          (fun z ↦ (labelBridgePath N L T z,a)))=
      (groundPathLaw N L r T ψ).compProd (physicalAllocationKernel (K:=K) m q r R C S s₀ u) := by
  let flag := eligibilityFlag (N:=N) (K:=K) (L:=L) m r R C S s₀ T u
  have hflag : ∀i,Measurable (flag i) := fun i ↦ eligibilityFlag_measurable m r R C S s₀ T u i
  let base := ((endpointWeightedBase ψ T).prod (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict
    (labelInteraction N L r T)
  have hr : Measurable (fun z : BridgeEndpoints N L×(Fin N→Bridge.Noise) ↦ fun i ↦ flag i (z.1,z.2 i)) :=
    Measurable.of_eval (fun i ↦ (hflag i).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hf : Measurable (fun z : (BridgeEndpoints N L×(Fin N→Bridge.Noise))×GridAllocation N K q ↦
      (labelBridgePath N L T z.1,z.2)) :=
    ((labelBridgePath_measurable N L T).comp measurable_fst).prodMk measurable_snd
  have H := congrArg (fun μ ↦ μ.map (fun z : (BridgeEndpoints N L×(Fin N→Bridge.Noise))×GridAllocation N K q ↦
      (labelBridgePath N L T z.1,z.2)))
    (allocated_flag_joint (endpointWeightedBase ψ T) (Measure.pi fun _ : Fin N ↦ Bridge.law)
      (gridAllocationKernel hL q) (fun z ↦ fun i ↦ flag i (z.1,z.2 i)) hr
      (labelInteraction_measurable N L r T))
  have hκ : ∀ᵐz ∂base,
      (gridAllocationKernel hL q).comap (fun z ↦ (z.1,fun i ↦ flag i (z.1,z.2 i)))
        (measurable_fst.prodMk hr) z =
      (physicalAllocationKernel (K:=K) m q r R C S s₀ u).comap (labelBridgePath N L T)
        (labelBridgePath_measurable N L T) z := by
    simpa only [Kernel.comap_apply] using
      (ae_restrict_of_ae (s:=labelInteraction N L r T)
        (recorded_allocation_is_physical hL hK (endpointWeightedBase ψ T) m q r R C S s₀ T u))
  rw [Measure.compProd_congr hκ,map_retained_compProd base _ (labelBridgePath_measurable N L T),
    show base.map (labelBridgePath N L T)=groundPathLaw N L r T ψ from genuine_ground_label_bridge ψ r T] at H
  simp only [Measure.map_finset_sum' hf.aemeasurable,
    Measure.map_map hf measurable_prodMk_right,Function.comp_def] at H
  rw [←H]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  have he : flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b=
      {z | (fun i ↦ flag i (z.1,z.2 i))=b} := by
    ext z
    exact funext_iff.symm
  rw [he]
  rfl

theorem physicalBranchLaw_sum {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (ψ : Jet N L) (g : Fin G) (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    (∑b,∑a : GridAllocation N K (G*M),physicalBranchLaw hL (endpointWeightedBase ψ T) g b a m r R C S s₀ T u)=
      physicalDatumLaw g ψ m r R C S s₀ T u := by
  have hd := physicalDatum_measurable (N:=N) (K:=K) (M:=M) (L:=L) g m r R C S s₀ u
  have H := congrArg (fun μ ↦ μ.map (physicalDatum (K:=K) (M:=M) g m r R C S s₀ u))
    (genuine_ground_allocated_raw hL hK ψ m (G*M) r R C S s₀ T u)
  dsimp only [physicalDatumLaw]
  rw [←H]
  simp only [Measure.map_finset_sum' hd.aemeasurable]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [physicalBranchLaw_raw,Measure.map_map hd ((labelBridgePath_measurable N L T).prodMk measurable_const)]
  rfl

lemma physicalBranchLaw_le {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (ψ : Jet N L) (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    physicalBranchLaw hL (endpointWeightedBase ψ T) g b a m r R C S s₀ T u ≤
      physicalDatumLaw g ψ m r R C S s₀ T u := by
  rw [←physicalBranchLaw_sum hL hK]
  calc
    _ ≤ ∑a' : GridAllocation N K (G*M), physicalBranchLaw hL (endpointWeightedBase ψ T) g b a' m r R C S s₀ T u :=
      Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ a)
    _ ≤ _ := Finset.single_le_sum (f:=fun b' : Fin N→Bool ↦ ∑a' : GridAllocation N K (G*M),
      physicalBranchLaw hL (endpointWeightedBase ψ T) g b' a' m r R C S s₀ T u)
      (fun _ _ ↦ bot_le) (Finset.mem_univ b)

lemma physicalBranchLaw_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    {ψ : Jet N L} {r : ℝ} (hψ : IsGroundVector N L r ψ)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (R C S s₀ T : ℝ) (hT : 0≤T) (u : Time) :
    IsFiniteMeasure (physicalBranchLaw hL (endpointWeightedBase ψ T) g b a m r R C S s₀ T u) := by
  let := physicalDatumLaw_probability (K:=K) (M:=M) g hψ m R C S s₀ T hT u
  exact isFiniteMeasure_of_le _ (physicalBranchLaw_le hL hK ψ g b a m r R C S s₀ T u)

theorem physicalBranchLaw_normalized {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u,
      IsProbabilityMeasure (datumGroupReference hL g a m r R C S t u d) ∧
      ∀i : {i // i∈groupUnion g a},IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u i.val d) := by
  apply (ae_map_iff (physicalBranchDatum_measurable g b a (2*t)).aemeasurable
    ((measurable_probability_kernel _).inter ?_)).mpr
      (actual_branch_normalized hL hK h50 μ m r R C S s₀ t u g b a)
  change MeasurableSet {d : PhysicalDatum N K M G L | ∀i : {i // i∈groupUnion g a},
    IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u i.val d)}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurable_probability_kernel _

end HardSphere.Groups
end
end

end OAI
