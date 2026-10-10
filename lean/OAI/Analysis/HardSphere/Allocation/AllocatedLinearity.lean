import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalCellUniform
import OAI.Analysis.HardSphere.Allocation.PhysicalReferenceRaw

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {Ω A G Y J : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
  [Fintype A] [DecidableEq A] [Fintype G] [DecidableEq G] [Fintype J]
omit [DecidableEq A] [Fintype G] [DecidableEq G] in
lemma allocatedTagLaw_sum (μ : J→Measure Ω) (I : G→Ω→Finset A)
    (hI : ∀g i,MeasurableSet {ω | i∈I g ω}) (κ : A→Kernel Ω Y) (g : G) :
    allocatedTagLaw (∑j,μ j) I κ g=∑j,allocatedTagLaw (μ j) I κ g := by
  classical
  apply Measure.ext
  intro s hs
  simp only [allocatedTagLaw,Measure.finsetSum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Measure.bind_apply hs (κ i).aemeasurable,←lintegral_indicator (hI g i)]
  exact lintegral_finsetSum_measure _ _ _
end HardSphere.Comparison
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
attribute [local instance] Comparison.permBathSpace Comparison.permBathSingleton

def physicalRead {N K M G : ℕ} (L : Length) (extra tag : Fin 3→Fin K) (b : Bool)
    (i : Fin (N+1)) : Kernel (ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M))
      (Torus L×Torus L×Configuration N L) :=
  ((physicalCellPost L extra tag b) ∘ₖ orderedKernel (uniformBathOrder N) i).comap
    (fun p ↦ p.1 midpointTime) ((continuous_eval_const midpointTime).measurable.comp measurable_fst)

lemma physical_branch_allocated_reference {N K M G : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints (N+1) L)) [SFinite μ]
    (g : Fin G) (flags : Fin (N+1)→Bool) (a : GridAllocation (N+1) K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (extra tag : Fin 3→Fin K) (b : Bool) :
    taggedPhysicalBathKernel (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) b ∘ₘ
      taggedReference
        ((physicalBranchLaw hL μ g flags a m r R C S s₀ (2*t) u).compProd
          (physicalPrimaryReference hL g m t r R C S u
            (fun i : {i // i∈groupUnion g a} ↦ i.val) extra))
        (physicalTagEvent (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) tag) =
    allocatedTagLaw ((rawPhysicalBranch hL μ g flags a m r R C S s₀ (2*t) u).map
      (fun z ↦ (labelBridgePath (N+1) L (2*t) z,a)))
      (fun g p ↦ groupUnion g p.2) (physicalRead L extra tag b) g := by
  classical
  rw [physical_branch_observed_reference hL hK h50]
  unfold allocatedTagLaw
  apply Finset.sum_congr rfl
  intro i _
  have hmap : Measurable (fun z ↦ (labelBridgePath (N+1) L (2*t) z,a)) :=
    (labelBridgePath_measurable (N+1) L (2*t)).prodMk measurable_const
  have hA : MeasurableSet {p : ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M) | i∈groupUnion g p.2} :=
    ((measurable_of_countable (fun a ↦ i∈groupUnion g a)).comp measurable_snd).setOf
  rw [Measure.restrict_map hmap hA]
  by_cases hi : i∈groupUnion g a
  · rw [ite_eq_left hi]
    have he : (fun z ↦ (labelBridgePath (N+1) L (2*t) z,a)) ⁻¹'
        {p : ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M) | i∈groupUnion g p.2}=univ := by
      ext z; simp [hi]
    rw [he,Measure.restrict_univ,physicalRead,comp_comap_map,
      Measure.map_map (show Measurable (fun p : ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M) ↦ p.1 midpointTime) from
        (continuous_eval_const midpointTime).measurable.comp measurable_fst) hmap]
    rfl
  · rw [ite_eq_right hi]
    have he : (fun z ↦ (labelBridgePath (N+1) L (2*t) z,a)) ⁻¹'
        {p : ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M) | i∈groupUnion g p.2}=∅ := by
      ext z; simp [hi]
    simp [he]

theorem physical_branch_reference_sum {N K M G : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (ψ : Jet (N+1) L) (g : Fin G) (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (extra tag : Fin 3→Fin K) (b : Bool) :
    (∑flags,∑a : GridAllocation (N+1) K (G*M),
      taggedPhysicalBathKernel (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) b ∘ₘ
        taggedReference
          ((physicalBranchLaw hL (endpointWeightedBase ψ (2*t)) g flags a m r R C S s₀ (2*t) u).compProd
            (physicalPrimaryReference hL g m t r R C S u
              (fun i : {i // i∈groupUnion g a} ↦ i.val) extra))
          (physicalTagEvent (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) tag)) =
    allocatedTagLaw ((groundPathLaw (N+1) L r (2*t) ψ).compProd
      (physicalAllocationKernel m (G*M) r R C S s₀ u))
      (fun g p ↦ groupUnion g p.2) (physicalRead L extra tag b) g := by
  have hI : ∀g : Fin G,∀i : Fin (N+1),MeasurableSet
      {p : ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M) | i∈groupUnion g p.2} := by
    intro g i
    exact ((measurable_of_countable (fun a ↦ i∈groupUnion g a)).comp measurable_snd).setOf
  simp_rw [physical_branch_allocated_reference hL hK h50]
  simp_rw [←allocatedTagLaw_sum _ _ hI]
  congr 1
  exact genuine_ground_allocated_raw hL hK ψ m (G*M) r R C S s₀ (2*t) u

theorem physical_allocated_reference_le {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (R C S s₀ t : ℝ) (ht : 0≤t) (u : Time)
    (extra tag : Fin 3→Fin K) (b : Bool) :
    (∑g : Fin G,allocatedTagLaw ((groundPathLaw (N+1) L r (2*t) ψ).compProd
      (physicalAllocationKernel m (G*M) r R C S s₀ u))
      (fun g p ↦ groupUnion g p.2) (physicalRead L extra tag b) g) ≤
    (N+1) • (physicalCellPost L extra tag b ∘ₘ
      (((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration N L ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2)))) := by
  have hT : 0≤2*t := mul_nonneg (by norm_num) ht
  let := hψ.groundPathLaw_probability hT
  refine (sum_physical_group_tags_le hL hK m r R C S s₀ u _ _).trans ?_
  simp_rw [physicalRead,comp_comap_map,allocation_slice_law hψ (2*t) hT midpointTime]
  exact le_of_eq (all_tags_reference ψ hψ.2.1 hψ.2.2.1 (uniformBathOrder N) (physicalCellPost L extra tag b))

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

def physicalCellVolumePost {N K : ℕ} (L : Length) (extra tag : Fin 3→Fin K) (b : Bool) :
    Kernel (Torus L×Configuration N L) (Torus L×Torus L×Configuration N L) :=
  (cellExtraKernel volume (centeredCell L (gridCenter L tag))
    (centeredCell L (gridCenter L extra)) (centeredCell_measurable L _)).map (cellObservation b)

theorem physicalCellPost_le {N K : ℕ} [NeZero K] {L : Length} (hL : 1≤L.val)
    (extra tag : Fin 3→Fin K) (b : Bool) (P : Measure (Torus L×Configuration N L)) [SFinite P] :
    physicalCellPost L extra tag b ∘ₘ P≤physicalCellVolumePost L extra tag b ∘ₘ P := by
  rw [physicalCellPost,physicalCellVolumePost,←Measure.map_comp _ _ (cellObservation_measurable b),
    ←Measure.map_comp _ _ (cellObservation_measurable b)]
  apply Measure.map_mono _ (cellObservation_measurable b)
  rw [cellExtraKernel,cellExtraKernel,restrict_kernel_comp,restrict_kernel_comp,
    ←Measure.compProd_eq_comp_prod,←Measure.compProd_eq_comp_prod,
    Measure.compProd_const,Measure.compProd_const,Measure.restrict_univ]
  apply Measure.restrict_mono_measure
  exact Measure.prod_mono le_rfl (cellPathReference_midpoint_le hL extra)

theorem physical_all_references_le {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (R C S s₀ t : ℝ) (ht : 0≤t) (u : Time)
    (extra tag : Fin 3→Fin K) (b : Bool) :
    (∑g : Fin G,∑flags,∑a : GridAllocation (N+1) K (G*M),
      taggedPhysicalBathKernel (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) b ∘ₘ
        taggedReference
          ((physicalBranchLaw hL (endpointWeightedBase ψ (2*t)) g flags a m r R C S s₀ (2*t) u).compProd
            (physicalPrimaryReference hL g m t r R C S u
              (fun i : {i // i∈groupUnion g a} ↦ i.val) extra))
          (physicalTagEvent (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) tag)) ≤
    (N+1) • (physicalCellVolumePost L extra tag b ∘ₘ
      (((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration N L ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2)))) := by
  simp_rw [physical_branch_reference_sum hL hK h50]
  exact (physical_allocated_reference_le hL hK hψ m R C S s₀ t ht u extra tag b).trans
    (nsmul_le_nsmul_right (physicalCellPost_le (by linarith) extra tag b _) (N+1))

end HardSphere.Groups
end
end

end OAI
