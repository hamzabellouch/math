import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.ExpInteriorUnique
import OAI.Analysis.BiholderTransport.Coordinates.ExpNonconjugacy

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma interior_minimizingVectors_subset (x : M) :
    interior (minimizingVectors (n := n) x) ⊆ injectivityDomain x := by
  intro p hp
  have h : {a : ℝ | a • p ∈ minimizingVectors (n := n) x} ∈ 𝓝 (1:ℝ) := by
    have H := (continuous_id.smul continuous_const : Continuous (fun a : ℝ => a • p))
    apply H.continuousAt.preimage_mem_nhds
    change minimizingVectors (n := n) x ∈ 𝓝 ((1:ℝ) • p)
    simpa only [one_smul] using mem_interior_iff_mem_nhds.mp hp
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp h
  let a := 1+δ/2
  have ha : 1<a := by dsimp [a]; linarith
  have hpa : a • p ∈ minimizingVectors (n := n) x := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    dsimp [a]
    rw [add_sub_cancel_left,abs_of_pos (by positivity : 0<δ/2)]
    linarith
  refine ⟨a,ha,?_⟩
  change dist x (riemannianExp x (a • p)) = a*‖p‖
  change dist x (riemannianExp x (a • p)) = ‖a • p‖ at hpa
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (lt_trans zero_lt_one ha)] using hpa

lemma injectivityDomain_subset_interior_minimizingVectors (x : M) :
    injectivityDomain (n := n) x ⊆ interior (minimizingVectors x) := by
  intro p hp
  obtain ⟨U,hU,hpU,hinj⟩ := riemannianExp_locally_injective hp
  let K := minimizingVectors (n := n) x \ U
  have hK : IsCompact K := (isCompact_minimizingVectors x).diff hU
  have hclosed : IsClosed (riemannianExp (n := n) x '' K) :=
    (hK.image (continuous_riemannianExp x)).isClosed
  have hnot : riemannianExp x p ∉ riemannianExp x '' K := by
    rintro ⟨q,hq,he⟩
    have heq := riemannianExp_interior_unique hp hq.1 he.symm
    exact hq.2 (heq ▸ hpU)
  have hnear : ∀ᶠ v in 𝓝 p, v ∈ U ∧ riemannianExp x v ∉ riemannianExp x '' K :=
    Filter.Eventually.and (hU.mem_nhds hpU)
      ((continuous_riemannianExp x).continuousAt.preimage_mem_nhds
        (hclosed.isOpen_compl.mem_nhds hnot))
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hnear] with v hv
  obtain ⟨q,hq,he⟩ := exists_minimizing_vector (n := n) x (riemannianExp x v)
  have hqU : q ∈ U := by
    by_contra hqU
    exact hv.2 ⟨q,⟨hq,hqU⟩,he⟩
  have hvq := hinj hv.1 hqU he.symm
  exact hvq ▸ hq

lemma injectivityDomain_eq_interior_minimizingVectors (x : M) :
    injectivityDomain (n := n) x = interior (minimizingVectors x) :=
  Set.Subset.antisymm (injectivityDomain_subset_interior_minimizingVectors x)
    (interior_minimizingVectors_subset x)

lemma isOpen_injectivityDomain (x : M) : IsOpen (injectivityDomain (n := n) x) := by
  rw [injectivityDomain_eq_interior_minimizingVectors]
  exact isOpen_interior

end WeakMTWTransport

end

end OAI
