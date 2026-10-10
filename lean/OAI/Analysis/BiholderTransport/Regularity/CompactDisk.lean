import Mathlib

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

namespace WeakMTWTransport
variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

lemma continuous_bundle_norm : Continuous (fun z : TotalSpace F E => ‖z.2‖) := by
  have h : Continuous (fun z : TotalSpace F E => inner ℝ z.2 z.2) :=
    (continuous_id : Continuous (id : TotalSpace F E → _)).inner_bundle continuous_id
  simpa only [← norm_eq_sqrt_real_inner] using h.sqrt

lemma isCompact_bundle_disk [CompactSpace B] [T2Space B]
    [FiniteDimensional ℝ F] (R : ℝ) :
    IsCompact {z : TotalSpace F E | ‖z.2‖ ≤ R} := by
  classical
  have hsclosed : IsClosed {z : TotalSpace F E | ‖z.2‖ ≤ R} :=
    isClosed_le continuous_bundle_norm continuous_const
  by_cases hR : R < 0
  · have : {z : TotalSpace F E | ‖z.2‖ ≤ R} = ∅ := by
      ext z
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact not_le.mpr ((hR.trans_le (norm_nonneg _)))
    rw [this]
    exact isCompact_empty
  have hlocal (x : B) : ∃ C : ℝ, 0 < C ∧ ∃ K : Set B,
      K ∈ 𝓝 x ∧ IsCompact K ∧ K ⊆ (trivializationAt F E x).baseSet ∧
      ∀ y ∈ K, ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ < C := by
    obtain ⟨C,hC,hbound⟩ := eventually_norm_trivializationAt_lt F E x
    obtain ⟨K,hK,hKs,hKc⟩ := local_compact_nhds
      (inter_mem ((trivializationAt F E x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E x)) hbound)
    exact ⟨C,hC,K,hK,hKc,fun y hy => (hKs hy).1,fun y hy => (hKs hy).2⟩
  choose C hC K hKn hKc hKb hKC using hlocal
  let L (x : B) : Set (TotalSpace F E) :=
    (trivializationAt F E x).toOpenPartialHomeomorph.symm ''
      (K x ×ˢ Metric.closedBall (0 : F) (C x * R))
  have hLc (x : B) : IsCompact (L x) := by
    apply ((hKc x).prod (isCompact_closedBall (0 : F) (C x * R))).image_of_continuousOn
    apply (trivializationAt F E x).toOpenPartialHomeomorph.continuousOn_symm.mono
    intro y hy
    change y ∈ (trivializationAt F E x).target
    exact (trivializationAt F E x).mem_target.mpr (hKb x hy.1)
  obtain ⟨t,ht⟩ := finite_cover_nhds hKn
  apply (t.isCompact_biUnion (fun x _ => hLc x)).of_isClosed_subset hsclosed
  intro z hz
  have hzm : z.1 ∈ ⋃ x ∈ t, K x := by rw [ht]; trivial
  obtain ⟨x,hx,hzK⟩ := mem_iUnion₂.mp hzm
  apply mem_iUnion₂.mpr ⟨x,hx,?_⟩
  have hzb := hKb x hzK
  have hzs : z ∈ (trivializationAt F E x).source :=
    (trivializationAt F E x).mem_source.mpr hzb
  refine ⟨(trivializationAt F E x) z,?_,?_⟩
  · refine ⟨?_,?_⟩
    · rwa [Trivialization.coe_fst _ hzs]
    · rw [Metric.mem_closedBall,dist_zero_right]
      have he : (trivializationAt F E x z).2 =
          (trivializationAt F E x).continuousLinearMapAt ℝ z.1 z.2 := by
        rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hzb]
      rw [he]
      calc
        _ ≤ ‖(trivializationAt F E x).continuousLinearMapAt ℝ z.1‖ * ‖z.2‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ C x * R := mul_le_mul (hKC x z.1 hzK).le hz (norm_nonneg _) (hC x).le
  · exact (trivializationAt F E x).left_inv hzs

end WeakMTWTransport

end

end OAI
