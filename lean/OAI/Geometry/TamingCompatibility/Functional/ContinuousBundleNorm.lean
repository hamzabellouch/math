import Mathlib

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
namespace TamingCompatibility
variable {B F : Type*} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

omit [CompactSpace B] [T2Space B] [ProperSpace F] in
lemma continuous_bundle_norm : Continuous (fun p : TotalSpace F E => ‖p.2‖) := by
  have h : Continuous (fun p : TotalSpace F E => inner ℝ p.2 p.2) :=
    continuous_id.inner_bundle continuous_id
  convert h.sqrt using 1
  funext p
  simp

theorem isCompact_bundle_closedBall (r : ℝ) :
    IsCompact {p : TotalSpace F E | ‖p.2‖ ≤ r} := by
  have hlocal (x : B) : ∃ K : Set B, ∃ C : ℝ,
      IsCompact K ∧ x ∈ interior K ∧
      (K ⊆ (trivializationAt F E x).baseSet) ∧
      ∀ y ∈ K, ∀ v : E y, ‖v‖ ≤ r →
        ‖(trivializationAt F E x).continuousLinearMapAt ℝ y v‖ ≤ C := by
    obtain ⟨C, hC, hevent⟩ := eventually_norm_trivializationAt_lt F E x
    have hn : {y | ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ < C} ∩
        (trivializationAt F E x).baseSet ∈ 𝓝 x :=
      inter_mem hevent ((trivializationAt F E x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E x))
    obtain ⟨U, hUs, hUo, hxU⟩ := mem_nhds_iff.mp hn
    obtain ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset hUo hxU
    refine ⟨K, C * max r 0, hKc, hxK, fun y hy => (hUs (hKU hy)).2, ?_⟩
    intro y hy v hv
    exact (ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul ((hUs (hKU hy)).1.le) (hv.trans (le_max_left _ _))
        (norm_nonneg _) hC.le)
  choose K C hK hxK hKb hbound using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (K x))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.mpr ⟨x, hxK x⟩)
  let A (x : B) : Set (TotalSpace F E) :=
    (trivializationAt F E x).toOpenPartialHomeomorph.symm ''
      (K x ×ˢ Metric.closedBall (0 : F) (C x))
  have hAc (x : B) : IsCompact (A x) := by
    apply ((hK x).prod (isCompact_closedBall (0 : F) (C x))).image_of_continuousOn
    apply (trivializationAt F E x).toOpenPartialHomeomorph.continuousOn_symm.mono
    intro q hq
    exact (trivializationAt F E x).mem_target.mpr (hKb x hq.1)
  have hsc : IsCompact (⋃ x ∈ t, A x) := t.isCompact_biUnion (fun x _ => hAc x)
  apply hsc.of_isClosed_subset
    (isClosed_le continuous_bundle_norm continuous_const)
  intro p hp
  obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.mp (ht (mem_univ p.proj))
  have hpk : p.proj ∈ K x := interior_subset hx
  have hpb : p.proj ∈ (trivializationAt F E x).baseSet := hKb x hpk
  apply mem_iUnion₂.mpr
  refine ⟨x, hxt, ?_⟩
  refine ⟨(trivializationAt F E x) p, ?_, ?_⟩
  · constructor
    · simpa only [(trivializationAt F E x).coe_fst' hpb] using hpk
    · rw [Metric.mem_closedBall, dist_zero_right]
      rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hpb p.2]
      exact hbound x _ hpk _ hp
  · exact (trivializationAt F E x).toOpenPartialHomeomorph.left_inv
      ((trivializationAt F E x).mem_source.mpr hpb)

theorem isCompact_bundle_unitSphere :
    IsCompact {p : TotalSpace F E | ‖p.2‖ = 1} :=
  (isCompact_bundle_closedBall (E := E) 1).of_isClosed_subset
    (isClosed_eq continuous_bundle_norm continuous_const) (fun _ h => h.le)

end TamingCompatibility

end

end OAI
