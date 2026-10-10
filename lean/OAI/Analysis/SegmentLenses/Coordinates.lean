import OAI.Analysis.SegmentLenses.ForestDual

namespace OAI

/-!
# Coordinate identification and bounded multipliers
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex


section PrimalCoordinateDensity
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

theorem primal_small_tail (x : Primal V) (H : Finset V) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Finset V, Ancestral (· ≤ ·) K ∧ H ⊆ K ∧ ‖primalTail K x‖ < ε := by
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := Metric.mem_closure_iff.mp
    (UniformSpace.Completion.denseRange_coe x) ε hε
  let K := ancestralHull (H ∪ u.coeff.support)
  have hK : Ancestral (· ≤ ·) K := ancestralHull_ancestral _
  have hs : u.coeff.support ⊆ K := Finset.subset_union_right.trans (subset_ancestralHull _)
  have hfix : primalTail K (u : Primal V) = 0 := by
    change (u : Primal V) - primalHead K u = 0
    rw [primalHead_fix _ u hs, sub_self]
  refine ⟨K, hK, Finset.subset_union_left.trans (subset_ancestralHull _), ?_⟩
  have he : primalTail K x = primalTail K (x - u) := by rw [map_sub, hfix, sub_zero]
  rw [he]
  exact (norm_primalTail_le hK _).trans_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hu)

theorem primal_eq_zero_of_coordinates (x : Primal V) (hx : ∀ v, coordinate v x = 0) : x = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨K, hK, hsub, htail⟩ := primal_small_tail x ∅ hε
  have hz : primalHead K x = 0 := by simp [primalHead_apply, hx]
  simpa only [primalTail, sub_apply, ContinuousLinearMap.id_apply, hz,
    sub_zero, zero_add] using htail



theorem coordinateSpan_eq_top_of_reflexive (hV : Reflexive (Primal V)) :
    coordinateSpan V = ⊤ := by
  let M := coordinateSpan V
  let : IsClosed (M : Set (FullDual V)) := Submodule.isClosed_topologicalClosure _
  let : NormedAddCommGroup (FullDual V ⧸ M) := Submodule.Quotient.normedAddCommGroup M
  apply top_unique
  intro x hx
  by_contra hxm
  have hqx : M.mkQL x ≠ 0 := by
    intro hz
    apply hxm
    exact (Submodule.Quotient.mk_eq_zero M).mp hz
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector ℝ (M.mkQL x) (norm_ne_zero_iff.mpr hqx)
  obtain ⟨p, hp⟩ := hV (g.comp M.mkQL)
  have hpc : ∀ v, coordinate v p = 0 := by
    intro v
    have he := congrArg (fun f : StrongDual ℝ (FullDual V) => f (coordinate v)) hp
    change coordinate v p = g (M.mkQL (coordinate v)) at he
    rwa [show M.mkQL (coordinate v) = 0 by
      exact (Submodule.Quotient.mk_eq_zero M).mpr (coordinate_mem v), map_zero] at he
  have hp0 := primal_eq_zero_of_coordinates p hpc
  have he := congrArg (fun f : StrongDual ℝ (FullDual V) => f x) hp
  change x p = g (M.mkQL x) at he
  rw [hp0, map_zero, hgx] at he
  exact hqx (norm_eq_zero.mp he.symm)

theorem fullDual_small_tail_of_reflexive (hV : Reflexive (Primal V))
    (x : FullDual V) (H : Finset V) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Finset V, Ancestral (· ≤ ·) K ∧ H ⊆ K ∧ ‖tail K x‖ < ε := by
  have hx : x ∈ coordinateSpan V := by rw [coordinateSpan_eq_top_of_reflexive hV]; trivial
  exact predual_small_tail (⟨x, hx⟩ : CoordinatePredual V) H hε


theorem predual_head_tendsto (x : CoordinatePredual V) (H : ℕ → Finset V)
    (hH : ∀ n, Ancestral (· ≤ ·) (H n)) (hmono : Monotone H)
    (hex : ∀ v, ∃ n, v ∈ H n) :
    Filter.Tendsto (fun n => head (H n) x.val) Filter.atTop (nhds x.val) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK, z, hz, he⟩ := predual_finite_approx x hε
  have hevent : ∀ᶠ n in Filter.atTop, K ⊆ H n := by
    apply (Finset.eventually_all _).mpr
    intro v hv
    obtain ⟨N, hN⟩ := hex v
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn => hmono hn hN⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨N, fun n hn => ?_⟩
  have hz' := head_eq_of_subset (hN n hn) z hz
  have htail : tail (H n) x.val = tail (H n) (x.val - z) := by
    change tailLinear (H n) x.val = tailLinear (H n) (x.val - z)
    rw [map_sub]
    simp only [tailLinear_apply, tail, hz', sub_self, sub_zero]
  rw [dist_eq_norm, norm_sub_rev]
  change ‖tail (H n) x.val‖ < ε
  rw [htail]
  exact (norm_tail_le (hH n) _).trans_lt he

theorem fullDual_head_tendsto_of_reflexive (hV : Reflexive (Primal V))
    (x : FullDual V) (H : ℕ → Finset V)
    (hH : ∀ n, Ancestral (· ≤ ·) (H n)) (hmono : Monotone H)
    (hex : ∀ v, ∃ n, v ∈ H n) :
    Filter.Tendsto (fun n => head (H n) x) Filter.atTop (nhds x) := by
  have hx : x ∈ coordinateSpan V := by rw [coordinateSpan_eq_top_of_reflexive hV]; trivial
  exact predual_head_tendsto (⟨x, hx⟩ : CoordinatePredual V) H hH hmono hex



theorem fullDual_all_radius_average_of_reflexive [Infinite V] (hV : Reflexive (Primal V))
    {t : ℝ} (ht : 0 < t) :
    (Real.sqrt (1 + t ^ 2 / 4) - 1) / 2 ≤ averagedModulus (FullDual V) t := by
  apply averagedModulus_lower fullDual_not_finite ht.le
  intro x ε hε
  have hx : x.val ∈ coordinateSpan V := by rw [coordinateSpan_eq_top_of_reflexive hV]; trivial
  obtain ⟨H, hH, hw⟩ := predual_averaged_witness (⟨x.val, hx⟩ : CoordinatePredual V)
    x.property ht hε
  let f : FullDual V →L[ℝ] (H → ℝ) :=
    ContinuousLinearMap.pi (fun v => ContinuousLinearMap.apply ℝ ℝ (unitVector v.val))
  refine ⟨CofiniteSubspace.ofMap f, ?_⟩
  intro y
  have hy : y.val ∈ coordinateSpan V := by rw [coordinateSpan_eq_top_of_reflexive hV]; trivial
  apply hw (⟨y.val, hy⟩ : CoordinatePredual V) _ y.property.2.ge
  apply Finset.sum_eq_zero
  intro v hv
  have he := congrFun y.property.1 (⟨v, hv⟩ : H)
  change y.val (unitVector v) = 0 at he
  rw [he, zero_smul]

end PrimalCoordinateDensity

theorem forest_coordinateSpan_eq_top : coordinateSpan ForestVertex = ⊤ := by
  classical
  exact coordinateSpan_eq_top_of_reflexive forest_primal_reflexive

theorem forest_all_radius_average {t : ℝ} (ht : 0 < t) :
    (Real.sqrt (1 + t ^ 2 / 4) - 1) / 2 ≤ averagedModulus X t := by
  classical
  exact fullDual_all_radius_average_of_reflexive forest_primal_reflexive ht

section Separability
variable {V : Type*} [SegmentSystem V] [Countable V]

theorem coordinateSpan_isSeparable : TopologicalSpace.IsSeparable (coordinateSpan V : Set (FullDual V)) :=
  ((Set.countable_range (coordinate (V := V))).isSeparable.span).closure

theorem fullDual_separable_of_coordinateSpan (hV : coordinateSpan V = ⊤) : TopologicalSpace.SeparableSpace (FullDual V) := by
  have h := coordinateSpan_isSeparable (V := V)
  rw [hV, Submodule.top_coe] at h
  exact TopologicalSpace.isSeparable_univ_iff.mp h

end Separability

instance : Countable ForestVertex := by unfold ForestVertex; infer_instance

theorem forest_separable : TopologicalSpace.SeparableSpace X :=
  fullDual_separable_of_coordinateSpan forest_coordinateSpan_eq_top



end SegmentLenses

end

end OAI
