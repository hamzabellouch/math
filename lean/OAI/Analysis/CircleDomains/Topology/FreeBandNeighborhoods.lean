import OAI.Analysis.CircleDomains.Topology.CountableBandNeighborhoods
import OAI.Analysis.CircleDomains.Rigidity.BoundaryTrace
import Mathlib.Topology.Separation.Regular

namespace OAI

/-! Zero band budget produces the actual unique trace, and narrow
neighborhoods can be chosen with closure in a prescribed chart region. -/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem real_band_fiber_eq_trace_of_zero_width
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [FirstCountableTopology X] {D : Set X} {f : X → ℝ} {M : ℝ}
    (hM : ∀ z ∈ D, |f z| ≤ M) {x : X} (hx : x ∈ closure D)
    (hwidth : limsup f (𝓝[D] x) - liminf f (𝓝[D] x) ≤ 0) :
    ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = realBoundaryTrace D f x := by
  have he := intervalFiberHull_clusterGraph_eq_boundary_band hM hx
  obtain ⟨t, ht⟩ := clusterGraph_fiber_nonempty_of_mem_closure hM hx
  have hh := subset_intervalFiberHull (clusterGraph D f) ht
  have hi : liminf f (𝓝[D] x) ≤ limsup f (𝓝[D] x) := by
    have hmem : t ∈ Icc (liminf f (𝓝[D] x)) (limsup f (𝓝[D] x)) := he ▸ hh
    exact hmem.1.trans hmem.2
  have heq : limsup f (𝓝[D] x) = liminf f (𝓝[D] x) := by linarith
  intro t
  change t ∈ {t | (x, t) ∈ intervalFiberHull (clusterGraph D f)} ↔ _
  rw [he, heq, Icc_self]
  rfl

theorem exists_narrow_real_band_neighborhood_closure
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {D W : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    {x : X} {a : ℝ} (hW : IsOpen W) (hxW : x ∈ W)
    (htrace : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) → t = a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧
      ∀ y ∈ V, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
        t ∈ Ioo (a - ε) (a + ε) := by
  obtain ⟨V, hV, hxV, hv⟩ := exists_narrow_real_band_neighborhood hM htrace hε
  obtain ⟨Q, hQ, hxQ, hQV⟩ := normal_exists_closure_subset
    (isClosed_singleton : IsClosed ({x} : Set X)) (hV.inter hW)
      (singleton_subset_iff.mpr ⟨hxV, hxW⟩)
  refine ⟨Q, hQ, hxQ (mem_singleton x), hQV.trans inter_subset_right, ?_⟩
  intro y hy t ht
  exact hv y (hQV (subset_closure hy)).1 t ht

theorem countable_narrow_real_band_cover_closure
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X]
    {D F W : Set X} {f a : X → ℝ} {M : ℝ}
    (hM : ∀ z ∈ D, |f z| ≤ M) (hW : IsOpen W) (hFW : F ⊆ W)
    (htrace : ∀ x ∈ F, ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) → t = a x) :
    ∃ (S : Set X) (V : X → Set X), S ⊆ F ∧ S.Countable ∧
      F ⊆ ⋃ x ∈ S, V x ∧ ∀ x ∈ S,
        IsOpen (V x) ∧ x ∈ V x ∧ closure (V x) ⊆ W ∧
        ∀ y ∈ V x, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
          t ∈ Ico (a x - 1 / 2) (a x - 1 / 2 + 1) := by
  have hn : ∀ x ∈ F, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧
      ∀ y ∈ V, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
        t ∈ Ico (a x - 1 / 2) (a x - 1 / 2 + 1) := by
    intro x hx
    obtain ⟨V, hV, hxV, hVW, hv⟩ := exists_narrow_real_band_neighborhood_closure
      hM hW (hFW hx) (htrace x hx) (by norm_num : (0 : ℝ) < 1 / 4)
    refine ⟨V, hV, hxV, hVW, ?_⟩
    intro y hy t ht
    have hb := hv y hy t ht
    constructor <;> linarith [hb.1, hb.2]
  have hc : ∀ x, ∃ V : Set X, x ∈ F → IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧
      ∀ y ∈ V, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
        t ∈ Ico (a x - 1 / 2) (a x - 1 / 2 + 1) := by
    intro x
    by_cases hx : x ∈ F
    · obtain ⟨V, hV⟩ := hn x hx
      exact ⟨V, fun _ => hV⟩
    · exact ⟨∅, fun h => (hx h).elim⟩
  choose V hV using hc
  obtain ⟨S, hSF, hSc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := F) (f := V) (fun x hx =>
      mem_nhdsWithin_of_mem_nhds ((hV x hx).1.mem_nhds (hV x hx).2.1))
  exact ⟨S, V, hSF, hSc, hcover, fun x hx => hV x (hSF hx)⟩

end CircleDomainRigidity

end OAI
