import OAI.Analysis.CircleDomains.Selection.BandGraph

namespace OAI

/-! Singleton fibers of a compact band graph have uniformly narrow
nearby fibers. This gives the local branch ranges used near free points. -/

open Set
open scoped Topology

namespace CircleDomainRigidity

theorem exists_open_compact_band_range
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set (X × ℝ)} (hK : IsCompact K) {x : X} {W : Set ℝ}
    (hW : IsOpen W) (hfiber : ∀ t, (x, t) ∈ K → t ∈ W) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, ∀ t, (y, t) ∈ K → t ∈ W := by
  let F := Prod.fst '' (K ∩ Prod.snd ⁻¹' Wᶜ)
  have hF : IsClosed F :=
    ((hK.inter_right (hW.isClosed_compl.preimage continuous_snd)).image continuous_fst).isClosed
  refine ⟨Fᶜ, hF.isOpen_compl, ?_, ?_⟩
  · rintro ⟨⟨y, t⟩, ⟨ht, hnot⟩, hy⟩
    change y = x at hy
    subst y
    exact hnot (hfiber t ht)
  · intro y hy t ht
    by_contra hnot
    exact hy ⟨(y, t), ⟨ht, hnot⟩, rfl⟩

theorem exists_narrow_real_band_neighborhood
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {D : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    {x : X} {a : ℝ}
    (htrace : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) → t = a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
        t ∈ Ioo (a - ε) (a + ε) := by
  apply exists_open_compact_band_range
    (isCompact_intervalFiberHull (isCompact_clusterGraph hM)) isOpen_Ioo
  intro t ht
  rw [htrace t ht]
  constructor <;> linarith

end CircleDomainRigidity

end OAI
