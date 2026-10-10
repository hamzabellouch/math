import OAI.Analysis.CircleDomains.Topology.AffinePathTime
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.Compact

namespace OAI

/-! Replacing all visits to one open disk by a boundary path. The new
path introduces no points except on the boundary and removes every
interior visit. This is the path surgery used for singleton contacts. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_first_closed_visit
    {X : Type*} [TopologicalSpace X] (γ : C(PathTime, X))
    {U : Set X} (hU : IsOpen U) (hstart : γ ⊥ ∉ closure U)
    (hvisit : (range γ ∩ U).Nonempty) :
    ∃ a : PathTime, γ a ∈ frontier U ∧ ∀ t ≤ a, γ t ∉ U := by
  let T : Set PathTime := γ ⁻¹' closure U
  have hT : IsCompact T := (isClosed_closure.preimage γ.continuous).isCompact
  have hne : T.Nonempty := by
    obtain ⟨z, ⟨t, rfl⟩, hz⟩ := hvisit
    exact ⟨t, subset_closure hz⟩
  let a := sInf T
  have ha : γ a ∈ closure U := hT.sInf_mem hne
  have hpos : ⊥ < a := by
    apply bot_lt_iff_ne_bot.mpr
    intro he
    exact hstart (he ▸ ha)
  have hbefore : MapsTo γ (Iio a) (closure U)ᶜ := by
    intro t ht hm
    exact ht.not_ge (sInf_le (show t ∈ T from hm))
  have hcl : a ∈ closure (Iio a) := by
    rw [closure_Iio' ⟨⊥, hpos⟩]
    exact (le_rfl : a ≤ a)
  have hnot : γ a ∉ U :=
    (closure_minimal (compl_subset_compl.mpr (subset_closure : U ⊆ closure U))
      hU.isClosed_compl) (hbefore.closure γ.continuous hcl)
  refine ⟨a, ?_, ?_⟩
  · rw [hU.frontier_eq]
    exact ⟨ha, hnot⟩
  · intro t ht
    rcases ht.eq_or_lt with rfl | hlt
    · exact hnot
    · exact fun hm => hbefore hlt (subset_closure hm)

private theorem joinedIn_initial_without_open
    {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    (U : Set X) (a : PathTime) (ha : ∀ t ≤ a, γ t ∉ U) :
    JoinedIn (range γ \ U) x (γ a) := by
  have h0 : (0 : PathTime) = ⊥ := Subtype.ext rfl
  have h1 : (1 : PathTime) = ⊤ := Subtype.ext rfl
  let α : Path x (γ a) := {
    toFun := γ ∘ affinePathTime ⊥ a
    continuous_toFun := γ.continuous.comp (affinePathTime ⊥ a).continuous
    source' := by
      change γ (affinePathTime ⊥ a (0 : PathTime)) = x
      rw [h0, affinePathTime_zero, ← h0, Path.source]
    target' := by
      change γ (affinePathTime ⊥ a (1 : PathTime)) = γ a
      rw [h1, affinePathTime_one] }
  refine ⟨α, ?_⟩
  intro t
  exact ⟨mem_range_self _, ha _ (affinePathTime_mem_Icc bot_le t).2⟩

theorem exists_boundary_detour
    {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    {U : Set X} (hU : IsOpen U) (hx : x ∉ closure U) (hy : y ∉ closure U)
    (hboundary : IsPathConnected (frontier U)) :
    ∃ δ : Path x y, range δ ⊆ (range γ \ U) ∪ frontier U := by
  have h0 : (0 : PathTime) = ⊥ := Subtype.ext rfl
  by_cases hvisit : (range γ ∩ U).Nonempty
  · obtain ⟨a, haf, ha⟩ := exists_first_closed_visit γ.toContinuousMap hU
      (by change γ ⊥ ∉ closure U; rw [← h0, Path.source]; exact hx) hvisit
    have hvisit' : (range γ.symm ∩ U).Nonempty := by simpa only [Path.symm_range] using hvisit
    obtain ⟨b, hbf, hb⟩ := exists_first_closed_visit γ.symm.toContinuousMap hU
      (by change γ.symm ⊥ ∉ closure U; rw [← h0, Path.source]; exact hy) hvisit'
    have hleft : JoinedIn ((range γ \ U) ∪ frontier U) x (γ a) :=
      (joinedIn_initial_without_open γ U a ha).mono subset_union_left
    have hright : JoinedIn ((range γ \ U) ∪ frontier U) y (γ.symm b) := by
      apply (joinedIn_initial_without_open γ.symm U b hb).mono
      rw [Path.symm_range]
      exact subset_union_left
    have hmiddle : JoinedIn ((range γ \ U) ∪ frontier U) (γ a) (γ.symm b) :=
      (hboundary.joinedIn _ haf _ hbf).mono subset_union_right
    let h := (hleft.trans hmiddle).trans hright.symm
    exact ⟨h.somePath, by rintro z ⟨t, rfl⟩; exact h.somePath_mem t⟩
  · refine ⟨γ, ?_⟩
    intro z hz
    exact Or.inl ⟨hz, fun hu => hvisit ⟨z, hz, hu⟩⟩

end CircleDomainRigidity

end

end OAI
