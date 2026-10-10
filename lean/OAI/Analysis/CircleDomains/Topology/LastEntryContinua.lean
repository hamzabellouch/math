import OAI.Analysis.CircleDomains.Probability.ExitTimeMeasurability

namespace OAI

/-! The last-entry tails are actual compact connected sets. Their only point
outside the open collar is their initial boundary point. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def lastEntryTail (γ : C(PathTime, X)) (V : Set X) : Set X :=
  γ '' Ici (lastEntryTime γ V)

theorem isCompact_lastEntryTail (γ : C(PathTime, X)) (V : Set X) :
    IsCompact (lastEntryTail γ V) :=
  isClosed_Ici.isCompact.image γ.continuous

theorem isConnected_lastEntryTail (γ : C(PathTime, X)) (V : Set X) :
    IsConnected (lastEntryTail γ V) :=
  (isConnected_Ici (a := lastEntryTime γ V)).image γ γ.continuous.continuousOn

theorem lastEntry_mem_tail (γ : C(PathTime, X)) (V : Set X) :
    γ (lastEntryTime γ V) ∈ lastEntryTail γ V := ⟨_, mem_Ici.mpr le_rfl, rfl⟩

theorem endpoint_mem_tail (γ : C(PathTime, X)) (V : Set X) :
    γ ⊤ ∈ lastEntryTail γ V := ⟨_, mem_Ici.mpr le_top, rfl⟩

theorem lastEntryTail_subset_closure (γ : C(PathTime, X)) {V : Set X}
    (hV : IsOpen V) (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) :
    lastEntryTail γ V ⊆ closure V := by
  rintro x ⟨t, ht, rfl⟩
  exact lastEntry_final_segment γ hV hstart hend ht

theorem lastEntryTail_outside (γ : C(PathTime, X)) (V : Set X) {x : X}
    (hx : x ∈ lastEntryTail γ V) (hxV : x ∉ V) :
    x = γ (lastEntryTime γ V) := by
  obtain ⟨t, ht, rfl⟩ := hx
  have he : t = lastEntryTime γ V := by
    apply le_antisymm _ ht
    by_contra hn
    exact hxV (mem_after_lastEntry γ V (lt_of_not_ge hn))
  rw [he]

theorem isConnected_union_lastEntryTails (γ δ : C(PathTime, X)) (V : Set X)
    (hend : γ ⊤ = δ ⊤) :
    IsConnected (lastEntryTail γ V ∪ lastEntryTail δ V) := by
  apply IsConnected.union
  · exact ⟨γ ⊤, endpoint_mem_tail γ V, hend.symm ▸ endpoint_mem_tail δ V⟩
  · exact isConnected_lastEntryTail γ V
  · exact isConnected_lastEntryTail δ V

end CircleDomainRigidity

end

end OAI
