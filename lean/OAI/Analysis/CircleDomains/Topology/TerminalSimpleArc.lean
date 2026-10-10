import OAI.Analysis.CircleDomains.Topology.PathImageSimpleArc
import OAI.Analysis.CircleDomains.Topology.LastEntryContinua
import OAI.Analysis.CircleDomains.Topology.AffinePathTime

namespace OAI

/-! Erase loops in the terminal portion after the last collar hit.
The resulting arc meets the collar only at its initial endpoint. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem exists_terminal_simple_arc
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (γ : C(PathTime, Sphere)) {V : Set Sphere} (hV : IsOpen V)
    (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) :
    ∃ α : C(PathTime, Sphere), Injective α ∧
      α ⊥ = γ (lastEntryTime γ V) ∧ α ⊤ = γ ⊤ ∧
      range α ⊆ lastEntryTail γ V ∧ α ⊥ ∈ frontier V ∧
      ∀ t ∈ Ioo (⊥ : PathTime) ⊤, α t ∈ V \ {γ ⊤} := by
  have hfront := lastEntry_frontier γ hV hstart hend
  have hne : γ (lastEntryTime γ V) ≠ γ ⊤ := by
    intro h
    exact disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hV) (h ▸ hfront) hend
  have hlt : lastEntryTime γ V < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    exact hne (congrArg γ h)
  let δ : C(PathTime, Sphere) := γ.comp (affinePathTime (lastEntryTime γ V) ⊤)
  have hδ0 : δ ⊥ = γ (lastEntryTime γ V) := by
    exact congrArg γ (affinePathTime_zero _ _)
  have hδ1 : δ ⊤ = γ ⊤ := by exact congrArg γ (affinePathTime_one _ _)
  obtain ⟨α, hinj, hα0, hα1, hsub⟩ := exists_simple_subarc harcs δ
    (by simpa only [hδ0, hδ1] using hne)
  have hα0' := hα0.trans hδ0
  have hα1' := hα1.trans hδ1
  have htail : range α ⊆ lastEntryTail γ V := by
    intro x hx
    obtain ⟨t, rfl⟩ := hsub hx
    exact ⟨affinePathTime (lastEntryTime γ V) ⊤ t,
      (affinePathTime_mem_Icc hlt.le t).1, rfl⟩
  refine ⟨α, hinj, hα0', hα1', htail, ?_, ?_⟩
  · simpa only [hα0'] using hfront
  intro t ht
  constructor
  · by_contra hn
    have he := lastEntryTail_outside γ V (htail (mem_range_self t)) hn
    have he' : α t = α ⊥ := he.trans hα0'.symm
    exact ht.1.ne' (hinj he')
  · intro he
    exact ht.2.ne (hinj (he.trans hα1'.symm))

end CircleDomainRigidity

end

end OAI
