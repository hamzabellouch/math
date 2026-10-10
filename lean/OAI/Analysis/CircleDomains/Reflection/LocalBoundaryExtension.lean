import Mathlib.Topology.ExtendFrom

namespace OAI

/-! Local continuous extensions provide a single canonical extension
to the closure. This glues boundary values without choosing compatible
values by hand. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma tendsto_of_local_extension {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A O : Set X} {f g : X → Y} (hO : IsOpen O) {x : X} (hx : x∈O)
    (hg : ContinuousOn g O) (he : EqOn g f (O∩A)) :
    Tendsto f (𝓝[A] x) (𝓝 (g x)) := by
  apply ((hg.continuousAt (hO.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hx),self_mem_nhdsWithin] with z hzO hzA
  exact he ⟨hzO,hzA⟩

lemma continuousOn_extendFrom_of_local_extensions {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [RegularSpace Y]
    {A K : Set X} {f : X → Y} (hK : K⊆closure A)
    (hl : ∀x∈K,∃(O:Set X)(g:X→Y),IsOpen O ∧ x∈O ∧ ContinuousOn g O ∧ EqOn g f (O∩A)) :
    ContinuousOn (extendFrom A f) K := by
  apply continuousOn_extendFrom hK
  intro x hx
  obtain ⟨O,g,hO,hxO,hg,he⟩ := hl x hx
  exact ⟨g x,tendsto_of_local_extension hO hxO hg he⟩

lemma extendFrom_eq_local_extension {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {A O : Set X} {f g : X → Y} (hO : IsOpen O) (hg : ContinuousOn g O)
    (he : EqOn g f (O∩A)) : EqOn (extendFrom A f) g (O∩closure A) := by
  intro x hx
  exact extendFrom_eq hx.2 (tendsto_of_local_extension hO hx.1 hg he)

end CircleDomainRigidity

end

end OAI
