import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSkeleton
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesBasic
import OAI.NumberTheory.Ostmann.Construction.CanonicalSourceLabels

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction

theorem templateAt_of_matches {T : List SourceSlot} {a b : State} {l : ℕ}
    (ha : Template.Matches T a.small) (hb : Template.Matches T b.small)
    (ht : a.TemplateAt l) : b.TemplateAt l := by
  intro q hq j hj
  have hm : (q.role,q.origin) ∈ a.small.map (fun x => (x.role,x.origin)) := by
    rw [ha,←hb]
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  obtain ⟨z,hz,he⟩ := List.mem_map.mp hm
  exact ht z hz j ((congrArg Prod.fst he).trans hj)

theorem root_values_nodup_of_supported {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) :
    (h.root.small.map SmallSlot.value).Nodup := by
  have hn := List.nodup_ofFn.mpr (HistoryPairBulkCoordinates.root_value_injective h hs)
  simpa only [List.get_eq_getElem,List.ofFn_getElem_eq_map] using hn

theorem compensation_values_nodup_of_supported
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ} {a : State}
    {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    (u.map SmallSlot.value).Nodup := by
  have hn := root_values_nodup_of_supported (History.supported_left hs)
  have he := (History.supported_child_small hs).1.map SmallSlot.value
  have hfull := he.nodup_iff.mp hn
  rw [List.map_append,List.nodup_append] at hfull
  exact hfull.1

theorem child_primeSmall_of_perm {a child : State} {u inherited : List SmallSlot}
    (ha : a.PrimeSmall) (hu : ∀q∈u,q.value.Prime)
    (hinherited : ∀q∈inherited,q∈a.small)
    (hp : child.small.Perm (u++inherited)) : child.PrimeSmall := by
  intro q hq
  rcases List.mem_append.mp (hp.mem_iff.mp hq) with hq | hq
  · exact hu q hq
  · exact ha q (hinherited q hq)

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
