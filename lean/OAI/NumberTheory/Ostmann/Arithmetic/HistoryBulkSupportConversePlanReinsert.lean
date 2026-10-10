import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportCode
import OAI.NumberTheory.Ostmann.Construction.ReorderNaturalityReinsertMap

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction CanonicalOccurrenceTransport OccurrencePermutation

theorem select_permutationOrder_map {A B : Type} {xs ys : List A}
    (p : xs.Perm ys) (f : A → B) (d : B) :
    select d (permutationOrder p) (xs.map f) = ys.map f := by
  have hx : List.ofFn (fun i : Fin xs.length => f (xs.get i)) = xs.map f := by
    rw [←Function.comp_def,←List.map_ofFn,List.ofFn_get]
  have hy : List.ofFn (fun i : Fin ys.length => f (ys.get i)) = ys.map f := by
    rw [←Function.comp_def,←List.map_ofFn,List.ofFn_get]
  have hi (i : Fin ys.length) : xs.get ((indexEquiv p).symm i) = ys.get i := by
    simpa only [Equiv.apply_symm_apply] using (get_indexEquiv p ((indexEquiv p).symm i)).symm
  rw [←hx]
  change select d (List.ofFn (fun i => ((indexEquiv p).symm i).val)) _ = _
  rw [select_ofFn]
  calc
    _ = List.ofFn (fun i : Fin ys.length => f (ys.get i)) := by
      congr 1
      funext i
      rw [hi]
    _ = _ := hy

theorem select_reinsert_of_same_lengths (j : ℕ) (T : List SourceSlot)
    (u h u' h' : List SmallSlot)
    (hu : u.length = (Template.extracted j T).length)
    (hh : h.length = (Template.remainder j T).length)
    (hu' : u'.length = (Template.extracted j T).length)
    (hh' : h'.length = (Template.remainder j T).length)
    (hnd : (u++h).Nodup) (d : SmallSlot) :
    select d (permutationOrder (Template.reinsert_perm j T u h hu hh).symm) (u'++h') =
      Template.reinsert j T u' h' := by
  obtain ⟨f,hfu,hfh,hfr⟩ := Template.exists_reinsert_common_map j T u h u' h'
    hu hh hu' hh' hnd
  calc
    _ = select d (permutationOrder (Template.reinsert_perm j T u h hu hh).symm)
        ((u++h).map f) := by rw [List.map_append,hfu,hfh]
    _ = (Template.reinsert j T u h).map f :=
      select_permutationOrder_map (Template.reinsert_perm j T u h hu hh).symm f d
    _ = _ := hfr

theorem select_reinsert_map_of_same_lengths {B : Type} (j : ℕ) (T : List SourceSlot)
    (u h u' h' : List SmallSlot)
    (hu : u.length = (Template.extracted j T).length)
    (hh : h.length = (Template.remainder j T).length)
    (hu' : u'.length = (Template.extracted j T).length)
    (hh' : h'.length = (Template.remainder j T).length)
    (hnd : (u++h).Nodup) (f : SmallSlot → B) (d : B) :
    select d (permutationOrder (Template.reinsert_perm j T u h hu hh).symm)
      ((u'++h').map f) = (Template.reinsert j T u' h').map f := by
  obtain ⟨g,hgu,hgh,hgr⟩ := Template.exists_reinsert_common_map j T u h u' h'
    hu hh hu' hh' hnd
  have hgs : (u++h).map g = u'++h' := by rw [List.map_append,hgu,hgh]
  calc
    _ = select d (permutationOrder (Template.reinsert_perm j T u h hu hh).symm)
        ((u++h).map (f ∘ g)) := by rw [←List.map_map,hgs]
    _ = (Template.reinsert j T u h).map (f ∘ g) :=
      select_permutationOrder_map (Template.reinsert_perm j T u h hu hh).symm (f ∘ g) d
    _ = _ := by rw [←List.map_map,hgr]

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
