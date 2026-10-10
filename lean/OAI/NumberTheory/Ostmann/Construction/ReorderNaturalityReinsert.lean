import OAI.NumberTheory.Ostmann.Construction.ReorderNaturality
import OAI.NumberTheory.Ostmann.Construction.ReorderNaturalityReinsertMap

namespace OAI

noncomputable section
namespace Ostmann.Construction.Template
open Arithmetic.OccurrencePermutation Arithmetic.HistorySymbolicSlots Characters.RationalHistory

variable {j : ℕ} {T : List SourceSlot} {u h u' h' : List SmallSlot}

def reinsertPositions (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length)
    (hu' : u'.length=(extracted j T).length) (hh' : h'.length=(remainder j T).length) :
    Fin (reinsert j T u h).length ≃ Fin (reinsert j T u' h').length :=
  finCongr (by rw [reinsert_length j T u h hu hh,reinsert_length j T u' h' hu' hh',hu,hh,hu',hh'])

def splitPositions (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length)
    (hu' : u'.length=(extracted j T).length) (hh' : h'.length=(remainder j T).length) :
    Fin (u++h).length ≃ Fin (u'++h').length :=
  finCongr (by simp only [List.length_append,hu,hh,hu',hh'])

@[simp] theorem reinsertPositions_val
    (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length)
    (hu' : u'.length=(extracted j T).length) (hh' : h'.length=(remainder j T).length)
    (i : Fin (reinsert j T u h).length) : (reinsertPositions hu hh hu' hh' i).val=i.val := rfl

@[simp] theorem splitPositions_val
    (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length)
    (hu' : u'.length=(extracted j T).length) (hh' : h'.length=(remainder j T).length)
    (i : Fin (u++h).length) : (splitPositions hu hh hu' hh' i).val=i.val := rfl

theorem indexEquiv_reinsert_naturality
    (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length)
    (hu' : u'.length=(extracted j T).length) (hh' : h'.length=(remainder j T).length)
    (hnd : (u++h).Nodup) (hnd' : (u'++h').Nodup) :
    (indexEquiv (reinsert_perm j T u h hu hh)).trans (splitPositions hu hh hu' hh')=
      (reinsertPositions hu hh hu' hh').trans (indexEquiv (reinsert_perm j T u' h' hu' hh')) := by
  obtain ⟨f,hfu,hfh,hfr⟩ := exists_reinsert_common_map j T u h u' h' hu hh hu' hh' hnd
  have hfs : (u++h).map f=u'++h' := by rw [List.map_append,hfu,hfh]
  apply indexEquiv_naturality _ _ hnd'
  intro i a ha
  change (u'++h').get (finCongr _ a)=(reinsert j T u' h').get (finCongr _ i)
  rw [get_finCongr_of_map_eq f hfs,get_finCongr_of_map_eq f hfr,ha]

theorem indexEquiv_reinsert_val
    (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length)
    (hu' : u'.length=(extracted j T).length) (hh' : h'.length=(remainder j T).length)
    (hnd : (u++h).Nodup) (hnd' : (u'++h').Nodup)
    (i : Fin (reinsert j T u h).length) :
    (indexEquiv (reinsert_perm j T u h hu hh) i).val=
      (indexEquiv (reinsert_perm j T u' h' hu' hh') (reinsertPositions hu hh hu' hh' i)).val := by
  exact congrArg Fin.val (Equiv.congr_fun (indexEquiv_reinsert_naturality hu hh hu' hh' hnd hnd') i)

theorem reorder_reinsert_naturality {ι κ : Type*}
    (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length)
    (hu' : u'.length=(extracted j T).length) (hh' : h'.length=(remainder j T).length)
    (hnd : (u++h).Nodup) (hnd' : (u'++h').Nodup)
    (f : Fin (reinsert j T u h).length→Expr ι)
    (f' : Fin (reinsert j T u' h').length→Expr κ) (R : Expr ι→Expr κ)
    (hf : ∀i,f' (reinsertPositions hu hh hu' hh' i)=R (f i)) (a : Fin (u++h).length) :
    reorder (reinsert_perm j T u' h' hu' hh') f' (splitPositions hu hh hu' hh' a)=
      R (reorder (reinsert_perm j T u h hu hh) f a) := by
  obtain ⟨g,hgu,hgh,hgr⟩ := exists_reinsert_common_map j T u h u' h' hu hh hu' hh' hnd
  have hgs : (u++h).map g=u'++h' := by rw [List.map_append,hgu,hgh]
  apply reorder_naturality _ _ hnd' (reinsertPositions hu hh hu' hh')
    (splitPositions hu hh hu' hh') _ f f' R hf a
  intro i a ha
  change (u'++h').get (finCongr _ a)=(reinsert j T u' h').get (finCongr _ i)
  rw [get_finCongr_of_map_eq g hgs,get_finCongr_of_map_eq g hgr,ha]

theorem reorder_reinsert_symm_naturality {ι κ : Type*}
    (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length)
    (hu' : u'.length=(extracted j T).length) (hh' : h'.length=(remainder j T).length)
    (hnd : (u++h).Nodup) (hnd' : (u'++h').Nodup)
    (f : Fin (u++h).length→Expr ι) (f' : Fin (u'++h').length→Expr κ) (R : Expr ι→Expr κ)
    (hf : ∀i,f' (splitPositions hu hh hu' hh' i)=R (f i))
    (a : Fin (reinsert j T u h).length) :
    reorder (reinsert_perm j T u' h' hu' hh').symm f' (reinsertPositions hu hh hu' hh' a)=
      R (reorder (reinsert_perm j T u h hu hh).symm f a) := by
  obtain ⟨g,hgu,hgh,hgr⟩ := exists_reinsert_common_map j T u h u' h' hu hh hu' hh' hnd
  have hgs : (u++h).map g=u'++h' := by rw [List.map_append,hgu,hgh]
  have hndr : (reinsert j T u' h').Nodup := (reinsert_perm j T u' h' hu' hh').nodup_iff.mpr hnd'
  apply reorder_naturality _ _ hndr (splitPositions hu hh hu' hh')
    (reinsertPositions hu hh hu' hh') _ f f' R hf a
  intro i a ha
  change (reinsert j T u' h').get (finCongr _ a)=(u'++h').get (finCongr _ i)
  rw [get_finCongr_of_map_eq g hgr,get_finCongr_of_map_eq g hgs,ha]

end Ostmann.Construction.Template

end

end OAI
