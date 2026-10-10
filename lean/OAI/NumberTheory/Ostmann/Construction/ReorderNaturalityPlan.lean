import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportCode
import OAI.NumberTheory.Ostmann.Construction.ReorderNaturalityReinsert

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.OccurrencePermutation

lemma indexEquiv_symm_of_nodup {A : Type*} {xs ys : List A} (h : xs.Perm ys)
    (hx : xs.Nodup) : indexEquiv h.symm=(indexEquiv h).symm := by
  apply indexEquiv_eq_of_get h.symm hx
  intro i
  have he := get_indexEquiv h ((indexEquiv h).symm i)
  simpa only [Equiv.apply_symm_apply] using he.symm

end Ostmann.Arithmetic.OccurrencePermutation

namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.OccurrencePermutation

theorem permutationOrder_eq_range {A : Type} {xs ys : List A}
    (h : xs.Perm ys) (hxy : xs=ys) (hx : xs.Nodup) :
    permutationOrder h=List.range xs.length := by
  subst ys
  have he := indexEquiv_eq_of_get h hx (Equiv.refl _) (fun i => rfl)
  unfold permutationOrder
  rw [he]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

theorem permutationOrder_reinsert_symm_eq {j : ℕ} {T : List SourceSlot}
    {u h u' h' : List SmallSlot}
    (hu : u.length=(Template.extracted j T).length)
    (hh : h.length=(Template.remainder j T).length)
    (hu' : u'.length=(Template.extracted j T).length)
    (hh' : h'.length=(Template.remainder j T).length)
    (hnd : (u++h).Nodup) (hnd' : (u'++h').Nodup) :
    permutationOrder (Template.reinsert_perm j T u h hu hh).symm=
      permutationOrder (Template.reinsert_perm j T u' h' hu' hh').symm := by
  have hx : (Template.reinsert j T u h).Nodup := (Template.reinsert_perm j T u h hu hh).nodup_iff.mpr hnd
  have hx' : (Template.reinsert j T u' h').Nodup := (Template.reinsert_perm j T u' h' hu' hh').nodup_iff.mpr hnd'
  unfold permutationOrder
  rw [indexEquiv_symm_of_nodup _ hx,indexEquiv_symm_of_nodup _ hx',Equiv.symm_symm,Equiv.symm_symm]
  apply List.ext_getElem
  · simpa only [List.length_ofFn,Fintype.card_fin] using Fintype.card_congr (Template.reinsertPositions hu hh hu' hh')
  · intro n hn hn'
    simp only [List.getElem_ofFn]
    exact Template.indexEquiv_reinsert_val hu hh hu' hh' hnd hnd' ⟨n,by simpa only [List.length_ofFn] using hn⟩

theorem permutationOrder_reinsert_eq {j : ℕ} {T : List SourceSlot}
    {u h u' h' : List SmallSlot}
    (hu : u.length=(Template.extracted j T).length)
    (hh : h.length=(Template.remainder j T).length)
    (hu' : u'.length=(Template.extracted j T).length)
    (hh' : h'.length=(Template.remainder j T).length)
    (hnd : (u++h).Nodup) (hnd' : (u'++h').Nodup) :
    permutationOrder (Template.reinsert_perm j T u h hu hh)=
      permutationOrder (Template.reinsert_perm j T u' h' hu' hh') := by
  obtain ⟨f,hfu,hfh,hfr⟩ := Template.exists_reinsert_common_map j T u h u' h' hu hh hu' hh' hnd
  have hfs : (u++h).map f=u'++h' := by rw [List.map_append,hfu,hfh]
  have hmatch : ∀i a,(u++h).get a=(Template.reinsert j T u h).get i →
      (u'++h').get (Template.splitPositions hu hh hu' hh' a)=
        (Template.reinsert j T u' h').get (Template.reinsertPositions hu hh hu' hh' i) := by
    intro i a ha
    change (u'++h').get (finCongr _ a)=(Template.reinsert j T u' h').get (finCongr _ i)
    rw [get_finCongr_of_map_eq f hfs,get_finCongr_of_map_eq f hfr,ha]
  unfold permutationOrder
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_append,hu,hh,hu',hh']
  · intro n hn hn'
    simp only [List.getElem_ofFn]
    have he := indexEquiv_symm_naturality (Template.reinsert_perm j T u h hu hh)
      (Template.reinsert_perm j T u' h' hu' hh') hnd'
      (Template.reinsertPositions hu hh hu' hh') (Template.splitPositions hu hh hu' hh')
      hmatch ⟨n,by simpa only [List.length_ofFn] using hn⟩
    exact congrArg Fin.val he

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
