import OAI.NumberTheory.Ostmann.Construction.ReorderNaturalityIndex
import OAI.NumberTheory.Ostmann.Construction.TemplateReinsert

namespace OAI

noncomputable section
namespace Ostmann.Construction

theorem exists_map_of_nodup_length {A B : Type*} (xs : List A) (ys : List B)
    (hx : xs.Nodup) (hlen : xs.length=ys.length) (b0 : B) : ∃f:A→B,xs.map f=ys := by
  let f := Function.extend xs.get (fun i => ys.get (finCongr hlen i)) (fun _ => b0)
  refine ⟨f,?_⟩
  apply List.ext_get (by simpa only [List.length_map] using hlen)
  intro n hn hn'
  simp only [List.get_eq_getElem,List.getElem_map]
  change f (xs.get ⟨n,by simpa only [List.length_map] using hn⟩)=ys.get ⟨n,hn'⟩
  exact hx.injective_get.extend_apply _ _ _

namespace Template

theorem reinsert_map (j : ℕ) (T : List SourceSlot) (u h : List SmallSlot)
    (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length)
    (f : SmallSlot→SmallSlot) :
    reinsert j T (u.map f) (h.map f)=(reinsert j T u h).map f := by
  induction T generalizing u h with
  | nil => simp [reinsert]
  | cons q T ih =>
    by_cases hq : q.role=.compensation j
    · cases u with
      | nil => simp [extracted,hq] at hu
      | cons a u =>
        have hu' : u.length=(extracted j T).length := by simpa [extracted,hq] using hu
        have hh' : h.length=(remainder j T).length := by simpa [remainder,hq] using hh
        simpa only [reinsert,hq,ite_true,List.headD_cons,List.tail_cons,List.map_cons] using
          congrArg (List.cons (f a)) (ih u h hu' hh')
    · cases h with
      | nil => simp [remainder,hq] at hh
      | cons a h =>
        have hu' : u.length=(extracted j T).length := by simpa [extracted,hq] using hu
        have hh' : h.length=(remainder j T).length := by simpa [remainder,hq] using hh
        simpa only [reinsert,hq,ite_false,List.headD_cons,List.tail_cons,List.map_cons] using
          congrArg (List.cons (f a)) (ih u h hu' hh')

theorem exists_reinsert_common_map (j : ℕ) (T : List SourceSlot)
    (u h u' h' : List SmallSlot)
    (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length)
    (hu' : u'.length=(extracted j T).length) (hh' : h'.length=(remainder j T).length)
    (hnd : (u++h).Nodup) :
    ∃f:SmallSlot→SmallSlot,u.map f=u' ∧ h.map f=h' ∧
      (reinsert j T u h).map f=reinsert j T u' h' := by
  obtain ⟨f,hf⟩ := exists_map_of_nodup_length (u++h) (u'++h') hnd
    (by simp only [List.length_append,hu,hh,hu',hh']) ⟨.bulk,0,0⟩
  rw [List.map_append] at hf
  obtain ⟨hfu,hfh⟩ := List.append_inj hf (by simp only [List.length_map,hu,hu'])
  refine ⟨f,hfu,hfh,?_⟩
  rw [← reinsert_map j T u h hu hh f,hfu,hfh]

end Template
end Ostmann.Construction

end

end OAI
