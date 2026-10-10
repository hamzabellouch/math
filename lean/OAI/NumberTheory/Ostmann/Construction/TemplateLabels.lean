import OAI.NumberTheory.Ostmann.Construction.PrimeSources
import OAI.NumberTheory.Ostmann.Construction.TemplateReinsert

namespace OAI

noncomputable section
namespace Ostmann.Construction.Template

def Matches (T : List SourceSlot) (x : List SmallSlot) : Prop :=
  x.map (fun q => (q.role,q.origin))=T.map (fun q => (q.role,q.origin))

theorem matches_length {T : List SourceSlot} {x : List SmallSlot} (h : Matches T x) :
    x.length=T.length := by
  have hlen := congrArg List.length h
  simpa only [List.length_map] using hlen

theorem assignedSlots_matches (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) : Matches T (assignedSlots sources T x) := by
  unfold Matches assignedSlots sample
  rw [List.map_ofFn]
  exact List.ofFn_getElem_eq_map T (fun q => (q.role,q.origin))

theorem reinsert_matches (j : ℕ) (T : List SourceSlot) (u h : List SmallSlot)
    (hu : Matches (extracted j T) u) (hh : Matches (remainder j T) h) :
    Matches T (reinsert j T u h) := by
  induction T generalizing u h with
  | nil => rfl
  | cons q T ih =>
    by_cases hq : q.role=.compensation j
    · cases u with
      | nil => simp [Matches,extracted,hq] at hu
      | cons a u =>
        have hu' : (a.role,a.origin)=(q.role,q.origin) ∧ Matches (extracted j T) u := by
          simpa [Matches,extracted,hq] using hu
        have hh' : Matches (remainder j T) h := by simpa [Matches,remainder,hq] using hh
        have hi := ih u h hu'.2 hh'
        simpa only [Matches,reinsert,hq,ite_true,List.headD_cons,List.tail_cons,List.map_cons,
          hu'.1,List.cons.injEq,true_and] using hi
    · cases h with
      | nil => simp [Matches,remainder,hq] at hh
      | cons a h =>
        have hu' : Matches (extracted j T) u := by simpa [Matches,extracted,hq] using hu
        have hh' : (a.role,a.origin)=(q.role,q.origin) ∧ Matches (remainder j T) h := by
          simpa [Matches,remainder,hq] using hh
        have hi := ih u h hu' hh'.2
        simpa only [Matches,reinsert,hq,ite_false,List.headD_cons,List.tail_cons,List.map_cons,
          hh'.1,List.cons.injEq,true_and] using hi

theorem matches_halves (T : List SourceSlot) (x : List SmallSlot)
    (h : Matches (T++T) x) :
    Matches T (x.take T.length) ∧ Matches T (x.drop T.length) := by
  have ht := congrArg (List.take T.length) h
  have hd := congrArg (List.drop T.length) h
  constructor
  · simpa [Matches,List.map_append] using ht
  · simpa [Matches,List.map_append] using hd

end Ostmann.Construction.Template

end

end OAI
