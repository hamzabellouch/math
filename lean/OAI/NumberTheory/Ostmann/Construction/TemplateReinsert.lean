import OAI.NumberTheory.Ostmann.Construction.Template

namespace OAI

noncomputable section
namespace Ostmann.Construction.Template

def extracted (j : ℕ) (T : List SourceSlot) : List SourceSlot :=
  T.filter (fun q => decide (q.role = .compensation j))

def reinsert (j : ℕ) : List SourceSlot → List SmallSlot → List SmallSlot → List SmallSlot
  | [], _, _ => []
  | q::T, u, h => if q.role = .compensation j then
      u.headD ⟨q.role,0,q.origin⟩ :: reinsert j T u.tail h
    else h.headD ⟨q.role,0,q.origin⟩ :: reinsert j T u h.tail

theorem reinsert_perm (j : ℕ) (T : List SourceSlot) (u h : List SmallSlot)
    (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length) :
    (reinsert j T u h).Perm (u++h) := by
  induction T generalizing u h with
  | nil =>
    have hu0 : u=[] := List.length_eq_zero_iff.mp (by simpa [extracted] using hu)
    have hh0 : h=[] := List.length_eq_zero_iff.mp (by simpa [remainder] using hh)
    simp [reinsert, hu0, hh0]
  | cons q T ih =>
    by_cases hq : q.role=.compensation j
    · cases u with
      | nil => simp [extracted, hq] at hu
      | cons a u =>
        have hu' : u.length=(extracted j T).length := by simpa [extracted, hq] using hu
        have hh' : h.length=(remainder j T).length := by simpa [remainder, hq] using hh
        simpa only [reinsert, hq, ite_true, List.headD_cons, List.tail_cons,
          List.cons_append] using List.Perm.cons a (ih u h hu' hh')
    · cases h with
      | nil => simp [remainder, hq] at hh
      | cons a h =>
        have hu' : u.length=(extracted j T).length := by simpa [extracted, hq] using hu
        have hh' : h.length=(remainder j T).length := by simpa [remainder, hq] using hh
        have hp := List.Perm.cons a (ih u h hu' hh')
        have hm : (a::(u++h)).Perm (u++a::h) := (List.perm_middle).symm
        simpa only [reinsert, hq, ite_false, List.headD_cons, List.tail_cons] using hp.trans hm

theorem reinsert_length (j : ℕ) (T : List SourceSlot) (u h : List SmallSlot)
    (hu : u.length=(extracted j T).length) (hh : h.length=(remainder j T).length) :
    (reinsert j T u h).length=u.length+h.length := by
  simpa only [List.length_append] using (reinsert_perm j T u h hu hh).length_eq

end Ostmann.Construction.Template

end

end OAI
