import Mathlib

namespace OAI

                               
section
namespace UniformKServer.KeyEdits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I J : Type*}

/-- Fixed earlier and later structures implement precedence. Label recycling
is immaterial to this one-edit operation: an unchanged record has its old
label and both other structures are held fixed. -/
def overlay (earlier : Option J) (label : I → J) (later : J) (o : Option I) : J :=
  earlier.getD ((o.map label).getD later)

def changed (earlier : Option J) (label : I → J) (later : J) (old new : Option I) : ℝ :=
  if overlay earlier label later old = overlay earlier label later new then 0 else 1

def uncovered (o : Option I) : ℝ := if o.isNone then 1 else 0

def retirement (old : Option I) (keep : I → Bool) : ℝ :=
  match old with
  | none => 0
  | some i => if keep i then 0 else 1

def next (old : List I) (keep : I → Bool) (n : I) : List I := old.filter keep ++ [n]
theorem first_persists (old : List I) (keep cover : I → Bool) (n i : I)
    (hfirst : old.find? cover = some i) (hkeep : keep i = true) :
    (next old keep n).find? cover = some i := by
  unfold next
  induction old with
  | nil => simp at hfirst
  | cons a old ih =>
    by_cases ha : cover a = true
    · have hai : a = i := by simpa [ha] using hfirst
      subst a
      simp [hkeep,ha]
    · have ht : old.find? cover = some i := by simpa [ha] using hfirst
      have hi := ih ht
      by_cases hk : keep a = true <;> simp [hk,ha,hi]

theorem changed_bounds (earlier : Option J) (label : I → J) (later : J) (old new : Option I) :
    changed earlier label later old new ∈ Set.Icc (0:ℝ) 1 := by
  unfold changed
  split_ifs <;> constructor <;> norm_num

@[simp] theorem changed_self (earlier : Option J) (label : I → J) (later : J) (old : Option I) :
    changed earlier label later old old = 0 := by simp [changed]

theorem uncovered_bounds (o : Option I) : uncovered o ∈ Set.Icc (0:ℝ) 1 := by
  cases o <;> norm_num [uncovered]

theorem none_charge (earlier : Option J) (label : I → J) (later : J) (new : Option I) :
    changed earlier label later none new+uncovered new-uncovered (none : Option I) ≤ 0 := by
  cases new with
  | none => simp [uncovered]
  | some i =>
    have h := (changed_bounds earlier label later none (some i)).2
    simp only [uncovered,Option.isNone_some,Bool.false_eq_true,ite_false,Option.isNone_none,ite_true] at *
    linarith
/-- All three rows of the source noncoverage table, including changes hidden
by higher-priority structures. Covers/radii are persistent for old records. -/
theorem insertion_stationary (old : List I) (keep cover : I → Bool) (n : I)
    (earlier : Option J) (label : I → J) (later : J) :
    changed earlier label later (old.find? cover) ((next old keep n).find? cover) +
      uncovered ((next old keep n).find? cover)-uncovered (old.find? cover) ≤
        2*retirement (old.find? cover) keep
 := by
  cases hfirst : old.find? cover with
  | none =>
    simpa only [retirement,mul_zero] using
      none_charge earlier label later ((next old keep n).find? cover)
  | some i =>
    by_cases hk : keep i = true
    · rw [first_persists old keep cover n i hfirst hk,changed_self]
      simp [retirement,hk]
    · have hc := (changed_bounds earlier label later (some i) ((next old keep n).find? cover)).2
      have hu := (uncovered_bounds ((next old keep n).find? cover)).2
      simp only [uncovered,Option.isNone_some,Bool.false_eq_true,ite_false,retirement,ite_eq_right hk] at *
      linarith

theorem insertion_mover (old : List I) (keep cover : I → Bool) (n : I)
    (earlier : Option J) (label : I → J) (later : J) :
    changed earlier label later (old.find? cover) ((next old keep n).find? cover) -
      uncovered (old.find? cover) ≤ retirement (old.find? cover) keep := by
  cases hfirst : old.find? cover with
  | none =>
    have hc := (changed_bounds earlier label later none ((next old keep n).find? cover)).2
    simp only [uncovered,Option.isNone_none,ite_true,retirement]
    linarith
  | some i =>
    by_cases hk : keep i = true
    · rw [first_persists old keep cover n i hfirst hk,changed_self]
      simp [uncovered,retirement,hk]
    · simpa only [uncovered,Option.isNone_some,Bool.false_eq_true,ite_false,sub_zero,retirement,ite_eq_right hk]
        using (changed_bounds earlier label later (some i) ((next old keep n).find? cover)).2

theorem shadowed (j : J) (label : I → J) (later : J) (old new : Option I) :
    changed (some j) label later old new = 0 := by simp [changed,overlay]
end
end UniformKServer.KeyEdits

end

end OAI
