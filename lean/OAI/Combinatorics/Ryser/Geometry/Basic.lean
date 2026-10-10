import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Filter
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample

abbrev Point (F : Type*) := F × F
abbrev Direction (F : Type*) := Option F
abbrev AffineLine (F : Type*) := Direction F × F
abbrev ProjectivePoint (F : Type*) := Point F ⊕ Direction F
abbrev ProjectiveLine (F : Type*) := Option (AffineLine F)

variable {F : Type*} [Field F]

def projection : Direction F → Point F → F
  | none, p => p.1
  | some a, p => p.2 - a * p.1

def Incidence (p : Point F) (l : AffineLine F) : Prop :=
  projection l.1 p = l.2

instance [DecidableEq F] (p : Point F) (l : AffineLine F) :
    Decidable (Incidence p l) :=
  inferInstanceAs (Decidable (projection l.1 p = l.2))

def lineThrough (d : Direction F) (p : Point F) : AffineLine F :=
  (d, projection d p)

@[simp] theorem projection_none (p : Point F) : projection none p = p.1 := rfl
@[simp] theorem projection_some (a : F) (p : Point F) :
    projection (some a) p = p.2 - a * p.1 := rfl
@[simp] theorem projection_some_zero (p : Point F) :
    projection (some 0) p = p.2 := by simp [projection]

@[simp] theorem incidence_mk (p : Point F) (d : Direction F) (b : F) :
    Incidence p (d, b) ↔ projection d p = b := Iff.rfl

@[simp] theorem lineThrough_direction (d : Direction F) (p : Point F) :
    (lineThrough d p).1 = d := rfl
@[simp] theorem lineThrough_offset (d : Direction F) (p : Point F) :
    (lineThrough d p).2 = projection d p := rfl
@[simp] theorem incidence_lineThrough (d : Direction F) (p : Point F) :
    Incidence p (lineThrough d p) := rfl

@[simp] theorem incidence_lineThrough_iff (d : Direction F) (p q : Point F) :
    Incidence p (lineThrough d q) ↔ projection d p = projection d q := Iff.rfl

theorem lineThrough_eq_iff (d : Direction F) (p q : Point F) :
    lineThrough d p = lineThrough d q ↔ projection d p = projection d q := by
  simp only [lineThrough, Prod.mk.injEq, true_and]

theorem eq_lineThrough_of_incidence {p : Point F} {l : AffineLine F}
    (h : Incidence p l) : l = lineThrough l.1 p := by
  apply Prod.ext
  · rfl
  · exact h.symm

theorem point_eq_of_projection_axes {p q : Point F}
    (hx : projection none p = projection none q)
    (hy : projection (some 0) p = projection (some 0) q) : p = q := by
  apply Prod.ext hx
  simpa only [projection_some_zero] using hy

theorem projection_add (d : Direction F) (p q : Point F) :
    projection d (p.1 + q.1, p.2 + q.2) = projection d p + projection d q := by
  cases d with
  | none => rfl
  | some slope => simp only [projection]; ring

theorem projection_sub (d : Direction F) (p q : Point F) :
    projection d (p.1 - q.1, p.2 - q.2) = projection d p - projection d q := by
  cases d with
  | none => rfl
  | some slope => simp only [projection]; ring

theorem projection_mul (d : Direction F) (c : F) (p : Point F) :
    projection d (c * p.1, c * p.2) = c * projection d p := by
  cases d with
  | none => rfl
  | some slope => simp only [projection]; ring

def ProjectiveIncidence : ProjectivePoint F → ProjectiveLine F → Prop
  | Sum.inl p, some l => Incidence p l
  | Sum.inr d, some l => d = l.1
  | Sum.inl _, none => False
  | Sum.inr _, none => True

instance [DecidableEq F] (p : ProjectivePoint F) (l : ProjectiveLine F) :
    Decidable (ProjectiveIncidence p l) := by
  cases p <;> cases l <;> simp only [ProjectiveIncidence] <;> infer_instance

@[simp] theorem projectiveIncidence_finite_affine (p : Point F) (l : AffineLine F) :
    ProjectiveIncidence (Sum.inl p) (some l) ↔ Incidence p l := Iff.rfl
@[simp] theorem projectiveIncidence_infinite_affine (d : Direction F) (l : AffineLine F) :
    ProjectiveIncidence (Sum.inr d) (some l) ↔ d = l.1 := Iff.rfl
@[simp] theorem projectiveIncidence_finite_infinity (p : Point F) :
    ¬ ProjectiveIncidence (Sum.inl p) (none : ProjectiveLine F) := not_false
@[simp] theorem projectiveIncidence_infinite_infinity (d : Direction F) :
    ProjectiveIncidence (Sum.inr d) (none : ProjectiveLine F) := trivial

section Finite
variable [Fintype F] [DecidableEq F]

def linePoints (l : AffineLine F) : Finset (Point F) :=
  Finset.univ.filter fun p => Incidence p l

def affinePencil (p : ProjectivePoint F) : Finset (AffineLine F) :=
  Finset.univ.filter fun l => ProjectiveIncidence p (some l)

def projectiveLinePoints (l : ProjectiveLine F) : Finset (ProjectivePoint F) :=
  Finset.univ.filter fun p => ProjectiveIncidence p l

def projectivePencil (p : ProjectivePoint F) : Finset (ProjectiveLine F) :=
  Finset.univ.filter fun l => ProjectiveIncidence p l

@[simp] theorem mem_linePoints (p : Point F) (l : AffineLine F) :
    p ∈ linePoints l ↔ Incidence p l := by simp only [linePoints, Finset.mem_filter,
    Finset.mem_univ, true_and]

@[simp] theorem mem_affinePencil (p : ProjectivePoint F) (l : AffineLine F) :
    l ∈ affinePencil p ↔ ProjectiveIncidence p (some l) := by
  simp only [affinePencil, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_projectiveLinePoints (p : ProjectivePoint F) (l : ProjectiveLine F) :
    p ∈ projectiveLinePoints l ↔ ProjectiveIncidence p l := by
  simp only [projectiveLinePoints, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_projectivePencil (p : ProjectivePoint F) (l : ProjectiveLine F) :
    l ∈ projectivePencil p ↔ ProjectiveIncidence p l := by
  simp only [projectivePencil, Finset.mem_filter, Finset.mem_univ, true_and]

end Finite
end RyserCoveringCounterexample

end OAI
