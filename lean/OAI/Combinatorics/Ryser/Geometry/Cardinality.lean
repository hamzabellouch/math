import OAI.Combinatorics.Ryser.Geometry.Basic
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [instFieldF : Field F] [Fintype F] [instDecidableEqF : DecidableEq F]

@[simp] theorem card_point :
    Fintype.card (Point F) = Fintype.card F ^ 2 := let _ := instFieldF; let _ := instDecidableEqF; by
  simp only [Point, Fintype.card_prod, pow_two]

@[simp] theorem card_direction :
    Fintype.card (Direction F) = Fintype.card F + 1 := let _ := instFieldF; let _ := instDecidableEqF; by
  exact Fintype.card_option

@[simp] theorem card_affineLine :
    Fintype.card (AffineLine F) = Fintype.card F * (Fintype.card F + 1) := by
  simp only [AffineLine, Fintype.card_prod, card_direction, Nat.mul_comm]

@[simp] theorem card_projectivePoint :
    Fintype.card (ProjectivePoint F) =
      Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp only [ProjectivePoint, Fintype.card_sum, card_point, card_direction, Nat.add_assoc]

@[simp] theorem card_projectiveLine :
    Fintype.card (ProjectiveLine F) =
      Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp only [ProjectiveLine, Fintype.card_option, card_affineLine,
    Nat.mul_add, Nat.mul_one, pow_two]

def linePointEquiv (l : AffineLine F) : F ≃ ↥(linePoints l) := by
  rcases l with ⟨d, b⟩
  cases d with
  | none =>
      refine
        { toFun := fun t => ⟨(b, t), by simp [Incidence, projection]⟩
          invFun := fun p => p.val.2
          left_inv := fun _ => rfl
          right_inv := ?_ }
      intro p
      apply Subtype.ext
      apply Prod.ext
      · have hp := (mem_linePoints p.val (none, b)).mp p.property
        change p.val.1 = b at hp
        exact hp.symm
      · rfl
  | some a =>
      refine
        { toFun := fun t => ⟨(t, b + a * t), by simp [Incidence, projection]⟩
          invFun := fun p => p.val.1
          left_inv := fun _ => rfl
          right_inv := ?_ }
      intro p
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · have hp := (mem_linePoints p.val (some a, b)).mp p.property
        change p.val.2 - a * p.val.1 = b at hp
        simpa only [sub_add_cancel] using
          (congrArg (fun u : F => u + a * p.val.1) hp).symm

@[simp] theorem card_linePoints (l : AffineLine F) :
    (linePoints l).card = Fintype.card F := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (linePointEquiv l)).symm

theorem card_projection_fiber (d : Direction F) (b : F) :
    (Finset.univ.filter (fun p : Point F => projection d p = b)).card =
      Fintype.card F :=
  card_linePoints (d, b)

def affinePencilFiniteEquiv (p : Point F) :
    Direction F ≃ ↥(affinePencil (Sum.inl p)) where
  toFun d := ⟨lineThrough d p, by simp⟩
  invFun l := l.val.1
  left_inv _ := rfl
  right_inv l := by
    apply Subtype.ext
    have hl : Incidence p l.val :=
      (mem_affinePencil (Sum.inl p) l.val).mp l.property
    exact (eq_lineThrough_of_incidence hl).symm

def affinePencilInfiniteEquiv (d : Direction F) :
    F ≃ ↥(affinePencil (Sum.inr d)) where
  toFun b := ⟨(d, b), by simp⟩
  invFun l := l.val.2
  left_inv _ := rfl
  right_inv l := by
    apply Subtype.ext
    apply Prod.ext
    · exact (mem_affinePencil (Sum.inr d) l.val).mp l.property
    · rfl

@[simp] theorem card_affinePencil_finite (p : Point F) :
    (affinePencil (Sum.inl p)).card = Fintype.card F + 1 := by
  simpa only [Fintype.card_coe, card_direction] using
    (Fintype.card_congr (affinePencilFiniteEquiv p)).symm

@[simp] theorem card_affinePencil_infinite (d : Direction F) :
    (affinePencil (Sum.inr d)).card = Fintype.card F := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr (affinePencilInfiniteEquiv d)).symm

theorem projectiveLinePoints_some (l : AffineLine F) :
    projectiveLinePoints (some l) = (linePoints l).disjSum {l.1} := by
  ext p
  cases p with
  | inl p => simp
  | inr d => simp

theorem projectiveLinePoints_none :
    projectiveLinePoints (none : ProjectiveLine F) =
      (∅ : Finset (Point F)).disjSum (Finset.univ : Finset (Direction F)) := by
  ext p
  cases p with
  | inl p => simp
  | inr d => simp

theorem projectivePencil_finite (p : Point F) :
    projectivePencil (Sum.inl p) =
      (affinePencil (Sum.inl p)).map Function.Embedding.some := by
  ext l
  cases l with
  | none => simp [Finset.mem_map]
  | some l => simp [Finset.mem_map]

theorem projectivePencil_infinite (d : Direction F) :
    projectivePencil (Sum.inr d) = (affinePencil (Sum.inr d)).insertNone := by
  ext l
  cases l with
  | none => simp
  | some l => simp

@[simp] theorem card_projectiveLinePoints (l : ProjectiveLine F) :
    (projectiveLinePoints l).card = Fintype.card F + 1 := by
  cases l with
  | none =>
      rw [projectiveLinePoints_none, Finset.card_disjSum, Finset.card_empty,
        Finset.card_univ, card_direction, Nat.zero_add]
  | some l =>
      rw [projectiveLinePoints_some, Finset.card_disjSum, card_linePoints,
        Finset.card_singleton]

@[simp] theorem card_projectivePencil (p : ProjectivePoint F) :
    (projectivePencil p).card = Fintype.card F + 1 := by
  cases p with
  | inl p =>
      rw [projectivePencil_finite, Finset.card_map, card_affinePencil_finite]
  | inr d =>
      rw [projectivePencil_infinite, Finset.card_insertNone, card_affinePencil_infinite]

end RyserCoveringCounterexample

end OAI
