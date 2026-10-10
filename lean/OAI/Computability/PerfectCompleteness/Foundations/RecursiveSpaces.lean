import Mathlib.Basic.Finite.Prod
import OAI.Computability.PerfectCompleteness.Foundations.PartitionsLemmas

namespace OAI

section

namespace PerfectCompleteness.RecursiveSpaces

open PointwiseSpaces

universe u v w

def Slots (branch : Nat → Nat) : Nat → Type
  | 0 => Unit
  | n + 1 => Fin (branch n) × Slots branch n

instance slotsFintype (branch : Nat → Nat) (n : Nat) : Fintype (Slots branch n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
      letI : Fintype (Slots branch n) := ih
      exact inferInstanceAs (Fintype (Fin (branch n) × Slots branch n))

instance slotsDecidableEq (branch : Nat → Nat) (n : Nat) :
    DecidableEq (Slots branch n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
      letI : DecidableEq (Slots branch n) := ih
      exact inferInstanceAs (DecidableEq (Fin (branch n) × Slots branch n))

variable {branch : Nat → Nat} {n : Nat}

abbrev Assignment (A : Slots branch n → Type u) := ∀ s, A s

abbrev childFamily (A : Slots branch (n + 1) → Type u) (i : Fin (branch n)) :
    Slots branch n → Type u := fun s => A (i, s)

def childRestriction (A : Slots branch (n + 1) → Type u) (i : Fin (branch n)) :
    Assignment A → Assignment (childFamily A i) := fun x s => x (i, s)

theorem assignment_finite (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    Finite (Assignment A) := by
  infer_instance

theorem childRestriction_surjective (A : Slots branch (n + 1) → Type u)
    (hnonempty : ∀ s, Nonempty (A s)) (i : Fin (branch n)) :
    Function.Surjective (childRestriction A i) := by
  classical
  intro y
  let base : ∀ j : Fin (branch n), Assignment (childFamily A j) :=
    fun j s => Classical.choice (hnonempty (j, s))
  refine ⟨fun s => Function.update base i y s.1 s.2, ?_⟩
  funext s
  simp only [childRestriction, Function.update_self]

def space (𝕜 : Type w) [Field 𝕜] (branch : Nat → Nat) :
    (n : Nat) → (A : Slots branch n → Type u) →
      Submodule 𝕜 (Assignment A → 𝕜)
  | 0, _ => ⊤
  | n + 1, A => childSpace (childRestriction A)
      (fun i => space 𝕜 branch n (childFamily A i))

variable {𝕜 : Type w} [Field 𝕜]

@[simp] theorem space_zero (A : Slots branch 0 → Type u) :
    space 𝕜 branch 0 A = ⊤ := rfl

theorem space_succ (A : Slots branch (n + 1) → Type u) :
    space 𝕜 branch (n + 1) A = childSpace (childRestriction A)
      (fun i => space 𝕜 branch n (childFamily A i)) := rfl

theorem space_finite [Finite 𝕜] (A : Slots branch n → Type u)
    [∀ s, Finite (A s)] : Finite (space 𝕜 branch n A) := by
  infer_instance

theorem one_mem_space (branch : Nat → Nat) :
    ∀ (n : Nat) (A : Slots branch n → Type u),
      (∀ k < n, 0 < branch k) → (1 : Assignment A → 𝕜) ∈ space 𝕜 branch n A := by
  intro n
  induction n with
  | zero =>
      intro A _
      exact Submodule.mem_top
  | succ n ih =>
      intro A hbranch
      let i : Fin (branch n) := ⟨0, hbranch n (Nat.lt_succ_self n)⟩
      apply one_mem_childSpace_of_child (childRestriction A)
        (fun j => space 𝕜 branch n (childFamily A j)) i
      exact ih (childFamily A i)
        (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n)))

theorem space_le_squareSpace (A : Slots branch n → Type u)
    (hbranch : ∀ k < n, 0 < branch k) :
    space 𝕜 branch n A ≤ squareSpace (space 𝕜 branch n A) :=
  le_squareSpace _ (one_mem_space branch n A hbranch)

theorem one_mem_space_square (A : Slots branch n → Type u)
    (hbranch : ∀ k < n, 0 < branch k) :
    (1 : Assignment A → 𝕜) ∈ squareSpace (space 𝕜 branch n A) :=
  one_mem_squareSpace _ (one_mem_space branch n A hbranch)

theorem child_square_le_space (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) :
    (squareSpace (space 𝕜 branch n (childFamily A i))).map
        (pullback 𝕜 (childRestriction A i)) ≤ space 𝕜 branch (n + 1) A :=
  child_square_le (childRestriction A) (fun j => space 𝕜 branch n (childFamily A j)) i

theorem child_le_space (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (hbranch : ∀ k < n, 0 < branch k) :
    (space 𝕜 branch n (childFamily A i)).map
        (pullback 𝕜 (childRestriction A i)) ≤ space 𝕜 branch (n + 1) A :=
  child_le (childRestriction A) (fun j => space 𝕜 branch n (childFamily A j)) i
    (one_mem_space branch n (childFamily A i) hbranch)

theorem child_pullback_injective (A : Slots branch (n + 1) → Type u)
    (hnonempty : ∀ s, Nonempty (A s)) (i : Fin (branch n)) :
    Function.Injective (pullback 𝕜 (childRestriction A i)) :=
  pullback_injective _ (childRestriction_surjective A hnonempty i)

def project {A : Slots branch n → Type u} {B : Slots branch n → Type v}
    (e : ∀ s, A s → B s) : Assignment A → Assignment B :=
  fun x s => e s (x s)

@[simp] theorem project_apply {A : Slots branch n → Type u} {B : Slots branch n → Type v}
    (e : ∀ s, A s → B s) (x : Assignment A) (s : Slots branch n) :
    project e x s = e s (x s) := rfl

theorem project_surjective {A : Slots branch n → Type u} {B : Slots branch n → Type v}
    (e : ∀ s, A s → B s) (he : ∀ s, Function.Surjective (e s)) :
    Function.Surjective (project e) :=
  Function.Surjective.piMap he

theorem project_child {A : Slots branch (n + 1) → Type u}
    {B : Slots branch (n + 1) → Type v} (e : ∀ s, A s → B s)
    (i : Fin (branch n)) (x : Assignment A) :
    project (fun s => e (i, s)) (childRestriction A i x) =
      childRestriction B i (project e x) := rfl

theorem space_project_le (branch : Nat → Nat) :
    ∀ (n : Nat) (A : Slots branch n → Type u) (B : Slots branch n → Type v)
      (e : ∀ s, A s → B s),
      (space 𝕜 branch n B).map (pullback 𝕜 (project e)) ≤ space 𝕜 branch n A := by
  intro n
  induction n with
  | zero =>
      intro A B e
      exact le_top
  | succ n ih =>
      intro A B e
      apply childSpace_pullback_le (project e) (childRestriction B) (childRestriction A)
        (fun i => project (fun s => e (i, s)))
        (fun i => space 𝕜 branch n (childFamily B i))
        (fun i => space 𝕜 branch n (childFamily A i))
      · intro i x
        exact project_child e i x
      · intro i
        exact ih (childFamily A i) (childFamily B i) (fun s => e (i, s))

theorem squareSpace_project_le (A : Slots branch n → Type u) (B : Slots branch n → Type v)
    (e : ∀ s, A s → B s) :
    (squareSpace (space 𝕜 branch n B)).map (pullback 𝕜 (project e)) ≤
      squareSpace (space 𝕜 branch n A) :=
  squareSpace_pullback_le _ _ _ (space_project_le branch n A B e)

def spacePullback (A : Slots branch n → Type u) (B : Slots branch n → Type v)
    (e : ∀ s, A s → B s) : space 𝕜 branch n B →ₗ[𝕜] space 𝕜 branch n A where
  toFun f := ⟨pullback 𝕜 (project e) f,
    space_project_le branch n A B e (Submodule.mem_map_of_mem f.property)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem spacePullback_apply (A : Slots branch n → Type u) (B : Slots branch n → Type v)
    (e : ∀ s, A s → B s) (f : space 𝕜 branch n B) (x : Assignment A) :
    (spacePullback A B e f).val x = f.val (project e x) := rfl

theorem spacePullback_injective (A : Slots branch n → Type u) (B : Slots branch n → Type v)
    (e : ∀ s, A s → B s) (he : ∀ s, Function.Surjective (e s)) :
    Function.Injective (spacePullback (𝕜 := 𝕜) A B e) := by
  intro f g h
  apply Subtype.ext
  exact pullback_injective (project e) (project_surjective e he) (congrArg Subtype.val h)

end PerfectCompleteness.RecursiveSpaces

end

end OAI
