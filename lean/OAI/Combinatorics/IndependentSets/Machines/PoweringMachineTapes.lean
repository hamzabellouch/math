import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.PoweringMachineWord

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineTapes

abbrev Tape (max : Nat) := Fin 11 ⊕ Fin max

def table (max : Nat) : Tape max := .inl 0
def start (max : Nat) : Tape max := .inl 1
def query (max : Nat) : Tape max := .inl 2
def scan (max : Nat) : Tape max := .inl 3
def reverse (max : Nat) : Tape max := .inl 4
def scratch (max : Nat) : Tape max := .inl 5
def leftEndpoint (max : Nat) : Tape max := .inl 6
def rightEndpoint (max : Nat) : Tape max := .inl 7
def leftCopy (max : Nat) : Tape max := .inl 8
def rightCopy (max : Nat) : Tape max := .inl 9
def rowOutput (max : Nat) : Tape max := .inl 10

def endpoint (max : Nat) (target : Bool) : Tape max :=
  if target then rightEndpoint max else leftEndpoint max

@[simp] theorem endpoint_false (max : Nat) : endpoint max false = leftEndpoint max := rfl
@[simp] theorem endpoint_true (max : Nat) : endpoint max true = rightEndpoint max := rfl

def wordSharedRole (target : Bool) (i : Fin 6) : Fin 11 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else
  if i = 3 then 4 else if i = 4 then 5 else if target then 7 else 6

def trajectoryPlacement {t max : Nat} (h : t ≤ max) : Fin (t + 1) → Tape max :=
  Fin.cases (start max) (fun i => .inr (Fin.castLE h i))

def wordPlacement {t max : Nat} (h : t ≤ max) (target : Bool) :
    PoweringMachineWord.Tape t → Tape max
  | .inl i => .inl (wordSharedRole target i)
  | .inr i => trajectoryPlacement h i

@[simp] theorem wordPlacement_inl_zero {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 0) = table max := rfl
@[simp] theorem wordPlacement_inl_one {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 1) = query max := rfl
@[simp] theorem wordPlacement_inl_two {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 2) = scan max := rfl
@[simp] theorem wordPlacement_inl_three {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 3) = reverse max := rfl
@[simp] theorem wordPlacement_inl_four {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 4) = scratch max := rfl
@[simp] theorem wordPlacement_inl_five {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 5) = endpoint max target := by cases target <;> rfl
@[simp] theorem wordPlacement_first {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inr (PoweringMachineWord.first t)) = start max := rfl
@[simp] theorem wordPlacement_succ {t max : Nat} (h : t ≤ max) (target : Bool) (i : Fin t) :
    wordPlacement h target (.inr i.succ) = .inr (Fin.castLE h i) := rfl

def relationPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 2 else
    if i = 3 then 3 else if i = 4 then 10 else 5)

@[simp] theorem relationPlacement_zero (max : Nat) : relationPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem relationPlacement_one (max : Nat) : relationPlacement max 1 = table max := rfl
@[simp] theorem relationPlacement_two (max : Nat) : relationPlacement max 2 = query max := rfl
@[simp] theorem relationPlacement_three (max : Nat) : relationPlacement max 3 = scan max := rfl
@[simp] theorem relationPlacement_four (max : Nat) : relationPlacement max 4 = rowOutput max := rfl
@[simp] theorem relationPlacement_five (max : Nat) : relationPlacement max 5 = scratch max := rfl

def equalityPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 7 else if i = 2 then 8 else
    if i = 3 then 9 else if i = 4 then 5 else 10)

@[simp] theorem equalityPlacement_zero (max : Nat) : equalityPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem equalityPlacement_one (max : Nat) : equalityPlacement max 1 = rightEndpoint max := rfl
@[simp] theorem equalityPlacement_two (max : Nat) : equalityPlacement max 2 = leftCopy max := rfl
@[simp] theorem equalityPlacement_three (max : Nat) : equalityPlacement max 3 = rightCopy max := rfl
@[simp] theorem equalityPlacement_four (max : Nat) : equalityPlacement max 4 = scratch max := rfl
@[simp] theorem equalityPlacement_five (max : Nat) : equalityPlacement max 5 = rowOutput max := rfl

theorem wordSharedRole_injective (target : Bool) : Function.Injective (wordSharedRole target) := by
  cases target <;> decide

theorem wordSharedRole_ne_start (target : Bool) :
    ∀ i : Fin 6, wordSharedRole target i ≠ 1 := by
  cases target <;> decide

theorem wordSharedRole_ne_rowOutput (target : Bool) :
    ∀ i : Fin 6, wordSharedRole target i ≠ 10 := by
  cases target <;> decide

theorem trajectoryPlacement_injective {t max : Nat} (ht : t ≤ max) :
    Function.Injective (trajectoryPlacement ht) := by
  intro a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro _
      rfl
    · intro h
      change (Sum.inl (1 : Fin 11) : Tape max) = .inr (Fin.castLE ht j) at h
      cases h
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro h
      change (Sum.inr (Fin.castLE ht i) : Tape max) = .inl (1 : Fin 11) at h
      cases h
    · intro h
      change (Sum.inr (Fin.castLE ht i) : Tape max) = .inr (Fin.castLE ht j) at h
      have hc : Fin.castLE ht i = Fin.castLE ht j := Sum.inr.inj h
      have hv : i.val = j.val := congrArg (fun x : Fin max => x.val) hc
      have hij : i = j := Fin.ext hv
      exact congrArg Fin.succ hij

theorem wordShared_ne_trajectory {t max : Nat} (ht : t ≤ max) (target : Bool)
    (i : Fin 6) :
    ∀ j : Fin (t + 1),
      (Sum.inl (wordSharedRole target i) : Tape max) ≠ trajectoryPlacement ht j := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · intro h
    change (Sum.inl (wordSharedRole target i) : Tape max) = .inl (1 : Fin 11) at h
    exact wordSharedRole_ne_start target i (Sum.inl.inj h)
  · intro h
    change (Sum.inl (wordSharedRole target i) : Tape max) = .inr (Fin.castLE ht k) at h
    cases h

theorem wordPlacement_injective {t max : Nat} (ht : t ≤ max) (target : Bool) :
    Function.Injective (wordPlacement ht target) := by
  intro a b h
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          exact congrArg Sum.inl (wordSharedRole_injective target (Sum.inl.inj h))
      | inr j =>
          exact False.elim (wordShared_ne_trajectory ht target i j h)
  | inr i =>
      cases b with
      | inl j =>
          exact False.elim (wordShared_ne_trajectory ht target j i h.symm)
      | inr j =>
          exact congrArg Sum.inr (trajectoryPlacement_injective ht h)

theorem relationPlacement_injective (max : Nat) : Function.Injective (relationPlacement max) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [relationPlacement]

theorem equalityPlacement_injective (max : Nat) : Function.Injective (equalityPlacement max) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [equalityPlacement]

theorem wordPlacement_ne_rowOutput {t max : Nat} (ht : t ≤ max) (target : Bool)
    (i : PoweringMachineWord.Tape t) : wordPlacement ht target i ≠ rowOutput max := by
  cases i with
  | inl i =>
      intro h
      exact wordSharedRole_ne_rowOutput target i (Sum.inl.inj h)
  | inr j =>
      refine Fin.cases ?_ (fun i => ?_) j
      · intro h
        change (Sum.inl (1 : Fin 11) : Tape max) = .inl (10 : Fin 11) at h
        have hne : (1 : Fin 11) ≠ 10 := by decide
        exact hne (Sum.inl.inj h)
      · intro h
        change (Sum.inr (Fin.castLE ht i) : Tape max) = .inl (10 : Fin 11) at h
        cases h

theorem shared_ne_wordPlacement_succ {t max : Nat} (ht : t ≤ max) (target : Bool)
    (role : Fin 11) (i : Fin t) :
    (Sum.inl role : Tape max) ≠ wordPlacement ht target (.inr i.succ) := by
  intro h
  change (Sum.inl role : Tape max) = .inr (Fin.castLE ht i) at h
  cases h

end IndependentSetsGames.Foundations.Complexity.PoweringMachineTapes

end OAI
