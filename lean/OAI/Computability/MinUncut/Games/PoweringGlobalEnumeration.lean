import Mathlib
import OAI.Computability.MinUncut.Machines.PoweringMachineRotor

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringGlobalEnumeration

open PoweringMachineLoop PoweringMachineInitialize

def headerTapeEquiv : HeaderTape ≃ Fin 4 where
  toFun
    | .source => 0
    | .counter => 1
    | .vertices => 2
    | .darts => 3
  invFun i := if i = 0 then .source else if i = 1 then .counter
    else if i = 2 then .vertices else .darts
  left_inv tape := by cases tape <;> rfl
  right_inv i := by fin_cases i <;> rfl

def unitTapeEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := (Fin.eq_zero i).symm

def sharedTapeEquiv (max : Nat) : PoweringMachineTapes.Tape max ≃ Fin (11 + max) :=
  finSumFinEquiv

def extraTapeEquiv (max : Nat) : ExtraTape max ≃ Fin (11 + max + 1) :=
  (Equiv.sumCongr (sharedTapeEquiv max) unitTapeEquiv).trans finSumFinEquiv

def globalTapeEquiv (max : Nat) : GlobalTape max ≃ Fin (4 + (11 + max + 1)) :=
  (Equiv.sumCongr headerTapeEquiv (extraTapeEquiv max)).trans finSumFinEquiv

def enumeration (max : Nat) : Fin (4 + (11 + max + 1)) ≃ GlobalTape max :=
  (globalTapeEquiv max).symm

@[simp] theorem globalTapeEquiv_enumeration (max : Nat) (i : Fin (4 + (11 + max + 1))) :
    globalTapeEquiv max (enumeration max i) = i :=
  (globalTapeEquiv max).apply_symm_apply i

@[simp] theorem enumeration_globalTapeEquiv (max : Nat) (tape : GlobalTape max) :
    enumeration max (globalTapeEquiv max tape) = tape :=
  (globalTapeEquiv max).symm_apply_apply tape

@[simp] theorem source_index (max : Nat) :
    (globalTapeEquiv max (.inl .source)).val = 0 := rfl

@[simp] theorem counter_index (max : Nat) :
    (globalTapeEquiv max (.inl .counter)).val = 1 := rfl

@[simp] theorem vertices_index (max : Nat) :
    (globalTapeEquiv max (.inl .vertices)).val = 2 := rfl

@[simp] theorem darts_index (max : Nat) :
    (globalTapeEquiv max (.inl .darts)).val = 3 := rfl

theorem sharedRole_index (max : Nat) (i : Fin 11) :
    (globalTapeEquiv max (.inr (.inl (.inl i)))).val = 4 + i.val := rfl

theorem trajectory_index (max : Nat) (i : Fin max) :
    (globalTapeEquiv max (.inr (.inl (.inr i)))).val = 4 + (11 + i.val) := rfl

@[simp] theorem finalOutput_index (max : Nat) :
    (globalTapeEquiv max (finalOutput max)).val = 4 + (11 + max) := rfl

theorem card_globalTape (max : Nat) :
    Fintype.card (GlobalTape max) = 4 + (11 + max + 1) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (globalTapeEquiv max)

theorem natCard_globalTape (max : Nat) :
    Nat.card (GlobalTape max) = 4 + (11 + max + 1) := by
  simpa only [Nat.card_fin] using Nat.card_congr (globalTapeEquiv max)

def allTapes (max : Nat) : List (GlobalTape max) := List.ofFn (enumeration max)

theorem allTapes_length (max : Nat) : (allTapes max).length = 4 + (11 + max + 1) := by
  simpa only [allTapes] using (List.length_ofFn (f := enumeration max))

theorem mem_allTapes (max : Nat) (tape : GlobalTape max) : tape ∈ allTapes max := by
  change tape ∈ List.ofFn (enumeration max)
  apply List.mem_ofFn.mpr
  exact ⟨globalTapeEquiv max tape, enumeration_globalTapeEquiv max tape⟩

end MinUncutGames.Foundations.Complexity.PoweringGlobalEnumeration

end

end OAI
