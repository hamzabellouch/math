import Mathlib
import OAI.Analysis.MatrixSigning.Realization.FixedSubroutineBridge
import OAI.Analysis.MatrixSigning.Machines.CopyInput

namespace OAI

namespace KS.W01.FixedCopy
open KS.W29

theorem activeFor_append (M : BinaryMachine) (c : Config M.states) (xs ys : List Bool) :
    Sequential.ActiveFor M c (xs ++ ys) ↔
      Sequential.ActiveFor M c xs ∧ Sequential.ActiveFor M (M.run c xs) ys := by
  induction xs generalizing c with
  | nil => simp [Sequential.ActiveFor, BinaryMachine.run]
  | cons b bs ih => simp [Sequential.ActiveFor, BinaryMachine.run, ih, and_assoc]

theorem reverse_active (xs ys zs bits : List Bool) (hlen : bits.length = xs.length) :
    Sequential.ActiveFor CopyInput.machine (CopyInput.cfg (some 0) xs ys zs) bits := by
  induction xs generalizing zs bits with
  | nil =>
      have hb : bits = [] := List.length_eq_zero_iff.mp hlen
      subst bits
      trivial
  | cons x xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons b bs =>
          constructor
          · exact Option.some_ne_none _
          · rw [CopyInput.reverse_step]
            exact ih _ _ (by simpa using hlen)

theorem restore_active (xs ys zs bits : List Bool) (hlen : bits.length ≤ zs.length + 1) :
    Sequential.ActiveFor CopyInput.machine (CopyInput.cfg (some 1) xs ys zs) bits := by
  induction bits generalizing xs ys zs with
  | nil => trivial
  | cons b bs ih =>
      constructor
      · exact Option.some_ne_none _
      · cases zs with
        | nil =>
            have hb : bs = [] := by
              apply List.length_eq_zero_iff.mp
              simp only [List.length_cons, List.length_nil] at hlen
              omega
            subst bs
            trivial
        | cons z zs =>
            rw [CopyInput.copy_step]
            apply ih
            simp only [List.length_cons] at hlen
            omega

theorem copy_haltsAfter (xs bits : List Bool) (hlen : bits.length = 2 * xs.length + 2) :
    Sequential.HaltsAfter CopyInput.machine (CopyInput.machine.init xs) bits := by
  constructor
  · obtain ⟨left, a, right, b, rfl, hl, hr⟩ := CopyInput.split_copy_fuel bits xs.length hlen
    have hi : CopyInput.machine.init xs = CopyInput.cfg (some 0) xs [] [] := by
      simp [BinaryMachine.init, CopyInput.cfg, CopyInput.machine]
    rw [hi]
    apply (activeFor_append CopyInput.machine (CopyInput.cfg (some 0) xs [] [])
      left (a :: (right ++ [b]))).mpr
    constructor
    · exact reverse_active xs [] [] left hl
    · rw [CopyInput.run_reverse xs [] [] left hl]
      simp only [List.append_nil, Sequential.ActiveFor]
      constructor
      · exact Option.some_ne_none _
      · rw [CopyInput.reverse_done]
        apply restore_active
        simp [hr]
  · rw [CopyInput.run_eq_copy xs bits hlen]
    rfl

def machine {k : ℕ} (ports : Fin 3 ↪ Fin k) : FixedStack.Machine :=
  FixedStack.lift3 CopyInput.machine ports

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) : FixedSequential.Program k :=
  FixedSequential.ofMachine (machine ports)

theorem config_ext {k q : ℕ} {c d : FixedStack.Config k q}
    (hs : c.state = d.state) (ht : c.«stacks» = d.«stacks») : c = d := by
  cases c
  cases d
  cases hs
  cases ht
  rfl

theorem project_start {k : ℕ} (ports : Fin 3 ↪ Fin k) («stacks» : Fin k → List Bool)
    (xs : List Bool) (hsrc : «stacks» (ports 0) = xs)
    (hdst : «stacks» (ports 1) = []) (hscratch : «stacks» (ports 2) = []) :
    FixedStack.project ports (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) =
      CopyInput.machine.init xs := by
  change Config.mk (some 0) (fun j => «stacks» (ports j)) =
    Config.mk (some 0) (fun j => if j = 0 then xs else [])
  congr 1
  funext j
  fin_cases j <;> simp [hsrc, hdst, hscratch]

theorem run_copy_restore {k : ℕ} (ports : Fin 3 ↪ Fin k)
    («stacks» : Fin k → List Bool) (xs bits : List Bool)
    (hsrc : «stacks» (ports 0) = xs) (hdst : «stacks» (ports 1) = [])
    (hscratch : «stacks» (ports 2) = []) (hlen : bits.length = 2 * xs.length + 2) :
    (machine ports).run (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits =
      ⟨none, Function.update «stacks» (ports 1) xs⟩ := by
  have hp := FixedStack.lift3_project_run CopyInput.machine ports
    (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits
  erw [project_start ports «stacks» xs hsrc hdst hscratch,
    CopyInput.run_eq_copy xs bits hlen] at hp
  have hstate := congrArg (fun c : Config 2 => c.state) hp
  have h0 := congrArg (fun c : Config 2 => c.«stacks» 0) hp
  have h1 := congrArg (fun c : Config 2 => c.«stacks» 1) hp
  have h2 := congrArg (fun c : Config 2 => c.«stacks» 2) hp
  dsimp only [FixedStack.project, CopyInput.cfg] at hstate h0 h1 h2
  apply config_ext hstate
  funext j
  change ((FixedStack.lift3 CopyInput.machine ports).run
    (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits).«stacks» j =
      Function.update «stacks» (ports 1) xs j
  by_cases hj1 : j = ports 1
  · subst j
    simpa [Function.update] using h1
  · erw [Function.update_of_ne hj1]
    by_cases hj0 : j = ports 0
    · subst j
      simpa [hsrc] using h0
    · by_cases hj2 : j = ports 2
      · subst j
        simpa [hscratch] using h2
      · exact FixedStack.lift3_run_preserves_other CopyInput.machine ports
          (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits j (by
            intro r
            fin_cases r <;> assumption)

theorem haltsAfter {k : ℕ} (ports : Fin 3 ↪ Fin k) («stacks» : Fin k → List Bool)
    (xs bits : List Bool) (hsrc : «stacks» (ports 0) = xs)
    (hdst : «stacks» (ports 1) = []) (hscratch : «stacks» (ports 2) = [])
    (hlen : bits.length = 2 * xs.length + 2) :
    FixedSequential.HaltsAfter (program ports) (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits := by
  apply (FixedSequential.haltsAfter_lift3_iff CopyInput.machine ports
    (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) bits).mpr
  erw [project_start ports «stacks» xs hsrc hdst hscratch]
  exact copy_haltsAfter xs bits hlen

theorem haltsFromWithin {k : ℕ} (ports : Fin 3 ↪ Fin k) («stacks» : Fin k → List Bool)
    (xs : List Bool) (hsrc : «stacks» (ports 0) = xs)
    (hdst : «stacks» (ports 1) = []) (hscratch : «stacks» (ports 2) = []) :
    FixedSequential.HaltsFromWithin (program ports)
      (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) (2 * xs.length + 2) := by
  intro bits hlen
  exact (haltsAfter ports «stacks» xs bits hsrc hdst hscratch hlen).2

theorem haltsFromWithin_polynomial {k : ℕ} (ports : Fin 3 ↪ Fin k)
    («stacks» : Fin k → List Bool) (xs : List Bool) (hsrc : «stacks» (ports 0) = xs)
    (hdst : «stacks» (ports 1) = []) (hscratch : «stacks» (ports 2) = []) :
    FixedSequential.HaltsFromWithin (program ports)
      (⟨some 0, «stacks»⟩ : FixedStack.Config k 2) (polynomialFuel 2 1 xs.length) := by
  have ht : polynomialFuel 2 1 xs.length = 2 * xs.length + 2 := by
    simp [polynomialFuel, Nat.mul_add]
  rw [ht]
  exact haltsFromWithin ports «stacks» xs hsrc hdst hscratch

end KS.W01.FixedCopy

end OAI
