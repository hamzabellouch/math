import Mathlib.Data.List.Perm.Basic
import OAI.NumberTheory.Ostmann.Construction.InitialSmallCellList
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredPrimeLaws
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeNext

namespace OAI

/-! # The actual four-at-a-time compensation cell schedule -/
namespace Ostmann
open scoped Classical

def scheduledSmallLength : List ℕ → ℕ
  | [] => 6
  | _ :: cs => 4 + scheduledSmallLength cs

def scheduledSmallCell (top : ℕ) : (cs : List ℕ) → Fin (scheduledSmallLength cs) → ℕ
  | [] => fun _ => top
  | c :: cs => Fin.append (fun _ : Fin 4 => c) (scheduledSmallCell top cs)

def scheduledSmallCellList (top : ℕ) (cs : List ℕ) : List ℕ :=
  cs.flatMap (fun c => List.replicate 4 c) ++ List.replicate 6 top

theorem scheduledSmallLength_eq (cs : List ℕ) :
    scheduledSmallLength cs = 6 + 4 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [scheduledSmallLength, List.length_cons, ih]; omega

theorem initialSmallCellList_schedule_perm (top : ℕ) (cs : List ℕ) :
    (initialSmallCellList top cs ++ initialSmallCellList top cs).Perm
      (scheduledSmallCellList top cs) := by
  let T := List.replicate 3 top
  let U := cs.flatMap (fun c => [c, c])
  have hswap : ((T ++ U) ++ (T ++ U)).Perm ((T ++ T) ++ (U ++ U)) := by
    simpa only [List.append_assoc] using
      ((List.perm_append_comm (l₁ := U) (l₂ := T)).append_right U).append_left T
  have hflat : (U ++ U).Perm (cs.flatMap (fun c => List.replicate 4 c)) := by
    simpa only [U, List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append] using List.flatMap_append_perm cs (fun c => [c, c]) (fun c => [c, c])
  have htop : T ++ T = List.replicate 6 top := by
    dsimp only [T]
    rfl
  exact (hswap.trans ((List.Perm.refl _).append hflat)).trans
    (by simpa only [htop, scheduledSmallCellList] using
      (List.perm_append_comm (l₁ := List.replicate 6 top)
        (l₂ := cs.flatMap (fun c => List.replicate 4 c))))

noncomputable def scheduledRegularPrimeSets (cell : ℕ → Finset ℕ) (bulk : Finset ℕ)
    (top : ℕ) (cs : List ℕ) (n m : ℕ) :
    MovingRegularSlot n (scheduledSmallLength cs) m → Finset ℕ :=
  fun i => Sum.elim (fun j => cell (scheduledSmallCell top cs j)) (fun _ => bulk) i.2

theorem scheduledRegularPrimeSets_restore (cell : ℕ → Finset ℕ) (bulk : Finset ℕ)
    (top c : ℕ) (cs : List ℕ) (n m : ℕ) :
    scheduledRegularPrimeSets cell bulk top (c :: cs) n m =
      movingRestoredPrimeSets n (scheduledSmallLength cs) m (cell c)
        (scheduledRegularPrimeSets cell bulk top cs n m) := by
  funext i
  rcases i with ⟨j, i | i⟩
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) i
    · simp only [scheduledRegularPrimeSets, scheduledSmallCell, movingRestoredPrimeSets,
        movingReverseTemplate, Equiv.coe_fn_symm_mk, Sum.elim_inl,
        Fin.addCases_left]
      exact congrArg cell (Fin.append_left _ _ t)
    · simp only [scheduledRegularPrimeSets, scheduledSmallCell, movingRestoredPrimeSets,
        movingReverseTemplate, Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr,
        Fin.addCases_right]
      exact congrArg cell (Fin.append_right _ _ t)
  · rfl

theorem scheduledRegularPrimeSets_doubled (cell : ℕ → Finset ℕ) (bulk : Finset ℕ)
    (top : ℕ) (cs : List ℕ) (n m : ℕ) (P : Finset ℕ) :
    movingTemplateDoubledPrior n (scheduledSmallLength cs) m
      (fun i => primeSubsetPrior P (scheduledRegularPrimeSets cell bulk top cs n m i)) =
    (fun i => primeSubsetPrior P
      (scheduledRegularPrimeSets cell bulk top cs (n + 1) m i)) := rfl

end Ostmann

end OAI
