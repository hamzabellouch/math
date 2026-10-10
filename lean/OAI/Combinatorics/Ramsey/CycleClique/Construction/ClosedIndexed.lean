import OAI.Combinatorics.Ramsey.CycleClique.Construction.ColouredPathStart
import Mathlib.Algebra.Group.Fin.Basic

namespace OAI

/-! An indexed path whose endpoints are adjacent can be started at any of its vertices. -/

namespace CycleClique.Construction
theorem cycleNext_eq_add_one {r : ℕ} (i : Fin (r + 1)) : cycleNext i = i + 1 := by
  cases r with
  | zero =>
    apply Fin.ext
    have h₁ := (cycleNext i).isLt
    have h₂ := (i + 1).isLt
    omega
  | succ r => apply Fin.ext; rfl

theorem indexedPath_closed_cycle {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f)
    (hclose : G.Adj (f (Fin.last r)) (f 0)) :
    ∀ i, G.Adj (f i) (f (cycleNext i)) := by
  intro i
  by_cases hi : i.val = r
  · have heq : i = Fin.last r := Fin.ext hi
    have hn : cycleNext i = 0 := by
      apply Fin.ext
      simp only [cycleNext, hi, Nat.mod_self, Fin.val_zero]
    rw [hn, heq]
    exact hclose
  · let j : Fin r := ⟨i.val, by have := i.isLt; omega⟩
    have hleft : j.castSucc = i := Fin.ext rfl
    have hright : j.succ = cycleNext i := by
      apply Fin.ext
      exact (Nat.mod_eq_of_lt (by have := i.isLt; omega)).symm
    simpa only [hleft, hright] using hf.2 j

theorem indexedPath_closed_ending {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f)
    (hclose : G.Adj (f (Fin.last r)) (f 0)) (j : Fin (r + 1)) :
    ∃ g : Fin (r + 1) → V, IsIndexedPath G g ∧
      g (Fin.last r) = f j ∧ Set.range g = Set.range f := by
  let c := j - Fin.last r
  let g : Fin (r + 1) → V := fun i => f (i + c)
  have hadd : ∀ i : Fin r, i.succ = i.castSucc + (1 : Fin (r + 1)) := by
    intro i
    apply Fin.ext
    rw [Fin.val_add_one_of_lt (show i.castSucc < Fin.last r from i.isLt)]
    rfl
  have hg : IsIndexedPath G g := by
    refine ⟨hf.1.comp (fun a b h => add_right_cancel h), ?_⟩
    intro i
    have h := indexedPath_closed_cycle hf hclose (i.castSucc + c)
    simpa only [g, cycleNext_eq_add_one, hadd, add_assoc, add_comm 1 c] using h
  refine ⟨g, hg, ?_, ?_⟩
  · change f (Fin.last r + (j - Fin.last r)) = f j
    congr 1
    abel
  · ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i + c, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i - c, by simp [g]⟩

end CycleClique.Construction

end OAI
