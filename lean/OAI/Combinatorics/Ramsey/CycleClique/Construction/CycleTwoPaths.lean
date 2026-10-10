import OAI.Combinatorics.Ramsey.CycleClique.Construction.LongestPaths

namespace OAI

/-! Closing two internally disjoint indexed paths into their exact cycle. -/

namespace CycleClique.Construction
private def twoPathLabel {V : Type*} {a b : ℕ} (_hb : 2 ≤ b)
    (f : Fin (a + 1) → V) (g : Fin (b + 1) → V) (i : Fin (a + b)) : V :=
  if hi : i.val ≤ a then f ⟨i.val, by omega⟩ else g ⟨i.val - a, by have := i.isLt; omega⟩

private theorem twoPathLabel_left {V : Type*} {a b : ℕ} (hb : 2 ≤ b)
    (f : Fin (a + 1) → V) (g : Fin (b + 1) → V) {i : Fin (a + b)}
    (hi : i.val ≤ a) : twoPathLabel hb f g i = f ⟨i.val, by omega⟩ := by
  simp only [twoPathLabel, dite_eq_left hi]

private theorem twoPathLabel_right {V : Type*} {a b : ℕ} (hb : 2 ≤ b)
    (f : Fin (a + 1) → V) (g : Fin (b + 1) → V) {i : Fin (a + b)}
    (hi : a < i.val) : twoPathLabel hb f g i = g ⟨i.val - a, by have := i.isLt; omega⟩ := by
  simp only [twoPathLabel, dite_eq_right (by omega : ¬ i.val ≤ a)]

theorem cycle_of_two_indexed_paths {V : Type*} {H : SimpleGraph V} {a b : ℕ}
    (hb : 2 ≤ b) (f : Fin (a + 1) → V) (g : Fin (b + 1) → V)
    (hf : IsIndexedPath H f) (hg : IsIndexedPath H g)
    (hstart : g 0 = f (Fin.last a)) (hend : g (Fin.last b) = f 0)
    (hdisjoint : ∀ i : Fin (b + 1), 0 < i.val → i.val < b →
      ∀ j : Fin (a + 1), f j ≠ g i) : HasCycle H (a + b) := by
  let : NeZero b := ⟨by omega⟩
  refine ⟨twoPathLabel hb f g, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    by_cases hi : i.val ≤ a
    · by_cases hj : j.val ≤ a
      · rw [twoPathLabel_left hb f g hi, twoPathLabel_left hb f g hj] at hij
        exact congrArg (fun x : Fin (a + 1) => x.val) (hf.1 hij)
      · rw [twoPathLabel_left hb f g hi, twoPathLabel_right hb f g (by omega)] at hij
        exact False.elim (hdisjoint ⟨j.val - a, by have := j.isLt; omega⟩
          (by dsimp; omega) (by dsimp; have := j.isLt; omega) _ hij)
    · by_cases hj : j.val ≤ a
      · rw [twoPathLabel_right hb f g (by omega), twoPathLabel_left hb f g hj] at hij
        exact False.elim (hdisjoint ⟨i.val - a, by have := i.isLt; omega⟩
          (by dsimp; omega) (by dsimp; have := i.isLt; omega) _ hij.symm)
      · rw [twoPathLabel_right hb f g (by omega), twoPathLabel_right hb f g (by omega)] at hij
        have hval := congrArg Fin.val (hg.1 hij)
        dsimp at hval
        omega
  · intro i
    by_cases hlast : i.val + 1 = a + b
    · have hn : (cycleNext i).val = 0 := by simp [cycleNext, hlast]
      have hleft : twoPathLabel hb f g i = g ⟨b - 1, by omega⟩ := by
        rw [twoPathLabel_right hb f g (by omega)]
        congr 1
        apply Fin.ext
        dsimp
        omega
      have hright : twoPathLabel hb f g (cycleNext i) = f 0 := by
        rw [twoPathLabel_left hb f g (by omega)]
        congr 1
        apply Fin.ext
        simpa only [Fin.val_zero] using hn
      rw [hleft, hright, ← hend]
      have h := hg.2 ⟨b - 1, by omega⟩
      have hi : (⟨b - 1, by omega⟩ : Fin b).succ = Fin.last b := by
        apply Fin.ext
        change b - 1 + 1 = b
        omega
      rw [hi] at h
      exact h
    · have hn : (cycleNext i).val = i.val + 1 := Nat.mod_eq_of_lt (by have := i.isLt; omega)
      by_cases hbefore : i.val < a
      · let p : Fin a := ⟨i.val, hbefore⟩
        have hleft : twoPathLabel hb f g i = f p.castSucc := by
          rw [twoPathLabel_left hb f g (by omega)]
          rfl
        have hright : twoPathLabel hb f g (cycleNext i) = f p.succ := by
          rw [twoPathLabel_left hb f g (by omega)]
          congr 1
          exact Fin.ext hn
        rw [hleft, hright]
        exact hf.2 p
      · by_cases heq : i.val = a
        · have hleft : twoPathLabel hb f g i = f (Fin.last a) := by
            rw [twoPathLabel_left hb f g (by omega)]
            congr 1
            exact Fin.ext heq
          have hright : twoPathLabel hb f g (cycleNext i) = g (Fin.succ (0 : Fin b)) := by
            rw [twoPathLabel_right hb f g (by omega)]
            congr 1
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_zero]
            omega
          rw [hleft, hright, ← hstart]
          exact hg.2 0
        · let p : Fin b := ⟨i.val - a, by have := i.isLt; omega⟩
          have hleft : twoPathLabel hb f g i = g p.castSucc := by
            rw [twoPathLabel_right hb f g (by omega)]
            rfl
          have hright : twoPathLabel hb f g (cycleNext i) = g p.succ := by
            rw [twoPathLabel_right hb f g (by omega)]
            congr 1
            apply Fin.ext
            dsimp [p]
            omega
          rw [hleft, hright]
          exact hg.2 p

end CycleClique.Construction

end OAI
