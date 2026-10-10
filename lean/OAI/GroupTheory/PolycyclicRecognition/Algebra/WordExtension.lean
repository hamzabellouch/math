import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordLogarithms

namespace OAI

/-! # Extending controlled words by one increment -/

namespace PolycyclicRecognition

/-- Prefixes depend only on the increments preceding them. -/
theorem wordPrefix_congr {A : Type*} [Monoid A] {u v : ℕ → A} (m : ℕ)
    (h : ∀ i < m, u i = v i) : wordPrefix u m = wordPrefix v m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [wordPrefix_succ, wordPrefix_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h m (Nat.lt_succ_self m)]

/-- Append a prescribed increment, with irrelevant later increments fixed to it. -/
def extendWord {A : Type*} (u : ℕ → A) (m : ℕ) (a : A) : ℕ → A :=
  fun i => if i < m then u i else a

@[simp] theorem extendWord_before {A : Type*} (u : ℕ → A) (m : ℕ) (a : A)
    {i : ℕ} (hi : i < m) : extendWord u m a i = u i := by simp [extendWord, hi]

@[simp] theorem extendWord_at {A : Type*} (u : ℕ → A) (m : ℕ) (a : A) :
    extendWord u m a m = a := by simp [extendWord]

theorem wordPrefix_extendWord {A : Type*} [Monoid A] (u : ℕ → A) (m : ℕ) (a : A)
    {j : ℕ} (hj : j ≤ m) : wordPrefix (extendWord u m a) j = wordPrefix u j :=
  wordPrefix_congr j (fun _i hi => extendWord_before u m a (hi.trans_le hj))

@[simp] theorem wordPrefix_extendWord_succ {A : Type*} [Monoid A]
    (u : ℕ → A) (m : ℕ) (a : A) :
    wordPrefix (extendWord u m a) (m + 1) = wordPrefix u m * a := by
  rw [wordPrefix_succ, wordPrefix_extendWord u m a le_rfl, extendWord_at]

end PolycyclicRecognition

end OAI
