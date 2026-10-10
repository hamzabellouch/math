import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Separated binary words in a complex base

For a base of modulus at least two, distinct binary strings of the same
length evaluate at distance at least one. This is the counting ingredient
for excluding expanding characters of conjugation.
-/

namespace PolycyclicRecognition

def complexBit (b : Bool) : ℂ := if b then 1 else 0

def complexBinaryWord (z : ℂ) : List Bool → ℂ
  | [] => 0
  | b :: l => complexBit b + z * complexBinaryWord z l

theorem complexBit_dist_le (a b : Bool) : ‖complexBit a - complexBit b‖ ≤ 1 := by
  cases a <;> cases b <;> norm_num [complexBit]

theorem complexBinaryWord_separated {z : ℂ} (hz : 2 ≤ ‖z‖) :
    ∀ (l k : List Bool), l.length = k.length → l ≠ k →
      1 ≤ ‖complexBinaryWord z l - complexBinaryWord z k‖ := by
  intro l
  induction l with
  | nil =>
    intro k hk hne
    have : k = [] := List.length_eq_zero_iff.mp hk.symm
    exact (hne this.symm).elim
  | cons a l ih =>
    intro k hk hne
    cases k with
    | nil => simp at hk
    | cons b k =>
      by_cases he : l = k
      · subst k
        have hab : a ≠ b := by intro h; exact hne (h ▸ rfl)
        cases a <;> cases b <;> simp_all [complexBinaryWord, complexBit]
      · have hd := ih k (by simpa using hk) he
        have ht := norm_add_le
          (complexBinaryWord z (a :: l) - complexBinaryWord z (b :: k))
          (complexBit b - complexBit a)
        have hid : (complexBinaryWord z (a :: l) - complexBinaryWord z (b :: k)) +
            (complexBit b - complexBit a) =
            z * (complexBinaryWord z l - complexBinaryWord z k) := by
          simp only [complexBinaryWord]
          ring
        rw [hid, norm_mul] at ht
        have hm : 2 ≤ ‖z‖ * ‖complexBinaryWord z l - complexBinaryWord z k‖ := by
          nlinarith [norm_nonneg z]
        linarith [complexBit_dist_le b a]

theorem complexBinaryWord_injective_length {z : ℂ} (hz : 2 ≤ ‖z‖)
    {l k : List Bool} (hlen : l.length = k.length)
    (he : complexBinaryWord z l = complexBinaryWord z k) : l = k := by
  by_contra hne
  have h := complexBinaryWord_separated hz l k hlen hne
  simp only [he, sub_self, norm_zero] at h
  norm_num at h

end PolycyclicRecognition

end OAI
