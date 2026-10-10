import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Monotone.Basic

namespace OAI

/-!
# Global candidate ordinals

Every level reserves its full candidate interval. Retained candidates are
indexed by an order embedding into that interval. Hence rejected candidates
still consume their original ordinal, and labels at distinct levels cannot
collide. None of the arithmetic requires candidate counts to be positive.
-/

namespace ReflexiveFixedPoints.GlobalCandidateOrdinals

/-- Number of candidate ordinals consumed before a given level. -/
def base (count : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => base count k + count k

@[simp] theorem base_zero (count : ℕ → ℕ) : base count 0 = 0 := rfl

@[simp] theorem base_succ (count : ℕ → ℕ) (k : ℕ) :
    base count (k + 1) = base count k + count k := rfl

/-- Any counter with the candidate-count recurrence is monotone. -/
theorem base_monotone (B count : ℕ → ℕ)
    (hstep : ∀ k, B (k + 1) = B k + count k) : Monotone B := by
  apply monotone_nat_of_le_succ
  intro k
  rw [hstep k]
  omega

theorem base_mono (count : ℕ → ℕ) : Monotone (base count) :=
  base_monotone (base count) count (base_succ count)

variable {size count : ℕ → ℕ}

/-- The original ordinal of a retained entry. -/
def label (B : ℕ → ℕ) (embed : ∀ k, Fin (size k) ↪o Fin (count k))
    (s : Σ k, Fin (size k)) : ℕ := B s.1 + (embed s.1 s.2).val

@[simp] theorem label_mk (B : ℕ → ℕ)
    (embed : ∀ k, Fin (size k) ↪o Fin (count k)) (k : ℕ) (v : Fin (size k)) :
    label B embed ⟨k, v⟩ = B k + (embed k v).val := rfl

theorem base_le_label (B : ℕ → ℕ)
    (embed : ∀ k, Fin (size k) ↪o Fin (count k)) (k : ℕ) (v : Fin (size k)) :
    B k ≤ label B embed ⟨k, v⟩ := by
  simp only [label_mk]
  omega

theorem label_lt_next (B : ℕ → ℕ)
    (hstep : ∀ k, B (k + 1) = B k + count k)
    (embed : ∀ k, Fin (size k) ↪o Fin (count k)) (k : ℕ) (v : Fin (size k)) :
    label B embed ⟨k, v⟩ < B (k + 1) := by
  rw [label_mk, hstep k]
  exact Nat.add_lt_add_left (embed k v).isLt _

/-- Every earlier retained candidate lies before a later level's base. -/
theorem label_lt_of_level_lt (B : ℕ → ℕ)
    (hstep : ∀ k, B (k + 1) = B k + count k)
    (embed : ∀ k, Fin (size k) ↪o Fin (count k)) {k j : ℕ}
    (hkj : k < j) (v : Fin (size k)) : label B embed ⟨k, v⟩ < B j :=
  lt_of_lt_of_le (label_lt_next B hstep embed k v)
    (base_monotone B count hstep (Nat.succ_le_of_lt hkj))

theorem label_lt_of_level_lt_label (B : ℕ → ℕ)
    (hstep : ∀ k, B (k + 1) = B k + count k)
    (embed : ∀ k, Fin (size k) ↪o Fin (count k)) {k j : ℕ}
    (hkj : k < j) (v : Fin (size k)) (w : Fin (size j)) :
    label B embed ⟨k, v⟩ < label B embed ⟨j, w⟩ :=
  lt_of_lt_of_le (label_lt_of_level_lt B hstep embed hkj v)
    (base_le_label B embed j w)

/-- Labels distinguish both levels and retained entries within a level. -/
theorem label_injective (B : ℕ → ℕ)
    (hstep : ∀ k, B (k + 1) = B k + count k)
    (embed : ∀ k, Fin (size k) ↪o Fin (count k)) :
    Function.Injective
      (fun s : Σ k, Fin (size k) => B s.1 + (embed s.1 s.2).val) := by
  rintro ⟨k, v⟩ ⟨j, w⟩ h
  have hk : k = j := by
    rcases lt_trichotomy k j with hkj | hkj | hkj
    · have hlt := label_lt_of_level_lt_label B hstep embed hkj v w
      exact False.elim ((ne_of_lt hlt) h)
    · exact hkj
    · have hlt := label_lt_of_level_lt_label B hstep embed hkj w v
      exact False.elim ((ne_of_lt hlt) h.symm)
  subst j
  change B k + (embed k v).val = B k + (embed k w).val at h
  have hv : (embed k v).val = (embed k w).val := Nat.add_left_cancel h
  have hvw : v = w := (embed k).injective (Fin.ext hv)
  subst w
  rfl

end ReflexiveFixedPoints.GlobalCandidateOrdinals

end OAI
