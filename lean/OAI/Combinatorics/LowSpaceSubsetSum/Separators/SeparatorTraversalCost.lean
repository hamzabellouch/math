import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorTraversal

namespace OAI

/-!
# Occurrence charges for the separator traversal

Every occurrence has its own incidence multiplicity. The charge includes
one scan even when that multiplicity is zero; terminal charges are multiplied
by the number of compatible indices, with no Cartesian pair enumeration.
-/

namespace LowSpaceSubsetSum.SeparatorTraversal

open SeparatorIncidenceTable

variable {α β γ : Type*}

def mass (inc : γ → Array ℕ) (lo hi : ℕ) (xs : List γ) (charge : γ → ℕ) : ℕ :=
  (xs.map (fun x => charge x * count (inc x) lo hi)).sum

theorem mass_split (inc : γ → Array ℕ) (lo mid hi : ℕ) (xs : List γ) (charge : γ → ℕ)
    (hl : lo ≤ mid) (hh : mid ≤ hi) :
    mass inc lo mid xs charge + mass inc mid hi xs charge = mass inc lo hi xs charge := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
    simp only [mass, List.map_cons, List.sum_cons] at *
    have := count_split (inc x) lo mid hi hl hh
    nlinarith

theorem mass_keep (inc : γ → Array ℕ)
    (hs : ∀ x, Monotone (fun i : Fin (inc x).size => (inc x)[i.val]))
    (lo hi : ℕ) (xs : List γ) (charge : γ → ℕ) :
    mass inc lo hi (keep inc lo hi xs) charge = mass inc lo hi xs charge := by
  induction xs with
  | nil => simp [keep, mass]
  | cons x xs ih =>
    by_cases h : hit (inc x) lo hi = true
    · simp [keep, h, mass] at ih ⊢
      exact ih
    · have hf : hit (inc x) lo hi = false := Bool.eq_false_iff.mpr h
      have hz := count_zero_of_not_hit (inc x) (hs x) lo hi hf
      simpa [keep, hf, mass, hz] using ih

theorem kept_charge_le_mass (inc : γ → Array ℕ)
    (hs : ∀ x, Monotone (fun i : Fin (inc x).size => (inc x)[i.val]))
    (lo hi : ℕ) (xs : List γ) (charge : γ → ℕ) :
    ((keep inc lo hi xs).map charge).sum ≤ mass inc lo hi xs charge := by
  induction xs with
  | nil => simp [keep, mass]
  | cons x xs ih =>
    by_cases h : hit (inc x) lo hi = true
    · have hp := (hit_count (inc x) (hs x) lo hi).mp h
      have hm : charge x ≤ charge x * count (inc x) lo hi := by nlinarith
      simpa only [keep, List.filter_cons, h, ↓reduceIte, List.map_cons, List.sum_cons,
        mass] using Nat.add_le_add hm ih
    · have hf : hit (inc x) lo hi = false := Bool.eq_false_iff.mpr h
      have hz := count_zero_of_not_hit (inc x) (hs x) lo hi hf
      simpa [keep, hf, mass, hz] using ih

theorem keep_length_le_mass (inc : γ → Array ℕ)
    (hs : ∀ x, Monotone (fun i : Fin (inc x).size => (inc x)[i.val]))
    (lo hi : ℕ) (xs : List γ) :
    (keep inc lo hi xs).length ≤ mass inc lo hi xs (fun _ => 1) := by
  simpa using kept_charge_le_mass inc hs lo hi xs (fun _ => 1)

/-- Scans charged to each original occurrence, plus the supplied per-occurrence
terminal work. At depth zero a zero-incidence record still pays its root scan. -/
theorem scans_le (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ)
    (leaf : ℕ → List α → List β → Result)
    (hs₁ : ∀ x, Monotone (fun i : Fin (inc₁ x).size => (inc₁ x)[i.val]))
    (hs₂ : ∀ y, Monotone (fun i : Fin (inc₂ y).size => (inc₂ y)[i.val]))
    (charge₁ : α → ℕ) (charge₂ : β → ℕ)
    (hleaf : ∀ j xs ys, (leaf j xs ys).scans ≤
      (xs.map charge₁).sum + (ys.map charge₂).sum)
    (k lo hi : ℕ) (xs : List α) (ys : List β) :
    (run inc₁ inc₂ leaf k lo hi xs ys).scans ≤
      xs.length + ys.length +
      2 * k * (mass inc₁ lo hi xs (fun _ => 1) + mass inc₂ lo hi ys (fun _ => 1)) +
      mass inc₁ lo hi xs charge₁ + mass inc₂ lo hi ys charge₂ := by
  induction k generalizing lo hi xs ys with
  | zero =>
    have hf := hleaf lo (keep inc₁ lo hi xs) (keep inc₂ lo hi ys)
    have hx := kept_charge_le_mass inc₁ hs₁ lo hi xs charge₁
    have hy := kept_charge_le_mass inc₂ hs₂ lo hi ys charge₂
    simp only [run]
    split_ifs <;> dsimp only [finish] <;> omega
  | succ k ih =>
    have hf := hleaf lo (keep inc₁ lo hi xs) (keep inc₂ lo hi ys)
    have hx := kept_charge_le_mass inc₁ hs₁ lo hi xs charge₁
    have hy := kept_charge_le_mass inc₂ hs₂ lo hi ys charge₂
    simp only [run]
    split_ifs with he hsmall
    · dsimp only
      omega
    · dsimp only [finish]
      omega
    · dsimp only
      let mid := (lo + hi) / 2
      have hl : lo ≤ mid := by dsimp [mid]; omega
      have hh : mid ≤ hi := by dsimp [mid]; omega
      have h₁ := ih lo mid (keep inc₁ lo hi xs) (keep inc₂ lo hi ys)
      have h₂ := ih mid hi (keep inc₁ lo hi xs) (keep inc₂ lo hi ys)
      have hsx := mass_split inc₁ lo mid hi (keep inc₁ lo hi xs) (fun _ => 1) hl hh
      have hsy := mass_split inc₂ lo mid hi (keep inc₂ lo hi ys) (fun _ => 1) hl hh
      have hcx := mass_split inc₁ lo mid hi (keep inc₁ lo hi xs) charge₁ hl hh
      have hcy := mass_split inc₂ lo mid hi (keep inc₂ lo hi ys) charge₂ hl hh
      rw [mass_keep inc₁ hs₁] at hsx hcx
      rw [mass_keep inc₂ hs₂] at hsy hcy
      have hnx := keep_length_le_mass inc₁ hs₁ lo hi xs
      have hny := keep_length_le_mass inc₂ hs₂ lo hi ys
      nlinarith

end LowSpaceSubsetSum.SeparatorTraversal

end OAI
