import Mathlib

namespace OAI

namespace PlanarHalving

abbrev Point := ℝ × ℝ

def orient (p q r : Point) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

def GeneralPosition {n : ℕ} (P : Fin n → Point) : Prop :=
  Function.Injective P ∧ ∀ i j l, i ≠ j → j ≠ l → i ≠ l →
    orient (P i) (P j) (P l) ≠ 0

noncomputable def sideCount {n : ℕ} (P : Fin n → Point) (i j : Fin n) : ℕ :=
  (Finset.univ.filter fun l => 0 < orient (P i) (P j) (P l)).card

noncomputable def halvingCount {n : ℕ} (P : Fin n → Point) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ sideCount P ij.1 ij.2 = (n - 2) / 2 ∧
      sideCount P ij.2 ij.1 = (n - 2) / 2).card

noncomputable def slope (p q : Point) : ℝ := (q.2 - p.2) / (q.1 - p.1)

def Generic {n : ℕ} (P : Fin n → Point) : Prop :=
  GeneralPosition P ∧
  (∀ i j, i ≠ j → (P i).1 ≠ (P j).1) ∧
  (∀ i j a b, i < j → a < b → slope (P i) (P j) = slope (P a) (P b) →
    i = a ∧ j = b) ∧
  (∀ i j a b c d, i < j → a < b → c < d →
    (i, j) ≠ (a, b) → (c, d) ≠ (i, j) → (c, d) ≠ (a, b) →
    ∀ z : Point, z ∈ openSegment ℝ (P i) (P j) →
      z ∈ openSegment ℝ (P a) (P b) → z ∉ segment ℝ (P c) (P d))

noncomputable def belowCount {n : ℕ} (P : Fin n → Point) (i j : Fin n) : ℕ :=
  let s := slope (P i) (P j)
  (Finset.univ.filter fun l => (P l).2 - s * (P l).1 <
    (P i).2 - s * (P i).1).card

noncomputable def switchCount {n : ℕ} (P : Fin n → Point) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ 0 < k ∧ k < n ∧ belowCount P ij.1 ij.2 = k - 1).card

theorem power_bounds :
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∃ n₀ : ℕ,
      ∀ n : ℕ, Even n → n₀ ≤ n → ∀ P : Fin n → Point,
        GeneralPosition P → (halvingCount P : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε)) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ n : ℕ, 1 ≤ n → ∀ P : Fin n → Point, Generic P →
        ∀ k : ℕ, k ≤ n → (switchCount P k : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε)) :=
  sorry

end PlanarHalving

end OAI
