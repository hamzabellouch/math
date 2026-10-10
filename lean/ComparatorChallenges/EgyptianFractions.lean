import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

def IsEgyptianExpansion {k : ℕ} (x : ℚ) (n : Fin k → ℕ) : Prop :=
  (∀ i, 2 ≤ n i) ∧ StrictMono n ∧
    (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = x

def egyptianLengths (a b : ℕ) : Set ℕ :=
  {k | ∃ n : Fin k → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n}

def egyptianLength (a b : ℕ) : ℕ :=
  sInf (egyptianLengths a b)

def maxEgyptianLength (b : ℕ) : ℕ :=
  (Finset.range b).sup (fun a => if 1 ≤ a then egyptianLength a b else 0)

def IsOneExpansion {k : ℕ} (n : Fin k → ℕ) : Prop :=
  (∀ i, 1 ≤ n i) ∧ StrictMono n ∧
    (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = 1

def OneExpansions (k : ℕ) : Set (Fin k → ℕ) :=
  {n | IsOneExpansion n}

def F (k : ℕ) : ℕ :=
  (OneExpansions k).ncard

def D (k : ℕ) : Set ℕ :=
  {m | 2 ≤ m ∧ ∃ n : Fin k → ℕ,
    IsOneExpansion n ∧ ∃ i : Fin k, n i = m}

def missingDenominators (k : ℕ) : Set ℕ :=
  {m : ℕ | 2 ≤ m} \ D k

def v (k : ℕ) : ℕ :=
  sInf (missingDenominators k)

def prescribedSlope (k : ℕ) : ℝ :=
  Real.log (Real.log (v k : ℝ)) / (k : ℝ)

theorem egyptian_length_is_minimum :
    ∀ a b : ℕ, 1 ≤ a → a < b →
  (∃ n : Fin (egyptianLength a b) → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) ∧
  (∀ k : ℕ, (∃ n : Fin k → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) →
    egyptianLength a b ≤ k) := by
  sorry

theorem main_double_log_order :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∃ b0 : ℕ,
  ∀ b : ℕ, b0 ≤ b →
    c1 * Real.log (Real.log (b : ℝ)) ≤ (maxEgyptianLength b : ℝ) ∧
    (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) := by
  sorry

theorem one_expansions_finite_and_bounded :
    (∀ k : ℕ, Set.Finite (OneExpansions k) ∧
    F k ≤ k ^ (2 ^ k - 1)) ∧
  (∀ k : ℕ, ∀ n : Fin k → ℕ, IsOneExpansion n →
    ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val)) := by
  sorry

theorem counting_double_log_order :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k0 : ℕ,
  ∀ k : ℕ, k0 ≤ k →
    c * (k : ℝ) ≤ Real.log (Real.log (F k : ℝ)) ∧
    Real.log (Real.log (F k : ℝ)) ≤ C * (k : ℝ) := by
  sorry

theorem exact_marker_padding :
    ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
  ∀ m : ℕ, (∃ i : Fin r, n i = m) →
    ∃ n' : Fin (r + 1) → ℕ,
      IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m := by
  sorry

theorem every_exact_marker_occurs :
    ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k := by
  sorry

theorem quantitative_marked_length :
    ∀ ε : ℝ, 0 < ε → ∃ mε : ℕ, 2 ≤ mε ∧
  ∀ m : ℕ, mε ≤ m →
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsOneExpansion n ∧
      (∃ i : Fin k, n i = m) ∧
      (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  sorry

theorem missing_denominator_semantics :
    ∀ k : ℕ,
  Set.Finite (D k) ∧
  (∃ m : ℕ, m ∈ missingDenominators k) ∧
  2 ≤ v k ∧ v k ∉ D k ∧
  (∀ m : ℕ, 2 ≤ m → m < v k → m ∈ D k) ∧
  (1 ≤ k → v k ≤ 1 + k ^ (2 ^ (k - 1))) := by
  sorry

theorem prescribed_denominator_corollary :
    (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
    Real.exp (Real.exp ((k : ℝ) / 600)) ≤ (v k : ℝ) ∧
    v k ≤ 1 + k ^ (2 ^ (k - 1))) ∧
  (Real.log 2 / 257 ≤ Filter.liminf prescribedSlope Filter.atTop ∧
    Filter.liminf prescribedSlope Filter.atTop ≤
      Filter.limsup prescribedSlope Filter.atTop ∧
    Filter.limsup prescribedSlope Filter.atTop ≤ Real.log 2) ∧
  (∀ c : ℝ, c < Real.log 2 / 257 → ∃ k0 : ℕ,
    ∀ k : ℕ, k0 ≤ k →
      Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ)) := by
  sorry

end Problem337

end

end OAI
