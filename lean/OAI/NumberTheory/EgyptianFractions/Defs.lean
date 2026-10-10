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

end Problem337

end

end OAI
