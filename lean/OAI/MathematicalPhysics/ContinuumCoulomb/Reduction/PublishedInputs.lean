import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Rational normalization and complement square completion

Both continuum Coulomb manuscripts use the field-free signed square-lattice
Heisenberg problem of Cubitt, Montanaro and Piddock, *Universal quantum
Hamiltonians*, PNAS 115 (2018), 9497–9502; the theorem identifiers are
Theorem 48, Lemma 47 and Section 10.1 of arXiv:1701.05182v4 (2019).
Rational normalization transfers coefficient approximation bounds to its
thresholds. Scalar square completion bounds the continuum complement.
-/

namespace ContinuumCoulomb

/-- Lower threshold after rounding and removing a scalar identity term. -/
def normalizedSourceLower (aRound cRound ε : ℝ) : ℝ :=
  aRound - cRound + 5 * ε

/-- Upper threshold after rounding and removing a scalar identity term. -/
def normalizedSourceUpper (bRound cRound ε : ℝ) : ℝ :=
  bRound - cRound - 5 * ε

/-- The `3ε` Hamiltonian error and two scalar rounding errors preserve YES. -/
theorem normalizedSource_yes
    {energy roundedEnergy a c aRound cRound ε : ℝ}
    (henergy : |roundedEnergy - (energy - c)| ≤ 3 * ε)
    (ha : |aRound - a| ≤ ε) (hc : |cRound - c| ≤ ε)
    (hyes : energy ≤ a) :
    roundedEnergy ≤ normalizedSourceLower aRound cRound ε := by
  obtain ⟨_, henergy'⟩ := abs_le.mp henergy
  obtain ⟨ha', _⟩ := abs_le.mp ha
  obtain ⟨_, hc'⟩ := abs_le.mp hc
  unfold normalizedSourceLower
  linarith

/-- The same errors preserve NO with the inward-adjusted upper threshold. -/
theorem normalizedSource_no
    {energy roundedEnergy b c bRound cRound ε : ℝ}
    (henergy : |roundedEnergy - (energy - c)| ≤ 3 * ε)
    (hb : |bRound - b| ≤ ε) (hc : |cRound - c| ≤ ε)
    (hno : b ≤ energy) :
    normalizedSourceUpper bRound cRound ε ≤ roundedEnergy := by
  obtain ⟨henergy', _⟩ := abs_le.mp henergy
  obtain ⟨_, hb'⟩ := abs_le.mp hb
  obtain ⟨hc', _⟩ := abs_le.mp hc
  unfold normalizedSourceUpper
  linarith

/-- The rounded source gap loses at most `12ε`. -/
theorem normalizedSource_gap
    {a b aRound bRound cRound ε : ℝ}
    (ha : |aRound - a| ≤ ε) (hb : |bRound - b| ≤ ε) :
    b - a - 12 * ε ≤
      normalizedSourceUpper bRound cRound ε -
        normalizedSourceLower aRound cRound ε := by
  obtain ⟨_, ha'⟩ := abs_le.mp ha
  obtain ⟨hb', _⟩ := abs_le.mp hb
  unfold normalizedSourceLower normalizedSourceUpper
  linarith

/-- The manuscripts' choice `ε = δ / 100` retains at least `22δ/25`. -/
theorem normalizedSource_gap_fraction
    {a b aRound bRound cRound δ : ℝ}
    (hgap : δ ≤ b - a)
    (ha : |aRound - a| ≤ δ / 100)
    (hb : |bRound - b| ≤ δ / 100) :
    22 * δ / 25 ≤
      normalizedSourceUpper bRound cRound (δ / 100) -
        normalizedSourceLower aRound cRound (δ / 100) := by
  have h := normalizedSource_gap (cRound := cRound) ha hb
  linarith

/-- In particular the rational source normalization leaves a positive gap. -/
theorem normalizedSource_gap_pos
    {a b aRound bRound cRound δ : ℝ}
    (hδ : 0 < δ) (hgap : δ ≤ b - a)
    (ha : |aRound - a| ≤ δ / 100)
    (hb : |bRound - b| ≤ δ / 100) :
    normalizedSourceLower aRound cRound (δ / 100) <
      normalizedSourceUpper bRound cRound (δ / 100) := by
  have h := normalizedSource_gap_fraction (cRound := cRound) hgap ha hb
  linarith

/-- Exact scalar square completion in the continuum-complement estimate. -/
theorem complement_square_completion
    (c β p q : ℝ) (hc : 0 < c) :
    -(2 * β ^ 2 / c) * p ^ 2 + c / 2 * q ^ 2 ≤
      c * q ^ 2 - 2 * β * p * q := by
  have hsq : 0 ≤ (c * q - 2 * β * p) ^ 2 / (2 * c) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have hid :
      c * q ^ 2 - 2 * β * p * q -
          (-(2 * β ^ 2 / c) * p ^ 2 + c / 2 * q ^ 2) =
        (c * q - 2 * β * p) ^ 2 / (2 * c) := by
    field_simp
    ring
  linarith

/-- The square completion gives the lower energy bound on a normalized
decomposition, once its low block, high block and mixed term are controlled.
This is the scalar step of `lem:continuum-elimination` in the binary-charge
manuscript and `prop:complement` in the unit-charge manuscript. -/
theorem complement_energy_lower
    {c β p q E low high mixed : ℝ}
    (hc : 0 < c) (hE : E ≤ c / 2)
    (hnorm : p ^ 2 + q ^ 2 = 1)
    (hlow : E * p ^ 2 ≤ low)
    (hhigh : c * q ^ 2 ≤ high)
    (hmixed : -(2 * β * p * q) ≤ mixed) :
    E - 2 * β ^ 2 / c ≤ low + high + mixed := by
  have hs := complement_square_completion c β p q hc
  have hβ : 0 ≤ 2 * β ^ 2 / c := by positivity
  have hq : 0 ≤ (c / 2 - E + 2 * β ^ 2 / c) * q ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith

end ContinuumCoulomb

end OAI
