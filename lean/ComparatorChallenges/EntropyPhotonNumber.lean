import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber

/-- The number-basis indices for `n` bosonic modes. -/
abbrev NumberIndex (n : ℕ) := Fin n → ℕ

/-- The full, untruncated bosonic Fock space `ℓ²(ℕⁿ, ℂ)`. -/
abbrev Fock (n : ℕ) := lp (fun _ : NumberIndex n => ℂ) 2

/-- A number-basis vector. -/
def numberKet {n : ℕ} (k : NumberIndex n) : Fock n := lp.single 2 k 1

/-- Matrix entries of an operator in the number basis. -/
def entry {n : ℕ} (T : Fock n →L[ℂ] Fock n) (k l : NumberIndex n) : ℂ :=
  inner ℂ (numberKet k) (T (numberKet l))

/-- Positive trace-one operators. For a positive bounded operator on this
Hilbert space, summability of its diagonal is the positive trace-class
criterion; `HasSum ... 1` includes summability as well as normalization. -/
structure State (n : ℕ) where
  op : Fock n →L[ℂ] Fock n
  positive : op.IsPositive
  trace_one : HasSum (fun k => (entry op k k).re) 1

/-- Total number of quanta in a number-basis vector. -/
def totalNumber {n : ℕ} (k : NumberIndex n) : ℕ := ∑ j, k j

/-- Exactly finiteness of the expectation of the nonnegative number operator. -/
def FiniteEnergy {n : ℕ} (ρ : State n) : Prop :=
  Summable (fun k => (totalNumber k : ℝ) * (entry ρ.op k k).re)

/-- `−Tr ρ log ρ`, using the continuous extension of `−t log t` at zero
and continuous functional calculus for the positive operator `ρ`. -/
def entropy {n : ℕ} (ρ : State n) : ℝ :=
  ∑' k, (entry (cfc (fun z : ℂ => (-(z.re * Real.log z.re) : ℂ)) ρ.op) k k).re

/-- The thermal entropy per mode, with the convention `0 log 0 = 0`. -/
def g (t : ℝ) : ℝ := (t + 1) * Real.log (t + 1) - t * Real.log t

/-- The inverse of increasing `g : [0,∞) → [0,∞)`, expressed by its lower
level cut. Only its values on `[0,∞)` occur in the main theorem. -/
def gInv (s : ℝ) : ℝ := sInf {t : ℝ | 0 ≤ t ∧ s ≤ g t}

/-- One-mode passive beam-splitter coefficient, in number bases. It is the
coefficient of `(c†)^k (d†)^e` in
`(√η c† − √(1−η) d†)^a (√(1−η) c† + √η d†)^b`,
with the normalized number-vector factorials. -/
def oneModeBeamCoefficient (η : ℝ) (k e a b : ℕ) : ℝ :=
  if k + e = a + b then
    Real.sqrt (((k.factorial : ℝ) * e.factorial) / (a.factorial * b.factorial)) *
      ∑ p ∈ Finset.range (a + 1), ∑ q ∈ Finset.range (b + 1),
        if p + q = k then
          (a.choose p : ℝ) * b.choose q *
            Real.sqrt η ^ p * (-Real.sqrt (1 - η)) ^ (a - p) *
            Real.sqrt (1 - η) ^ q * Real.sqrt η ^ (b - q)
        else 0
  else 0

/-- The same passive rotation is performed on all mode indices. -/
def beamCoefficient {n : ℕ} (η : ℝ) (k e a b : NumberIndex n) : ℝ :=
  ∏ j, oneModeBeamCoefficient η (k j) (e j) (a j) (b j)

/-- Choices of the first input number in the total-number sector of `(k,e)`. -/
abbrev SectorSplit {n : ℕ} (k e : NumberIndex n) := ∀ j, Fin (k j + e j + 1)

def splitLeft {n : ℕ} {k e : NumberIndex n} (a : SectorSplit k e) : NumberIndex n :=
  fun j => a j

def splitRight {n : ℕ} {k e : NumberIndex n} (a : SectorSplit k e) : NumberIndex n :=
  fun j => k j + e j - a j

/-- A single discarded-number diagonal block of `U(ρA ⊗ ρB)U†`.
The sums are finite because passive mixing preserves number in each paired
mode. The two unrestricted density matrices allow all internal entanglement. -/
def outputBlock {n : ℕ} (η : ℝ) (ρA ρB : State n)
    (k l e : NumberIndex n) : ℂ :=
  ∑ a : SectorSplit k e, ∑ b : SectorSplit l e,
    (beamCoefficient η k e (splitLeft a) (splitRight a) : ℂ) *
      entry ρA.op (splitLeft a) (splitLeft b) *
      entry ρB.op (splitRight a) (splitRight b) *
      (beamCoefficient η l e (splitLeft b) (splitRight b) : ℂ)

/-- Reduced state after passive beam-splitter mixing of independent ports.
The second row of the orthogonal rotation is `(-√(1−η),√η)`; changing its
sign has no effect on this reduced state. `HasSum` records the actual partial
trace, not a default value for a possibly divergent series. -/
def IsBeamSplitterOutput {n : ℕ} (η : ℝ) (ρA ρB ρC : State n) : Prop :=
  ∀ k l, HasSum (outputBlock η ρA ρB k l) (entry ρC.op k l)

/-- The entropy photon-number inequality for arbitrary finite-energy inputs
and any positive finite number of modes. -/
theorem entropy_photon_number_inequality
    (n : ℕ) (hn : 1 ≤ n) (ρA ρB ρC : State n)
    (hA : FiniteEnergy ρA) (hB : FiniteEnergy ρB)
    (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hC : IsBeamSplitterOutput η ρA ρB ρC) :
    η * gInv (entropy ρA / n) + (1 - η) * gInv (entropy ρB / n) ≤
      gInv (entropy ρC / n) := by
  sorry

end EntropyPhotonNumber

end

end OAI
