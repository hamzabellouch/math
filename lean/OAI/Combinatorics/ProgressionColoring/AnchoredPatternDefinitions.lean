import OAI.Combinatorics.ProgressionColoring.UniformMesh
import OAI.Combinatorics.ProgressionColoring.AdaptiveMesh
import OAI.Combinatorics.ProgressionColoring.LabelCounts

namespace OAI

/-!
# Actual eligible return-period words

The literal real paths, mesh labels, eligibility predicate, and finite event
indices are shared by counting and long-period geometry. Their definitions do
not depend on arrangement estimates. Counting is proved in `AnchoredPatterns`.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.AnchoredPatterns

open Set
open scoped BigOperators

/-- Starts and drift vectors of an actual local path. -/
structure Realization (D : ℕ) where
  x : Fin D → ℝ
  y : Fin D → ℝ
  u : Fin D → ℝ
  v : Fin D → ℝ

variable {D h : ℕ}

/-- Equivalent to reduced denominator one when `h > 0`; no drift restriction
is part of stationarity. -/
def stationary (lambda : ℕ) (t : Fin D → Fin h) (i : Fin D) : Prop :=
  h ∣ lambda * (t i).val

def firstPath (R : Realization D) (t : Fin D → Fin h) (z : Fin h) (i : Fin D) : ℝ :=
  R.x i + (z.val : ℝ) / h * ((t i).val + R.u i)

def secondPath (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h)
    (z : Fin h) (i : Fin D) : ℝ :=
  R.y i + (z.val : ℝ) / h * ((lambda : ℝ) * (t i).val + R.v i)

def regular (eta : ℝ) (R : Realization D) (lambda : ℕ)
    (t : Fin D → Fin h) (z : Fin h) : Prop :=
  ∀ i, ¬ stationary lambda t i → eta ≤ rho (secondPath R lambda t z i)

def regularPositions (eta : ℝ) (R : Realization D) (lambda : ℕ)
    (t : Fin D → Fin h) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter (regular eta R lambda t)

def fullLabel (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (R : Realization D)
    (lambda : ℕ) (t : Fin D → Fin h) (z : Fin h) : FullLabel D (Fin n) A.Label :=
  (fun i => UniformMesh.label n hn (firstPath R t z i),
    fun i => A.meshLabel (secondPath R lambda t z i))

def recordedWord (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) :
    Fin h → Option (FullLabel D (Fin n) A.Label) := by
  classical
  exact fun z => if regular eta R lambda t z then
    some (fullLabel n hn A R lambda t z) else none

structure EligibleRealization (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (lambda : ℕ) (t : Fin D → Fin h) (R : Realization D) : Prop where
  regular_many : h ≤ 2 * (regularPositions eta R lambda t).card
  regular_injective : ∀ z z', regular eta R lambda t z → regular eta R lambda t z' →
    fullLabel n hn A R lambda t z = fullLabel n hn A R lambda t z' → z = z'
  first_drift : ∀ i, |R.u i| ≤ 1 / (n : ℝ)
  rotating_drift : ∀ i, ¬ stationary lambda t i → |R.v i| ≤ A.H
  stationary_drift : ∀ i, stationary lambda t i → ∀ z,
    regular eta R lambda t z → |R.v i| ≤ A.width (A.meshLabel (secondPath R lambda t z i))

/-- The word itself is the pattern. Distinct realizing parameters do not
give distinct eligible objects. -/
def eligibleOptionFullLabel (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (lambda : ℕ) (t : Fin D → Fin h)
    (word : Fin h → Option (FullLabel D (Fin n) A.Label)) : Prop :=
  ∃ R : Realization D, EligibleRealization n hn A eta lambda t R ∧
    recordedWord n hn A eta R lambda t = word

/-- Actual step/word pairs, rather than a family of realizing parameters. -/
def eligiblePairs (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (lambda : ℕ) :
    Finset ((Fin D → Fin h) × (Fin h → Option (FullLabel D (Fin n) A.Label))) := by
  classical
  exact Finset.univ.filter (fun p => eligibleOptionFullLabel n hn A eta lambda p.1 p.2)

/-- Incidences with one fixed literal full label. -/
def through (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ) (lambda : ℕ)
    (beta : FullLabel D (Fin n) A.Label) :
    Finset ((Fin D → Fin h) × (Fin h → Option (FullLabel D (Fin n) A.Label))) := by
  classical
  exact (eligiblePairs n hn A eta lambda).filter (fun p => ∃ z, p.2 z = some beta)

@[simp] theorem mem_eligiblePairs (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (eta : ℝ) (lambda : ℕ)
    (p : (Fin D → Fin h) × (Fin h → Option (FullLabel D (Fin n) A.Label))) :
    p ∈ eligiblePairs n hn A eta lambda ↔
      eligibleOptionFullLabel n hn A eta lambda p.1 p.2 := by
  classical
  simp [eligiblePairs]

@[simp] theorem mem_through (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh)
    (eta : ℝ) (lambda : ℕ) (beta : FullLabel D (Fin n) A.Label)
    (p : (Fin D → Fin h) × (Fin h → Option (FullLabel D (Fin n) A.Label))) :
    p ∈ through n hn A eta lambda beta ↔
      eligibleOptionFullLabel n hn A eta lambda p.1 p.2 ∧ ∃ z, p.2 z = some beta := by
  classical
  simp [through]

theorem recordedWord_eq_some_iff (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (eta : ℝ)
    (R : Realization D) (lambda : ℕ) (t : Fin D → Fin h) (z : Fin h)
    (beta : FullLabel D (Fin n) A.Label) :
    recordedWord n hn A eta R lambda t z = some beta ↔
      regular eta R lambda t z ∧ fullLabel n hn A R lambda t z = beta := by
  classical
  by_cases hz : regular eta R lambda t z <;> simp [recordedWord, hz]

end QuantitativeVanDerWaerden.AnchoredPatterns

end

end OAI
