import Mathlib

namespace OAI

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter

namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure TracialVector (M : VonNeumannAlgebra H) where
  vacuum : H
  norm_vacuum : ‖vacuum‖ = 1
  tracial : ∀ A ∈ M, ∀ B ∈ M,
    inner ℂ vacuum ((A * B) vacuum) = inner ℂ vacuum ((B * A) vacuum)
  separating : ∀ A ∈ M, A vacuum = 0 → A = 0

def trace {M : VonNeumannAlgebra H} (τ : TracialVector M) (A : H →L[ℂ] H) : ℂ :=
  inner ℂ τ.vacuum (A τ.vacuum)

def wordEval {n : ℕ} (X : Fin n → H →L[ℂ] H) (w : List (Fin n)) : H →L[ℂ] H :=
  (w.map X).prod

def wordMoment {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (w : List (Fin n)) : ℂ := trace τ (wordEval X w)

def FreeSubalgebras {ι : Type} {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A : ι → Subalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (j : Fin k → ι) (a : Fin k → H →L[ℂ] H),
    (∀ r, a r ∈ A (j r)) → (∀ r, trace τ (a r) = 0) →
    (∀ (r : ℕ) (hr : r + 1 < k),
      j ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩ ≠ j ⟨r + 1, hr⟩) →
    trace τ (List.ofFn a).prod = 0

def FreeStandardNoise {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X S : Fin n → H →L[ℂ] H) : Prop :=
  (∀ i k, trace τ (S i ^ k) =
    if Even k then (catalan (k / 2) : ℂ) else 0) ∧
  FreeSubalgebras τ (fun j : Option (Fin n) => match j with
    | none => Algebra.adjoin ℂ (Set.range X)
    | some i => Algebra.adjoin ℂ {S i})

def polynomialL2 {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range (fun w : List (Fin n) => wordEval X w τ.vacuum))).topologicalClosure

def derivativeMoment {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : List (Fin n)) : ℂ :=
  ∑ r : Fin w.length, if w[r.val] = i then
    wordMoment τ X (w.take r.val) * wordMoment τ X (w.drop (r.val + 1)) else 0

def ConjugateSystem {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (ξ : Fin n → H) : Prop :=
  ∀ i, ξ i ∈ polynomialL2 τ X ∧ ∀ w : List (Fin n),
    inner ℂ (ξ i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w

def freeFisher {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) : ℝ≥0∞ :=
  ⨅ (ξ : Fin n → H) (_ : ConjugateSystem τ X ξ), ENNReal.ofReal (∑ i, ‖ξ i‖ ^ 2)

def heatTuple {n : ℕ} (X S : Fin n → H →L[ℂ] H) (s : ℝ) :
    Fin n → H →L[ℂ] H := fun i => X i + (Real.sqrt s : ℂ) • S i

def chiStar {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X S : Fin n → H →L[ℂ] H) : EReal :=
  let b : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal ((n : ℝ) / (1 + s))
  let f : ℝ → ℝ≥0∞ := fun s => freeFisher τ (heatTuple X S s)
  ((n / 2 * Real.log (2 * Real.pi * Real.exp 1) : ℝ) : EReal) +
    (1 / 2 : EReal) * (∫⁻ s in Set.Ioi (0 : ℝ), b s - f s).toEReal -
    (1 / 2 : EReal) * (∫⁻ s in Set.Ioi (0 : ℝ), f s - b s).toEReal

abbrev MatrixCoordinates (n d : ℕ) := EuclideanSpace ℝ (Fin n × Fin d × Fin d)

def hermitianMatrix {n d : ℕ} (a : MatrixCoordinates n d) (i : Fin n) :
    Matrix (Fin d) (Fin d) ℂ := fun j k =>
  if j = k then (a (i, j, j) : ℂ)
  else if j < k then ((a (i, j, k) : ℂ) + Complex.I * (a (i, k, j) : ℂ)) / Real.sqrt 2
  else ((a (i, k, j) : ℂ) - Complex.I * (a (i, j, k) : ℂ)) / Real.sqrt 2

def matrixOpNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

def matrixMoment {n d : ℕ} (a : MatrixCoordinates n d) (w : List (Fin n)) : ℂ :=
  (d : ℂ)⁻¹ * Matrix.trace (w.map (hermitianMatrix a)).prod

def microstates {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (R : ℝ) (m d : ℕ) (ε : ℝ) : Set (MatrixCoordinates n d) :=
  {a | (∀ i, matrixOpNorm (hermitianMatrix a i) ≤ R) ∧
    ∀ w : List (Fin n), w.length ≤ m → ‖matrixMoment a w - wordMoment τ X w‖ < ε}

def chiCutoff {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (R : ℝ) : EReal :=
  ⨅ m : ℕ, ⨅ ε : {ε : ℝ // 0 < ε},
    limsup (fun d : ℕ =>
      (((((d + 1 : ℕ) : ℝ) ^ 2)⁻¹ : ℝ) : EReal) *
        (volume (microstates τ X R m (d + 1) ε.val)).log +
      (((n : ℝ) / 2 * Real.log (d + 1) : ℝ) : EReal)) atTop

def chi {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) : EReal :=
  ⨆ R : {R : ℝ // 0 < R}, chiCutoff τ X R.val

open MeasureTheory

theorem main :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (M : VonNeumannAlgebra H) (τ : TracialVector M)
      (n : ℕ) (X S : Fin n → H →L[ℂ] H),
      2 ≤ n ∧
      (∀ i, X i ∈ M ∧ IsSelfAdjoint (X i)) ∧
      (∀ i, S i ∈ M ∧ IsSelfAdjoint (S i)) ∧
      FreeStandardNoise τ X S ∧
      (⊥ : EReal) < chi τ X ∧
      chi τ X ≤ chiStar τ X S - (1 / 2 : EReal) ∧
      chiStar τ X S - (1 / 2 : EReal) < (⊤ : EReal) := by
  sorry

end FiniteEntropySeparation

end

end OAI
