import Mathlib

namespace OAI

universe u

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Filter

namespace GAD

abbrev Basis (n : ℕ) := Fin n → Fin 2
abbrev QMatrix (n : ℕ) := Matrix (Basis n) (Basis n) ℂ

/-- The spectral definition of -Tr(P log P), with 0 log 0 = 0. -/
def entropy {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog P)).re

def IsState {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : Prop :=
  P.PosSemidef ∧ Matrix.trace P = 1


def kraus (γ ν : ℝ) (r : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if r = 0 then
    !![(Real.sqrt (1 - ν) : ℂ), 0;
       0, (Real.sqrt (1 - ν) * Real.sqrt (1 - γ) : ℂ)]
  else if r = 1 then
    !![0, (Real.sqrt (γ * (1 - ν)) : ℂ); 0, 0]
  else if r = 2 then
    !![(Real.sqrt ν * Real.sqrt (1 - γ) : ℂ), 0; 0, (Real.sqrt ν : ℂ)]
  else
    !![0, 0; (Real.sqrt (γ * ν) : ℂ), 0]

/-- Tensor products of the single-site Kraus operators, with the full Kraus index. -/
def tensorKraus (γ ν : ℝ) (n : ℕ) (r : Fin n → Fin 4) : QMatrix n :=
  fun i j ↦ ∏ k, kraus γ ν (r k) (i k) (j k)

/-- The memoryless n-fold generalized amplitude-damping channel. -/
def channel (γ ν : ℝ) (n : ℕ) (P : QMatrix n) : QMatrix n :=
  ∑ r : Fin n → Fin 4,
    tensorKraus γ ν n r * P * (tensorKraus γ ν n r).conjTranspose

/-- All finite ensembles, without any product or purity restriction. -/
structure Ensemble (n : ℕ) where
  size : ℕ
  weight : Fin size → ℝ
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_sum : ∑ a, weight a = 1
  signal : Fin size → QMatrix n
  signal_state : ∀ a, IsState (signal a)

def ensembleValue (γ ν : ℝ) {n : ℕ} (E : Ensemble n) : ℝ :=
  (entropy (∑ a, (E.weight a : ℂ) • channel γ ν n (E.signal a)) -
    ∑ a, E.weight a * entropy (channel γ ν n (E.signal a))) / Real.log 2


def holevo (γ ν : ℝ) (n : ℕ) : ℝ :=
  sSup (Set.range (ensembleValue γ ν : Ensemble n → ℝ))

/-- An unrestricted n-use quantum code with one collective output POVM. -/
structure Code (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encoding : Fin messages → QMatrix n
  encoding_state : ∀ a, IsState (encoding a)
  decoding : Fin messages → QMatrix n
  decoding_pos : ∀ a, (decoding a).PosSemidef
  decoding_sum : ∑ a, decoding a = 1

def averageError (γ ν : ℝ) {n : ℕ} (C : Code n) : ℝ :=
  1 - (∑ a, (Matrix.trace (C.decoding a * channel γ ν n (C.encoding a))).re) /
    (C.messages : ℝ)

/-- The liminf rate condition written as its eventual lower-bound characterization.
There is no preshared entanglement, feedback, or restriction on encodings/decoding. -/
def Achievable (γ ν R : ℝ) : Prop :=
  ∃ C : (n : ℕ) → Code n,
    Tendsto (fun n ↦ averageError γ ν (C n)) atTop (nhds 0) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      R - ε ≤ Real.log ((C n).messages : ℝ) / Real.log 2 / (n : ℝ)

/-- Operational unassisted classical capacity, not a definition by regularization. -/
def capacity (γ ν : ℝ) : ℝ := sSup {R : ℝ | Achievable γ ν R}

def g (u : ℝ) : ℝ := Real.binEntropy ((1 + Real.sqrt (1 - 4 * u)) / 2)

def v (γ ν p : ℝ) : ℝ := γ * ν * (1 - ν) + γ * (1 - γ) * (p - ν) ^ 2

def objective (γ ν p : ℝ) : ℝ :=
  Real.binEntropy ((1 - γ) * p + γ * ν) - g (v γ ν p)

def Maximizes (γ ν p : ℝ) : Prop :=
  p ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ q ∈ Set.Icc (0 : ℝ) 1, objective γ ν q ≤ objective γ ν p


def phaseSignal (p : ℝ) (s b : Fin 2) : ℂ :=
  if b = 0 then (Real.sqrt (1 - p) : ℂ)
  else if s = 0 then (Real.sqrt p : ℂ) else -(Real.sqrt p : ℂ)

def phaseProduct (p : ℝ) {n : ℕ} (s : Basis n) (i : Basis n) : ℂ :=
  ∏ k, phaseSignal p (s k) (i k)

def phaseState (p : ℝ) {n : ℕ} (s : Basis n) : QMatrix n :=
  fun i j ↦ phaseProduct p s i * star (phaseProduct p s j)

/-- Holevo value of the explicit 2^n equiprobable product signals. -/
def phaseValue (γ ν p : ℝ) (n : ℕ) : ℝ :=
  (entropy (∑ s : Basis n, (((2 : ℝ) ^ n)⁻¹ : ℂ) • channel γ ν n (phaseState p s)) -
    ∑ s : Basis n, ((2 : ℝ) ^ n)⁻¹ * entropy (channel γ ν n (phaseState p s))) /
    Real.log 2

theorem main (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hν : ν ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) * holevo γ ν 1) ∧
    (∃ p : ℝ, Maximizes γ ν p ∧
      ∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) / Real.log 2 * objective γ ν p) ∧
    capacity γ ν = holevo γ ν 1 ∧
    (∀ p : ℝ, Maximizes γ ν p → ∀ n : ℕ, 1 ≤ n →
      (∀ s : Basis n, IsState (phaseState p s)) ∧
      holevo γ ν n = phaseValue γ ν p n) := by
  sorry

end GAD
end

end OAI
