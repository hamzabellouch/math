import OAI.InformationTheory.QuantumCircuit.Model

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff

namespace QAC

/-- The orthogonal projection onto a normalized one-qubit vector. -/
def rankOne (v : Bit → ℂ) : QubitOperator := fun x y => v x * star (v y)

/-- The same data describe a product projection and its mismatch count.
Normalization is exactly the sum of the squared moduli being one. -/
structure Count (N : ℕ) where
  support : Finset (Fin N)
  vector : Fin N → Bit → ℂ
  normalized : ∀ i ∈ support, ∑ b, Complex.normSq (vector i b) = 1

namespace Count

def zero {N : ℕ} (M : Count N) : Operator N :=
  tensorMatrix fun i => if i ∈ M.support then rankOne (M.vector i) else 1

/-- The orthogonal projection specifying precisely the mismatch set F.
It is used only for F contained in the counted support. -/
def pattern {N : ℕ} (M : Count N) (F : Finset (Fin N)) : Operator N :=
  tensorMatrix fun i => if i ∈ M.support then
    (if i ∈ F then 1 - rankOne (M.vector i) else rankOne (M.vector i)) else 1

/-- The spectral projection [M ≥ r], explicitly expanded in its product eigenbasis. -/
def high {N : ℕ} (M : Count N) (r : ℝ) : Operator N :=
  ∑ F ∈ M.support.powerset, if r ≤ (F.card : ℝ) then M.pattern F else 0

/-- The mismatch operator ∑ᵢ (I - |vᵢ⟩⟨vᵢ|)ᵢ. -/
def operator {N : ℕ} (M : Count N) : Operator N :=
  ∑ i ∈ M.support, tensorMatrix fun j => if j = i then 1 - rankOne (M.vector i) else 1

end Count

abbrev LocalLayer (N : ℕ) := Fin N → Matrix.unitaryGroup Bit ℂ

def localMatrix {N : ℕ} (L : LocalLayer N) : Operator N :=
  tensorMatrix fun i => (L i : QubitOperator)

/-- A parallel layer of product-projection reflections, with disjoint supports. -/
structure ReflectionLayer (N : ℕ) where
  gates : List (Count N)
  disjoint : gates.Pairwise (fun A B => Disjoint A.support B.support)

def reflectionMatrix {N : ℕ} (R : ReflectionLayer N) : Operator N :=
  (R.gates.map fun A => (1 : Operator N) - (2 : ℂ) • A.zero).prod

/-- The enlarged normal form of depth at most `d`.
Identity local and reflection layers are allowed. -/
def IsCircuit {N : ℕ} : ℕ → Operator N → Prop
  | 0, U => ∃ L : LocalLayer N, U = localMatrix L
  | d + 1, U => ∃ (V : Operator N) (R : ReflectionLayer N) (L : LocalLayer N),
      IsCircuit d V ∧ U = V * reflectionMatrix R * localMatrix L

/-- Full uniform localization theorem, including s = 0 and arbitrary t > s. -/
def LocalizationStatement : Prop :=
  ∀ (d : ℕ) (s t : ℝ), 0 ≤ s → s < t →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U : Operator N, IsCircuit d U →
      ∀ M D : Count N,
        ‖M.high ((N : ℝ) ^ t) * U * D.zero * star U * M.zero‖ ≤
          Real.exp (-((N : ℝ) ^ s))

end QAC

end

end OAI
