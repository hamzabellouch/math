import Mathlib

namespace OAI

namespace Superstring

abbrev Symbol := List Bool
abbrev Word := List Symbol
abbrev Instance := List Word

/-- Prefix markers encode the list spine, including its final boundary. -/
def encodeList {α : Type} (enc : α → List Bool) : List α → List Bool
  | [] => [true]
  | a :: as => false :: (enc a ++ encodeList enc as)

def encodeSymbol : Symbol → List Bool := encodeList (fun b => [b])
def encodeWord : Word → List Bool := encodeList encodeSymbol
def encodeInstance : Instance → List Bool := encodeList encodeWord

/-- Ordinary contiguous substring containment, including the empty word. -/
def IsCommonSuperstring (S : Instance) (T : Word) : Prop :=
  ∀ s ∈ S, s <:+: T

/-- The optimum in symbols, not in bits. -/
noncomputable def opt (S : Instance) : ℕ :=
  sInf {n : ℕ | ∃ T : Word, IsCommonSuperstring S T ∧ T.length = n}

/-- A deterministic finite-stack-machine implementation, with a polynomial bound
on bit-level running time in the explicitly encoded input length. -/
def HasPolynomialImplementation (f : Instance → Word) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime encodeInstance encodeWord f,
    ∀ k : M.tm.K, Finite (M.tm.Γ k)

/-- The deterministic algorithm with its exact finite-alphabet bit-machine
certificate, contiguous coverage, and factor-two bound in symbols. -/
theorem main : ∃ f : Instance → Word,
    HasPolynomialImplementation f ∧
    ∀ S, IsCommonSuperstring S (f S) ∧ (f S).length ≤ 2 * opt S := by
  sorry

end Superstring

end OAI
