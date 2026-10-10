import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators
universe u

namespace Problem346

def symMonomialRaw (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (v : Fin n → V) : SymmetricAlgebra ℂ V :=
  ∏ i : Fin n, SymmetricAlgebra.ι ℂ V (v i)

def symPowSubmodule (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    Submodule ℂ (SymmetricAlgebra ℂ V) :=
  Submodule.span ℂ (Set.range (symMonomialRaw n V))

abbrev SymPow (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :=
  ↥(symPowSubmodule n V)

def symMonomial (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (v : Fin n → V) : SymPow n V :=
  ⟨symMonomialRaw n V v, Submodule.subset_span (Set.mem_range_self v)⟩

def foulkesFormula (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (v : Fin b → Fin a → V) : SymPow a (SymPow b V) := by
  classical
  exact
    ((a.factorial : ℂ) ^ b)⁻¹ •
      ∑ σ : Fin b → Equiv.Perm (Fin a),
        symMonomial a (SymPow b V)
          (fun i => symMonomial b V (fun j => v j ((σ j) i)))

def IsFoulkesMap (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)) : Prop :=
  ∀ v : Fin b → Fin a → V,
    μ (symMonomial b (SymPow a V) (fun j => symMonomial a V (v j))) =
      foulkesFormula a b V v

theorem canonical_foulkes_howe_surjective :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a b : ℕ), 2 ≤ a → a * (a - 1) ≤ b → ∃ μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V μ ∧ Function.Surjective μ ∧ ∀ ν : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V ν → ν = μ := by
  sorry

end Problem346

end

end OAI
