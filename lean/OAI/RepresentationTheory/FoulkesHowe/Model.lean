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

def IsPlethysmAction (outer inner : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (g : V ≃ₗ[ℂ] V)
    (L : SymPow outer (SymPow inner V) →ₗ[ℂ]
      SymPow outer (SymPow inner V)) : Prop :=
  ∀ v : Fin outer → Fin inner → V,
    L (symMonomial outer (SymPow inner V)
        (fun i => symMonomial inner V (v i))) =
      symMonomial outer (SymPow inner V)
        (fun i => symMonomial inner V (fun j => g (v i j)))

def IsGLEquivariantEmbedding (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (ι : SymPow a (SymPow b V) →ₗ[ℂ] SymPow b (SymPow a V)) : Prop :=
  Function.Injective ι ∧
    ∀ g : V ≃ₗ[ℂ] V,
      ∃ Lsource : SymPow b (SymPow a V) →ₗ[ℂ] SymPow b (SymPow a V),
      ∃ Ltarget : SymPow a (SymPow b V) →ₗ[ℂ] SymPow a (SymPow b V),
        IsPlethysmAction b a V g Lsource ∧
        IsPlethysmAction a b V g Ltarget ∧
        Function.Bijective Lsource ∧
        Function.Bijective Ltarget ∧
        Lsource.comp ι = ι.comp Ltarget

abbrev SymmetricMultilinearForm (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :=
  MultilinearMap ℂ (fun _ : Fin a => SymPow b V) ℂ

def IsSymmetricMultilinearForm (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (T : SymmetricMultilinearForm a b V) : Prop :=
  ∀ (σ : Equiv.Perm (Fin a)) (x : Fin a → SymPow b V),
    T (fun i => x (σ i)) = T x

end Problem346

end

end OAI
