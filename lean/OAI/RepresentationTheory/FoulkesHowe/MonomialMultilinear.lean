import OAI.RepresentationTheory.FoulkesHowe.Model

namespace OAI

noncomputable section

open scoped BigOperators

universe u v

namespace Problem346

/-- The product of degree-one generators, with its multilinearity bundled. -/
def symMonomialMultilinear (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin n => V) (SymPow n V) :=
  ((MultilinearMap.mkPiAlgebra ℂ (Fin n) (SymmetricAlgebra ℂ V)).compLinearMap
    (fun _ => SymmetricAlgebra.ι ℂ V)).codRestrict (symPowSubmodule n V)
      (fun x => Submodule.subset_span (Set.mem_range_self x))

@[simp]
theorem symMonomialMultilinear_apply (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (x : Fin n → V) :
    symMonomialMultilinear n V x = symMonomial n V x := rfl

theorem symMonomial_permute (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (σ : Equiv.Perm (Fin n)) (x : Fin n → V) :
    symMonomial n V (fun i => x (σ i)) = symMonomial n V x := by
  apply Subtype.ext
  exact Equiv.prod_comp σ (fun i => SymmetricAlgebra.ι ℂ V (x i))

/-- A functional on a symmetric power induces a symmetric multilinear form. -/
def monomialFunctional (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (φ : SymPow a (SymPow b V) →ₗ[ℂ] ℂ) : SymmetricMultilinearForm a b V :=
  φ.compMultilinearMap (symMonomialMultilinear a (SymPow b V))

@[simp]
theorem monomialFunctional_apply (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (φ : SymPow a (SymPow b V) →ₗ[ℂ] ℂ) (x : Fin a → SymPow b V) :
    monomialFunctional a b V φ x = φ (symMonomial a (SymPow b V) x) := rfl

theorem monomialFunctional_symmetric (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (φ : SymPow a (SymPow b V) →ₗ[ℂ] ℂ) :
    IsSymmetricMultilinearForm a b V (monomialFunctional a b V φ) := by
  intro σ x
  simp only [monomialFunctional_apply, symMonomial_permute]

/-- Monomial values determine every linear map out of a symmetric power. -/
theorem linearMap_eq_zero_of_symMonomial (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] {W : Type v} [AddCommGroup W] [Module ℂ W]
    (φ : SymPow n V →ₗ[ℂ] W)
    (hφ : ∀ x : Fin n → V, φ (symMonomial n V x) = 0) : φ = 0 := by
  ext x
  change φ x = 0
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact hφ v
  | zero => exact map_zero φ
  | add x y hx hy ihx ihy =>
      change φ (⟨x, hx⟩ + ⟨y, hy⟩) = 0
      rw [map_add, ihx, ihy, add_zero]
  | smul c x hx ih =>
      change φ (c • (⟨x, hx⟩ : SymPow n V)) = 0
      rw [map_smul, ih, smul_zero]

theorem monomialFunctional_eq_zero_iff (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (φ : SymPow a (SymPow b V) →ₗ[ℂ] ℂ) :
    monomialFunctional a b V φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    apply linearMap_eq_zero_of_symMonomial
    intro x
    exact congrArg (fun T : SymmetricMultilinearForm a b V => T x) h
  · rintro rfl
    rfl

/-- Flatten the `a` rows of `b` vector arguments of a form on `SymPow b V`. -/
def plethysmFormMultilinear (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V) :
    MultilinearMap ℂ (fun _ : Σ _ : Fin a, Fin b => V) ℂ :=
  T.compMultilinearMap (fun _ => symMonomialMultilinear b V)

@[simp]
theorem plethysmFormMultilinear_apply (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (x : (Σ _ : Fin a, Fin b) → V) :
    plethysmFormMultilinear a b V T x =
      T (fun i => symMonomial b V (fun j => x ⟨i,j⟩)) := rfl

theorem plethysmFormMultilinear_inner_permute (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (σ : Fin a → Equiv.Perm (Fin b)) (x : (Σ _ : Fin a, Fin b) → V) :
    plethysmFormMultilinear a b V T (fun ij => x ⟨ij.1, σ ij.1 ij.2⟩) =
      plethysmFormMultilinear a b V T x := by
  apply congrArg T
  funext i
  exact symMonomial_permute b V (σ i) (fun j => x ⟨i,j⟩)

theorem plethysmFormMultilinear_outer_permute (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T)
    (σ : Equiv.Perm (Fin a)) (x : (Σ _ : Fin a, Fin b) → V) :
    plethysmFormMultilinear a b V T (fun ij => x ⟨σ ij.1, ij.2⟩) =
      plethysmFormMultilinear a b V T x := by
  exact hT σ (fun i => symMonomial b V (fun j => x ⟨i,j⟩))

end Problem346

end

end OAI
