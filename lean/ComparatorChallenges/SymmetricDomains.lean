import Mathlib

namespace OAI

namespace Release061

abbrev Affine (n : ℕ) := Fin n → ℂ

def realCoordinates {n : ℕ} (z : Affine n) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun j => (z j).re) (fun j => (z j).im)

def IsAffineAlgebraic {n : ℕ} (V : Set (Affine n)) : Prop :=
  ∃ P : Set (MvPolynomial (Fin n) ℂ),
    V = {z | ∀ p ∈ P, MvPolynomial.eval z p = 0}

inductive IsSemialgebraic {n : ℕ} : Set (Affine n) → Prop
  | zero (p : MvPolynomial (Fin n ⊕ Fin n) ℝ) :
      IsSemialgebraic {z | MvPolynomial.eval (realCoordinates z) p = 0}
  | positive (p : MvPolynomial (Fin n ⊕ Fin n) ℝ) :
      IsSemialgebraic {z | 0 < MvPolynomial.eval (realCoordinates z) p}
  | compl {S : Set (Affine n)} : IsSemialgebraic S → IsSemialgebraic Sᶜ
  | union {S T : Set (Affine n)} :
      IsSemialgebraic S → IsSemialgebraic T → IsSemialgebraic (S ∪ T)

def HolomorphicOnSubset {n m : ℕ} (S : Set (Affine n)) (f : S → Affine m) : Prop :=
  ∀ p : S, ∃ W : Set (Affine n), IsOpen W ∧ (p : Affine n) ∈ W ∧
    ∃ F : Affine n → Affine m, AnalyticOnNhd ℂ F W ∧
      ∀ q : S, (q : Affine n) ∈ W → F q = f q

structure Biholomorph {n m : ℕ} (S : Set (Affine n)) (T : Set (Affine m)) where
  toHomeomorph : S ≃ₜ T
  holomorphic_toFun : HolomorphicOnSubset S (fun p => (toHomeomorph p : Affine m))
  holomorphic_invFun : HolomorphicOnSubset T (fun q => (toHomeomorph.symm q : Affine n))

def IsSmooth {n : ℕ} (S : Set (Affine n)) : Prop :=
  ∀ p : S, ∃ (m : ℕ) (W : Set (Affine n)), W ⊆ S ∧
    IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ (p : Affine n) ∈ W ∧
    ∃ D : Set (Affine m), IsOpen D ∧ Nonempty (Biholomorph W D)

def IsBoundedSymmetricDomain {n : ℕ} (D : Set (Affine n)) : Prop :=
  IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
    ∀ p : D, ∃ σ : Biholomorph D D,
      Function.Involutive σ.toHomeomorph ∧ σ.toHomeomorph p = p ∧
      ∃ W : Set D, IsOpen W ∧ p ∈ W ∧
        ∀ q ∈ W, σ.toHomeomorph q = q → q = p

theorem main {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hopen : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hconn : IsConnected U) (hsa : IsSemialgebraic U)
    (hbounded : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    IsSmooth U ∧ ∃ (m : ℕ) (D : Set (Affine m)),
      IsBoundedSymmetricDomain D ∧ Nonempty (Biholomorph U D) := by
  sorry

end Release061

end OAI
