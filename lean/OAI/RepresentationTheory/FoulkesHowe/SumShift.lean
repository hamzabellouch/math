import Mathlib

namespace OAI

noncomputable section

namespace Problem346.PolynomialShift

open MvPolynomial

universe u v w

abbrev Vars (ι : Type u) (σ : Type v) := ι ⊕ (ι ⊕ σ)
abbrev Poly (R : Type w) (ι : Type u) (σ : Type v) [CommRing R] :=
  MvPolynomial (Vars ι σ) R

variable (R : Type w) (ι : Type u) (σ : Type v) [CommRing R]

/-- Shift one unit of degree from the first coordinate block to the second. -/
def down : Derivation R (Poly R ι σ) (Poly R ι σ) :=
  mkDerivation R (Sum.elim (fun i => X (Sum.inr (Sum.inl i))) (fun _ => 0))

/-- The opposite shift. -/
def up : Derivation R (Poly R ι σ) (Poly R ι σ) :=
  mkDerivation R (Sum.elim (fun _ => 0)
    (Sum.elim (fun i => X (Sum.inl i)) (fun _ => 0)))

/-- Euler operator of the first coordinate block. -/
def sourceEuler : Derivation R (Poly R ι σ) (Poly R ι σ) :=
  mkDerivation R (Sum.elim (fun i => X (Sum.inl i)) (fun _ => 0))

/-- Euler operator of the second coordinate block. -/
def targetEuler : Derivation R (Poly R ι σ) (Poly R ι σ) :=
  mkDerivation R (Sum.elim (fun _ => 0)
    (Sum.elim (fun i => X (Sum.inr (Sum.inl i))) (fun _ => 0)))

/-- Source degree minus destination degree. -/
def weight : Derivation R (Poly R ι σ) (Poly R ι σ) :=
  sourceEuler R ι σ - targetEuler R ι σ

@[simp] theorem down_source (i : ι) :
    down R ι σ (X (Sum.inl i)) = X (Sum.inr (Sum.inl i)) := by
  simp [down]

@[simp] theorem down_target (i : ι) :
    down R ι σ (X (Sum.inr (Sum.inl i))) = 0 := by
  simp [down]

@[simp] theorem down_spectator (i : σ) :
    down R ι σ (X (Sum.inr (Sum.inr i))) = 0 := by
  simp [down]

@[simp] theorem up_source (i : ι) :
    up R ι σ (X (Sum.inl i)) = 0 := by
  simp [up]

@[simp] theorem up_target (i : ι) :
    up R ι σ (X (Sum.inr (Sum.inl i))) = X (Sum.inl i) := by
  simp [up]

@[simp] theorem up_spectator (i : σ) :
    up R ι σ (X (Sum.inr (Sum.inr i))) = 0 := by
  simp [up]

@[simp] theorem weight_source (i : ι) :
    weight R ι σ (X (Sum.inl i)) = X (Sum.inl i) := by
  simp [weight, sourceEuler, targetEuler]

@[simp] theorem weight_target (i : ι) :
    weight R ι σ (X (Sum.inr (Sum.inl i))) = -X (Sum.inr (Sum.inl i)) := by
  simp [weight, sourceEuler, targetEuler]

@[simp] theorem weight_spectator (i : σ) :
    weight R ι σ (X (Sum.inr (Sum.inr i))) = 0 := by
  simp [weight, sourceEuler, targetEuler]

/-- The fundamental commutator, with arbitrary spectator variables. -/
theorem up_down_commutator :
    ⁅up R ι σ, down R ι σ⁆ = weight R ι σ := by
  apply MvPolynomial.derivation_ext
  intro i
  rcases i with i | (i | i) <;> simp [Derivation.commutator_apply]

/-- The opposite shift raises the source-minus-destination weight by two. -/
theorem weight_up_commutator :
    ⁅weight R ι σ, up R ι σ⁆ = (2 : R) • up R ι σ := by
  apply MvPolynomial.derivation_ext
  intro i
  rcases i with i | (i | i) <;>
    simp [Derivation.commutator_apply, two_smul]

/-- The forward shift lowers the source-minus-destination weight by two. -/
theorem weight_down_commutator :
    ⁅weight R ι σ, down R ι σ⁆ = -(2 : R) • down R ι σ := by
  apply MvPolynomial.derivation_ext
  intro i
  rcases i with i | (i | i) <;>
    simp [Derivation.commutator_apply, two_smul]
  abel

end Problem346.PolynomialShift

end

end OAI
