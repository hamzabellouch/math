import Mathlib

namespace OAI

/-! The sharp complete inequality for bounded operators on complex Hilbert spaces. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace
open Set

namespace CrouzeixHilbert

universe u

abbrev Operator (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] := H →L[ℂ] H
abbrev Coeff (m : ℕ) := Matrix (Fin m) (Fin m) ℂ

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def numericalRange (A : Operator H) : Set ℂ :=
  {z | ∃ x : H, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z}

def numericalClosure (A : Operator H) : Set ℂ := closure (numericalRange A)

def supNorm {E : Type*} [NormedAddCommGroup E] (S : Set ℂ) (F : ℂ → E) : ℝ :=
  sSup (insert 0 ((fun z => ‖F z‖) '' S))

abbrev Amplification (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : ℕ) := UniformSpace.Completion (H ⊗[ℂ] EuclideanSpace ℂ (Fin m))

def tensorOperator (A : Operator H) {m : ℕ} (B : Coeff m) :
    Operator (Amplification H m) :=
  (TensorProduct.mapL A (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) B)).completion

def matrixPolynomial {m d : ℕ} (B : Fin (d + 1) → Coeff m) (z : ℂ) : Coeff m :=
  ∑ k : Fin (d + 1), z ^ (k : ℕ) • B k

def polynomialEval (A : Operator H) {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    Operator (Amplification H m) :=
  ∑ k : Fin (d + 1), tensorOperator (A ^ (k : ℕ)) (B k)

structure SmoothContour where
  path : ℝ → ℂ
  smooth : ContDiff ℝ 1 path
  closed : path 0 = path 1

def SmoothContour.index (Γ : SmoothContour) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - z)

structure CalculusContour (K U : Set ℂ) extends SmoothContour where
  avoids : ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ U \ K
  index_inside : ∀ z ∈ K, toSmoothContour.index z = 1
  index_outside : ∀ z ∉ U, toSmoothContour.index z = 0

def contourEval (A : Operator H) (Γ : SmoothContour) (f : ℂ → ℂ) : Operator H :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∫ t in (0 : ℝ)..1, (deriv Γ.path t * f (Γ.path t)) •
      Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - A)

def holomorphicEval (A : Operator H) (U : Set ℂ) (f : ℂ → ℂ) : Operator H := by
  classical
  exact if h : Nonempty (CalculusContour (numericalClosure A) U) then
    contourEval A (Classical.choice h).toSmoothContour f
  else 0

def matrixHolomorphicEval (A : Operator H) {m : ℕ} (U : Set ℂ)
    (F : ℂ → Coeff m) : Operator (Amplification H m) :=
  ∑ i, ∑ j, tensorOperator (holomorphicEval A U (fun z => F z i j))
    (Matrix.single i j 1)

def EntrywiseHolomorphic {m : ℕ} (U : Set ℂ) (F : ℂ → Coeff m) : Prop :=
  ∀ i j, DifferentiableOn ℂ (fun z => F z i j) U

abbrev RationalMatrix (m : ℕ) := Matrix (Fin m) (Fin m) (RatFunc ℂ)

def PolesOutside {m : ℕ} (K : Set ℂ) (R : RationalMatrix m) : Prop :=
  ∀ i j z, z ∈ K → (R i j).denom.eval z ≠ 0

def matrixRationalFunction {m : ℕ} (R : RationalMatrix m) (z : ℂ) : Coeff m :=
  fun i j => RatFunc.eval (RingHom.id ℂ) z (R i j)

def rationalEval (A : Operator H) (r : RatFunc ℂ) : Operator H :=
  (Polynomial.aeval A r.num) * Ring.inverse (Polynomial.aeval A r.denom)

def matrixRationalEval (A : Operator H) {m : ℕ} (R : RationalMatrix m) :
    Operator (Amplification H m) :=
  ∑ i, ∑ j, tensorOperator (rationalEval A (R i j)) (Matrix.single i j 1)

def NonzeroConclusion (A : Operator H) : Prop :=
  IsCompact (numericalClosure A) ∧
  Convex ℝ (numericalClosure A) ∧
  spectrum ℂ A ⊆ numericalClosure A ∧
  (∀ (m : ℕ), 0 < m → ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B) ∧
    supNorm (numericalRange A) (matrixPolynomial B) =
      supNorm (numericalClosure A) (matrixPolynomial B) ∧
    ∃ z ∈ numericalClosure A,
      supNorm (numericalClosure A) (matrixPolynomial B) = ‖matrixPolynomial B z‖) ∧
  (∀ (m : ℕ), 0 < m → ∀ (U : Set ℂ) (F : ℂ → Coeff m),
    IsOpen U → numericalClosure A ⊆ U → EntrywiseHolomorphic U F →
    Nonempty (CalculusContour (numericalClosure A) U) ∧
    (∀ Γ : CalculusContour (numericalClosure A) U, ∀ i j,
      holomorphicEval A U (fun z => F z i j) =
        contourEval A Γ.toSmoothContour (fun z => F z i j)) ∧
    ‖matrixHolomorphicEval A U F‖ ≤ 2 * supNorm (numericalClosure A) F ∧
    ∃ z ∈ numericalClosure A, supNorm (numericalClosure A) F = ‖F z‖) ∧
  (∀ (m : ℕ), 0 < m → ∀ (R : RationalMatrix m),
    PolesOutside (numericalClosure A) R →
    (∀ i j, IsUnit (Polynomial.aeval A (R i j).denom)) ∧
    ‖matrixRationalEval A R‖ ≤
      2 * supNorm (numericalClosure A) (matrixRationalFunction R) ∧
    (∃ z ∈ numericalClosure A,
      supNorm (numericalClosure A) (matrixRationalFunction R) =
        ‖matrixRationalFunction R z‖) ∧
    ∃ U : Set ℂ, IsOpen U ∧ numericalClosure A ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) ∧
      matrixRationalEval A R = matrixHolomorphicEval A U (matrixRationalFunction R))

def ZeroConclusion (A : Operator H) : Prop :=
  numericalRange A = ∅ ∧
  (∀ (m d : ℕ) (B : Fin (d + 1) → Coeff m),
    polynomialEval A B = 0 ∧
    supNorm (numericalRange A) (matrixPolynomial B) = 0 ∧
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B)) ∧
  (∀ (m : ℕ) (U : Set ℂ) (F : ℂ → Coeff m),
    matrixHolomorphicEval A U F = 0 ∧
    supNorm (numericalRange A) F = 0 ∧
    ‖matrixHolomorphicEval A U F‖ ≤ 2 * supNorm (numericalRange A) F) ∧
  (∀ (m : ℕ) (R : RationalMatrix m),
    matrixRationalEval A R = 0 ∧
    supNorm (numericalRange A) (matrixRationalFunction R) = 0 ∧
    ‖matrixRationalEval A R‖ ≤
      2 * supNorm (numericalRange A) (matrixRationalFunction R))

def SharpConstant : Prop :=
  ∃ (A : Operator (EuclideanSpace ℂ (Fin 2))) (B : Fin 2 → Coeff 1),
    supNorm (numericalRange A) (matrixPolynomial (d := 1) B) = 1 ∧
    ‖polynomialEval A (d := 1) B‖ = 2

end CrouzeixHilbert

namespace CrouzeixHilbert

universe u

theorem hilbert (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : Operator H) :
    (Nontrivial H → NonzeroConclusion A) ∧
    (Subsingleton H → ZeroConclusion A) ∧ SharpConstant := by
  sorry

end CrouzeixHilbert

end

end OAI
