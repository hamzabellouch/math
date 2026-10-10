import Mathlib

namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

abbrev Coeff (m : ℕ) := Matrix (Fin m) (Fin m) ℂ
abbrev CoeffSpace (m : ℕ) := EuclideanSpace ℂ (Fin m)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def numericalRange (A : H →L[ℂ] H) : Set ℂ :=
  {z | ∃ x : H, ‖x‖ = 1 ∧ inner ℂ x (A x) = z}

def numericalClosure (A : H →L[ℂ] H) : Set ℂ := closure (numericalRange A)

abbrev Amplification (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : ℕ) := UniformSpace.Completion (H ⊗[ℂ] CoeffSpace m)

def tensorOp {m : ℕ} (A : H →L[ℂ] H) (B : Coeff m) :
    Amplification H m →L[ℂ] Amplification H m :=
  (TensorProduct.mapL A (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) B)).completion

def matrixPolynomial {m d : ℕ} (B : Fin (d + 1) → Coeff m) (z : ℂ) : Coeff m :=
  ∑ k : Fin (d + 1), z ^ k.val • B k

def polynomialEval {m d : ℕ} (A : H →L[ℂ] H) (B : Fin (d + 1) → Coeff m) :
    Amplification H m →L[ℂ] Amplification H m :=
  ∑ k : Fin (d + 1), tensorOp (A ^ k.val) (B k)

def normSup {E : Type*} [Norm E] (S : Set ℂ) (f : ℂ → E) : ℝ :=
  if S.Nonempty then sSup ((fun z => ‖f z‖) '' S) else 0

def contourIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (γ : ℝ → ℂ) (f : ℂ → E) : E :=
  ∫ t : ℝ in (0 : ℝ)..1, deriv γ t • f (γ t)

def contourIndex (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * contourIntegral γ (fun w => (w - z)⁻¹)

def IsCauchyContour (K U : Set ℂ) (γ : ℝ → ℂ) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = γ 1 ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ U \ K) ∧
  (∀ z ∈ K, contourIndex γ z = 1) ∧
  (∀ z ∉ U, contourIndex γ z = 0)

def chosenContour (K U : Set ℂ) : ℝ → ℂ :=
  Classical.epsilon (IsCauchyContour K U)

variable [CompleteSpace H]

def dunfordIntegral (A : H →L[ℂ] H) (γ : ℝ → ℂ) (f : ℂ → ℂ) : H →L[ℂ] H :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    contourIntegral γ (fun z => f z • resolvent A z)

def holomorphicCalculus (A : H →L[ℂ] H) (U : Set ℂ) (f : ℂ → ℂ) : H →L[ℂ] H :=
  dunfordIntegral A (chosenContour (numericalClosure A) U) f

def matrixUnit {m : ℕ} (i j : Fin m) : Coeff m := Matrix.single i j 1

def holomorphicEval {m : ℕ} (A : H →L[ℂ] H) (U : Set ℂ) (F : ℂ → Coeff m) :
    Amplification H m →L[ℂ] Amplification H m :=
  ∑ i : Fin m, ∑ j : Fin m,
    tensorOp (holomorphicCalculus A U (fun z => F z i j)) (matrixUnit i j)

def contourEval {m : ℕ} (A : H →L[ℂ] H) (γ : ℝ → ℂ) (F : ℂ → Coeff m) :
    Amplification H m →L[ℂ] Amplification H m :=
  ∑ i : Fin m, ∑ j : Fin m,
    tensorOp (dunfordIntegral A γ (fun z => F z i j)) (matrixUnit i j)

def HolomorphicOn {m : ℕ} (F : ℂ → Coeff m) (U : Set ℂ) : Prop :=
  ∀ i j, DifferentiableOn ℂ (fun z => F z i j) U

abbrev RationalMatrix (m : ℕ) := Matrix (Fin m) (Fin m) (RatFunc ℂ)

def poleFreeSet {m : ℕ} (R : RationalMatrix m) : Set ℂ :=
  {z | ∀ i j, (R i j).denom.eval z ≠ 0}

def rationalFunction {m : ℕ} (R : RationalMatrix m) (z : ℂ) : Coeff m :=
  fun i j => RatFunc.eval (RingHom.id ℂ) z (R i j)

def rationalCalculus (A : H →L[ℂ] H) (r : RatFunc ℂ) : H →L[ℂ] H :=
  Polynomial.aeval A r.num * Ring.inverse (Polynomial.aeval A r.denom)

def rationalEval {m : ℕ} (A : H →L[ℂ] H) (R : RationalMatrix m) :
    Amplification H m →L[ℂ] Amplification H m :=
  ∑ i : Fin m, ∑ j : Fin m, tensorOp (rationalCalculus A (R i j)) (matrixUnit i j)

def PolynomialConclusion (A : H →L[ℂ] H) : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
    ‖polynomialEval A B‖ ≤ 2 * normSup (numericalRange A) (matrixPolynomial B) ∧
    2 * normSup (numericalRange A) (matrixPolynomial B) =
      2 * normSup (numericalClosure A) (matrixPolynomial B) ∧
    IsGreatest ((fun z => ‖matrixPolynomial B z‖) '' numericalClosure A)
      (normSup (numericalClosure A) (matrixPolynomial B))

def HolomorphicConclusion (A : H →L[ℂ] H) : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (U : Set ℂ), IsOpen U → numericalClosure A ⊆ U →
    ∀ (F : ℂ → Coeff m), HolomorphicOn F U →
      (∃ γ, IsCauchyContour (numericalClosure A) U γ) ∧
      (∀ γ, IsCauchyContour (numericalClosure A) U γ →
        ∀ i j, dunfordIntegral A γ (fun z => F z i j) =
          holomorphicCalculus A U (fun z => F z i j)) ∧
      IsGreatest ((fun z => ‖F z‖) '' numericalClosure A)
        (normSup (numericalClosure A) F) ∧
      ‖holomorphicEval A U F‖ ≤ 2 * normSup (numericalClosure A) F

def RationalConclusion (A : H →L[ℂ] H) : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (R : RationalMatrix m),
    numericalClosure A ⊆ poleFreeSet R →
      (∀ i j, IsUnit (Polynomial.aeval A (R i j).denom)) ∧
      rationalEval A R = holomorphicEval A (poleFreeSet R) (rationalFunction R) ∧
      IsGreatest ((fun z => ‖rationalFunction R z‖) '' numericalClosure A)
        (normSup (numericalClosure A) (rationalFunction R)) ∧
      ‖rationalEval A R‖ ≤ 2 * normSup (numericalClosure A) (rationalFunction R)

def NonzeroConclusion (A : H →L[ℂ] H) : Prop :=
  IsCompact (numericalClosure A) ∧ Convex ℝ (numericalClosure A) ∧
  spectrum ℂ A ⊆ numericalClosure A ∧ PolynomialConclusion A ∧
  HolomorphicConclusion A ∧ RationalConclusion A

def ZeroConclusion (A : H →L[ℂ] H) : Prop :=
  numericalRange A = ∅ ∧
  (∀ (m : ℕ) (F : ℂ → Coeff m), normSup (numericalRange A) F = 0) ∧
  ∀ (m : ℕ), 0 < m →
    (∀ T : Amplification H m →L[ℂ] Amplification H m, T = 0) ∧
    (∀ (d : ℕ) (B : Fin (d + 1) → Coeff m), polynomialEval A B = 0 ∧
      ‖polynomialEval A B‖ ≤ 2 * normSup (numericalRange A) (matrixPolynomial B)) ∧
    (∀ (U : Set ℂ) (F : ℂ → Coeff m), holomorphicEval A U F = 0 ∧
      ‖holomorphicEval A U F‖ ≤ 2 * normSup (numericalRange A) F) ∧
    (∀ (R : RationalMatrix m), rationalEval A R = 0 ∧
      ‖rationalEval A R‖ ≤ 2 * normSup (numericalRange A) (rationalFunction R))

def UniformlySharp : Prop :=
  ∀ c : ℝ, c < 2 → ∃ (n m d : ℕ), 0 < n ∧ 0 < m ∧
    ∃ (A : CoeffSpace n →L[ℂ] CoeffSpace n) (B : Fin (d + 1) → Coeff m),
      c * normSup (numericalRange A) (matrixPolynomial B) < ‖polynomialEval A B‖



end HilbertCrouzeix

end

end OAI
