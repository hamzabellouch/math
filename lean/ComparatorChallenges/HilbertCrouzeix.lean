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

section CompressionDefinitions
omit [CompleteSpace H]

def compression (A : H →L[ℂ] H) (E : Submodule ℂ H) [E.HasOrthogonalProjection] :
    E →L[ℂ] E := E.orthogonalProjectionOnto.comp (A.comp E.subtypeL)
def completedIsometry {V : Type*} {W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℂ V] [NormedSpace ℂ W]
    (f : V →ₗᵢ[ℂ] W) : UniformSpace.Completion V →ₗᵢ[ℂ] UniformSpace.Completion W :=
  { f.toContinuousLinearMap.completion.toLinearMap with
    norm_map' := f.isometry.completion_map.norm_map_of_map_zero
      (f.toContinuousLinearMap.completion.map_zero) }

def tensorInclusion (E : Submodule ℂ H) (m : ℕ) :
    Amplification E m →ₗᵢ[ℂ] Amplification H m :=
  completedIsometry (TensorProduct.mapIsometry E.subtypeₗᵢ (.id : CoeffSpace m →ₗᵢ[ℂ] CoeffSpace m))

end CompressionDefinitions

theorem numericalClosure_geometry (A : H →L[ℂ] H) :
    IsCompact (numericalClosure A) ∧ Convex ℝ (numericalClosure A) ∧
      spectrum ℂ A ⊆ numericalClosure A := by
  sorry

omit [CompleteSpace H] in
theorem exists_finite_compression {m d : ℕ} (A : H →L[ℂ] H)
    (B : Fin (d + 1) → Coeff m) (ξ : H ⊗[ℂ] CoeffSpace m) :
    ∃ (E : Submodule ℂ H) (hE : FiniteDimensional ℂ E),
      letI : FiniteDimensional ℂ E := hE
      ∃ η : Amplification E m,
        tensorInclusion E m η = (↑ξ : Amplification H m) ∧
        tensorInclusion E m (polynomialEval (compression A E) B η) =
          polynomialEval A B (↑ξ) := by
  sorry

theorem rational_denominator_isUnit [Nontrivial H] (A : H →L[ℂ] H)
    {m : ℕ} (R : RationalMatrix m) (hR : numericalClosure A ⊆ poleFreeSet R)
    (i j : Fin m) : IsUnit (Polynomial.aeval A (R i j).denom) := by
  sorry

theorem zeroConclusion [Subsingleton H] (A : H →L[ℂ] H) : ZeroConclusion A := by
  sorry

end HilbertCrouzeix

end

end OAI
