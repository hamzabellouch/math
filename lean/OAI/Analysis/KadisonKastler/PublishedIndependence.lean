import OAI.Analysis.KadisonKastler.PublishedMatrixUltraproduct
import OAI.Analysis.KadisonKastler.FreeHaar

namespace OAI

/-! # Popa's finite-base independence input

Popa, *Independence properties in subalgebras of ultraproduct II1
factors*, J. Funct. Anal. 266 (2014), Theorem 0.1(b), Theorem 4.3 and
its proof, printed pp. 20 and 24 (arXiv:1308.3982v3).

Theorem 4.3 explicitly permits both endpoint letters to be one. Its proof
constructs the diffuse abelian algebra from a Haar unitary. We retain
exactly that unitary and the mixed-moment identity, only for a finite
base algebra. Testing the conditional expectation against base elements
is its faithful-trace characterization. No controlled coordinate lift or
scalar freeness of a conjugated matrix model is assumed here.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {C : Type*} [CStarAlgebra C]

/-- Separability for the tracial two-norm, rather than the operator norm. -/
def TraceSeparable (τ : FaithfulTracialState C) (S : Set C) : Prop :=
  ∃ D : Set C, D.Countable ∧ D ⊆ S ∧
    ∀ x ∈ S, ∀ ε : ℝ, 0 < ε → ∃ y ∈ D, traceTwoNorm τ (x - y) < ε

/-- Orthogonality to the base algebra, equivalently zero conditional
expectation onto it. -/
def TraceOrthogonal (τ : FaithfulTracialState C) (D : StarSubalgebra ℂ C) (x : C) : Prop :=
  ∀ b ∈ D, τ.toLinearMap (b * x) = 0

/-- Popa's precise mixed word, with the initial and final letters optional.
The `r + 1` nonzero Haar powers are interleaved with the `r` letters in `l`. -/
def HaarEndpointIndependence (τ : FaithfulTracialState C)
    (D : StarSubalgebra ℂ C) (X : Submodule ℂ C) (w : unitary C) : Prop :=
  ∀ a b : C, (a ∈ X ∨ a = 1) → (b ∈ X ∨ b = 1) →
    ∀ k : ℤ, k ≠ 0 → ∀ l : List (C × ℤ),
    (∀ z ∈ l, z.1 ∈ X ∧ z.2 ≠ 0) →
    TraceOrthogonal τ D
      (a * haarPower w k * (l.map (fun z => z.1 * haarPower w z.2)).prod * b)

/-- The finite-base specialization of the published independence theorem.
Its domain remains a tracial ultraproduct in the input declarations below. -/
def FiniteBaseIndependence (τ : FaithfulTracialState C) : Prop :=
  ∀ (D : StarSubalgebra ℂ C), FiniteDimensional ℂ D →
    ∀ (X : Submodule ℂ C), TraceSeparable τ (X : Set C) →
    (∀ x ∈ X, TraceOrthogonal τ D x) →
    ∃ w : unitary C,
      (∀ b ∈ D, Commute (w : C) b) ∧
      (∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower w k) = 0) ∧
      HaarEndpointIndependence τ D X w

/-- The published independence input for the two ultraproducts actually
used in the controlled-lift construction: constant II1 factors and the
increasing finite-matrix model. -/
def PublishedPopaFiniteBaseIndependence : Prop :=
  (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (_hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τ : FaithfulTracialState (Algebra M)) (ω : Ultrafilter ℕ),
    (ω : Filter ℕ) ≤ Filter.atTop → ∀ Q : TracialUltrapower τ ω,
      FiniteBaseIndependence Q.trace) ∧
  (∀ (n : ℕ) [NeZero n] (ω : Ultrafilter ℕ),
    (ω : Filter ℕ) ≤ Filter.atTop → ∀ Q : FiniteMatrixUltraproduct n ω,
      FiniteBaseIndependence (concreteFactorTrace Q.factor))

end

end KadisonKastler

end OAI
