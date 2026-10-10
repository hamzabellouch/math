import OAI.Analysis.KadisonSimilarity.Representation.RepresentedFiniteSymmetrization
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixGNSRecovery

namespace OAI

/-! # Finite standard multiplicities from the centered free-corner test

This is a reduction theorem. Its centered-symmetry premise is an explicit
local conclusion to be supplied by the free-corner argument, and is not a
published-input predicate. Haar averaging, multiplicity padding, matrix
GNS transport, symmetry dilation, and restoring the original operator are
all performed by proved lemmas.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

/-- The centered-symmetry bound `c * (3δ)` for operators commuting with the
finite matrix tower gives the complete finite-standard bound
`(3c+2) * δ`. The only unproved premise in this reduction is the displayed
centered test itself; the initial perturbation is constructed by Haar
averaging rather than assumed. -/
theorem finite_standard_estimate_of_centered_tests
    (τ : A →ₚ[ℂ] ℂ)
    (F : ∀ j, Matrix (I j) (I j) ℂ →⋆ₐ[ℂ] A)
    (transition : ∀ j k, j ≤ k →
      Matrix (I j) (I j) ℂ →⋆ₐ[ℂ] Matrix (I k) (I k) ℂ)
    (hcompat : ∀ j k h a, F k (transition j k h a) = F j a)
    {c : ℝ} (hc : 0 ≤ c)
    (hcentered : ∀ (m : ℕ) [NeZero m]
      (Y₀ : HilbertCopies τ.GNS (4 * m) →L[ℂ] HilbertCopies τ.GNS (4 * m))
      (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator Y₀ (amplify (τ.gnsStarAlgHom a) (4 * m))‖ ≤
        (3 * δ) * ‖a‖) →
      (∀ j a, commutator Y₀ (amplify (τ.gnsStarAlgHom (F j a)) (4 * m)) = 0) →
      ∀ S : CStarMatrix (Fin (4 * m)) (Fin (4 * m)) A,
        star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * m) S = 0 →
        ‖commutator (matrixGNSLiftOperator τ Y₀)
          ((normalizedMatrixTrace τ (4 * m)).gnsStarAlgHom S)‖ ≤ c * (3 * δ))
    {r : ℕ} (Y : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (amplify (τ.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖)
    (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) A) :
    ‖commutator (amplify Y h)
      (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
      (3 * c + 2) * δ * ‖X‖ := by
  have hreplace : ∀ (m : ℕ) [NeZero m], ∀ e : Fin r ↪ Fin (4 * m),
      ∃ Y₀ : HilbertCopies τ.GNS (4 * m) →L[ℂ] HilbertCopies τ.GNS (4 * m),
        ‖Y₀ - padArrayOperator e Y‖ ≤ δ ∧
        ∀ S : CStarMatrix (Fin (4 * m)) (Fin (4 * m)) A,
          star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * m) S = 0 →
          ‖commutator (matrixGNSLiftOperator τ Y₀)
            ((normalizedMatrixTrace τ (4 * m)).gnsStarAlgHom S)‖ ≤ c * (3 * δ) := by
    intro m _ e
    have hpad : ∀ a, ‖commutator (padArrayOperator e Y)
        (amplifiedScalarRepresentation τ.gnsStarAlgHom (4 * m) a)‖ ≤ δ * ‖a‖ :=
      (scalar_bound_padArrayOperator_iff τ.gnsStarAlgHom e Y δ).mpr hscalar
    obtain ⟨Y₀, _, hclose, hnew, hstage⟩ :=
      exists_represented_finite_matrix_symmetrization
        (amplifiedScalarRepresentation τ.gnsStarAlgHom (4 * m))
        F transition hcompat (padArrayOperator e Y) hδ hpad
    exact ⟨Y₀, hclose, hcentered m Y₀ δ hδ hnew hstage⟩
  calc
    ‖commutator (amplify Y h)
        (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
        (c * (3 * δ) + 2 * δ) * ‖X‖ :=
      finite_standard_bound_of_matrixGNS_replacements τ Y
        (η := δ) (B := c * (3 * δ)) (by positivity) hreplace h X
    _ = (3 * c + 2) * δ * ‖X‖ := by ring

end KadisonSimilarity

end

end OAI
