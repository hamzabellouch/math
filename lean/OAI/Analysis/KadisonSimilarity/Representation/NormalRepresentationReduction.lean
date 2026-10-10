import OAI.Analysis.KadisonSimilarity.Representation.CountableAmplification
import OAI.Analysis.KadisonSimilarity.Representation.ReducingRepresentationTransfer

namespace OAI

/-! # Normal representations and countable tracial multiplicity

The published input below is local to a fixed finite von Neumann algebra with
faithful normal finite trace and a fixed normal representation on a separable
Hilbert space.  Hiai, *Concise lectures on selected topics of von Neumann
algebras*, arXiv:2004.02383v1 (2020), Corollary 5.14 and Remark 5.15, printed
page 50, represent every normal positive functional by a vector in the tracial
standard form.  Applied on each cyclic reducing summand, the usual countable
cyclic decomposition gives the displayed isometric intertwiner.  This is the
normal-representation consequence used in the manuscript's global section;
it is not asserted here for arbitrary C-star representations or arbitrary
positive functionals.  The countable cyclic decomposition is the standard
representation theory cited there to Takesaki, *Theory of Operator Algebras I*
(1979).

All commutator and matrix estimates below are derived from that geometric
input and the already proved finite-to-countable transfer.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The precise local standard-form embedding consequence of Hiai
Corollary 5.14 / Remark 5.15 and countable cyclic decomposition.  At the
published application `τ` is the faithful normal trace of a finite von
Neumann algebra and `σ` is a normal representation on separable `H`.
The range is reducing because both representations preserve adjoints. -/
def HiaiNormalStandardEmbeddingInput (τ : A →ₚ[ℂ] ℂ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∃ I : H →ₗᵢ[ℂ] CountableCopies τ.GNS,
    ∀ a, I.toContinuousLinearMap.comp (σ a) =
      (countableRepresentation τ.gnsStarAlgHom a).comp I.toContinuousLinearMap

/-- A countable standard-form estimate transfers to the given normal
representation with exactly the same constant. -/
theorem normal_representation_bound_of_countable
    (τ : A →ₚ[ℂ] ℂ) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (embedding : HiaiNormalStandardEmbeddingInput τ σ) {C : ℝ}
    (hcountable : ∀ (Z : CountableCopies τ.GNS →L[ℂ] CountableCopies τ.GNS)
      (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator Z (countableRepresentation τ.gnsStarAlgHom a)‖ ≤ δ * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
        ‖commutator (amplify Z n)
          (representedMatrix (countableRepresentation τ.gnsStarAlgHom) X)‖ ≤
          C * δ * ‖X‖)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤ C * δ * ‖X‖ := by
  obtain ⟨I, hI⟩ := embedding
  exact finite_estimate_of_reducing_representation σ
    (countableRepresentation τ.gnsStarAlgHom) I hI hcountable Y hδ hscalar n X

/-- The finite tracial multiplicity estimates imply the estimate for any
normal representation supplied by the local standard-form input. -/
theorem normal_representation_bound_of_finite
    (τ : A →ₚ[ℂ] ℂ) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (embedding : HiaiNormalStandardEmbeddingInput τ σ) {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (r : ℕ) (T : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
      (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator T (amplify (τ.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
        ‖commutator (amplify T n)
          (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
          C * δ * ‖X‖)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤ C * δ * ‖X‖ := by
  apply normal_representation_bound_of_countable τ σ embedding
    (fun Z δ hδ hscalar n X =>
      gns_countable_amplification_bound τ hC hfinite Z hδ hscalar n X)
    Y hδ hscalar n X

/-- In the faithful concrete representation this is the paper's full
operator-matrix commutator estimate. -/
theorem normal_factor_commutatorEstimate_of_finite
    (P : VonNeumannAlgebra H)
    [IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H))]
    (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ)
    (embedding : HiaiNormalStandardEmbeddingInput τ P.toStarSubalgebra.subtype)
    {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (r : ℕ) (T : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
      (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator T (amplify (τ.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) P.toStarSubalgebra),
        ‖commutator (amplify T n)
          (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
          C * δ * ‖X‖) :
    CommutatorEstimate P C := by
  apply commutatorEstimate_of_subtype_bound P
  intro Y δ hδ hscalar n X
  exact normal_representation_bound_of_finite τ P.toStarSubalgebra.subtype
    embedding hC hfinite Y hδ hscalar n X

end KadisonSimilarity

end

end OAI
