import OAI.Analysis.KadisonSimilarity.Representation.SquareArrayPadding
import OAI.Analysis.KadisonSimilarity.Representation.FiniteAmplificationReduction

namespace OAI

/-! Exact transfer from a reducing representation to a larger one. Extension
by zero preserves scalar and matrix commutator norms, so a standard-form
embedding costs no constant in the finite-factor estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
  (I : H →ₗᵢ[ℂ] K)
  (hI : ∀ a, I.toContinuousLinearMap.comp (σ a) =
    (ρ a).comp I.toContinuousLinearMap)

include hI in
/-- A star intertwiner also intertwines in the reverse direction through
its Hilbert adjoint. -/
theorem adjoint_intertwines_representations (a : A) :
    I.toContinuousLinearMap.adjoint.comp (ρ a) =
      (σ a).comp I.toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (hI (star a))
  simpa only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h.symm

/-- Extension by zero of the operator under study. -/
def reducingExtension (Y : H →L[ℂ] H) : K →L[ℂ] K :=
  I.toContinuousLinearMap.comp (Y.comp I.toContinuousLinearMap.adjoint)

include hI in
/-- The scalar commutator has exactly its original norm. -/
theorem norm_reducingExtension_commutator (Y : H →L[ℂ] H) (a : A) :
    ‖commutator (reducingExtension I Y) (ρ a)‖ = ‖commutator Y (σ a)‖ := by
  rw [reducingExtension, commutator_split_extension _ _ _ _ _ (hI a)
    (adjoint_intertwines_representations σ ρ I hI a)]
  exact norm_split_extension _ _ I.norm_toContinuousLinearMap_le
    (by simpa only [ContinuousLinearMap.adjoint.norm_map] using I.norm_toContinuousLinearMap_le)
    I.adjoint_comp_self _

include hI in
/-- The same exact identity holds at every finite matrix level. -/
theorem norm_reducingExtension_matrix_commutator
    (Y : H →L[ℂ] H) (n : ℕ) (X : Matrix (Fin n) (Fin n) A) :
    ‖commutator (amplify (reducingExtension I Y) n)
      (matrixOperator (X.map ρ))‖ =
    ‖commutator (amplify Y n) (matrixOperator (X.map σ))‖ := by
  let J := mapCopies I.toContinuousLinearMap n
  let R := mapCopies I.toContinuousLinearMap.adjoint n
  have hJ : ‖J‖ ≤ 1 := (norm_mapCopies_le _ _).trans I.norm_toContinuousLinearMap_le
  have hR : ‖R‖ ≤ 1 := (norm_mapCopies_le _ _).trans (by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using I.norm_toContinuousLinearMap_le)
  have hRJ : R.comp J = ContinuousLinearMap.id ℂ (HilbertCopies H n) := by
    dsimp [R, J]
    rw [← mapCopies_comp_eq, I.adjoint_comp_self]
    exact mapCopies_id_eq n
  have hJA : J.comp (matrixOperator (X.map σ)) =
      (matrixOperator (X.map ρ)).comp J :=
    mapCopies_intertwines_matrix _ _ _ (fun i j => hI (X i j))
  have hRB : R.comp (matrixOperator (X.map ρ)) =
      (matrixOperator (X.map σ)).comp R :=
    mapCopies_intertwines_matrix _ _ _
      (fun i j => adjoint_intertwines_representations σ ρ I hI (X i j))
  have hext : amplify (reducingExtension I Y) n = J.comp ((amplify Y n).comp R) := by
    ext ξ i
    rfl
  rw [hext, commutator_split_extension _ _ _ _ _ hJA hRB,
    norm_split_extension J R hJ hR hRJ]

variable [PartialOrder A] [StarOrderedRing A]

/-- A faithful star representation preserves the norm of every actual
C-star matrix, including the zero-size case. -/
theorem norm_representedMatrix_of_injective
    (hσ : Function.Injective σ) (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖representedMatrix σ X‖ = ‖X‖ := by
  apply NonUnitalStarAlgHom.norm_map (representedMatrixHom σ n) _ X
  intro S T h
  have hentry : (CStarMatrix.ofMatrix.symm S).map σ =
      (CStarMatrix.ofMatrix.symm T).map σ :=
    operatorMatrixRepresentation_injective n h
  apply CStarMatrix.ofMatrix.symm.injective
  ext i j
  exact hσ (congrFun (congrFun hentry i) j)

include hI in
/-- Any complete commutator bound for the larger representation restricts
to its reducing subrepresentation without loss. The scalar premise uses
the actual C-star norm of the represented algebra's source. -/
theorem finite_estimate_of_reducing_representation {C : ℝ}
    (estimate : ∀ (Z : K →L[ℂ] K) (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator Z (ρ a)‖ ≤ δ * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
        ‖commutator (amplify Z n) (representedMatrix ρ X)‖ ≤ C * δ * ‖X‖)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (σ a)‖ ≤ δ * ‖a‖)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤ C * δ * ‖X‖ := by
  have hlarge : ∀ a, ‖commutator (reducingExtension I Y) (ρ a)‖ ≤ δ * ‖a‖ := by
    intro a
    rw [norm_reducingExtension_commutator σ ρ I hI]
    exact hscalar a
  have h := estimate (reducingExtension I Y) δ hδ hlarge n X
  change ‖commutator (amplify (reducingExtension I Y) n)
    (matrixOperator ((CStarMatrix.ofMatrix.symm X).map ρ))‖ ≤ _ at h
  rw [norm_reducingExtension_matrix_commutator σ ρ I hI] at h
  exact h

/-- For the faithful concrete subtype representation, the C-star matrix
estimate is exactly the paper's operator-matrix `CommutatorEstimate`. -/
theorem commutatorEstimate_of_subtype_bound (P : VonNeumannAlgebra H)
    [IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H))] {C : ℝ}
    (estimate : ∀ (Y : H →L[ℂ] H) (δ : ℝ), 0 ≤ δ →
      (∀ a : P.toStarSubalgebra,
        ‖commutator Y (a : H →L[ℂ] H)‖ ≤ δ * ‖a‖) →
      ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) P.toStarSubalgebra),
        ‖commutator (amplify Y n) (representedMatrix P.toStarSubalgebra.subtype X)‖ ≤
          C * δ * ‖X‖) : CommutatorEstimate P C := by
  intro Y n X hX
  let Z : CStarMatrix (Fin n) (Fin n) P.toStarSubalgebra :=
    CStarMatrix.ofMatrix (fun i j => ⟨X i j, hX i j⟩)
  have hnorm := norm_representedMatrix_of_injective P.toStarSubalgebra.subtype
    Subtype.val_injective n Z
  have h := estimate Y (scalarCommutatorNorm P Y) (scalarCommutatorNorm_nonneg P Y)
    (fun a => norm_commutator_le_scalarCommutatorNorm P Y a a.property) n Z
  rw [← hnorm] at h
  exact h

end KadisonSimilarity

end

end OAI
