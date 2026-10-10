import OAI.Analysis.KadisonSimilarity.Similarity.CompletelyBoundedImplementation
import OAI.Analysis.KadisonSimilarity.Tracial.FullColumns

namespace OAI

/-! The finite-column passage from the uniform commutator estimate to complete
boundedness of a derivation. The finite implementers need no uniform norm bound;
only their scalar commutator bounds are used. -/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology

variable {A H I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The scalar specialization of matrix Kaplansky density and the C*-quotient
norm used in the final derivation argument (Blackadar, I.9.1.3). -/
def ScalarKaplanskyClosure (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (P : VonNeumannAlgebra H) : Prop :=
  ∀ (V : H →L[ℂ] H) (d : ℝ), 0 ≤ d →
    (∀ a, ‖commutator V (σ a)‖ ≤ d * ‖a‖) → scalarCommutatorNorm P V ≤ d

/-- Data obtained by implementing a derivation on finitely many cyclic
summands, with strong convergence of the corresponding projections. -/
structure FiniteColumnImplementers (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (δ : A →L[ℂ] (H →L[ℂ] H)) (l : Filter I) where
  projection : I → H →L[ℂ] H
  implementer : I → H →L[ℂ] H
  projection_norm : ∀ i, ‖projection i‖ ≤ 1
  projection_tendsto : ∀ x, Tendsto (fun i => projection i x) l (𝓝 x)
  commutator_eq : ∀ i a, commutator (implementer i) (σ a) = (δ a).comp (projection i)

omit [CompleteSpace H] in
/-- Strong convergence is preserved by a fixed finite Hilbert amplification. -/
theorem amplify_tendsto_apply {l : Filter I} (Q : I → H →L[ℂ] H)
    (hQ : ∀ x, Tendsto (fun i => Q i x) l (𝓝 x)) (n : ℕ) (ξ : HilbertCopies H n) :
    Tendsto (fun i => amplify (Q i) n ξ) l (𝓝 ξ) := by
  have hp : Tendsto (fun i => fun j : Fin n => Q i (ξ j)) l (𝓝 (fun j => ξ j)) :=
    tendsto_pi_nhds.mpr fun j => hQ (ξ j)
  have h := ((PiLp.homeomorph 2 (fun _ : Fin n => H)).symm.continuous.tendsto
    (fun j : Fin n => ξ j)).comp hp
  convert h using 1
  · funext i
    apply PiLp.ext
    intro j
    rfl
  · congr 1

omit [PartialOrder A] [StarOrderedRing A] in
/-- The finite-column commutator identity at every matrix level. -/
theorem matrix_finite_column_identity (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (δ : A →L[ℂ] (H →L[ℂ] H)) (V Q : H →L[ℂ] H)
    (hV : ∀ a, commutator V (σ a) = (δ a).comp Q)
    (n : ℕ) (X : Matrix (Fin n) (Fin n) A) :
    commutator (amplify V n) (matrixOperator (X.map σ)) =
      (matrixOperator (X.map δ)).comp (amplify Q n) := by
  rw [commutator_amplify_matrixOperator]
  ext ξ i
  simp [matrixOperator, amplify, hV]

/-- A uniform matrix commutator estimate controls an arbitrary derivation
once cyclic implementation has supplied its finite columns. -/
theorem derivation_completeBound_of_finite_columns {l : Filter I} [l.NeBot]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (δ : A →L[ℂ] (H →L[ℂ] H))
    (P : VonNeumannAlgebra H) (hσ : ∀ a, σ a ∈ P)
    (kaplansky : ScalarKaplanskyClosure σ P)
    (columns : FiniteColumnImplementers σ δ l)
    {C : ℝ} (hC : 0 ≤ C) (estimate : CommutatorEstimate P C) :
    CompleteBound δ (C * ‖δ‖) := by
  have hscalar (i : I) : scalarCommutatorNorm P (columns.implementer i) ≤ ‖δ‖ := by
    apply kaplansky _ _ (norm_nonneg _)
    intro a
    rw [columns.commutator_eq]
    calc
      _ ≤ ‖δ a‖ * ‖columns.projection i‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖δ‖ * ‖a‖) * 1 := mul_le_mul (δ.le_opNorm a) (columns.projection_norm i)
        (norm_nonneg _) (by positivity)
      _ = ‖δ‖ * ‖a‖ := mul_one _
  intro n X
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  have hlim := ((matrixOperator (X.map δ)).continuous.tendsto ξ).comp
    (amplify_tendsto_apply columns.projection columns.projection_tendsto n ξ)
  apply le_of_tendsto hlim.norm
  apply Eventually.of_forall
  intro i
  have hmatrix := estimate (columns.implementer i) n (X.map σ) (fun j k => hσ (X j k))
  rw [matrix_finite_column_identity σ δ _ _ (columns.commutator_eq i)] at hmatrix
  have hnorm : ‖matrixOperator (X.map σ)‖ ≤ ‖CStarMatrix.ofMatrix X‖ := by
    simpa only [one_mul] using completeBound_starHom σ n X
  calc
    _ ≤ ‖(matrixOperator (X.map δ)).comp (amplify (columns.projection i) n)‖ * ‖ξ‖ :=
      ((matrixOperator (X.map δ)).comp (amplify (columns.projection i) n)).le_opNorm ξ
    _ ≤ (C * ‖δ‖ * ‖CStarMatrix.ofMatrix X‖) * ‖ξ‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg ξ)
      exact hmatrix.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (hscalar i) hC) hnorm (norm_nonneg _) (by positivity))
    _ = (C * ‖δ‖) * ‖CStarMatrix.ofMatrix X‖ * ‖ξ‖ := rfl

end KadisonSimilarity

end

end OAI
