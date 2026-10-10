import OAI.Analysis.KadisonSimilarity.Representation.QuantitativeImplementation
import OAI.Analysis.KadisonSimilarity.Derivation.CyclicDerivations

namespace OAI

/-! # Implementation of completely bounded rectangular derivations -/

noncomputable section
namespace KadisonSimilarity

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [PartialOrder A] [StarOrderedRing A]

/-- A uniform square-matrix bound for an operator-valued map between two spaces. -/
def RectangularCompleteBound (δ : A → (K →L[ℂ] F)) (D : ℝ) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (Fin n) (Fin n) A,
    ‖rectangularMatrixOperator (X.map δ)‖ ≤ D * ‖CStarMatrix.ofMatrix X‖

/-- The diagonal of the triangular representation is a star representation. -/
def rectangularDiagonalStarHom (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : A →⋆ₐ[ℂ] (RectangularSum F K →L[ℂ] RectangularSum F K) :=
  { (rectangularRepresentation ρ σ 0 (by intros; simp)).1 with
    map_star' := by
      intro a
      change rectangularTriangular (ρ (star a)) 0 (σ (star a)) =
        (rectangularTriangular (ρ a) 0 (σ a)).adjoint
      apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
      intro x y
      change inner ℂ (rectangularTriangular (ρ (star a)) 0 (σ (star a)) x).fst y.fst +
          inner ℂ (rectangularTriangular (ρ (star a)) 0 (σ (star a)) x).snd y.snd =
        inner ℂ x.fst (rectangularTriangular (ρ a) 0 (σ a) y).fst +
          inner ℂ x.snd (rectangularTriangular (ρ a) 0 (σ a) y).snd
      rw [rectangularTriangular_fst, rectangularTriangular_snd,
        rectangularTriangular_fst, rectangularTriangular_snd]
      simp only [zero_apply, add_zero, map_star,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] }

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem rectangularDiagonalStarHom_apply
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : A) :
    rectangularDiagonalStarHom ρ σ a = rectangularTriangular (ρ a) 0 (σ a) := rfl

omit [CompleteSpace F] [CompleteSpace K] in
private theorem norm_rectangularInl_le_one : ‖rectangularInl (F := F) (K := K)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖WithLp.toLp 2 (x, 0)‖ ≤ 1 * ‖x‖
  simp [WithLp.norm_toLp_fst]

omit [CompleteSpace F] [CompleteSpace K] in
private theorem norm_rectangularSnd_le_one : ‖WithLp.sndL 2 ℂ F K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using WithLp.norm_snd_le F x

omit [CompleteSpace F] [CompleteSpace K] in
/-- The off-diagonal square matrix is an isometric-coordinate compression. -/
theorem matrixOperator_offDiagonal {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (K →L[ℂ] F)) :
    matrixOperator (fun i j => (rectangularInl (F := F) (K := K)).comp ((X i j).comp (WithLp.sndL 2 ℂ F K))) =
      (mapCopies (rectangularInl (F := F) (K := K)) n).comp
        ((rectangularMatrixOperator X).comp (mapCopies (WithLp.sndL 2 ℂ F K) n)) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  calc
    _ = ∑ j : Fin n, (rectangularInl (F := F) (K := K))
        (X i j ((WithLp.sndL 2 ℂ F K) (ξ j))) :=
      matrixOperator_apply (H := RectangularSum F K) _ ξ i
    _ = (rectangularInl (F := F) (K := K))
        (∑ j : Fin n, X i j ((WithLp.sndL 2 ℂ F K) (ξ j))) := by
      rw [map_sum]
    _ = _ := by
      change _ = (mapCopies (rectangularInl (F := F) (K := K)) n
        (rectangularMatrixOperator X (mapCopies (WithLp.sndL 2 ℂ F K) n ξ))) i
      rw [mapCopies_apply, rectangularMatrixOperator_apply]
      congr 1

private theorem norm_comp_contracts
    {E₁ E₂ E₃ E₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
    [NormedAddCommGroup E₄] [NormedSpace ℂ E₄]
    (L : E₃ →L[ℂ] E₄) (T : E₂ →L[ℂ] E₃) (R : E₁ →L[ℂ] E₂)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) : ‖L.comp (T.comp R)‖ ≤ ‖T‖ := by
  calc
    ‖L.comp (T.comp R)‖ ≤ ‖L‖ * (‖T‖ * ‖R‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := by gcongr
    _ = ‖T‖ := by ring

omit [CompleteSpace F] [CompleteSpace K] in
/-- The norm of the amplified off-diagonal block does not exceed that of the
original rectangular matrix. -/
theorem norm_matrixOperator_offDiagonal_le {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (K →L[ℂ] F)) :
    ‖matrixOperator (fun i j => (rectangularInl (F := F) (K := K)).comp ((X i j).comp (WithLp.sndL 2 ℂ F K)))‖ ≤
      ‖rectangularMatrixOperator X‖ := by
  have hL : ‖mapCopies (rectangularInl (F := F) (K := K)) n‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans norm_rectangularInl_le_one
  have hR : ‖mapCopies (WithLp.sndL 2 ℂ F K) n‖ ≤ 1 :=
    (norm_mapCopies_le _ _).trans norm_rectangularSnd_le_one
  calc
    _ = ‖(mapCopies (rectangularInl (F := F) (K := K)) n).comp
        ((rectangularMatrixOperator X).comp (mapCopies (WithLp.sndL 2 ℂ F K) n))‖ :=
      congrArg norm (matrixOperator_offDiagonal X)
    _ ≤ _ := norm_comp_contracts _ _ _ hL hR

/-- A rectangular complete bound controls the complete norm of its triangular
representation by one plus that bound. -/
theorem completeBound_rectangularRepresentation
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {D : ℝ} (hD : RectangularCompleteBound δ D) :
    CompleteBound (rectangularRepresentation ρ σ δ hδ).1 (1 + D) := by
  intro n X
  let d := rectangularDiagonalStarHom ρ σ
  have hp (a : A) : (rectangularRepresentation ρ σ δ hδ).1 a =
      d a + (rectangularInl (F := F) (K := K)).comp ((δ a).comp (WithLp.sndL 2 ℂ F K)) := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;>
      simp [d, rectangularRepresentation, rectangularTriangular,
        rectangularInl, rectangularInr, rectangularDiagonalStarHom]
  let Y : Matrix (Fin n) (Fin n) (RectangularSum F K →L[ℂ] RectangularSum F K) :=
    fun i j => (rectangularInl (F := F) (K := K)).comp
      ((δ (X i j)).comp (WithLp.sndL 2 ℂ F K))
  have hm : X.map (rectangularRepresentation ρ σ δ hδ).1 = X.map d + Y := by
    apply Matrix.ext
    intro i j
    exact hp (X i j)
  rw [hm]
  change ‖(operatorMatrixRepresentation (H := RectangularSum F K) n) (X.map d + Y)‖ ≤ _
  rw [map_add]
  calc
    _ ≤ ‖matrixOperator (X.map d)‖ +
        ‖matrixOperator (fun i j => (rectangularInl (F := F) (K := K)).comp
          ((δ (X i j)).comp (WithLp.sndL 2 ℂ F K)))‖ := norm_add_le _ _
    _ ≤ 1 * ‖CStarMatrix.ofMatrix X‖ + D * ‖CStarMatrix.ofMatrix X‖ :=
      add_le_add (completeBound_starHom d n X)
        ((norm_matrixOperator_offDiagonal_le (X.map δ)).trans (hD n X))
    _ = (1 + D) * ‖CStarMatrix.ofMatrix X‖ := by ring

omit [CompleteSpace F] [CompleteSpace K] in
/-- Rescaling a rectangular derivation rescales all of its matrix bounds. -/
theorem rectangularCompleteBound_normalized
    (δ : A →L[ℂ] (K →L[ℂ] F)) {D : ℝ} (hD : RectangularCompleteBound δ D) :
    RectangularCompleteBound (normalizedRectangularDerivation δ) (D * ‖δ‖⁻¹) := by
  intro n X
  let : SeminormedAddCommGroup (HilbertCopies K n →L[ℂ] HilbertCopies F n) := inferInstance
  let : NormedSpace ℂ (HilbertCopies K n →L[ℂ] HilbertCopies F n) := inferInstance
  have hm : X.map (normalizedRectangularDerivation δ) =
      ((‖δ‖⁻¹ : ℝ) : ℂ) • X.map δ := by
    apply Matrix.ext
    intro i j
    rfl
  rw [hm, rectangularMatrixOperator_smul, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg δ))]
  calc
    ‖δ‖⁻¹ * ‖rectangularMatrixOperator (X.map δ)‖ ≤
        ‖δ‖⁻¹ * (D * ‖CStarMatrix.ofMatrix X‖) :=
      mul_le_mul_of_nonneg_left (hD n X) (inv_nonneg.mpr (norm_nonneg δ))
    _ = (D * ‖δ‖⁻¹) * ‖CStarMatrix.ofMatrix X‖ := by ring

/-- The manuscript's completely bounded implementation lemma, using only the
explicit Paulsen input. The projection argument actually bounds the implementer
by the first power of the condition number, hence implies the stated square. -/
theorem rectangular_inner_of_completeBound
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {D : ℝ} (hD0 : 0 ≤ D) (hD : RectangularCompleteBound δ D)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ δ hδ)) :
    ∃ V : K →L[ℂ] F, (∀ a, δ a = V.comp (σ a) - (ρ a).comp V) ∧
      ‖V‖ ≤ ‖δ‖ * (1 + D * ‖δ‖⁻¹) ^ 2 := by
  let : SeminormedAddCommGroup (K →L[ℂ] F) := inferInstance
  let : NormedSpace ℂ (K →L[ℂ] F) := inferInstance
  by_cases hz : δ = 0
  · refine ⟨0, ?_, ?_⟩
    · intro a
      simp [hz]
    · simp [hz]
  let δ₀ := normalizedRectangularDerivation δ
  let G : ℝ := 1 + D * ‖δ‖⁻¹
  have hG : 1 ≤ G := by
    dsimp [G]
    exact le_add_of_nonneg_right (mul_nonneg hD0 (inv_nonneg.mpr (norm_nonneg δ)))
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hcb : CompleteBound (normalizedRectangularRepresentation ρ σ δ hδ).1 G :=
    completeBound_rectangularRepresentation ρ σ δ₀
      (normalizedRectangularDerivation_leibniz ρ σ δ hδ)
      (rectangularCompleteBound_normalized δ hD)
  obtain ⟨S, hSnorm, hSstar⟩ := paulsen G hG0 hcb
  obtain ⟨V₀, hV₀, hVnorm⟩ := rectangular_inner_of_similarity_norm ρ σ δ₀
    (normalizedRectangularDerivation_leibniz ρ σ δ hδ) S hSstar
  have hn : ‖δ‖ ≠ 0 := (norm_ne_zero_iff (E := A →L[ℂ] (K →L[ℂ] F))).mpr hz
  have hc : (‖δ‖ : ℂ) * ((‖δ‖⁻¹ : ℝ) : ℂ) = 1 := by
    norm_cast
    exact mul_inv_cancel₀ hn
  have hrec (a : A) : δ a = (‖δ‖ : ℂ) • δ₀ a := by
    simp only [δ₀, normalizedRectangularDerivation, smul_apply, smul_smul, hc, one_smul]
  refine ⟨(‖δ‖ : ℂ) • V₀, ?_, ?_⟩
  · intro a
    rw [hrec a, hV₀ a]
    ext x
    simp only [smul_apply, sub_apply, ContinuousLinearMap.comp_apply, map_smul, smul_sub]
  · calc
      ‖(‖δ‖ : ℂ) • V₀‖ = ‖δ‖ * ‖V₀‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg δ)]
      _ ≤ ‖δ‖ * G := mul_le_mul_of_nonneg_left (hVnorm.trans hSnorm) (norm_nonneg δ)
      _ ≤ ‖δ‖ * G ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg δ)
        nlinarith

/-- The cyclic implementation constant, conditional on Dickson, Paulsen, and
cyclic-column approximation. -/
theorem cyclic_derivation_implementation
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (dickson : DicksonTwoBound (A := A) (RectangularSum F K))
    (hcyclic : ApproximateCyclicColumns σ)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ δ hδ)) :
    ∃ V : K →L[ℂ] F, (∀ a, δ a = V.comp (σ a) - (ρ a).comp V) ∧
      ‖V‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ‖δ‖ := by
  let D : ℝ := 4 * (4 * Real.sqrt 2) * ‖δ‖
  have hD : RectangularCompleteBound δ D :=
    cyclic_derivation_matrix_bound ρ σ δ hδ dickson hcyclic
  obtain ⟨V, hV, hb⟩ := rectangular_inner_of_completeBound ρ σ δ hδ
    (by dsimp [D]; positivity : 0 ≤ D) hD paulsen
  refine ⟨V, hV, ?_⟩
  by_cases hz : ‖δ‖ = 0
  · simpa [hz, D] using hb
  have hcancel : D * ‖δ‖⁻¹ = 4 * (4 * Real.sqrt 2) := by
    dsimp [D]
    rw [mul_assoc, mul_inv_cancel₀ hz, mul_one]
  calc
    ‖V‖ ≤ ‖δ‖ * (1 + D * ‖δ‖⁻¹) ^ 2 := hb
    _ = (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ‖δ‖ := by rw [hcancel]; ring

end KadisonSimilarity

end

end OAI
