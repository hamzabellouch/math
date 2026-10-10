import OAI.Analysis.KadisonSimilarity.Derivation.RectangularDerivations

namespace OAI

/-!
# The cyclic-domain completely bounded estimate

Approximate cyclic column factorization and the column Leibniz identity
bound every finite matrix amplification of a derivation.
-/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology CStarAlgebra

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [PartialOrder A] [StarOrderedRing A]

/-- Application of an operator-valued column to a single vector. -/
def columnAction {n : ℕ} (f : A → (K →L[ℂ] F))
    (W : Matrix (Fin n) (Fin 1) A) (ζ : K) : HilbertCopies F n :=
  rectangularMatrixOperator (W.map f) (PiLp.single 2 0 ζ)

omit [CStarAlgebra A] [CompleteSpace F] [CompleteSpace K] [PartialOrder A]
  [StarOrderedRing A] in
@[simp] theorem columnAction_apply {n : ℕ} (f : A → (K →L[ℂ] F))
    (W : Matrix (Fin n) (Fin 1) A) (ζ : K) (i : Fin n) :
    columnAction f W ζ i = f (W i 0) ζ := by
  simp [columnAction]

omit [CompleteSpace F] [CompleteSpace K] in
/-- A column bound controls its value on a unit vector. -/
theorem norm_columnAction_le {n : ℕ} {f : A → (K →L[ℂ] F)} {c : ℝ}
    (hc : ColumnBound f c) (W : Matrix (Fin n) (Fin 1) A) (ζ : K)
    (hζ : ‖ζ‖ = 1) : ‖columnAction f W ζ‖ ≤ c * ‖CStarMatrix.ofMatrix W‖ := by
  calc
    ‖columnAction f W ζ‖ ≤
        ‖rectangularMatrixOperator (W.map f)‖ * ‖(PiLp.single 2 (0 : Fin 1) ζ : HilbertCopies K 1)‖ :=
      (rectangularMatrixOperator (W.map f)).le_opNorm _
    _ = ‖rectangularMatrixOperator (W.map f)‖ := by
      rw [PiLp.norm_single, hζ, mul_one]
    _ ≤ c * ‖CStarMatrix.ofMatrix W‖ := hc n W

omit [PartialOrder A] [StarOrderedRing A] in
/-- The exact matrix-column Leibniz identity. -/
theorem rectangularDerivation_mul_column
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {n : ℕ} (X : Matrix (Fin n) (Fin n) A)
    (W : Matrix (Fin n) (Fin 1) A) (ζ : K) :
    columnAction δ (X * W) ζ =
      matrixOperator (X.map ρ) (columnAction δ W ζ) +
        rectangularMatrixOperator (X.map δ) (columnAction σ W ζ) := by
  apply PiLp.ext
  intro i
  simp only [PiLp.add_apply, columnAction_apply, Matrix.mul_apply,
    map_sum, sum_apply, hδ, add_apply,
    ContinuousLinearMap.comp_apply, Finset.sum_add_distrib,
    matrixOperator_apply, rectangularMatrixOperator_apply, Matrix.map_apply]

/-- Rectangular C-star matrix multiplication is submultiplicative in the
square-times-column case used below. -/
theorem norm_cstarMatrix_mul_column_le {n : ℕ}
    (X : Matrix (Fin n) (Fin n) A) (W : Matrix (Fin n) (Fin 1) A) :
    ‖CStarMatrix.ofMatrix (X * W)‖ ≤
      ‖CStarMatrix.ofMatrix X‖ * ‖CStarMatrix.ofMatrix W‖ := by
  have hcomp : CStarMatrix.toCLM (CStarMatrix.ofMatrix (X * W)) =
      (CStarMatrix.toCLM (CStarMatrix.ofMatrix W)).comp
        (CStarMatrix.toCLM (CStarMatrix.ofMatrix X)) := by
    apply ContinuousLinearMap.ext
    intro v
    apply (WithCStarModule.equiv A (Fin 1 → A)).injective
    change Matrix.vecMul v (X * W) = Matrix.vecMul (Matrix.vecMul v X) W
    exact (Matrix.vecMul_vecMul v X W).symm
  rw [CStarMatrix.norm_def, hcomp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

/-- Every unit vector in a finite Hilbert sum is a limit of bounded cyclic
columns applied to one unit vector. -/
def ApproximateCyclicColumns (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ n : ℕ, ∀ ξ : HilbertCopies K n, ‖ξ‖ = 1 →
    ∃ ζ : K, ‖ζ‖ = 1 ∧ ∃ W : ℕ → Matrix (Fin n) (Fin 1) A,
      (∀ j, ‖CStarMatrix.ofMatrix (W j)‖ ≤ 2) ∧
      Tendsto (fun j => columnAction σ (W j) ζ) atTop (𝓝 ξ)

/-- The column Leibniz identity gives a bound before taking an approximation
limit; only the column bound and the column norm enter. -/
theorem norm_derivation_on_column_le
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {c : ℝ} (hc : 0 ≤ c) (hcol : ColumnBound δ c)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) A)
    (W : Matrix (Fin n) (Fin 1) A) (hW : ‖CStarMatrix.ofMatrix W‖ ≤ 2)
    (ζ : K) (hζ : ‖ζ‖ = 1) :
    ‖rectangularMatrixOperator (X.map δ) (columnAction σ W ζ)‖ ≤
      (4 * c) * ‖CStarMatrix.ofMatrix X‖ := by
  have heq := rectangularDerivation_mul_column ρ σ δ hδ X W ζ
  have hsolve : rectangularMatrixOperator (X.map δ) (columnAction σ W ζ) =
      columnAction δ (X * W) ζ - matrixOperator (X.map ρ) (columnAction δ W ζ) := by
    exact eq_sub_of_add_eq' heq.symm
  have hρ : ‖matrixOperator (X.map ρ)‖ ≤ ‖CStarMatrix.ofMatrix X‖ := by
    simpa only [one_mul] using completeBound_starHom ρ n X
  calc
    ‖rectangularMatrixOperator (X.map δ) (columnAction σ W ζ)‖ =
        ‖columnAction δ (X * W) ζ -
          matrixOperator (X.map ρ) (columnAction δ W ζ)‖ := congrArg norm hsolve
    _ ≤ ‖columnAction δ (X * W) ζ‖ +
        ‖matrixOperator (X.map ρ) (columnAction δ W ζ)‖ := norm_sub_le _ _
    _ ≤ c * ‖CStarMatrix.ofMatrix (X * W)‖ +
        ‖matrixOperator (X.map ρ)‖ * ‖columnAction δ W ζ‖ :=
      add_le_add (norm_columnAction_le hcol _ ζ hζ) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ c * (‖CStarMatrix.ofMatrix X‖ * ‖CStarMatrix.ofMatrix W‖) +
        ‖CStarMatrix.ofMatrix X‖ * (c * ‖CStarMatrix.ofMatrix W‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (norm_cstarMatrix_mul_column_le X W) hc
      · exact mul_le_mul hρ (norm_columnAction_le hcol W ζ hζ)
          (norm_nonneg _) (norm_nonneg _)
    _ = (2 * c * ‖CStarMatrix.ofMatrix X‖) * ‖CStarMatrix.ofMatrix W‖ := by ring
    _ ≤ (2 * c * ‖CStarMatrix.ofMatrix X‖) * 2 :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    _ = (4 * c) * ‖CStarMatrix.ofMatrix X‖ := by ring

/-- Approximate cyclic column factorization upgrades the column estimate to
all square matrix amplifications. -/
theorem rectangularDerivation_bound_of_approximateCyclicColumns
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {c : ℝ} (hc : 0 ≤ c) (hcol : ColumnBound δ c)
    (hcyclic : ApproximateCyclicColumns σ)
    (n : ℕ) (X : Matrix (Fin n) (Fin n) A) :
    ‖rectangularMatrixOperator (X.map δ)‖ ≤ (4 * c) * ‖CStarMatrix.ofMatrix X‖ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro ξ hξ
  obtain ⟨ζ, hζ, W, hW, ht⟩ := hcyclic n ξ hξ
  have ht' := ((rectangularMatrixOperator (X.map δ)).continuous.tendsto ξ).comp ht
  exact le_of_tendsto ht'.norm (Filter.Eventually.of_forall fun j =>
    norm_derivation_on_column_le ρ σ δ hδ hc hcol X (W j) (hW j) ζ hζ)

/-- The row/column estimate and approximate cyclic column factorization give
a uniform matrix bound for a derivation. -/
theorem cyclic_derivation_matrix_bound
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (dickson : DicksonTwoBound (A := A) (RectangularSum F K))
    (hcyclic : ApproximateCyclicColumns σ)
    (n : ℕ) (X : Matrix (Fin n) (Fin n) A) :
    ‖rectangularMatrixOperator (X.map δ)‖ ≤
      (4 * (4 * Real.sqrt 2) * ‖δ‖) * ‖CStarMatrix.ofMatrix X‖ := by
  have hcol := (rectangularDerivation_row_column ρ σ δ hδ dickson).2
  have h := rectangularDerivation_bound_of_approximateCyclicColumns ρ σ δ hδ
    (by positivity : 0 ≤ (4 * Real.sqrt 2) * ‖δ‖) hcol hcyclic n X
  convert h using 1
  ring

/-- A derivation between representations on the same Hilbert space is
completely bounded under approximate cyclic column factorization. -/
theorem cyclic_derivation_completeBound
    (ρ σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] K))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (dickson : DicksonTwoBound (A := A) (RectangularSum K K))
    (hcyclic : ApproximateCyclicColumns σ) :
    CompleteBound δ (4 * (4 * Real.sqrt 2) * ‖δ‖) := by
  intro n X
  exact cyclic_derivation_matrix_bound ρ σ δ hδ dickson hcyclic n X

end KadisonSimilarity

end

end OAI
