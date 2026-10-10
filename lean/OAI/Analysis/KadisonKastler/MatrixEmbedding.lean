import OAI.Analysis.KadisonKastler.MatrixVonNeumann
import OAI.Analysis.KadisonKastler.ScalarMatrixTrace

namespace OAI

/-! # Trace-preserving finite-matrix embeddings from matrix units -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A ι : Type*} [CStarAlgebra A] [Fintype ι] [DecidableEq ι]

local instance matrixEmbeddingScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance matrixEmbeddingScalarStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

/-- The existing algebraic matrix-unit representation with the C⋆-matrix domain. -/
def matrixUnitsEmbedding (E : Generator.MatrixUnitSystem ι A) : CStarMatrix ι ι ℂ →⋆ₐ[ℂ] A :=
  E.hom.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom

theorem matrixUnitsEmbedding_apply (E : Generator.MatrixUnitSystem ι A)
    (x : CStarMatrix ι ι ℂ) :
    matrixUnitsEmbedding E x = ∑ i, ∑ j, x i j • E.entry i j := rfl

theorem matrixUnitsEmbedding_single (E : Generator.MatrixUnitSystem ι A)
    (i j : ι) (z : ℂ) :
    matrixUnitsEmbedding E (CStarMatrix.ofMatrix (Matrix.single i j z)) = z • E.entry i j :=
  E.hom_single i j z

variable [Nonempty ι]

theorem matrixUnitsEmbedding_injective [Nontrivial A] (E : Generator.MatrixUnitSystem ι A) :
    Function.Injective (matrixUnitsEmbedding E) := by
  intro x y h
  exact CStarMatrix.ofMatrix.symm.injective (E.injective h)

theorem norm_matrixUnitsEmbedding [Nontrivial A] (E : Generator.MatrixUnitSystem ι A)
    (x : CStarMatrix ι ι ℂ) : ‖matrixUnitsEmbedding E x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map _ (matrixUnitsEmbedding_injective E) x

omit [Nonempty ι] in
theorem matrixUnits_trace_diagonal (E : Generator.MatrixUnitSystem ι A)
    (τ : FaithfulTracialState A) (i : ι) :
    τ.toLinearMap (E.entry i i) = (Fintype.card ι : ℂ)⁻¹ := by
  have he (j : ι) : τ.toLinearMap (E.entry j j) = τ.toLinearMap (E.entry i i) := by
    simpa [E.mul_entry] using τ.tracial (E.entry j i) (E.entry i j)
  have h : (Fintype.card ι : ℂ) * τ.toLinearMap (E.entry i i) = 1 := by
    calc
      _ = ∑ j, τ.toLinearMap (E.entry j j) := by simp only [he, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      _ = τ.toLinearMap (∑ j, E.entry j j) := (map_sum _ _ _).symm
      _ = 1 := by rw [E.total, τ.map_one]
  exact eq_inv_of_mul_eq_one_right h

omit [Nonempty ι] in
theorem matrixUnits_trace_offDiagonal (E : Generator.MatrixUnitSystem ι A)
    (τ : FaithfulTracialState A) {i j : ι} (hij : i ≠ j) :
    τ.toLinearMap (E.entry i j) = 0 := by
  have h := τ.tracial (E.entry i i) (E.entry i j)
  simpa [E.mul_entry, hij, Ne.symm hij] using h

theorem matrixUnitsEmbedding_trace (E : Generator.MatrixUnitSystem ι A)
    (τ : FaithfulTracialState A) (x : CStarMatrix ι ι ℂ) :
    τ.toLinearMap (matrixUnitsEmbedding E x) = (matrixTrace scalarTrace).toLinearMap x := by
  have he (i j : ι) : τ.toLinearMap (E.entry i j) =
      if i = j then (Fintype.card ι : ℂ)⁻¹ else 0 := by
    split_ifs with h
    · subst j
      exact matrixUnits_trace_diagonal E τ i
    · exact matrixUnits_trace_offDiagonal E τ h
  simp only [matrixUnitsEmbedding_apply, map_sum, map_smul, he,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [matrixTrace_apply, scalarTrace, LinearMap.id_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

variable {B : Type*} [CStarAlgebra B]

local instance matrixEmbeddingOrder : PartialOrder A := CStarAlgebra.spectralOrder _
local instance matrixEmbeddingStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance matrixEmbeddingTargetOrder : PartialOrder B := CStarAlgebra.spectralOrder _
local instance matrixEmbeddingTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _

theorem matrixTrace_coefficientMatrixMap (τ : FaithfulTracialState A)
    (σ : FaithfulTracialState B) (φ : A →⋆ₐ[ℂ] B)
    (hφ : ∀ a, σ.toLinearMap (φ a) = τ.toLinearMap a) (x : CStarMatrix ι ι A) :
    (matrixTrace σ).toLinearMap (coefficientMatrixMap φ x) = (matrixTrace τ).toLinearMap x := by
  simp only [matrixTrace_apply, coefficientMatrixMap_apply, hφ]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n j : ℕ} [NeZero n]

local instance matrixEmbeddingConcreteOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance matrixEmbeddingConcreteStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The concrete finite model embeds by the chosen inner matrix units,
with the outer matrix coordinates represented on the Hilbert direct sum. -/
def finiteMatrixEmbedding (E : Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M)) :
    FiniteMatrixModel n j →⋆ₐ[ℂ] Algebra (matrixVonNeumann (ι := Fin n) M) :=
  (matrixAlgebraHom M).comp (coefficientMatrixMap (matrixUnitsEmbedding E))

theorem matrixVonNeumannTrace_map (τ : FaithfulTracialState (Algebra M))
    (x : CStarMatrix (Fin n) (Fin n) (Algebra M)) :
    (matrixVonNeumannTrace M τ).toLinearMap (matrixAlgebraHom M x) =
      (matrixTrace τ).toLinearMap x := by
  change (matrixTrace τ).toLinearMap
    ((matrixAlgebraEquiv M).symm ((matrixAlgebraEquiv M) x)) = _
  rw [StarAlgEquiv.symm_apply_apply]

theorem finiteMatrixEmbedding_trace
    (E : Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (τ : FaithfulTracialState (Algebra M)) (x : FiniteMatrixModel n j) :
    (matrixVonNeumannTrace M τ).toLinearMap (finiteMatrixEmbedding E x) =
      (finiteMatrixModelTrace n j).toLinearMap x := by
  change (matrixVonNeumannTrace M τ).toLinearMap
    (matrixAlgebraHom M (coefficientMatrixMap (matrixUnitsEmbedding E) x)) = _
  rw [matrixVonNeumannTrace_map]
  exact matrixTrace_coefficientMatrixMap (matrixTrace scalarTrace) τ
    (matrixUnitsEmbedding E) (matrixUnitsEmbedding_trace E τ) x

omit [NeZero n] in
/-- The outer scalar matrix algebra is fixed by every choice of inner matrix units. -/
theorem finiteMatrixEmbedding_scalar
    (E : Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (x : CStarMatrix (Fin n) (Fin n) ℂ) :
    finiteMatrixEmbedding E
        (coefficientMatrixMap (StarAlgHom.ofId ℂ (CStarMatrix (Fin (j + 1)) (Fin (j + 1)) ℂ)) x) =
      matrixAlgebraHom M (coefficientMatrixMap (StarAlgHom.ofId ℂ (Algebra M)) x) := by
  change matrixAlgebraHom M _ = matrixAlgebraHom M _
  congr 1
  apply CStarMatrix.ext
  intro i k
  change matrixUnitsEmbedding E (algebraMap ℂ _ (x i k)) = algebraMap ℂ _ (x i k)
  exact (matrixUnitsEmbedding E).commutes (x i k)

end

end KadisonKastler

end OAI
