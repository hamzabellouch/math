import OAI.Analysis.KadisonSimilarity.Tracial.GNSTracialGeometry
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialSymmetryExtraction

namespace OAI

/-! Normalized matrix traces and their actual GNS Hilbert spaces. The GNS
space of `M_n(A)` is identified with the square array of copies of the GNS
space of `A`; its algebra vectors have entries `n^(-1/2) V(a_ij)`. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

/-- Coordinatewise dense maps stay dense in a finite Hilbert sum. -/
private theorem denseRange_hilbert_entries {J D B : Type*} [Fintype J]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (f : D → B) (hf : DenseRange f) :
    DenseRange (fun x : J → D => WithLp.toLp 2 (fun j => f (x j))) := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : J => B)).symm
  have hpi : DenseRange (Pi.map (fun _ : J => f)) := DenseRange.piMap (fun _ => hf)
  exact e.surjective.denseRange.comp hpi e.continuous

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

local instance : NonUnitalContinuousFunctionalCalculus ℝ
    (CStarMatrix (Fin n) (Fin n) A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- The normalized sum of the diagonal functionals. -/
def normalizedMatrixTraceLinear (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    CStarMatrix (Fin n) (Fin n) A →ₗ[ℂ] ℂ where
  toFun X := (∑ i : Fin n, τ (X i i)) / (n : ℂ)
  map_add' X Y := by
    simp only [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib, add_div]
  map_smul' c X := by
    simp only [CStarMatrix.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul,
      ← Finset.mul_sum]
    ring

omit [NeZero n] in
/-- Positivity of a matrix gives positivity of each diagonal entry. -/
theorem matrix_diagonal_nonneg (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : 0 ≤ X) (i : Fin n) : 0 ≤ X i i := by
  have hs := CFC.sqrt_nonneg X
  have he : X = star (CFC.sqrt X) * CFC.sqrt X := by
    rw [hs.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self X hX]
  rw [he, CStarMatrix.mul_apply]
  simp only [CStarMatrix.star_apply]
  exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg _

/-- The normalized matrix trace as a positive linear functional. -/
def normalizedMatrixTrace (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (normalizedMatrixTraceLinear τ n) (fun X hX =>
    div_nonneg (Finset.sum_nonneg fun i _ => τ.map_nonneg (matrix_diagonal_nonneg X hX i))
      (by positivity))

@[simp] theorem normalizedMatrixTrace_apply (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    normalizedMatrixTrace τ n X = (∑ i : Fin n, τ (X i i)) / (n : ℂ) := rfl

theorem normalizedMatrixTrace_one (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) :
    normalizedMatrixTrace τ n 1 = 1 := by
  simp [normalizedMatrixTrace_apply, h1, NeZero.ne n]

theorem normalizedMatrixTrace_tracial (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a))
    (X Y : CStarMatrix (Fin n) (Fin n) A) :
    normalizedMatrixTrace τ n (X * Y) = normalizedMatrixTrace τ n (Y * X) := by
  simp only [normalizedMatrixTrace_apply, CStarMatrix.mul_apply, map_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact htr _ _

/-- Entrywise formula for the matrix GNS inner product. -/
theorem normalizedMatrixTrace_star_mul (τ : A →ₚ[ℂ] ℂ)
    (X Y : CStarMatrix (Fin n) (Fin n) A) :
    normalizedMatrixTrace τ n (star X * Y) =
      (n : ℂ)⁻¹ * ∑ i : Fin n, ∑ j : Fin n, τ (star (X i j) * Y i j) := by
  simp only [normalizedMatrixTrace_apply, CStarMatrix.mul_apply,
    CStarMatrix.star_apply, map_sum]
  rw [Finset.sum_comm]
  ring

/-- Square arrays use the ordinary Hilbert sum norm in both coordinates. -/
abbrev MatrixGNSArray (τ : A →ₚ[ℂ] ℂ) (n : ℕ) :=
  HilbertCopies (HilbertCopies τ.GNS n) n

/-- The unscaled array of represented matrix entries. -/
def matrixGNSArrayLinear (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    CStarMatrix (Fin n) (Fin n) A →ₗ[ℂ] MatrixGNSArray τ n where
  toFun X := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => gnsTracialVector τ (X i j)))
  map_add' X Y := by
    ext i j
    simp only [PiLp.add_apply, CStarMatrix.add_apply, map_add]
  map_smul' c X := by
    ext i j
    simp only [PiLp.smul_apply, CStarMatrix.smul_apply, map_smul,
      RingHom.id_apply]

@[simp] theorem matrixGNSArrayLinear_apply (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) (i j : Fin n) :
    matrixGNSArrayLinear τ n X i j = gnsTracialVector τ (X i j) := rfl

/-- Normalization converting the array norm into normalized tracial L² norm. -/
def matrixGNSScale (n : ℕ) : ℝ := (Real.sqrt n)⁻¹

theorem matrixGNSScale_pos : 0 < matrixGNSScale n := by
  unfold matrixGNSScale
  exact inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)))

omit [NeZero n] in
theorem matrixGNSScale_sq : matrixGNSScale n ^ 2 = (n : ℝ)⁻¹ := by
  rw [matrixGNSScale, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Normalized represented matrix vectors. -/
def matrixGNSVector (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    CStarMatrix (Fin n) (Fin n) A →ₗ[ℂ] MatrixGNSArray τ n :=
  (matrixGNSScale n : ℂ) • matrixGNSArrayLinear τ n

@[simp] theorem matrixGNSVector_apply (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) (i j : Fin n) :
    matrixGNSVector τ n X i j = (matrixGNSScale n : ℂ) • gnsTracialVector τ (X i j) := rfl

theorem matrixGNSVector_inner (τ : A →ₚ[ℂ] ℂ)
    (X Y : CStarMatrix (Fin n) (Fin n) A) :
    inner ℂ (matrixGNSVector τ n X) (matrixGNSVector τ n Y) =
      normalizedMatrixTrace τ n (star X * Y) := by
  have hc : (matrixGNSScale n : ℂ) * starRingEnd ℂ (matrixGNSScale n : ℂ) =
      (n : ℂ)⁻¹ := by
    rw [Complex.conj_ofReal]
    have hr : matrixGNSScale n * matrixGNSScale n = (n : ℝ)⁻¹ := by
      simpa only [pow_two] using (matrixGNSScale_sq (n := n))
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast] using
      congrArg (fun r : ℝ => (r : ℂ)) hr
  rw [normalizedMatrixTrace_star_mul]
  simp only [matrixGNSVector, LinearMap.smul_apply, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, hc]
  congr 1
  simp only [PiLp.inner_apply, matrixGNSArrayLinear_apply, gnsTracialVector_inner]

theorem matrixGNSVector_norm (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖matrixGNSVector τ n X‖ = ‖gnsTracialVector (normalizedMatrixTrace τ n) X‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    matrixGNSVector_inner, gnsTracialVector_inner]

/-- Faithfulness of the trace is preserved by normalized matrix extension. -/
theorem normalizedMatrixTrace_faithful (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0)
    (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : normalizedMatrixTrace τ n (star X * X) = 0) : X = 0 := by
  have hz : matrixGNSVector τ n X = 0 :=
    inner_self_eq_zero.mp (by rw [matrixGNSVector_inner, hX])
  have hc : (matrixGNSScale n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (matrixGNSScale_pos (n := n)).ne'
  ext i j
  have hcoord := congrArg (fun ξ : MatrixGNSArray τ n => ξ i j) hz
  change (matrixGNSScale n : ℂ) • gnsTracialVector τ (X i j) = 0 at hcoord
  have hv : gnsTracialVector τ (X i j) = 0 := (smul_eq_zero.mp hcoord).resolve_left hc
  change X i j = 0
  apply gnsTracialVector_injective τ hf
  simpa only [map_zero] using hv

/-- The normalized trace of one diagonal entry has weight `1/n`. -/
theorem normalizedMatrixTrace_single (τ : A →ₚ[ℂ] ℂ) (i : Fin n) (a : A) :
    normalizedMatrixTrace τ n (CStarMatrix.ofMatrix (Matrix.single i i a)) =
      τ a / (n : ℂ) := by
  simp [normalizedMatrixTrace_apply, Matrix.single_apply, apply_ite]

theorem normalizedMatrixTrace_matrixUnit (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (i : Fin n) :
    normalizedMatrixTrace τ n (CStarMatrix.ofMatrix (Matrix.single i i (1 : A))) =
      (n : ℂ)⁻¹ := by
  rw [normalizedMatrixTrace_single, h1, one_div]

/-- The completed matrix GNS space embeds isometrically in its entry array. -/
def matrixGNSIsometry (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    (normalizedMatrixTrace τ n).GNS →ₗᵢ[ℂ] MatrixGNSArray τ n :=
  (matrixGNSVector τ n).extendOfIsometry
    (gnsTracialVector_dense (normalizedMatrixTrace τ n)) (matrixGNSVector_norm τ)

@[simp] theorem matrixGNSIsometry_vector (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    matrixGNSIsometry τ n (gnsTracialVector (normalizedMatrixTrace τ n) X) =
      matrixGNSVector τ n X :=
  LinearMap.extendOfIsometry_eq _ (gnsTracialVector_dense (normalizedMatrixTrace τ n))
    (matrixGNSVector_norm τ) X

theorem matrixGNSArrayLinear_dense (τ : A →ₚ[ℂ] ℂ) :
    DenseRange (matrixGNSArrayLinear τ n) := by
  have hrow := denseRange_hilbert_entries (J := Fin n)
    (gnsTracialVector τ) (gnsTracialVector_dense τ)
  have harr := denseRange_hilbert_entries (J := Fin n)
    (fun x : Fin n → A => WithLp.toLp 2 (fun j => gnsTracialVector τ (x j))) hrow
  apply harr.mono
  rintro _ ⟨X, rfl⟩
  exact ⟨CStarMatrix.ofMatrix X, rfl⟩

theorem matrixGNSVector_dense (τ : A →ₚ[ℂ] ℂ) : DenseRange (matrixGNSVector τ n) := by
  have hc : (matrixGNSScale n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (matrixGNSScale_pos (n := n)).ne'
  apply (matrixGNSArrayLinear_dense (n := n) τ).mono
  rintro _ ⟨X, rfl⟩
  refine ⟨(matrixGNSScale n : ℂ)⁻¹ • X, ?_⟩
  change (matrixGNSScale n : ℂ) •
    matrixGNSArrayLinear τ n ((matrixGNSScale n : ℂ)⁻¹ • X) = matrixGNSArrayLinear τ n X
  rw [map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem matrixGNSIsometry_surjective (τ : A →ₚ[ℂ] ℂ) :
    Function.Surjective (matrixGNSIsometry τ n) := by
  have hd : DenseRange (matrixGNSIsometry τ n) := by
    apply (matrixGNSVector_dense (n := n) τ).mono
    rintro _ ⟨X, rfl⟩
    exact ⟨gnsTracialVector (normalizedMatrixTrace τ n) X, matrixGNSIsometry_vector τ X⟩
  intro x
  have hx := hd x
  rw [(matrixGNSIsometry τ n).isometry.isClosedEmbedding.isClosed_range.closure_eq] at hx
  exact hx

/-- The completed normalized matrix GNS space is exactly the square Hilbert array. -/
def matrixGNSUnitary (τ : A →ₚ[ℂ] ℂ) (n : ℕ) [NeZero n] :
    (normalizedMatrixTrace τ n).GNS ≃ₗᵢ[ℂ] MatrixGNSArray τ n :=
  LinearIsometryEquiv.ofSurjective (matrixGNSIsometry τ n) (matrixGNSIsometry_surjective τ)

@[simp] theorem matrixGNSUnitary_vector (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) (i j : Fin n) :
    matrixGNSUnitary τ n (gnsTracialVector (normalizedMatrixTrace τ n) X) i j =
      (matrixGNSScale n : ℂ) • gnsTracialVector τ (X i j) := by
  change matrixGNSIsometry τ n (gnsTracialVector (normalizedMatrixTrace τ n) X) i j = _
  rw [matrixGNSIsometry_vector, matrixGNSVector_apply]

/-- The ordinary matrix action on the row coordinate, with a standard copy
in each column coordinate. -/
def matrixLeftArray (τ : A →ₚ[ℂ] ℂ) (X : CStarMatrix (Fin n) (Fin n) A) :
    MatrixGNSArray τ n →L[ℂ] MatrixGNSArray τ n :=
  matrixOperator (fun i k => amplify (τ.gnsStarAlgHom (X i k)) n)

omit [NeZero n] in
@[simp] theorem matrixLeftArray_apply (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) (ξ : MatrixGNSArray τ n) (i j : Fin n) :
    matrixLeftArray τ X ξ i j = ∑ k : Fin n, τ.gnsStarAlgHom (X i k) (ξ k j) := by
  simp [matrixLeftArray, matrixOperator, amplify]

theorem matrixGNSVector_mul (τ : A →ₚ[ℂ] ℂ)
    (X Y : CStarMatrix (Fin n) (Fin n) A) :
    matrixGNSVector τ n (X * Y) = matrixLeftArray τ X (matrixGNSVector τ n Y) := by
  ext i j
  simp only [matrixGNSVector_apply, matrixLeftArray_apply, CStarMatrix.mul_apply,
    map_sum, map_smul, gnsTracialVector_left, Finset.smul_sum]

/-- The GNS left representation becomes actual left matrix multiplication
under the normalized array identification. -/
theorem matrixGNSUnitary_left (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) (ξ : (normalizedMatrixTrace τ n).GNS) :
    matrixGNSUnitary τ n ((normalizedMatrixTrace τ n).gnsStarAlgHom X ξ) =
      matrixLeftArray τ X (matrixGNSUnitary τ n ξ) := by
  ext i j
  refine (gnsTracialVector_dense (normalizedMatrixTrace τ n)).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro Y
  change matrixGNSIsometry τ n
    ((normalizedMatrixTrace τ n).gnsStarAlgHom X
      (gnsTracialVector (normalizedMatrixTrace τ n) Y)) i j =
    matrixLeftArray τ X (matrixGNSIsometry τ n
      (gnsTracialVector (normalizedMatrixTrace τ n) Y)) i j
  rw [gnsTracialVector_left, matrixGNSIsometry_vector, matrixGNSIsometry_vector,
    matrixGNSVector_mul]

/-- Conjugation by the normalized array unitary gives actual left matrix action. -/
theorem matrixGNSUnitary_conjugates_left (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    (matrixGNSUnitary τ n).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (((normalizedMatrixTrace τ n).gnsStarAlgHom X).comp
        (matrixGNSUnitary τ n).symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      matrixLeftArray τ X := by
  apply ContinuousLinearMap.ext
  intro ξ
  change matrixGNSUnitary τ n
    ((normalizedMatrixTrace τ n).gnsStarAlgHom X ((matrixGNSUnitary τ n).symm ξ)) = _
  rw [matrixGNSUnitary_left, LinearIsometryEquiv.apply_symm_apply]

end KadisonSimilarity

end

end OAI
