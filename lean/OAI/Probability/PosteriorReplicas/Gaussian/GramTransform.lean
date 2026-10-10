import OAI.Probability.PosteriorReplicas.Gaussian.GaussianRowMix

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def columnMix {m : ℕ} (v : Fin m → E) (M : Matrix (Fin m) (Fin m) ℝ) : Fin m → E :=
  fun j => ∑ i, M i j • v i

@[fun_prop] lemma measurable_columnMix {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (fun v : Fin m → E => columnMix v M) := by
  unfold columnMix
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gram_columnMix [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {m : ℕ} (v : Fin m → E) (M : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.gram ℝ (columnMix v M) = M.transpose * Matrix.gram ℝ v * M := by
  exact PosteriorRegression.gram_linear_combination v M

lemma gramVolume_columnMix {m : ℕ} (v : Fin m → E) (M : Matrix (Fin m) (Fin m) ℝ) :
    gramVolume (columnMix v M) = |M.det| * gramVolume v := by
  unfold gramVolume
  rw [gram_columnMix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have he : M.det * (Matrix.gram ℝ v).det * M.det = M.det^2 * (Matrix.gram ℝ v).det := by ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma columnMix_independent {m : ℕ} {v : Fin m → E} (hv : LinearIndependent ℝ v)
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.det ≠ 0) :
    LinearIndependent ℝ (columnMix v M) := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [gram_columnMix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero hM (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv)) hM

def pairingColumns {d ℓ m : ℕ} (v : Rows d m) (B : Rows d ℓ) : Rows ℓ m :=
  fun i => WithLp.toLp 2 (fun j => ⟪v i, B j⟫)

@[fun_prop] lemma measurable_pairingColumns {d ℓ m : ℕ} :
    Measurable (fun z : Rows d m × Rows d ℓ => pairingColumns z.1 z.2) := by
  unfold pairingColumns
  fun_prop

lemma pairingColumns_triangular {d ℓ m : ℕ} {v : Rows d m} (hv : LinearIndependent ℝ v)
    (B : Rows d ℓ) :
    pairingColumns v B = columnMix (pairingColumns (gramSchmidtNormed ℝ v) B) (pairingTriangular v) := by
  ext i j
  change ⟪v i, B j⟫ = _
  conv_lhs => rw [← pairingTriangular_expansion hv i]
  simp [columnMix, pairingColumns, sum_inner, inner_smul_left, Finset.sum_apply]

lemma orthonormal_pairingColumns_law {d ℓ m : ℕ} {v : Rows d m} (hv : Orthonormal ℝ v) :
    (gaussianRows d ℓ).map (pairingColumns v) = gaussianRows ℓ m := by
  have he : (pairingColumns v : Rows d ℓ → Rows ℓ m) = rowMix v ∘ vecTranspose := by
    funext B
    ext i j
    exact (rowMix_apply v (vecTranspose B) i j).symm
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianRows_transpose,
    gaussianRows_mix hv]

lemma pairingColumns_law {d ℓ m : ℕ} {v : Rows d m} (hv : LinearIndependent ℝ v) :
    (gaussianRows d ℓ).map (pairingColumns v) =
      (gaussianRows ℓ m).map (fun G => columnMix G (pairingTriangular v)) := by
  have he : (pairingColumns v : Rows d ℓ → Rows ℓ m) = (fun G => columnMix G (pairingTriangular v)) ∘
      pairingColumns (gramSchmidtNormed ℝ v) := funext (pairingColumns_triangular hv)
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    orthonormal_pairingColumns_law (gramSchmidtNormed_orthonormal hv)]

lemma ae_pairingColumns_independent {d ℓ m : ℕ} {v : Rows d m}
    (hv : LinearIndependent ℝ v) (hm : m ≤ ℓ) :
    ∀ᵐ B ∂gaussianRows d ℓ, LinearIndependent ℝ (pairingColumns v B) := by
  have he : ∀ᵐ G ∂gaussianRows ℓ m, LinearIndependent ℝ (columnMix G (pairingTriangular v)) := by
    filter_upwards [ae_gaussian_columns_independent (E := Vec ℓ) m (by simpa using hm)] with G hG
    apply columnMix_independent hG
    simpa only [Matrix.det_transpose] using (pairingTriangular_det_pos hv).ne'
  have he' : ∀ᵐ V ∂(gaussianRows d ℓ).map (pairingColumns v), LinearIndependent ℝ V := by
    rw [pairingColumns_law hv]
    exact (ae_map_iff (by fun_prop) isOpen_setOfPred_linearIndependent.measurableSet).mpr he
  exact (ae_map_iff (by fun_prop) isOpen_setOfPred_linearIndependent.measurableSet).mp he'

lemma gramVolume_pairingColumns {d ℓ m : ℕ} {v : Rows d m} (hv : LinearIndependent ℝ v)
    (B : Rows d ℓ) : gramVolume (pairingColumns v B) =
      gramVolume v * gramVolume (pairingColumns (gramSchmidtNormed ℝ v) B) := by
  rw [pairingColumns_triangular hv, gramVolume_columnMix]
  have hd : (pairingTriangular v).det = gramVolume v := by
    rw [← Matrix.det_transpose, pairingTriangular_det]
    rfl
  rw [hd, abs_of_nonneg (show 0 ≤ gramVolume v from Real.sqrt_nonneg _)]

end PosteriorReplicas
end

end OAI
