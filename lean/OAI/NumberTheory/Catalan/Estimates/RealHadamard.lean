import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

namespace OAI

noncomputable section

open scoped BigOperators InnerProductSpace

namespace InternalCatalan

theorem norm_det_le_of_entry_norm_eq {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : ∀ i j, ‖A i j‖ = w i) :
    ‖A.det‖ ≤ (Real.sqrt (m : ℝ)) ^ m * (∏ i, w i) := by
  classical
  let f : Fin m → EuclideanSpace ℂ (Fin m) :=
    fun i => WithLp.toLp 2 (A i)
  let e : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)) :=
    EuclideanSpace.basisFun (Fin m) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) =
      Fintype.card (Fin m) := finrank_euclideanSpace
  let b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  have hcoord : e.toBasis.toMatrix f = A.transpose := by
    ext i j
    change e.toBasis.repr (f j) i = A j i
    rw [OrthonormalBasis.coe_toBasis_repr_apply]
    rfl
  have hdet : e.toBasis.det f = A.det := by
    rw [Module.Basis.det_apply, hcoord, Matrix.det_transpose]
  have hchange : e.toBasis.det f =
      e.toBasis.det b * b.toBasis.det f := by
    simpa only [AlternatingMap.smul_apply, smul_eq_mul,
      OrthonormalBasis.coe_toBasis] using
      congrArg (fun D : AlternatingMap ℂ (EuclideanSpace ℂ (Fin m)) ℂ (Fin m) => D f)
        ((e.toBasis.det).eq_smul_basis_det b.toBasis)
  have hnormdet : ‖A.det‖ = ‖b.toBasis.det f‖ := by
    rw [← hdet, hchange, norm_mul,
      OrthonormalBasis.det_to_matrix_orthonormalBasis, one_mul]
  have htri : b.toBasis.det f = ∏ i, ⟪b i, f i⟫_ℂ :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hdim f
  have hrow (i : Fin m) : ‖f i‖ = Real.sqrt (m : ℝ) * w i := by
    rw [EuclideanSpace.norm_eq]
    simp only [f, hA, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq (hw i)]
  calc
    ‖A.det‖ = ∏ i, ‖⟪b i, f i⟫_ℂ‖ := by
      rw [hnormdet, htri, Complex.norm_prod]
    _ ≤ ∏ i, ‖f i‖ := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact norm_nonneg _
      · intro i _
        simpa only [OrthonormalBasis.norm_eq_one, one_mul] using
          norm_inner_le_norm (𝕜 := ℂ) (b i) (f i)
    _ = (Real.sqrt (m : ℝ)) ^ m * (∏ i, w i) := by
      simp_rw [hrow]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end InternalCatalan

end

end OAI
