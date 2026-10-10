import OAI.Probability.InvariantIsing.Cavity.CavityGaussianSpectral

namespace OAI

/-! The affine precision homotopy in `cav:q-precision`.  Since the
eigenvectors of its fixed symmetric coefficient do not change, path
nonsingularity rules out eigenvalues at or above one directly. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_precision_eigenvalues_lt_one {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - t • M).det) (i : Fin d) :
    hM.eigenvalues i < 1 := by
  by_contra! hEig
  have hEigenPos : 0 < hM.eigenvalues i := lt_of_lt_of_le zero_lt_one hEig
  let t := (hM.eigenvalues i)⁻¹
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(inv_pos.mpr hEigenPos).le, ?_⟩
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hEig
  have hz : (1 - t • M) *ᵥ (fun j => hM.eigenvectorBasis i j) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      hM.mulVec_eigenvectorBasis, smul_smul]
    simp [t, inv_mul_cancel₀ hEigenPos.ne']
  have hinj : Function.Injective (1 - t • M).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (hpath t ht))
  have hvzero : (fun j => hM.eigenvectorBasis i j) = 0 := by
    apply hinj
    simpa only [Matrix.mulVec_zero] using hz
  apply hM.eigenvectorBasis.orthonormal.ne_zero i
  ext j
  exact congrFun hvzero j

lemma cavity_precision_inner_pos {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hEig : ∀ i, hM.eigenvalues i < 1)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ 0) :
    0 < ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - M) x⟫ := by
  have he : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - M) x⟫ =
      ∑ i, (1 - hM.eigenvalues i) * (hM.eigenvectorBasis.repr x i) ^ 2 := by
    simp only [map_sub, map_one, sub_apply,
      one_apply_eq_self, inner_sub_right, real_inner_self_eq_norm_sq]
    have hq : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) M x⟫ =
        ∑ i, hM.eigenvalues i * (hM.eigenvectorBasis.repr x i) ^ 2 :=
      cavity_eigenbasis_quadratic M hM x
    rw [hq]
    have hn : ‖x‖ ^ 2 = ∑ i, (hM.eigenvectorBasis.repr x i) ^ 2 := by
      simpa only [hM.eigenvectorBasis.repr_apply_apply] using
        (hM.eigenvectorBasis.sum_sq_inner_right x).symm
    rw [hn, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  obtain ⟨i, hi⟩ : ∃ i, hM.eigenvectorBasis.repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply hM.eigenvectorBasis.repr.injective
    ext i
    simpa only [map_zero, PiLp.zero_apply] using h i
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (sub_pos.mpr (hEig j)).le (sq_nonneg _)
  · exact ⟨i, Finset.mem_univ i, mul_pos (sub_pos.mpr (hEig i)) (sq_pos_of_ne_zero hi)⟩

/-- The source's precision-continuation argument specialized to its actual
affine path. No continuity-of-eigenvalues input is needed. -/
theorem cavity_precision_posDef_of_path {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - t • M).det) :
    (1 - M).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.isHermitian_one.sub hM, ?_⟩
  intro v hv
  have hx : WithLp.toLp 2 v ≠ (0 : EuclideanSpace ℝ (Fin d)) := by
    intro h
    apply hv
    ext i
    exact congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) h
  have hp := cavity_precision_inner_pos M hM
    (cavity_precision_eigenvalues_lt_one M hM hpath) (WithLp.toLp 2 v) hx
  simpa only [Matrix.inner_toEuclideanCLM, PiLp.toLp_apply, star_trivial] using hp

end InvariantIsing

end

end OAI
