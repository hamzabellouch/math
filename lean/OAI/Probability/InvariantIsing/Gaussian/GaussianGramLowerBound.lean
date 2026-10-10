import OAI.Probability.InvariantIsing.Gaussian.GaussianTranspose

namespace OAI

/-! The actual Gram eigenvalues dominate the squared transposed least singular value. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma gaussianPattern_quadratic {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (x : EuclideanSpace ℝ (Fin N)) :
    ⟪x,(gaussianPatternCoupling 1 z).toEuclideanLin x⟫ =
      ‖gaussianPatternEuclideanOperator (gaussianPatternTranspose N m z) x‖^2/N := by
  have hn : ‖gaussianPatternEuclideanOperator (gaussianPatternTranspose N m z) x‖^2 =
      ((gaussianPatternArray z)ᵀ *ᵥ x.ofLp) ⬝ᵥ ((gaussianPatternArray z)ᵀ *ᵥ x.ofLp) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct,pow_two]
    rfl
  rw [hn]
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm]
  simp only [star_trivial]
  change x.ofLp ⬝ᵥ ((1/(N : ℝ)) • (gaussianPatternArray z*(gaussianPatternArray z)ᵀ)) *ᵥ x.ofLp = _
  rw [Matrix.smul_mulVec,dotProduct_smul,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  simp only [smul_eq_mul]
  ring

lemma gaussianPatternSingularMin_nonneg {N m : ℕ} (hm : 0 < m)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : 0 ≤ gaussianPatternSingularMin z := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    refine ⟨⟨EuclideanSpace.single (⟨0,hm⟩ : Fin m) (1 : ℝ),?_⟩⟩
    simp
  exact le_ciInf (fun _ => norm_nonneg _)

lemma gaussianPatternEigenvalues_lower_singular {N m : ℕ} (hN : 0 < N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (i : Fin N) :
    (gaussianPatternSingularMin (gaussianPatternTranspose N m z))^2/N ≤
      gaussianPatternEigenvalues z i := by
  let hA := gaussianPatternCoupling_isHermitian 1 z
  let u := hA.eigenvectorBasis i
  have hu : ‖u‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hb : BddBelow (Set.range (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 =>
      ‖gaussianPatternEuclideanOperator (gaussianPatternTranspose N m z) x‖)) :=
    ⟨0,by rintro _ ⟨x,rfl⟩; exact norm_nonneg _⟩
  have hl : gaussianPatternSingularMin (gaussianPatternTranspose N m z) ≤
      ‖gaussianPatternEuclideanOperator (gaussianPatternTranspose N m z) u‖ :=
    ciInf_le hb ⟨u,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩
  have hs := sq_le_sq₀ (gaussianPatternSingularMin_nonneg hN _) (norm_nonneg _) |>.2 hl
  have he : gaussianPatternEigenvalues z i = ⟪u,(gaussianPatternCoupling 1 z).toEuclideanLin u⟫ := by
    unfold gaussianPatternEigenvalues
    change hA.eigenvalues i = _
    rw [hA.eigenvalues_eq i,EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial,RCLike.re_to_real]
    exact dotProduct_comm _ _
  rw [he,gaussianPattern_quadratic]
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)

end InvariantIsing

end

end OAI
