import OAI.Probability.SignedSweeps.WordTwirl

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma projection_inner_eq [FiniteDimensional ℂ E] (P : E →ₗ[ℂ] E) (hP : P.IsSymmetric)
    (hPP : P * P = P) (x : E) :
    inner ℂ x (P x) = (‖P x‖ ^ 2 : ℂ) := by
  calc
    _ = inner ℂ x (P (P x)) := by rw [← Module.End.mul_apply, hPP]
    _ = inner ℂ (P x) (P x) := (hP x (P x)).symm
    _ = _ := inner_self_eq_norm_sq_to_K _

lemma positive_scalar_projection_lower (S : Submodule ℂ E) (T : E →ₗ[ℂ] E)
    (hT : T.IsPositive) (z : ℂ) (hz : ∀ x ∈ S, T x = z • x)
    {c : ℝ} (hc : c ≤ z.re) :
    (T - (c : ℂ) • S.starProjection.toLinearMap).IsPositive := by
  let P := S.starProjection.toLinearMap
  have hP : P.IsSymmetric := S.starProjection_isSymmetric
  have hPP : P * P = P := congrArg ContinuousLinearMap.toLinearMap
    S.isIdempotentElem_starProjection.eq
  have he (x : E) : T (P x) = z • P x := hz _ (S.starProjection_apply_mem x)
  refine ⟨hT.isSymmetric.sub (LinearMap.IsSymmetric.smul (Complex.conj_ofReal c) hP), ?_⟩
  intro x
  have hh := hT.re_inner_nonneg_right (x - P x)
  have hi := projection_inner_eq P hP hPP x
  have hxx : (inner ℂ (P x) (T x)).re =
      (inner ℂ x (T (P x))).re := by
    rw [← hT.isSymmetric]
    exact inner_re_symm (𝕜 := ℂ) _ _
  simp only [map_sub, inner_sub_right, inner_sub_left, RCLike.re_to_complex] at hh
  rw [hxx, he, inner_smul_right, inner_smul_right, hi, inner_self_eq_norm_sq_to_K] at hh
  simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hh
  have hs : (inner ℂ ((T - (c : ℂ) • P) x) x).re =
      (inner ℂ x (T x)).re - c * ‖P x‖ ^ 2 := by
    have hsym : (inner ℂ ((T - (c : ℂ) • P) x) x).re =
        (inner ℂ x ((T - (c : ℂ) • P) x)).re := inner_re_symm (𝕜 := ℂ) _ _
    rw [hsym]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_right, inner_smul_right,
      hi, Complex.sub_re, Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  change 0 ≤ (inner ℂ ((T - (c : ℂ) • P) x) x).re
  rw [hs]
  nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg ‖P x‖)]

omit [FiniteDimensional ℂ E] in
lemma positive_scalar_nonneg [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (z : ℂ) {x : E} (hx : x ≠ 0) (he : T x = z • x) : 0 ≤ z.re := by
  have h := hT.re_inner_nonneg_right x
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  simp only [RCLike.re_to_complex, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  exact (mul_nonneg_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hx))).mp h

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma wordTensor_diagonal_positive {p : ℕ} {C : Type*} [Fintype C]
    (x : C → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ)))).PosSemidef := by
  rw [wordTensor_diagonal, Matrix.posSemidef_diagonal_iff]
  intro w
  rw [← Complex.ofReal_prod]
  exact Complex.zero_le_real.mpr (Finset.prod_nonneg (fun i _ => hx (w i)))

theorem exists_word_density_lower {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (color : Fin (μ.1.colLen 0) ↪ C)
    (x : C → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ B : Matrix (Fin p → C) (Fin p → C) ℂ,
      matrixHilbertEquiv B ∈ wordTensorOrbitHull p C (Matrix.diagonal (fun i => (x i : ℂ))) ∧
      B.PosSemidef ∧
      ((wordMatrixEquiv p C).symm B -
        (((∏ i, x (rowColorWord μ color i)) /
          ((p + 1 : ℝ) ^ (Fintype.card C * Fintype.card C)) : ℝ) : ℂ) •
        (isotypicSubrepresentation (spechtRepresentation μ)
          (wordRepresentation p C)).toSubmodule.starProjection.toLinearMap).IsPositive := by
  let ρ := spechtRepresentation μ
  let σ := wordRepresentation p C
  let S := (isotypicSubrepresentation ρ σ).toSubmodule
  let P := S.starProjection.toLinearMap
  let A := wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ)))
  let U := (wordMatrixEquiv p C).symm A
  let w : ℝ := ∏ i, x (rowColorWord μ color i)
  let q : ℝ := (p + 1 : ℝ) ^ (Fintype.card C * Fintype.card C)
  have hw : 0 ≤ w := Finset.prod_nonneg (fun i _ => hx _)
  have hq : 0 < q := pow_pos (by positivity) _
  let f := spechtOrbitIntertwiner μ σ (EuclideanSpace.single (rowColorWord μ color) 1)
  have hf : f ≠ 0 := by
    intro h
    have hz : f (spechtGenerator μ) = f 0 := by rw [h]; rfl
    exact spechtGenerator_ne_zero μ (specht_occurs_word μ color hz)
  let := specht_irreducible μ
  obtain ⟨j, ⟨a, ha⟩, hj⟩ := intertwiner_isometric_scaling ρ σ
    (spechtRepresentation_norm μ) wordRepresentation_norm f hf
  let J : Specht μ →ₗᵢ[ℂ] WordSpace p C := ⟨j.toLinearMap, hj⟩
  have he (v : Specht μ) : U (J v) = (w : ℂ) • J v := by
    change U (j v) = (w : ℂ) • j v
    rw [ha]
    change U (a • f v) = (w : ℂ) • (a • f v)
    rw [map_smul]
    have h := rowColor_specht_eigen μ color (fun i => (x i : ℂ)) v
    rw [← Complex.ofReal_prod] at h
    exact (congrArg (a • ·) h).trans (smul_comm _ _ _)
  have hAP : wordMatrixEquiv p C P * A = A * wordMatrixEquiv p C P :=
    wordMatrix_projection_commute μ A (wordTensor_mem_commutant _)
  have hPU : P * U = U * P := by
    apply (wordMatrixEquiv p C).injective
    change wordMatrixEquiv p C (P * (wordMatrixEquiv p C).symm A) =
      wordMatrixEquiv p C ((wordMatrixEquiv p C).symm A * P)
    simpa only [map_mul, StarAlgEquiv.apply_symm_apply] using hAP
  have hP : P.IsSymmetric := S.starProjection_isSymmetric
  have hPP : P * P = P := congrArg ContinuousLinearMap.toLinearMap
    S.isIdempotentElem_starProjection.eq
  have hApos : A.PosSemidef := wordTensor_diagonal_positive x hx
  have hU : U.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr hApos
  have hPUpos := positive_commuting_projection U P hU hP hPP hPU
  have hJP (v : Specht μ) : P (J v) = J v :=
    S.starProjection_eq_self_iff.mpr (intertwiner_mem_isotypic ρ σ j v)
  have htrace := positive_trace_isometric_copy (P * U) hPUpos J (w : ℂ) (by
    intro v
    simp only [Module.End.mul_apply, he, map_smul, hJP])
  change w * (finrank ℂ (Specht μ) : ℝ) ≤ (LinearMap.trace ℂ (WordSpace p C) (P * U)).re at htrace
  obtain ⟨B, hB, hBcomm, z, hz⟩ := exists_word_scalar_twirl μ color
    (Matrix.diagonal (fun i => (x i : ℂ)))
  have hBpos := matrix_twirl_positive (wordUnitaryHom p C) hB hApos
  let T := (wordMatrixEquiv p C).symm B
  have hT : T.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr hBpos
  have hzpos : 0 ≤ z.re := by
    apply positive_scalar_nonneg T hT z (x := J (spechtGenerator μ))
    · simpa only [map_zero] using J.injective.ne (spechtGenerator_ne_zero μ)
    · exact hz _ (intertwiner_mem_isotypic ρ σ j _)
  have htr : LinearMap.trace ℂ (WordSpace p C) (T * P) =
      LinearMap.trace ℂ (WordSpace p C) (P * U) := by
    rw [LinearMap.trace_mul_comm ℂ P U, ← wordMatrix_trace, ← wordMatrix_trace]
    simp only [map_mul, T, U, StarAlgEquiv.apply_symm_apply]
    apply matrix_twirl_trace (wordUnitaryHom p C) hB
    intro g
    exact wordMatrix_projection_commute μ _ (wordTensor_mem_commutant _)
  rw [← htr, trace_scalar_projection S T z hz] at htrace
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] at htrace
  have hdim : (finrank ℂ S : ℝ) ≤ (finrank ℂ (Specht μ) : ℝ) * q := by
    have hn := isotypic_finrank_le_commutant ρ σ (spechtRepresentation_norm μ)
      wordRepresentation_norm j hj
    rw [(wordCommutantEquiv p C).finrank_eq] at hn
    have hn' := hn.trans (Nat.mul_le_mul_left _ wordCommutant_finrank_le)
    dsimp only [S, q]
    exact_mod_cast hn'
  have hDz : 0 < (finrank ℂ (Specht μ) : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hlower : w / q ≤ z.re := by
    apply (div_le_iff₀ hq).mpr
    have hh := htrace.trans (mul_le_mul_of_nonneg_left hdim hzpos)
    nlinarith
  exact ⟨B, hB, hBpos, positive_scalar_projection_lower S T hT z hz hlower⟩

end SignedSweeps
end

end OAI
