import OAI.Geometry.RCD.Harmonic.HarmonicGrams

namespace OAI

/-!
# Exact mean normalizations and their metric consequences

An exact normalization is the identity for the mean Sobolev Gram operator,
as in Huang--Huang, Theorem 4.1(2). All conclusions below are derived from
that identity. In particular, nondegeneracy of the original Gram operator
is not separately assumed.
-/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  (U : E →L[ℝ] SobolevSpace μ hQ)

/-- The adjoint of a coordinate normalization acts on the coefficients of
the scalar Sobolev column. -/
def IsExactMeanNormalization (s : Set X) (hs : MeasurableSet s)
    (A : E ≃L[ℝ] E) : Prop :=
  sobolevMeanGram μ hQ (U.comp (A : E →L[ℝ] E)) s hs =
    ContinuousLinearMap.id ℝ E

theorem meanGram_energy_of_exact_normalization (s : Set X) (hs : MeasurableSet s)
    (A : E ≃L[ℝ] E) (hA : IsExactMeanNormalization μ hQ U s hs A) (v : E) :
    ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ = ‖A.symm v‖ ^ 2 := by
  have h := congrArg (fun Q : E →L[ℝ] E => ⟪A.symm v, Q (A.symm v)⟫_ℝ) hA
  rw [sobolevMeanGram_comp] at h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using h

theorem meanGram_strictly_positive_of_exact_normalization
    (s : Set X) (hs : MeasurableSet s) (A : E ≃L[ℝ] E)
    (hA : IsExactMeanNormalization μ hQ U s hs A) {v : E} (hv : v ≠ 0) :
    0 < ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ := by
  rw [meanGram_energy_of_exact_normalization μ hQ U s hs A hA]
  apply sq_pos_of_pos
  exact norm_pos_iff.mpr (fun h => hv (A.symm.injective (by simpa using h)))

theorem meanGram_lower_of_exact_normalization
    (s : Set X) (hs : MeasurableSet s) (A : E ≃L[ℝ] E)
    (hA : IsExactMeanNormalization μ hQ U s hs A)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ‖(A : E →L[ℝ] E)‖ ≤ C) (v : E) :
    ‖v‖ ^ 2 ≤ C ^ 2 * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ := by
  rw [meanGram_energy_of_exact_normalization μ hQ U s hs A hA]
  have h := (A : E →L[ℝ] E).le_opNorm (A.symm v)
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h
  have hb := mul_le_mul_of_nonneg_right hbound (norm_nonneg (A.symm v))
  have hs := (sq_le_sq₀ (norm_nonneg v)
    (mul_nonneg hC (norm_nonneg (A.symm v)))).mpr (h.trans hb)
  simpa only [mul_pow] using hs

theorem meanGram_upper_of_exact_normalization
    (s : Set X) (hs : MeasurableSet s) (A : E ≃L[ℝ] E)
    (hA : IsExactMeanNormalization μ hQ U s hs A)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ‖(A.symm : E →L[ℝ] E)‖ ≤ C) (v : E) :
    ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ ≤ C ^ 2 * ‖v‖ ^ 2 := by
  rw [meanGram_energy_of_exact_normalization μ hQ U s hs A hA]
  have h := (A.symm : E →L[ℝ] E).le_opNorm v
  have hb := mul_le_mul_of_nonneg_right hbound (norm_nonneg v)
  have hs := (sq_le_sq₀ (norm_nonneg (A.symm v))
    (mul_nonneg hC (norm_nonneg v))).mpr (h.trans hb)
  simpa only [mul_pow] using hs

/-- The precise comparison needed for neighboring centers or scales. -/
theorem meanGram_comparison_of_normalizations
    (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (A B : E ≃L[ℝ] E)
    (hA : IsExactMeanNormalization μ hQ U s hs A)
    (hB : IsExactMeanNormalization μ hQ U t ht B)
    {C : ℝ} (hC : 0 ≤ C)
    (hcompare : ∀ v, ‖B.symm v‖ ≤ C * ‖A.symm v‖) (v : E) :
    ⟪v, sobolevMeanGram μ hQ U t ht v⟫_ℝ ≤
      C ^ 2 * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ := by
  rw [meanGram_energy_of_exact_normalization μ hQ U s hs A hA,
    meanGram_energy_of_exact_normalization μ hQ U t ht B hB]
  have h := (sq_le_sq₀ (norm_nonneg (B.symm v))
    (mul_nonneg hC (norm_nonneg (A.symm v)))).mpr (hcompare v)
  simpa only [mul_pow] using h

end RegularPointCoordinates

end

end OAI
