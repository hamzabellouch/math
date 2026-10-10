import OAI.Geometry.RCD.Harmonic.MeanGramControl

namespace OAI

/-!
# Comparing Gram means inside a common normalized region

Averaged Gram errors on an enlarged ball restrict to nearby balls with only
the volume-ratio cost. If one coordinate normalization makes both resulting
means close to the identity, their original quadratic forms are close to each
other. These are the comparison steps after harmonic transformation.
-/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem average_nonneg_le_of_subset {s t : Set X}
    (hst : s ⊆ t) (hs0 : 0 < μ.real s) (ht0 : 0 < μ.real t)
    {f : X → ℝ} (hf : IntegrableOn f t μ) (hnonneg : ∀ x, 0 ≤ f x)
    {C ε : ℝ} (hε : 0 ≤ ε) (hvol : μ.real t ≤ C * μ.real s)
    (havg : (μ.real t)⁻¹ * (∫ x in t, f x ∂μ) ≤ ε) :
    (μ.real s)⁻¹ * (∫ x in s, f x ∂μ) ≤ C * ε := by
  have hm : (∫ x in s, f x ∂μ) ≤ ∫ x in t, f x ∂μ :=
    setIntegral_mono_set hf (Filter.Eventually.of_forall hnonneg) (Filter.Eventually.of_forall hst)
  have hb : (∫ x in t, f x ∂μ) ≤ μ.real t * ε := by
    have hh := mul_le_mul_of_nonneg_left havg ht0.le
    simpa only [← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul] using hh
  calc
    (μ.real s)⁻¹ * (∫ x in s, f x ∂μ) ≤ (μ.real s)⁻¹ * (μ.real t * ε) :=
      mul_le_mul_of_nonneg_left (hm.trans hb) (inv_nonneg.mpr hs0.le)
    _ ≤ (μ.real s)⁻¹ * ((C * μ.real s) * ε) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvol hε) (inv_nonneg.mpr hs0.le)
    _ = C * ε := by field_simp

variable [MetricSpace X] [BorelSpace X] [ProperSpace X]
  (hQ : QuadraticCheegerEnergy μ)

theorem meanGram_sub_id_norm_le_of_subset {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    {s t : Set X} (hs : MeasurableSet s) (hst : s ⊆ t)
    (hszero : μ s ≠ 0) (hsfin : μ s ≠ ∞) (htzero : μ t ≠ 0) (htfin : μ t ≠ ∞)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hvol : μ.real t ≤ C * μ.real s)
    (herror : ∀ i j : Fin n, (μ.real t)⁻¹ * ∫ x in t,
      |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ ε) :
    ‖sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) s hs -
      ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤ (n : ℝ) ^ 2 * (C * ε) := by
  have hs0 : 0 < μ.real s := ENNReal.toReal_pos hszero hsfin
  have ht0 : 0 < μ.real t := ENNReal.toReal_pos htzero htfin
  apply meanGram_sub_id_norm_le μ hQ u s hs hszero hsfin (mul_nonneg hC hε)
  intro i j
  have hf : IntegrableOn (fun x => |localGamma μ hQ (u i) (u j) x -
      (if i = j then 1 else 0)|) t μ :=
    ((localGamma_memL1 μ hQ (u i) (u j)).integrableOn.sub (integrableOn_const htfin)).abs
  exact average_nonneg_le_of_subset μ hst hs0 ht0 hf (fun _ => abs_nonneg _) hε hvol (herror i j)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A common approximately orthonormal coordinate change compares the
original means, including when their smallest eigenvalues are very small. -/
theorem meanGrams_compare_from_common_normalization
    (U : E →L[ℝ] SobolevSpace μ hQ) (A : E ≃L[ℝ] E)
    (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsnorm : ‖sobolevMeanGram μ hQ (U.comp (A : E →L[ℝ] E)) s hs -
      ContinuousLinearMap.id ℝ E‖ ≤ δ)
    (htnorm : ‖sobolevMeanGram μ hQ (U.comp (A : E →L[ℝ] E)) t ht -
      ContinuousLinearMap.id ℝ E‖ ≤ δ) (v : E) :
    (1 - δ) * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ ≤
        (1 + δ) * ⟪v, sobolevMeanGram μ hQ U t ht v⟫_ℝ ∧
    (1 - δ) * ⟪v, sobolevMeanGram μ hQ U t ht v⟫_ℝ ≤
        (1 + δ) * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ := by
  have hform (b : Set X) (hb : MeasurableSet b) :
      ⟪A.symm v, sobolevMeanGram μ hQ (U.comp (A : E →L[ℝ] E)) b hb (A.symm v)⟫_ℝ =
        ⟪v, sobolevMeanGram μ hQ U b hb v⟫_ℝ := by
    rw [sobolevMeanGram_comp]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  have hslo := inner_lower_of_sub_id_norm _ hsnorm (A.symm v)
  have hsup := inner_upper_of_sub_id_norm _ hsnorm (A.symm v)
  have htlo := inner_lower_of_sub_id_norm _ htnorm (A.symm v)
  have htup := inner_upper_of_sub_id_norm _ htnorm (A.symm v)
  rw [hform s hs] at hslo hsup
  rw [hform t ht] at htlo htup
  have hpos : 0 ≤ 1 + δ := by linarith
  have hnonneg : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  constructor
  · exact (mul_le_mul_of_nonneg_left hsup hnonneg).trans
      (by nlinarith [mul_le_mul_of_nonneg_left htlo hpos])
  · exact (mul_le_mul_of_nonneg_left htup hnonneg).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hslo hpos])

end RegularPointCoordinates

end

end OAI
