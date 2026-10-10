import OAI.Geometry.RCD.Coordinates.LinearNormalization
import OAI.Geometry.RCD.Coordinates.MatrixNormConversion

namespace OAI

/-! # From averaged splitting-map errors to exact Gram normalization -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The normalized integral of the absolute error controls the error of
its mean on a positive finite-measure set. -/
theorem abs_average_sub_const_le (s : Set X)
    (hzero : μ s ≠ 0) (hfin : μ s ≠ ∞) {f : X → ℝ}
    (hf : IntegrableOn f s μ) (c : ℝ) :
    |(μ.real s)⁻¹ * (∫ x in s, f x ∂μ) - c| ≤
      (μ.real s)⁻¹ * ∫ x in s, |f x - c| ∂μ := by
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hfin.lt_top⟩
  have hμ : μ.real s ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hzero, hfin⟩
  have he : (μ.real s)⁻¹ * (∫ x in s, f x - c ∂μ) =
      (μ.real s)⁻¹ * (∫ x in s, f x ∂μ) - c := by
    rw [integral_sub hf (integrable_const c)]
    simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
    field_simp
  have hn : 0 ≤ (μ.real s)⁻¹ := by positivity
  rw [← he, abs_mul, abs_of_nonneg hn]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs
    hn

variable [MetricSpace X] [BorelSpace X] [ProperSpace X]
  (hQ : QuadraticCheegerEnergy μ)

/-- The first-order averaged Gram errors in a splitting-map definition
bound the actual mean Gram operator in Euclidean operator norm. -/
theorem meanGram_sub_id_norm_le {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (hs : MeasurableSet s) (hzero : μ s ≠ 0) (hfin : μ s ≠ ∞)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (herror : ∀ i j : Fin n,
      (μ.real s)⁻¹ * ∫ x in s,
        |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ epsilon) :
    ‖sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) s hs -
      ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤ (n : ℝ) ^ 2 * epsilon := by
  apply euclidean_operator_norm_le_of_entries _ hepsilon
  intro i j
  have hc := sobolevMeanGram_column_entry μ hQ u s hs j i
  have he : (sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) s hs
      (EuclideanSpace.single j 1)) i =
      (μ.real s)⁻¹ * ∫ x in s, localGamma μ hQ (u j) (u i) x ∂μ := by
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] using hc
  have hb := abs_average_sub_const_le μ s hzero hfin
    (localGamma_memL1 μ hQ (u j) (u i)).integrableOn (if j = i then 1 else 0)
  have havg := hb.trans (herror j i)
  simpa only [sub_apply, ContinuousLinearMap.id_apply, PiLp.sub_apply,
    PiLp.single_apply, he, eq_comm] using havg

/-- Small operator error yields the quantitative lower bound for the
quadratic form without assuming that the Gram operator is invertible. -/
theorem inner_lower_of_sub_id_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : E →L[ℝ] E) {delta : ℝ}
    (hbound : ‖Q - ContinuousLinearMap.id ℝ E‖ ≤ delta) (v : E) :
    (1 - delta) * ‖v‖ ^ 2 ≤ ⟪v, Q v⟫_ℝ := by
  have hn := (Q - ContinuousLinearMap.id ℝ E).le_opNorm v
  have hn' := hn.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg v))
  have hc := (abs_real_inner_le_norm v ((Q - ContinuousLinearMap.id ℝ E) v)).trans
    (mul_le_mul_of_nonneg_left hn' (norm_nonneg v))
  simp only [sub_apply, ContinuousLinearMap.id_apply, inner_sub_right,
    real_inner_self_eq_norm_sq] at hc
  have hl := (abs_le.mp hc).1
  nlinarith

/-- The matching upper quadratic-form bound. -/
theorem inner_upper_of_sub_id_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : E →L[ℝ] E) {delta : ℝ}
    (hbound : ‖Q - ContinuousLinearMap.id ℝ E‖ ≤ delta) (v : E) :
    ⟪v, Q v⟫_ℝ ≤ (1 + delta) * ‖v‖ ^ 2 := by
  have hn := (Q - ContinuousLinearMap.id ℝ E).le_opNorm v
  have hn' := hn.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg v))
  have hc := (abs_real_inner_le_norm v ((Q - ContinuousLinearMap.id ℝ E) v)).trans
    (mul_le_mul_of_nonneg_left hn' (norm_nonneg v))
  simp only [sub_apply, ContinuousLinearMap.id_apply, inner_sub_right,
    real_inner_self_eq_norm_sq] at hc
  have hl := (abs_le.mp hc).2
  nlinarith

/-- First-order Gram error bounds control both an exact normalizer and its
inverse. No closeness or norm bound for the chosen normalizer is assumed. -/
theorem exact_mean_normalizer_bounds {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (s : Set X) (hs : MeasurableSet s) (hzero : μ s ≠ 0) (hfin : μ s ≠ ∞)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (herror : ∀ i j : Fin n,
      (μ.real s)⁻¹ * ∫ x in s,
        |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ epsilon)
    (A : Euclidean n ≃L[ℝ] Euclidean n)
    (hA : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u) s hs A)
    (v : Euclidean n) :
    (1 - (n : ℝ) ^ 2 * epsilon) * ‖A v‖ ^ 2 ≤ ‖v‖ ^ 2 ∧
      ‖A.symm v‖ ^ 2 ≤ (1 + (n : ℝ) ^ 2 * epsilon) * ‖v‖ ^ 2 := by
  have hb := meanGram_sub_id_norm_le μ hQ u s hs hzero hfin hepsilon herror
  constructor
  · have hl := inner_lower_of_sub_id_norm _ hb (A v)
    rw [meanGram_energy_of_exact_normalization μ hQ (sobolevColumnMap μ hQ u) s hs A hA,
      ContinuousLinearEquiv.symm_apply_apply] at hl
    exact hl
  · have hu := inner_upper_of_sub_id_norm _ hb v
    rwa [meanGram_energy_of_exact_normalization μ hQ (sobolevColumnMap μ hQ u) s hs A hA] at hu

/-- The averaged first-order splitting-map estimate alone constructs an
exact mean normalizer once the dimension-dependent error is less than one. -/
theorem exists_exact_mean_normalization_of_gram_error {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (s : Set X) (hs : MeasurableSet s)
    (hzero : μ s ≠ 0) (hfin : μ s ≠ ∞) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsmall : (n : ℝ) ^ 2 * epsilon < 1)
    (herror : ∀ i j : Fin n,
      (μ.real s)⁻¹ * ∫ x in s,
        |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ epsilon) :
    ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
      IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u) s hs A := by
  apply exists_exact_mean_normalization μ hQ (sobolevColumnMap μ hQ u) s hs
  intro v hv
  have hlow := inner_lower_of_sub_id_norm _
    (meanGram_sub_id_norm_le μ hQ u s hs hzero hfin hepsilon herror) v
  exact (mul_pos (sub_pos.mpr hsmall) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le hlow

end RegularPointCoordinates

end

end OAI
