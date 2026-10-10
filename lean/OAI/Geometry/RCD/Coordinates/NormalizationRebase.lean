import OAI.Geometry.RCD.Coordinates.FiniteNormalizerGrowth

namespace OAI

/-! # Rebasing all exact normalizers in one working-scale frame -/

open Set MeasureTheory

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] [CompleteSpace E] in
/-- Changing the original working frame does not change any of the
subsequently normalized scalar functions. -/
theorem normalized_column_rebase (U : E →L[ℝ] SobolevSpace μ hQ)
    (T S : E ≃L[ℝ] E) :
    (U.comp (T : E →L[ℝ] E)).comp (S.trans T.symm : E →L[ℝ] E) =
      U.comp (S : E →L[ℝ] E) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- Exact mean normalization transports through a working-frame change. -/
theorem exact_mean_normalization_rebase (U : E →L[ℝ] SobolevSpace μ hQ)
    (T S : E ≃L[ℝ] E) (s : Set X) (hs : MeasurableSet s)
    (hS : IsExactMeanNormalization μ hQ U s hs S) :
    IsExactMeanNormalization μ hQ (U.comp (T : E →L[ℝ] E)) s hs (S.trans T.symm) := by
  change sobolevMeanGram μ hQ ((U.comp (T : E →L[ℝ] E)).comp
    (S.trans T.symm : E →L[ℝ] E)) s hs = ContinuousLinearMap.id ℝ E
  rw [normalized_column_rebase]
  exact hS

omit [BorelSpace X] [ProperSpace X] [CompleteSpace E] in
/-- The operation agrees componentwise with the actual transformed columns. -/
theorem transformedColumn_rebase {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (T S : Euclidean n ≃L[ℝ] Euclidean n) :
    transformedColumn μ hQ (transformedColumn μ hQ u T) (S.trans T.symm) =
      transformedColumn μ hQ u S := by
  funext i
  simp only [transformedColumn, sobolevColumnMap_transformed,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]

omit [ProperSpace X] in
/-- First-order splitting bounds are exactly preserved in every rebased
normalizer, including the same scalar representatives. -/
theorem firstOrderSplitting_rebase {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (T S : Euclidean n ≃L[ℝ] Euclidean n) (p : X) (r ε : ℝ) (w : X → Euclidean n)
    (h : FirstOrderSplittingOn μ hQ p r ε (transformedColumn μ hQ u S) w) :
    FirstOrderSplittingOn μ hQ p r ε
      (transformedColumn μ hQ (transformedColumn μ hQ u T) (S.trans T.symm)) w := by
  rw [transformedColumn_rebase]
  exact h

/-- The scalar regularizer has a uniform bound over the complete finite
range whenever its outer dyadic radius lies inside the working radius. -/
theorem dyadic_regularizer_le_working_radius {r R lambda : ℝ} (hr : 0 ≤ r)
    (k : ℕ) (hR : (2 : ℝ) ^ k * r ≤ R) :
    |lambda * r ^ 2| * (2 : ℝ) ^ k ≤ |lambda| * R ^ 2 := by
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hrR : r ≤ R := by nlinarith
  have hRR : 0 ≤ R := hr.trans hrR
  have hprod := mul_le_mul hR hrR hr hRR
  rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
  nlinarith [mul_le_mul_of_nonneg_left hprod (abs_nonneg lambda)]

/-- Keeping the dyadic room in the estimate makes the regularizer vanish
at fine scales even when the working radius and regularizer are fixed. -/
theorem dyadic_regularizer_le_geometric {r R lambda : ℝ} (hr : 0 ≤ r)
    (k : ℕ) (hR : (2 : ℝ) ^ k * r ≤ R) :
    |lambda * r ^ 2| * (2 : ℝ) ^ k ≤
      (|lambda| * R ^ 2) * (1 / 2 : ℝ) ^ k := by
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  have hR0 : 0 ≤ R := (mul_nonneg hp.le hr).trans hR
  have hs : ((2 : ℝ) ^ k * r) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hp.le hr) hR0).mpr hR
  have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg lambda)
  have hd := (div_le_div_iff_of_pos_right hp).mpr hm
  calc
    _ = |lambda| * ((2 : ℝ) ^ k * r) ^ 2 / (2 : ℝ) ^ k := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
      field_simp
    _ ≤ |lambda| * R ^ 2 / (2 : ℝ) ^ k := hd
    _ = _ := by rw [div_pow]; ring

end RegularPointCoordinates

end

end OAI
