import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftPowers
import OAI.Analysis.IrrationalRotation.Spectral.WeightedShiftPolar
import OAI.Analysis.IrrationalRotation.Rotation.PositiveDiagonalFields

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal

namespace Invariant233.WeightedShift

theorem diagonal_isSelfAdjoint_of_real (w : Weight) (a : ℤ → ℝ)
    (hw : ∀ k, w k = (a k : ℂ)) : IsSelfAdjoint (diagonal w) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro ξ η
  change ⟪diagonal w ξ, η⟫_ℂ = ⟪ξ, diagonal w η⟫_ℂ
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp only [diagonal_apply, hw, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem diagonal_isPositive_of_nonneg (w : Weight) (a : ℤ → ℝ)
    (hw : ∀ k, w k = (a k : ℂ)) (ha : ∀ k, 0 ≤ a k) :
    (diagonal w).IsPositive := by
  refine ContinuousLinearMap.isPositive_def'.mpr
    ⟨diagonal_isSelfAdjoint_of_real w a hw, ?_⟩
  intro ξ
  change 0 ≤ (⟪diagonal w ξ, ξ⟫_ℂ).re
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner (diagonal w ξ) ξ)]
  apply tsum_nonneg
  intro k
  rw [diagonal_apply, hw k]
  change 0 ≤ (⟪(a k : ℂ) • ξ k, ξ k⟫_ℂ).re
  rw [inner_smul_left]
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_nonneg (ha k)
  simp only [RCLike.inner_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (ξ k).re, sq_nonneg (ξ k).im]

theorem diagonal_nonneg_of_real_coordinates (w : Weight) (a : ℤ → ℝ)
    (hw : ∀ k, w k = (a k : ℂ)) (ha : ∀ k, 0 ≤ a k) :
    0 ≤ diagonal w :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (diagonal_isPositive_of_nonneg w a hw ha)

theorem diagonal_ker_eq_bot (w : Weight) (hw : ∀ k, w k ≠ 0) :
    (diagonal w).ker = ⊥ := LinearMap.ker_eq_bot.mpr (PolarSupport.diagonal_operator_injective w hw)

theorem operator_ker_eq_bot (w : Weight) (hw : ∀ k, w k ≠ 0) :
    (operator w).ker = ⊥ := LinearMap.ker_eq_bot.mpr (PolarSupport.operator_injective w hw)

theorem diagonal_denseRange_of_real (w : Weight) (a : ℤ → ℝ)
    (hw : ∀ k, w k = (a k : ℂ)) (hne : ∀ k, w k ≠ 0) :
    DenseRange (diagonal w) := by
  change Dense ((diagonal w).range : Set Hilbert)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hker : (diagonal w).ker = ⊥ := LinearMap.ker_eq_bot.mpr (PolarSupport.diagonal_operator_injective w hne)
  have horth := (diagonal w).orthogonal_ker
  rw [(diagonal_isSelfAdjoint_of_real w a hw).adjoint_eq, hker,
    Submodule.bot_orthogonal_eq_top] at horth
  exact horth.symm

theorem diagonal_single (w : Weight) (k : ℤ) :
    diagonal w (lp.single 2 k (1 : ℂ)) = w k • lp.single 2 k (1 : ℂ) := by
  ext j
  by_cases hj : j = k
  · subst j
    simp [diagonal_apply]
  · simp [diagonal_apply, hj]

theorem norm_coordinate_vector (k : ℤ) :
    ‖(lp.single 2 k (1 : ℂ) : Hilbert)‖ = 1 := by
  simp [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

theorem ae_strict_diagonal_of_real_weightedShift
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
    {σ : Y → Y} (hσ : Ergodic σ μ)
    {p : Y → Hilbert →L[ℂ] Hilbert} {w : Y → Weight} {a : Y → ℤ → ℝ}
    (hp : ∀ᵐ y ∂μ, IsStarProjection (p y))
    (hw : ∀ᵐ y ∂μ, ∀ k, w y k = (a y k : ℂ))
    (ha : ∀ᵐ y ∂μ, a y 0 ≠ 0)
    (hcov : ∀ᵐ y ∂μ, p (σ y) =
      (shift 1).symm.toLinearIsometry.toContinuousLinearMap * p y *
      (shift 1).toLinearIsometry.toContinuousLinearMap)
    (hinv : ∀ᵐ y ∂μ, (1 - p y) * operator (w y) * p y = 0)
    (hr : Measurable fun y =>
      (⟪(lp.single 2 0 (1 : ℂ) : Hilbert), p y (lp.single 2 0 (1 : ℂ))⟫_ℂ).re)
    (hmean0 : 0 < ∫ y,
      (⟪(lp.single 2 0 (1 : ℂ) : Hilbert), p y (lp.single 2 0 (1 : ℂ))⟫_ℂ).re ∂μ)
    (hmean1 : (∫ y,
      (⟪(lp.single 2 0 (1 : ℂ) : Hilbert), p y (lp.single 2 0 (1 : ℂ))⟫_ℂ).re ∂μ) < 1) :
    ∀ᵐ y ∂μ,
      0 < (⟪(lp.single 2 0 (1 : ℂ) : Hilbert), p y (lp.single 2 0 (1 : ℂ))⟫_ℂ).re ∧
      (⟪(lp.single 2 0 (1 : ℂ) : Hilbert), p y (lp.single 2 0 (1 : ℂ))⟫_ℂ).re < 1 := by
  let S : (Hilbert →L[ℂ] Hilbert)ˣ :=
    { val := (shift 1).toLinearIsometry.toContinuousLinearMap
      inv := (shift 1).symm.toLinearIsometry.toContinuousLinearMap
      val_inv := by
        apply ContinuousLinearMap.ext
        intro ξ
        exact (shift 1).apply_symm_apply ξ
      inv_val := by
        apply ContinuousLinearMap.ext
        intro ξ
        exact (shift 1).symm_apply_apply ξ }
  apply Fields.ae_strict_projection_diagonal_of_weighted_shift
    (D := fun y => diagonal (w y)) (f := fun y => a y 0) hσ S
    (norm_coordinate_vector 0) hp ?_ ha ?_ hcov ?_ hr hmean0 hmean1
  · filter_upwards [hw] with y hwy
    exact diagonal_isSelfAdjoint_of_real (w y) (a y) hwy
  · filter_upwards [hw] with y hwy
    simpa only [hwy 0] using diagonal_single (w y) 0
  · exact hinv

end Invariant233.WeightedShift

end

end OAI
