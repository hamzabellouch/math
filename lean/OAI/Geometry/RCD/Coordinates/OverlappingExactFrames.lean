import OAI.Geometry.RCD.Coordinates.ExactNormalizationComparison

namespace OAI

/-! # Comparing two exact frames through their common overlap -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

private theorem overlap_square_comparison {a b g t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : t ≤ 1 / 3)
    (hlo : (1 - t) * a ≤ g) (hhi : g ≤ (1 + t) * b) : a ≤ 2 * b := by
  have hl := mul_le_mul_of_nonneg_right (show (2 / 3 : ℝ) ≤ 1 - t by linarith) ha
  have hh := mul_le_mul_of_nonneg_right (show 1 + t ≤ (4 / 3 : ℝ) by linarith) hb
  linarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The same positive overlap compares exact normalizers centered at two
points. Only the already controlled volume-ratio loss enters the bound. -/
theorem overlapping_exact_frames {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (p q : X) (R : ℝ)
    (Np Nq : Euclidean n ≃L[ℝ] Euclidean n) {ε C : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hsmall : (n : ℝ) ^ 2 * (C * ε) ≤ 1 / 3)
    (vp vq : X → Euclidean n)
    (hp : FirstOrderSplittingOn μ hQ p R ε (transformedColumn μ hQ u Np) vp)
    (hq : FirstOrderSplittingOn μ hQ q R ε (transformedColumn μ hQ u Nq) vq)
    (hep : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u) (ball p R) measurableSet_ball Np)
    (heq : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u) (ball q R) measurableSet_ball Nq)
    (S : Set X) (hS : MeasurableSet S) (hSp : S ⊆ ball p R) (hSq : S ⊆ ball q R)
    (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ∞)
    (hp0 : μ (ball p R) ≠ 0) (hpfin : μ (ball p R) ≠ ∞)
    (hq0 : μ (ball q R) ≠ 0) (hqfin : μ (ball q R) ≠ ∞)
    (hvp : μ.real (ball p R) ≤ C * μ.real S)
    (hvq : μ.real (ball q R) ≤ C * μ.real S) :
    ‖Np.symm.toContinuousLinearMap.comp Nq.toContinuousLinearMap‖ ≤ Real.sqrt 2 ∧
    ‖Nq.symm.toContinuousLinearMap.comp Np.toContinuousLinearMap‖ ≤ Real.sqrt 2 := by
  have hforms (b : Euclidean n) :
      ‖Np.symm b‖ ^ 2 ≤ 2 * ‖Nq.symm b‖ ^ 2 ∧
      ‖Nq.symm b‖ ^ 2 ≤ 2 * ‖Np.symm b‖ ^ 2 := by
    have hp' := exact_normalization_subball_bounds μ hQ u Np hp hep S hS hSp
      hS0 hSfin hp0 hpfin hC hε hvp b
    have hq' := exact_normalization_subball_bounds μ hQ u Nq hq heq S hS hSq
      hS0 hSfin hq0 hqfin hC hε hvq b
    rw [← exact_mean_inverse_norm_sq μ hQ _ (ball p R) measurableSet_ball Np hep b] at hp'
    rw [← exact_mean_inverse_norm_sq μ hQ _ (ball q R) measurableSet_ball Nq heq b] at hq'
    exact ⟨overlap_square_comparison (sq_nonneg _) (sq_nonneg _) hsmall hp'.1 hq'.2,
      overlap_square_comparison (sq_nonneg _) (sq_nonneg _) hsmall hq'.1 hp'.2⟩
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2)
    intro b
    have hh := (hforms (Nq b)).1
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hh
    change ‖Np.symm (Nq b)‖ ≤ Real.sqrt 2 * ‖b‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hh
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2)
    intro b
    have hh := (hforms (Np b)).2
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hh
    change ‖Nq.symm (Np b)‖ ≤ Real.sqrt 2 * ‖b‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hh

end RegularPointCoordinates

end

end OAI
