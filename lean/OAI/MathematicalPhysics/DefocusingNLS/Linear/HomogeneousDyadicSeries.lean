import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDilation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! # A quantitative dyadic criterion for membership in the faithful Y space

Summable bounds on normalized annular pieces give convergence in Y and
identify the physical representative of the sum.
-/

open MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousDyadicPiece (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (v : ℕ → HomogeneousY a k) (n : ℕ) : HomogeneousY a k :=
  homogeneousDilation a k ((2 : ℝ) ^ n) ha ha1 hk (one_le_pow₀ (by norm_num)) (v n)

theorem homogeneousDyadicPiece_norm_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (v : ℕ → HomogeneousY a k) (C : ℝ) (hC : ∀ n, ‖v n‖ ≤ C) (n : ℕ) :
    ‖homogeneousDyadicPiece a k ha ha1 hk v n‖ ≤ C * (2 ^ (-a) : ℝ) ^ n := by
  have h := homogeneousDilation_norm_le a k ((2 : ℝ) ^ n) ha ha1 hk
    (one_le_pow₀ (by norm_num)) (v n)
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (hC n) (by positivity)).trans_eq (mul_comm _ _))

theorem summable_homogeneousDyadicPiece (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (v : ℕ → HomogeneousY a k) (C : ℝ) (hC : ∀ n, ‖v n‖ ≤ C) :
    Summable (homogeneousDyadicPiece a k ha ha1 hk v) := by
  have hr : ‖(2 ^ (-a) : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact ((summable_geometric_of_norm_lt_one hr).mul_left C).of_norm_bounded
    (homogeneousDyadicPiece_norm_le a k ha ha1 hk v C hC)

theorem homogeneousDyadicSeries_norm_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (v : ℕ → HomogeneousY a k) (C : ℝ) (hC : ∀ n, ‖v n‖ ≤ C) :
    ‖∑' n, homogeneousDyadicPiece a k ha ha1 hk v n‖ ≤ C / (1 - 2 ^ (-a)) := by
  have hr : ‖(2 ^ (-a) : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  simpa only [div_eq_mul_inv] using tsum_of_norm_bounded
    ((hasSum_geometric_of_norm_lt_one hr).mul_left C)
    (homogeneousDyadicPiece_norm_le a k ha ha1 hk v C hC)

theorem homogeneousDyadicSeries_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (v : ℕ → HomogeneousY a k) (C : ℝ) (hC : ∀ n, ‖v n‖ ≤ C) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk
      (∑' n, homogeneousDyadicPiece a k ha ha1 hk v n) y =
      ∑' n, (((2 : ℝ) ^ n) ^ (-2 * a) : ℝ) *
        homogeneousPhysicalCLM a k ha ha1 hk (v n) (((2 : ℝ) ^ n)⁻¹ • y) := by
  have hsum := (homogeneousPointEvaluation a k ha ha1 hk y).map_tsum
    (summable_homogeneousDyadicPiece a k ha ha1 hk v C hC)
  change homogeneousPhysicalCLM a k ha ha1 hk
    (∑' n, homogeneousDyadicPiece a k ha ha1 hk v n) y =
      ∑' n, homogeneousPhysicalCLM a k ha ha1 hk (homogeneousDyadicPiece a k ha ha1 hk v n) y at hsum
  rw [hsum]
  apply tsum_congr
  intro n
  exact homogeneousDilation_physical a k ((2 : ℝ) ^ n) ha ha1 hk
    (one_le_pow₀ (by norm_num)) (v n) y

/-- A function reconstructed from uniformly controlled normalized annuli belongs to Y. -/
theorem exists_homogeneous_of_dyadic_representation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (v : ℕ → HomogeneousY a k) (C : ℝ) (hC : ∀ n, ‖v n‖ ≤ C)
    (Q : E → ℂ)
    (hQ : ∀ y, Q y = ∑' n, (((2 : ℝ) ^ n) ^ (-2 * a) : ℝ) *
      homogeneousPhysicalCLM a k ha ha1 hk (v n) (((2 : ℝ) ^ n)⁻¹ • y)) :
    ∃ q : HomogeneousY a k, (∀ y, homogeneousPhysicalCLM a k ha ha1 hk q y = Q y) ∧
      ‖q‖ ≤ C / (1 - 2 ^ (-a)) := by
  refine ⟨∑' n, homogeneousDyadicPiece a k ha ha1 hk v n, ?_,
    homogeneousDyadicSeries_norm_le a k ha ha1 hk v C hC⟩
  intro y
  rw [homogeneousDyadicSeries_physical a k ha ha1 hk v C hC, ← hQ]

end DefocusingNLS

end OAI
