import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Group.Bounded
import OAI.Geometry.NodalSets.Waves.WaveEstimates

namespace OAI

namespace Yau.Waves
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_dilate_translate {beta : E → F} (hb : ContDiff ℝ ∞ beta)
    (s : ℝ) (y x : E) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z ↦ beta (s • (z - y))) x =
      s ^ k • iteratedFDeriv ℝ k beta (s • (x - y)) := by
  rw [iteratedFDeriv_comp_sub (f := fun z ↦ beta (s • z))]
  exact congrFun (iteratedFDeriv_comp_const_smul s
    (hb.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))) (x - y)

theorem compact_smooth_derivative_bound {beta : E → F} (hb : ContDiff ℝ ∞ beta)
    (hs : HasCompactSupport beta) (k : ℕ) :
    ∃ C > 0, ∀ x, ‖iteratedFDeriv ℝ k beta x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hs.iteratedFDeriv k).exists_bound_of_continuous
    (hb.continuous_iteratedFDeriv (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  exact (hC x).trans (le_max_left _ _)

theorem scaled_compact_derivative_bound {beta : E → F} (hb : ContDiff ℝ ∞ beta)
    (hs : HasCompactSupport beta) (k : ℕ) :
    ∃ C > 0, ∀ N : ℝ, 0 < N → ∀ y x : E,
      ‖iteratedFDeriv ℝ k (fun z ↦ beta (N ^ (1 / 3 : ℝ) • (z - y))) x‖ ≤
        C * N ^ ((k : ℝ) / 3) := by
  obtain ⟨C, hC, hbound⟩ := compact_smooth_derivative_bound hb hs k
  refine ⟨C, hC, ?_⟩
  intro N hN y x
  rw [iteratedFDeriv_dilate_translate hb, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.rpow_nonneg hN.le _) _)]
  have he : (N ^ (1 / 3 : ℝ)) ^ k = N ^ ((k : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [he, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hbound _) (Real.rpow_nonneg hN.le _)

variable [FiniteDimensional ℝ E]

def baseCutoff : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

def scaledCutoff (N : ℝ) (y : E) : E → ℝ :=
  fun x ↦ (baseCutoff (E := E)) (N ^ (1 / 3 : ℝ) • (x - y))

lemma scaledCutoff_contDiff (N : ℝ) (y : E) : ContDiff ℝ ∞ (scaledCutoff N y) :=
  (baseCutoff (E := E)).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)

lemma scaledCutoff_mem_Icc (N : ℝ) (y x : E) :
    scaledCutoff N y x ∈ Set.Icc (0 : ℝ) 1 := ⟨(baseCutoff (E := E)).nonneg, (baseCutoff (E := E)).le_one⟩

lemma scaledCutoff_eq_one {N : ℝ} (hN : 0 < N) (y x : E)
    (hx : ‖x - y‖ ≤ N ^ (-1 / 3 : ℝ)) : scaledCutoff N y x = 1 := by
  apply (baseCutoff (E := E)).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hN _)]
  change N ^ (1 / 3 : ℝ) * ‖x - y‖ ≤ 1
  calc
    _ ≤ N ^ (1 / 3 : ℝ) * N ^ (-1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hN.le _)
    _ = 1 := by rw [← Real.rpow_add hN]; norm_num

theorem scaledCutoff_support {N : ℝ} (hN : 0 < N) (y : E) :
    Function.support (scaledCutoff N y) = Metric.ball y (2 * N ^ (-1 / 3 : ℝ)) := by
  ext x
  change (baseCutoff (E := E)) (N ^ (1 / 3 : ℝ) • (x - y)) ≠ 0 ↔ _
  rw [← Function.mem_support, (baseCutoff (E := E)).support_eq]
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hN _)]
  change N ^ (1 / 3 : ℝ) * ‖x - y‖ < 2 ↔ ‖x - y‖ < 2 * N ^ (-1 / 3 : ℝ)
  rw [mul_comm, ← lt_div_iff₀ (Real.rpow_pos_of_pos hN _)]
  have he : N ^ (-1 / 3 : ℝ) = (N ^ (1 / 3 : ℝ))⁻¹ := by
    rw [show (-1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring, Real.rpow_neg hN.le]
  rw [he, div_eq_mul_inv]

theorem scaledCutoff_derivative_bound (k : ℕ) :
    ∃ C > 0, ∀ N : ℝ, 0 < N → ∀ y x : E,
      ‖iteratedFDeriv ℝ k (scaledCutoff N y) x‖ ≤ C * N ^ ((k : ℝ) / 3) :=
  scaled_compact_derivative_bound (baseCutoff (E := E)).contDiff (baseCutoff (E := E)).hasCompactSupport k

end
end Yau.Waves

end OAI
