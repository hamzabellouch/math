import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.HardExteriorOscillation
import OAI.Analysis.RieszRectifiability.Nets.NativeCellMeanBounds

namespace OAI

/-!
# Means of exterior hard-truncated fields

For bounded data supported outside a ball, the far-kernel estimate controls the
directional oscillation of the hard-truncated transform near the ball's center.
Averaging this estimate over a measurable set of finite positive mass gives the
same bound for the difference between its cell mean and the central value.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def exteriorCellMeanConstant (n : ℕ) (G M : ℝ) : ℝ :=
  M * vectorKernelFarConstant n * G * 2 ^ n

theorem hard_exterior_directional_difference {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G M : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (hM : 0 ≤ M) (hfM : ∀ y, |f y| ≤ M)
    (a x e : Ambient d) (he : ‖e‖ ≤ 1) (R ε : ℝ)
    (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R / 2) (hx : 2 * dist x a ≤ R)
    (hs : ∀ y, f y ≠ 0 → R ≤ dist a y) :
    |inner ℝ e (truncated n μ ε f x) - inner ℝ e (truncated n μ ε f a)| ≤
      exteriorCellMeanConstant n G M := by
  have hb := hard_truncated_exterior_difference_bound n hn G M μ hg f hf hM hfM
    a x R ε hR hε hεR hx hs
  have hK : 0 ≤ M * vectorKernelFarConstant n :=
    mul_nonneg hM (vectorKernelFarConstant_pos n).le
  have htail : 0 ≤ 2 * (G * 2 ^ n / R) := by positivity [hg.1]
  calc
    _ = |inner ℝ e (truncated n μ ε f x - truncated n μ ε f a)| := by rw [inner_sub_right]
    _ ≤ ‖truncated n μ ε f x - truncated n μ ε f a‖ := by
      have ht := norm_inner_le_norm (𝕜 := ℝ) e (truncated n μ ε f x - truncated n μ ε f a)
      simpa only [Real.norm_eq_abs, one_mul] using!
        ht.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
    _ ≤ (M * vectorKernelFarConstant n * dist x a) * (2 * (G * 2 ^ n / R)) := hb
    _ ≤ (M * vectorKernelFarConstant n * (R / 2)) * (2 * (G * 2 ^ n / R)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hK) htail
    _ = _ := by unfold exteriorCellMeanConstant; field_simp

theorem hard_exterior_cellMean_near_center {d : ℕ} {ε : ℝ} (n : ℕ) (hn : 1 ≤ n)
    (G M : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (hu : MemLp (truncated n μ ε f) 2 μ)
    (hM : 0 ≤ M) (hfM : ∀ y, |f y| ≤ M)
    (a e : Ambient d) (he : ‖e‖ ≤ 1) (R : ℝ)
    (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R / 2)
    (hs : ∀ y, f y ≠ 0 → R ≤ dist a y)
    (A : Set (Ambient d)) (hA : MeasurableSet A) (hfin : μ A < ∞) (hpos : 0 < μ.real A)
    (hnear : ∀ x ∈ A, 2 * dist x a ≤ R) :
    |cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε f x)) -
      inner ℝ e (truncated n μ ε f a)| ≤ exteriorCellMeanConstant n G M := by
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  have hi := ((memLp_inner_const_of_vector μ _ hu e).restrict A).integrable (by norm_num)
  apply cellMean_near_constant (μ.restrict A) _ hi (by simpa only [Measure.real,
    Measure.restrict_apply_univ] using! hpos)
  filter_upwards [ae_restrict_mem hA] with x hx
  exact hard_exterior_directional_difference n hn G M μ hg f hf hM hfM a x e he
    R ε hR hε hεR (hnear x hx) hs

end

end RieszRectifiability

end OAI
