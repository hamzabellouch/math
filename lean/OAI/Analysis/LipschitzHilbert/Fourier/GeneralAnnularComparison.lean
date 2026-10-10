import OAI.Analysis.LipschitzHilbert.Fourier.GeneralAnnularErrors
import OAI.Analysis.LipschitzHilbert.Fourier.BandAverageComparison

namespace OAI

/-! Square comparison for arbitrary fixed positive annular endpoints. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

def annularErrorConstant (a b : ℝ) : ℝ := 4 + 2 * Real.pi * b + 4 * (2 * Real.pi * a)⁻¹

theorem annularErrorConstant_pos {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    0 < annularErrorConstant a b := by unfold annularErrorConstant; positivity

theorem annularErrorConstant_low {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (2 * Real.pi * b) ^ 2 ≤ annularErrorConstant a b ^ 2 := by
  apply pow_le_pow_left₀ (by positivity)
  unfold annularErrorConstant
  have hc : 0 ≤ (2 * Real.pi * a)⁻¹ := by positivity
  linarith

theorem annularErrorConstant_high {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    8 * (1 + (2 * Real.pi * a)⁻¹ ^ 2) ≤ annularErrorConstant a b ^ 2 := by
  have hc : 0 ≤ (2 * Real.pi * a)⁻¹ := by positivity
  have hd : 4 + 4 * (2 * Real.pi * a)⁻¹ ≤ annularErrorConstant a b := by
    unfold annularErrorConstant
    have : 0 ≤ 2 * Real.pi * b := by positivity
    linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 4 + 4 * (2 * Real.pi * a)⁻¹) hd 2
  nlinarith [sq_nonneg ((2 * Real.pi * a)⁻¹)]

theorem general_annular_square_comparison {N : ℕ} (g : FiniteLineGrid) (offset : ℕ)
    (f : Fin N → SchwartzMap ℝ ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hlow : ∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0)
    (hdepth : offset + N ≤ g.depth)
    (hmesh : ∀ i, g.meshWidth (offset + i) = ((4 : ℝ) ^ i)⁻¹) :
    (∑ i : Fin (N + 1), ∫ x, ‖partialBandSum f i.val x -
      g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖ ^ 2 ∂g.lineMeasure) ≤
      (4 * annularErrorConstant a b) ^ 2 * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  let D := annularErrorConstant a b
  have hD : 0 < D := annularErrorConstant_pos ha hb
  have h := finite_energy_schur g.lineMeasure
    (fun (i : Fin (N + 1)) (j : Fin N) => bandErrorAt g (f j) (offset + i.val) i.val j.val)
    (fun i j => bandErrorAt_memLp g (f j) (offset + i.val) i.val j.val)
    (fun i j => D * (1 / 2 : ℝ) ^ Nat.dist i.val j.val)
    (fun _ _ => mul_pos hD (by positivity))
    (fun j => ∫ x, ‖f j x‖ ^ 2) (fun j => integral_nonneg (fun _ => sq_nonneg _))
    (R := 4 * D) (C := 4 * D) (by positivity)
    (fun i => by
      rw [← Finset.mul_sum, mul_comm 4 D]
      exact mul_le_mul_of_nonneg_left (sum_half_distance_le_four N i.val) hD.le)
    (fun j => by
      simp only [Nat.dist_comm]
      rw [← Finset.mul_sum, mul_comm 4 D]
      exact mul_le_mul_of_nonneg_left (sum_half_distance_le_four (N + 1) j.val) hD.le)
    (fun i j => by
      have he := general_annular_error g (f j) ha hb
        (annularErrorConstant_low ha hb) (annularErrorConstant_high ha hb) j.val
        (hlow j) (hhigh j) (by have := i.isLt; omega) (hmesh i.val)
      have hsq : ((1 / 2 : ℝ) ^ Nat.dist i.val j.val) ^ 2 =
          (1 / 4 : ℝ) ^ Nat.dist i.val j.val := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      simpa only [mul_pow, hsq, mul_assoc] using he)
  have heq : (∑ i : Fin (N + 1), ∫ x,
      ‖∑ j, bandErrorAt g (f j) (offset + i.val) i.val j.val x‖ ^ 2 ∂g.lineMeasure) =
      ∑ i : Fin (N + 1), ∫ x, ‖partialBandSum f i.val x -
        g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖ ^ 2 ∂g.lineMeasure := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [bandErrorAt_sum g f (offset + i.val) i.val] with x hx
    rw [hx]
  rw [heq] at h
  simpa only [pow_two] using h

end LipschitzHilbert

end

end OAI
