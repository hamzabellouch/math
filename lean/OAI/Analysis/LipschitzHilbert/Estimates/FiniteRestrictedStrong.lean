import OAI.Analysis.LipschitzHilbert.Estimates.DyadicMeasureClass
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! The finite-amplitude restricted-to-strong estimate from Section 2.
The matrix entries are the restricted bilinear pairings. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def restrictedStrongConstant : ℝ :=
  1+32*measureClassLogConstant*(∑' k, measureClassKernel k)

theorem restrictedStrongConstant_pos : 0<restrictedStrongConstant := by
  have hK : 0≤∑' k, measureClassKernel k := tsum_nonneg measureClassKernel_nonneg
  have hC : 0≤measureClassLogConstant := by unfold measureClassLogConstant; positivity
  unfold restrictedStrongConstant
  positivity

theorem finite_restricted_strong (I J : Finset ℤ) (m n : ℤ → ℝ)
    (B : ℤ → ℤ → ℂ) (C : ℝ) (hC : 0≤C)
    (hm : ∀ i∈I, 0<m i) (hn : ∀ j∈J, 0<n j)
    (hB : ∀ i∈I, ∀ j∈J, ‖B i j‖≤
      C*((1+|Real.log (m i/n j)|)^3)⁻¹*Real.sqrt (m i)*Real.sqrt (n j)) :
    ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j‖≤
      C*restrictedStrongConstant*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2)*
        Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2) := by
  have hnum := finite_log_amplitude_sum I J m n
    (fun i => dyadicMeasureClass (m i)) (fun j => dyadicMeasureClass (n j)) hm hn
    (fun i hi => (dyadicMeasureClass_bounds (hm i hi)).1)
    (fun i hi => (dyadicMeasureClass_bounds (hm i hi)).2.le)
    (fun j hj => (dyadicMeasureClass_bounds (hn j hj)).1)
    (fun j hj => (dyadicMeasureClass_bounds (hn j hj)).2.le)
  have hmajor : ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j‖≤
      C*(∑ i∈I, ∑ j∈J, ((1+|Real.log (m i/n j)|)^3)⁻¹*
        ((2:ℝ)^i*Real.sqrt (m i))*((2:ℝ)^j*Real.sqrt (n j))) := by
    calc
      _ ≤ ∑ i∈I, ‖∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j‖ := norm_sum_le _ _
      _ ≤ ∑ i∈I, ∑ j∈J, ‖((2:ℝ)^i*(2:ℝ)^j) • B i j‖ :=
        Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i∈I, ∑ j∈J, C*(((1+|Real.log (m i/n j)|)^3)⁻¹*
          ((2:ℝ)^i*Real.sqrt (m i))*((2:ℝ)^j*Real.sqrt (n j))) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤(2:ℝ)^i*(2:ℝ)^j)]
        calc
          _ ≤ ((2:ℝ)^i*(2:ℝ)^j)*
              (C*((1+|Real.log (m i/n j)|)^3)⁻¹*Real.sqrt (m i)*Real.sqrt (n j)) :=
            mul_le_mul_of_nonneg_left (hB i hi j hj) (by positivity)
          _ = _ := by ring
      _ = _ := by simp only [Finset.mul_sum]
  apply hmajor.trans
  calc
    _ ≤ C*((32*measureClassLogConstant*(∑' k, measureClassKernel k))*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2)*
        Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2)) :=
      mul_le_mul_of_nonneg_left hnum hC
    _ ≤ C*restrictedStrongConstant*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2)*
        Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2) := by
      dsimp only [restrictedStrongConstant]
      nlinarith only [mul_nonneg hC (mul_nonneg
        (Real.sqrt_nonneg (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2))
        (Real.sqrt_nonneg (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2)))]

end LipschitzHilbert

end

end OAI
