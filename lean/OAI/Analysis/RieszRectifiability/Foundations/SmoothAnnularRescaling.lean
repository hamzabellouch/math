import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactSmoothAnnularKernel
import OAI.Analysis.RieszRectifiability.Nets.SmoothAnnularCellComparison
import OAI.Analysis.RieszRectifiability.Kernel.BlowupScalarPairing

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem annularSmoothBallCutoff_physical {d : ℕ} (a b x : Ambient d)
    (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    annularSmoothBallCutoff (a + s • b) (s * r) (mul_pos hs hr) (a + s • x) =
      annularSmoothBallCutoff b r hr x := by
  simp only [ContDiffBump.apply, annularSmoothBallCutoff, add_sub_add_left_eq_sub,
    ← smul_sub, smul_smul]
  have hratio : 2 * (s * r) / (s * r) = 2 * r / r := by field_simp
  have hcoef : (s * r)⁻¹ * s = r⁻¹ := by field_simp
  rw [hratio, hcoef]

theorem annularSmoothBallCutoff_normalized {d : ℕ} (a b x : Ambient d)
    (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    annularSmoothBallCutoff b r hr (s⁻¹ • (x - a)) =
      annularSmoothBallCutoff (a + s • b) (s * r) (mul_pos hs hr) x := by
  have hx : a + s • (s⁻¹ • (x - a)) = x := by
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    abel
  simpa only [hx] using!
    (annularSmoothBallCutoff_physical a b (s⁻¹ • (x - a)) s r hs hr).symm

theorem smoothAnnularWeight_normalized {d : ℕ} (a b x : Ambient d)
    (s r R : ℝ) (hs : 0 < s) (hr : 0 < r) (hR : 0 < R) :
    smoothAnnularWeight b r R hr hR (s⁻¹ • (x - a)) =
      smoothAnnularWeight (a + s • b) (s * r) (s * R) (mul_pos hs hr) (mul_pos hs hR) x := by
  rw [smoothAnnularWeight, smoothAnnularWeight,
    annularSmoothBallCutoff_normalized a b x s R hs hR,
    annularSmoothBallCutoff_normalized a b x s r hs hr]

theorem smoothAnnularKernel_normalized {d : ℕ} (n : ℕ) (a b x : Ambient d)
    (s r R : ℝ) (hs : 0 < s) (hr : 0 < r) (hR : 0 < R) :
    smoothAnnularKernel n b r R hr hR (s⁻¹ • (x - a)) =
      s ^ n • smoothAnnularKernel n (a + s • b) (s * r) (s * R)
        (mul_pos hs hr) (mul_pos hs hR) x := by
  have hc : s⁻¹ • ((a + s • b) - a) = b := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  have hk := kernel_normalized n a (a + s • b) x s hs
  rw [hc] at hk
  rw [smoothAnnularKernel, smoothAnnularKernel, smoothAnnularWeight_normalized a b x s r R hs hr hR, hk,
    smul_smul, smul_smul, mul_comm]

theorem smoothAnnularTransform_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a b : Ambient d) (s r R : ℝ) (hs : 0 < s) (hr : 0 < r) (hR : 0 < R) :
    smoothAnnularTransform n (blowupMeasure n μ a s) b r R hr hR =
      smoothAnnularTransform n μ (a + s • b) (s * r) (s * R)
        (mul_pos hs hr) (mul_pos hs hR) := by
  change (∫ x, smoothAnnularKernel n b r R hr hR x ∂blowupMeasure n μ a s) = _
  rw [blowupMeasure_integral n μ a s hs]
  simp_rw [smoothAnnularKernel_normalized n a b _ s r R hs hr hR]
  rw [integral_smul, smul_smul, inv_mul_cancel₀ (pow_ne_zero n hs.ne'), one_smul]
  rfl

end

end RieszRectifiability

end OAI
