import OAI.Analysis.LipschitzHilbert.Estimates.TwoPointEnvelope
import OAI.Analysis.LipschitzHilbert.Fourier.PlanarPositiveConvolution

namespace OAI

/-! Two-point lattice overlap after normalization by tile area. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

def tileEnvelope (a b l W : ℝ) (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  lineEnvelope a l n z.1 * lineEnvelope b W n z.2

theorem tileEnvelope_nonneg (a b l W : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    0 ≤ tileEnvelope a b l W n z :=
  mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem tileEnvelope_measurable (a b l W : ℝ) (n : ℕ) :
    Measurable (tileEnvelope a b l W n) := by
  unfold tileEnvelope lineEnvelope
  fun_prop

theorem tileEnvelope_integrable (a b l W : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hl : 0 < l) (hW : 0 < W) : Integrable (tileEnvelope a b l W n) :=
  (integrable_lineEnvelope a l hl hn).mul_prod (integrable_lineEnvelope b W hW hn)

theorem two_point_tile_kernel {ι : Type*} [Fintype ι]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site)
    (a b l W : ℝ) (hl : 0 < l) (hW : 0 < W) (z z' : ℝ × ℝ) :
    (∑ i, tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z *
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z') / (l*W) ≤
    (64 * (4*Real.pi)^2) * (lineKernel l (z.1-z'.1) * lineKernel W (z.2-z'.2)) := by
  have h := div_le_div_of_nonneg_right
    (two_point_tile_envelope site hinj a b l W z.1 z.2 z'.1 z'.2 hl hW)
    (mul_nonneg hl.le hW.le)
  convert h using 1
  · rfl
  · rw [lineKernel_shift, lineKernel_shift]
    ring

end LipschitzHilbert

end

end OAI
