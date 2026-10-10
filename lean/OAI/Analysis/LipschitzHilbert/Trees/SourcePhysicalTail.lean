import OAI.Analysis.LipschitzHilbert.Trees.SourceLineRescale
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferencePolynomialTail

namespace OAI

/-! Restore the physical horizontal variable and the exact coefficient
normalization after proving the normalized reference tail. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LipschitzHilbert

/-- An exact normalized-packet identity transfers a relative tail to the
original physical interval. The interval scale introduces no loss. -/
theorem source_physical_tail (r c u H δ small large : ℝ) (hr : 0 < r) (hc : 0 < c)
    (F Q : ℝ → ℝ) (hF : Measurable F) (heq : ∀ x, F (r*x) = c*Q x)
    (hthreshold : c*small ≤ large)
    (htail : (volume.restrict (Ico u (u+H))) {x | small ≤ |Q x|} ≤
      ENNReal.ofReal δ*ENNReal.ofReal H) :
    (volume.restrict (Ico (r*u) (r*(u+H)))) {x | large ≤ |F x|} ≤
      ENNReal.ofReal δ*ENNReal.ofReal (r*H) := by
  apply source_line_rescale_tail r u H δ hr _ (measurableSet_le measurable_const (by simpa only [Real.norm_eq_abs] using hF.norm))
  apply (measure_mono (show (fun x : ℝ => r*x) ⁻¹' {x | large ≤ |F x|} ⊆
    {x | small ≤ |Q x|} from ?_)).trans htail
  intro x hx
  change large ≤ |F (r*x)| at hx
  rw [heq x,abs_mul,abs_of_pos hc] at hx
  exact (mul_le_mul_iff_right₀ hc).mp (hthreshold.trans hx)

/-- The exact factor in the physical mixed-packet identity is
`P.constant * pi^2`. Restoring it only changes the fixed polynomial exponent. -/
theorem eventually_source_physical_threshold (a : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ C : ℝ, C ≤ L^a →
      (C*Real.pi^2)*L^(a+4) ≤ L^(2*a+5) := by
  filter_upwards [eventually_ge_atTop (max 1 (Real.pi^2))] with L hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  intro C hC
  calc
    _ ≤ (L^a*L)*L^(a+4) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL0.le _)
      exact mul_le_mul hC ((le_max_right _ _).trans hlarge)
        (sq_nonneg _) (Real.rpow_nonneg hL0.le _)
    _ = (L^a*L^(1:ℝ))*L^(a+4) := by rw [Real.rpow_one]
    _ = _ := by
      rw [← Real.rpow_add hL0,← Real.rpow_add hL0]
      congr 1
      ring

end LipschitzHilbert

end

end OAI
