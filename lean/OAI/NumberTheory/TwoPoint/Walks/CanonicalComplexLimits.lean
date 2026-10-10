import OAI.NumberTheory.TwoPoint.Bounds.ComplexGraphUpper

namespace OAI

/-! The canonical graph and centering error scales tend to zero with fixed W. -/

namespace TwoPointCorrelations

open Filter
open scoped Topology

lemma canonical_eta_tendsto_zero (W : ℝ) (hW : 0 < W) :
    Tendsto (fun L : ℝ => Real.exp (-(primeSupplyCount W L : ℝ))) atTop (𝓝 0) := by
  have hp : 0 < 1 / (1200 * W) := by positivity
  have hb := (tendsto_rpow_neg_atTop hp).const_mul (Real.exp 1)
  simp only [mul_zero] at hb
  apply squeeze_zero' (Eventually.of_forall (fun _ => (Real.exp_pos _).le)) _ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  exact primeSupplyCount_saving L W hL hW

lemma canonical_complex_error_tendsto_zero (W Cg Cc : ℝ) (hW : 0 < W) :
    Tendsto (fun L : ℝ => Cg * Real.exp (-(primeSupplyCount W L : ℝ)) +
      2 * Cc * L ^ (-3 / 40 : ℝ)) atTop (𝓝 0) := by
  have h₁ := (canonical_eta_tendsto_zero W hW).const_mul Cg
  have h₂ := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 40 by norm_num)).const_mul (2 * Cc)
  simpa only [mul_zero, zero_add, neg_div] using h₁.add h₂

end TwoPointCorrelations

end OAI
