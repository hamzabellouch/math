import OAI.NumberTheory.CubicMoment.Estimates.RadialCubing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! The zero-frequency transform of the hyperbolic Eisenstein kernel.
This fixes the archimedean normalization before taking a residue. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma integral_Ioi_translate (f : ℝ → ℂ) (b : ℝ) :
    (∫ x in Ioi (0:ℝ), f (x+b)) = ∫ x in Ioi b, f x := by
  have h := integral_add_right_eq_self (μ := volume) ((Ioi b).indicator f) b
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioi]
  convert h using 1
  apply integral_congr_ae
  filter_upwards with x
  have hx : x+b ∈ Ioi b ↔ x ∈ Ioi (0:ℝ) := by
    simp only [mem_Ioi]
    constructor <;> intro h <;> linarith
  simp only [indicator, hx]

lemma cubicTheta_radial_power_integral {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) :
    (∫ z : ℂ, ((Complex.normSq z+v^2:ℝ):ℂ)^(-s)) =
      (Real.pi:ℂ)*((v^2:ℝ):ℂ)^(1-s)/(s-1) := by
  have hrad : (∫ z : ℂ, ((Complex.normSq z+v^2:ℝ):ℂ)^(-s)) =
      (2*Real.pi:ℂ)*(∫ r in Ioi (0:ℝ),
        (r:ℂ)*((r^2+v^2:ℝ):ℂ)^(-s)) := by
    simpa only [Complex.normSq_eq_norm_sq] using
      complex_radial_integral (fun r => ((r^2+v^2:ℝ):ℂ)^(-s))
  have hsq := integral_comp_rpow_Ioi
    (fun u : ℝ => ((u+v^2:ℝ):ℂ)^(-s)) (show (2:ℝ) ≠ 0 by norm_num)
  have hsq' : (2:ℂ)*(∫ r in Ioi (0:ℝ),
      (r:ℂ)*((r^2+v^2:ℝ):ℂ)^(-s)) =
      ∫ u in Ioi (0:ℝ), ((u+v^2:ℝ):ℂ)^(-s) := by
    rw [← integral_const_mul]
    convert hsq using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    norm_num [Complex.real_smul, Real.rpow_ofNat]
    ring
  rw [hrad, show (2*Real.pi:ℂ) = (Real.pi:ℂ)*2 by ring, mul_assoc, hsq',
    integral_Ioi_translate (fun x : ℝ => (x:ℂ)^(-s)),
    integral_Ioi_cpow_of_lt (show (-s).re < -1 by simpa using neg_lt_neg hs)
      (sq_pos_of_pos hv)]
  rw [show -s+1 = -(s-1) by ring, neg_div_neg_eq, neg_sub]
  ring

end CubicFirstMoment

end

end OAI
