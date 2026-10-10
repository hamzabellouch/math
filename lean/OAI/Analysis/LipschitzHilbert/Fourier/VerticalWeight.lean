import OAI.Analysis.LipschitzHilbert.Packets.PolynomialPacket
import OAI.Analysis.LipschitzHilbert.Packets.LinePacketReplacement

namespace OAI

/-! Absorb the transverse factor of the top polynomial into fixed packet
decay. The resulting constant is uniform over the reference line. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem vertical_weighted_envelope (y s a W R X : ℝ) (q n : ℕ)
    (hW : 0 < W) (hR : 0 < R) (hWR : W ≤ R) (hs : |s-a| ≤ R) (hX : 0 ≤ X) :
    polynomialWeight a R q y * (X*lineEnvelope s W (n+2*q) y) ≤
      (16^q*X)*lineEnvelope s W n y := by
  have h := mul_le_mul_of_nonneg_left
    (polynomialWeight_mul_envelope y s a W R q n hW hR hWR hs) hX
  convert h using 1 <;> ring

theorem vertical_weighted_wave (f : SchwartzMap ℝ ℂ)
    (y s a W R X : ℝ) (q n : ℕ)
    (hW : 0 < W) (hR : 0 < R) (hWR : W ≤ R) (hs : |s-a| ≤ R) (hX : 0 ≤ X)
    (x : ℝ) (hf : ‖f x‖ ≤ X*lineEnvelope s W (n+2*q) y) :
    ‖((polynomialWeight a R q y : ℂ) • f) x‖ ≤
      (16^q*X)*lineEnvelope s W n y := by
  rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans (polynomialWeight_one_le a R q y))]
  exact (mul_le_mul_of_nonneg_left hf
    (zero_le_one.trans (polynomialWeight_one_le a R q y))).trans
      (vertical_weighted_envelope y s a W R X q n hW hR hWR hs hX)

theorem vertical_weighted_derivative (f : SchwartzMap ℝ ℂ)
    (y s a W R X : ℝ) (q n : ℕ)
    (hW : 0 < W) (hR : 0 < R) (hWR : W ≤ R) (hs : |s-a| ≤ R) (hX : 0 ≤ X)
    (x : ℝ) (hf : ‖deriv f x‖ ≤ X*lineEnvelope s W (n+2*q) y) :
    ‖deriv ((polynomialWeight a R q y : ℂ) • f) x‖ ≤
      (16^q*X)*lineEnvelope s W n y := by
  have hd := (f.differentiable x).hasDerivAt.const_mul (polynomialWeight a R q y : ℂ)
  change ‖deriv (fun t => (polynomialWeight a R q y : ℂ)*f t) x‖ ≤ _
  rw [hd.deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans (polynomialWeight_one_le a R q y))]
  exact (mul_le_mul_of_nonneg_left hf
    (zero_le_one.trans (polynomialWeight_one_le a R q y))).trans
      (vertical_weighted_envelope y s a W R X q n hW hR hWR hs hX)

end LipschitzHilbert

end

end OAI
