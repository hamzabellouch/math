import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFixedOrderThreshold

namespace OAI

/-! The grid scale-ratio threshold has a polynomial reciprocal. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

def geometricScaleThreshold (a E : ℝ) (e : ℕ) (x : ℝ) : ℝ :=
  min 1 ((a-a/2)/(2*(E*x^e)))

lemma geometricScaleThreshold_pos {a E : ℝ} (ha : 0 < a) (hE : 0 < E)
    (e : ℕ) {x : ℝ} (hx : 1 ≤ x) : 0 < geometricScaleThreshold a E e x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  unfold geometricScaleThreshold
  exact lt_min zero_lt_one (div_pos (by linarith) (by positivity))

theorem geometricScaleThreshold_inverse_polynomial {a E : ℝ} (ha : 0 < a) (hE : 0 < E) (e : ℕ) :
    HasPolynomialBound (fun x => (geometricScaleThreshold a E e x)⁻¹) := by
  have hp : HasPolynomialBound (fun x : ℝ => 1+(4*E/a)*x^e) :=
    (polynomialBound_const zero_le_one).add
      ((polynomialBound_const (by positivity : 0 ≤ 4*E/a)).mul (polynomialBound_id.pow e))
  apply HasPolynomialBound.of_le hp
  · intro x hx
    exact inv_nonneg.mpr (geometricScaleThreshold_pos ha hE e hx).le
  · intro x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hv : 0 < (a-a/2)/(2*(E*x^e)) := div_pos (by linarith) (by positivity)
    calc
      (geometricScaleThreshold a E e x)⁻¹ ≤ 1+((a-a/2)/(2*(E*x^e)))⁻¹ := by
        simpa only [inv_one,geometricScaleThreshold] using min_inverse_le_add zero_lt_one hv
      _ = 1+(4*E/a)*x^e := by
        rw [inv_div]
        have hhalf : a-a/2 = a/2 := by ring
        rw [hhalf]
        field_simp
        ring

end ClosedSurfaceR4.ExactCorrection

end

end OAI
