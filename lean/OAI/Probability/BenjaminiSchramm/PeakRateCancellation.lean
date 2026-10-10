import OAI.Probability.BenjaminiSchramm.CriticalPeakComparison

namespace OAI

noncomputable section
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

lemma peak_rate_cancellation (P X K : ℝ≥0∞) (c b ε t k L r : ℝ) (hc : 0 < c)
    (hP : ENNReal.ofReal (c*Real.exp (-(b+ε)*t)) ≤ P)
    (hX : P*X ≤ K*ENNReal.ofReal (Real.exp (L*r-b*(t+k)))) :
    X ≤ ENNReal.ofReal c⁻¹*K*ENNReal.ofReal (Real.exp (L*r+ε*t-b*k)) := by
  let A := ENNReal.ofReal (c*Real.exp (-(b+ε)*t))
  let D := ENNReal.ofReal (c⁻¹*Real.exp ((b+ε)*t))
  have hDA : D*A=1 := by
    dsimp [D,A]
    rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ c⁻¹*Real.exp ((b+ε)*t))]
    have he : (c⁻¹*Real.exp ((b+ε)*t))*(c*Real.exp (-(b+ε)*t))=1 := by
      calc
        _ = (c⁻¹*c)*(Real.exp ((b+ε)*t)*Real.exp (-(b+ε)*t)) := by ring
        _ = 1 := by
          rw [inv_mul_cancel₀ hc.ne',←Real.exp_add,
            show (b+ε)*t+ -(b+ε)*t=0 by ring,Real.exp_zero,one_mul]
    rw [he,ENNReal.ofReal_one]
  calc
    _ = D*(A*X) := by rw [←mul_assoc,hDA,one_mul]
    _ ≤ D*(K*ENNReal.ofReal (Real.exp (L*r-b*(t+k)))) :=
      mul_le_mul' le_rfl ((mul_le_mul' hP le_rfl).trans hX)
    _ = _ := by
      dsimp [D]
      have he : (c⁻¹*Real.exp ((b+ε)*t))*Real.exp (L*r-b*(t+k)) =
          c⁻¹*Real.exp (L*r+ε*t-b*k) := by
        rw [mul_assoc,←Real.exp_add]
        congr 2
        ring
      calc
        _ = K*(ENNReal.ofReal (c⁻¹*Real.exp ((b+ε)*t))*
            ENNReal.ofReal (Real.exp (L*r-b*(t+k)))) := by ac_rfl
        _ = K*ENNReal.ofReal (c⁻¹*Real.exp (L*r+ε*t-b*k)) := by
          rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ c⁻¹*Real.exp ((b+ε)*t)),he]
        _ = _ := by rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]; ac_rfl

end Percolation.BenjaminiSchramm

end

end OAI
