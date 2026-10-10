import OAI.MeasureTheory.Falconer.Geometry.ProjectionCollisionMean
import OAI.MeasureTheory.Falconer.Angular.AngularUniformAbsorption

namespace OAI

/-! # Scalar absorption for the projection-test average -/

namespace Falconer

theorem projection_profile_scalar_bound {R H C F A k a sig n N : ℝ}
    (hR : 1 ≤ R) (hH : 0 < H) (hC : 0 ≤ C) (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hk : 0 ≤ k) (ha : 0 ≤ a) (hsig : 0 < sig) (hn : 0 ≤ n) (hnN : n ≤ N)
    (hcoef : (4*C+2*C*F*A)*(1+2*N) ≤ R^sig) :
    C*(2*R^(500*sig)/H)*(2+n*(F*(A*R^(k+a*sig))*R^sig)) ≤
      (1/H)*R^(k+(a+502)*sig) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hpower : 1 ≤ R^(k+(a+1)*sig) := Real.one_le_rpow hR (by positivity)
  have hinner : 2+n*(F*(A*R^(k+a*sig))*R^sig) ≤
      (2+n*F*A)*R^(k+(a+1)*sig) := by
    have he : R^(k+a*sig)*R^sig = R^(k+(a+1)*sig) := by
      rw [← Real.rpow_add hRp]
      congr 1
      ring
    calc
      _ = 2+(n*F*A)*(R^(k+a*sig)*R^sig) := by ring
      _ = 2+(n*F*A)*R^(k+(a+1)*sig) := by rw [he]
      _ ≤ 2*R^(k+(a+1)*sig)+(n*F*A)*R^(k+(a+1)*sig) := by nlinarith
      _ = _ := by ring
  have hpoly : 2*C*(2+n*F*A) ≤ (4*C+2*C*F*A)*(1+2*N) := by
    have hN : 0 ≤ N := hn.trans hnN
    have hn' : n ≤ 2*N := by linarith
    have hc : 0 ≤ 2*C*F*A := by positivity
    have hh := mul_le_mul_of_nonneg_left hn' hc
    have hh' : 0 ≤ 4*C*(2*N) := by positivity
    nlinarith
  calc
    _ ≤ C*(2*R^(500*sig)/H)*((2+n*F*A)*R^(k+(a+1)*sig)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (1/H)*(2*C*(2+n*F*A))*R^(k+(a+501)*sig) := by
      have he : R^(500*sig)*R^(k+(a+1)*sig) = R^(k+(a+501)*sig) := by
        rw [← Real.rpow_add hRp]
        congr 1
        ring
      rw [← he]
      ring
    _ ≤ (1/H)*R^sig*R^(k+(a+501)*sig) := by
      gcongr
      exact hpoly.trans hcoef
    _ = _ := by
      rw [mul_assoc,← Real.rpow_add hRp]
      congr 2
      ring

end Falconer

end OAI
