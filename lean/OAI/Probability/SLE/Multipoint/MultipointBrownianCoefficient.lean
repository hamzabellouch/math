import OAI.Probability.SLE.Multipoint.MultipointAngular
import OAI.Probability.SLE.Multipoint.MultipointYoung

namespace OAI

/-! The Brownian cross coefficient in the regularized multipoint product,
including the singular powers when `p < 1`. -/

noncomputable section

namespace SLEExactGauge.Multipoint

def angularCoefficientConstant (p : ℝ) : ℝ := (p+q p)*3^(eta p)

lemma angularCoefficientConstant_pos {p : ℝ} (hp : 0 < p) :
    0 < angularCoefficientConstant p := by
  unfold angularCoefficientConstant
  exact mul_pos (add_pos hp (q_pos hp)) (Real.rpow_pos_of_pos (by norm_num) _)

lemma velocity_power_identity {D v e : ℝ} (hD : 0 ≤ D) (hv : 0 < v) :
    (D*v^2)^e * v^(1-2*e) = D^e*v := by
  rw [Real.mul_rpow hD (sq_nonneg v), ← Real.rpow_natCast v 2,
    ← Real.rpow_mul hv.le, mul_assoc, ← Real.rpow_add hv]
  norm_num

lemma pair_velocity_power_identity {Di Dj vi vj e : ℝ}
    (hDi : 0 ≤ Di) (hDj : 0 ≤ Dj) (hvi : 0 < vi) (hvj : 0 < vj) :
    (Di*vi^2)^e*(Dj*vj^2)^e*(vi*vj)^(1-2*e) = Di^e*Dj^e*vi*vj := by
  rw [Real.mul_rpow hvi.le hvj.le]
  calc
    _ = ((Di*vi^2)^e*vi^(1-2*e))*((Dj*vj^2)^e*vj^(1-2*e)) := by ring
    _ = _ := by rw [velocity_power_identity hDi hvi, velocity_power_identity hDj hvj]; ring

/-- The magnitude of one Brownian cross term is absorbed at its two
endpoints, leaving exactly the inverse-regulator interaction cost. -/
theorem angular_pair_absorption {p δi δj θi θj vi vj ε : ℝ}
    (hp : 0 < p) (hδi : 0 < δi) (hδi1 : δi ≤ 1)
    (hδj : 0 < δj) (hδj1 : δj ≤ 1)
    (hθi : 0 < Real.sin θi) (hθj : 0 < Real.sin θj)
    (hvi : 0 < vi) (hvj : 0 < vj) (hε : 0 < ε) :
    (|angularFactorFirst p δi θi| / angularFactor p δi θi * vi) *
      (|angularFactorFirst p δj θj| / angularFactor p δj θj * vj) ≤
    ε*(damping p δi θi*vi^2+damping p δj θj*vj^2) +
      youngConstant p (angularCoefficientConstant p ^ 2) ε *
        (δi*δj)^(-exponent p)*(vi*vj) := by
  let Di := damping p δi θi
  let Dj := damping p δj θj
  let C := angularCoefficientConstant p
  have hDi : 0 < Di := mul_pos (div_pos hδi (angularFactor_pos hδi hθi))
    (Real.rpow_pos_of_pos hθi _)
  have hDj : 0 < Dj := mul_pos (div_pos hδj (angularFactor_pos hδj hθj))
    (Real.rpow_pos_of_pos hθj _)
  have hC : 0 < C := angularCoefficientConstant_pos hp
  have hi := normalized_angularFactorFirst_bound hp hδi hδi1 hθi
  have hj := normalized_angularFactorFirst_bound hp hδj hδj1 hθj
  change _ ≤ C*δi^(-1-eta p)*Di^(eta p) at hi
  change _ ≤ C*δj^(-1-eta p)*Dj^(eta p) at hj
  have hmul := mul_le_mul hi hj (div_nonneg (abs_nonneg _) (angularFactor_pos hδj hθj).le)
    (by positivity : 0 ≤ C*δi^(-1-eta p)*Di^(eta p))
  have hmulv := mul_le_mul_of_nonneg_right hmul (mul_pos hvi hvj).le
  calc
    _ ≤ C^2*(δi*δj)^(-1-eta p)*Di^(eta p)*Dj^(eta p)*vi*vj := by
      rw [Real.mul_rpow hδi.le hδj.le]
      convert hmulv using 1 <;> ring
    _ = C^2*(δi*δj)^(-1-eta p)*(Di*vi^2)^(eta p)*
        (Dj*vj^2)^(eta p)*(vi*vj)^(1-2*eta p) := by
      calc
        _ = C^2*(δi*δj)^(-1-eta p)*(Di^(eta p)*Dj^(eta p)*vi*vj) := by ring
        _ = C^2*(δi*δj)^(-1-eta p)*
            ((Di*vi^2)^(eta p)*(Dj*vj^2)^(eta p)*(vi*vj)^(1-2*eta p)) := by
          rw [pair_velocity_power_identity hDi.le hDj.le hvi hvj]
        _ = _ := by ring
    _ ≤ _ := weighted_pair_absorption hp (sq_pos_of_pos hC) hε (mul_pos hδi hδj)
      (mul_nonneg hDi.le (sq_nonneg vi)) (mul_nonneg hDj.le (sq_nonneg vj))
      (mul_pos hvi hvj).le

end SLEExactGauge.Multipoint

end

end OAI
