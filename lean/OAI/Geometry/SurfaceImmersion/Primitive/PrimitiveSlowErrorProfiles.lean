import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveSlowScales

namespace OAI

/-! Uniform all-order power profiles for the two primitive error terms. -/
noncomputable section
namespace ClosedSurfaceR4.PrimitiveRealization

lemma normalized_slow_error_profile {z d d' b κ a η C : ℝ} {q : ℕ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hηb : η ≤ 2*z^κ)
    (ha : a ≤ d+κ*q-2*d') (hb : a ≤ 3*d-b-2*d') :
    (C*(z^d*η^q+(z^d)^3/z^b))/(z^d')^2 ≤ C*(2^q+1)*z^a := by
  have hpa : z^d*(z^κ)^q/(z^d')^2 = z^(d+κ*q-2*d') := by
    simpa only [Real.rpow_zero,div_one,Real.rpow_natCast,sub_zero] using
      ExactCorrection.scale_ratio_power hz d κ 0 (q : ℝ) d'
  have hpb := ExactCorrection.scale_cubic_quotient hz d b d'
  calc
    _ ≤ (C*(z^d*(2*z^κ)^q+(z^d)^3/z^b))/(z^d')^2 := by gcongr
    _ = C*2^q*z^(d+κ*q-2*d')+C*z^(3*d-b-2*d') := by
      rw [mul_pow]
      calc
        _ = (C*2^q)*(z^d*(z^κ)^q/(z^d')^2)+C*(((z^d)^3/z^b)/(z^d')^2) := by ring
        _ = _ := by rw [hpa,hpb]
    _ ≤ C*2^q*z^a+C*z^a := add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hz hz1 ha)
        (mul_nonneg hC (pow_nonneg (by norm_num) _)))
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hz hz1 hb) hC)
    _ = _ := by ring

lemma slow_parameter_bound_of_exponents {z b b' : ℝ} {loss : ℕ}
    (hz : 0 < z) (hz1 : z ≤ 1) :
    z^b'/z^b+z/(z^b')^loss ≤ 2*z^(min (b'-b) (1-b'*loss)) := by
  have hfirst : z^b'/z^b = z^(b'-b) := (Real.rpow_sub hz _ _).symm
  have hsecond : z/(z^b')^loss = z^(1-b'*(loss : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hz.le,Real.rpow_sub hz,Real.rpow_one]
  rw [hfirst,hsecond]
  have h₁ := Real.rpow_le_rpow_of_exponent_ge hz hz1
    (min_le_left (b'-b) (1-b'*loss))
  have h₂ := Real.rpow_le_rpow_of_exponent_ge hz hz1
    (min_le_right (b'-b) (1-b'*loss))
  linarith

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
