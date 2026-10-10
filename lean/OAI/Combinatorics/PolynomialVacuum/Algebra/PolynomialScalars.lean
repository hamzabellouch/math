import OAI.Combinatorics.PolynomialVacuum.Algebra.Projectors

namespace OAI

namespace PolynomialVacuumAlgebra

theorem xStar_polynomial : xStar = (q-q^3+q^5-q^7)/2 := by
  apply mul_right_cancel₀ (show q+q⁻¹ ≠ 0 from by
    intro hz
    have h := xStar_mul_q_sum
    rw [hz,mul_zero] at h
    exact zero_ne_one h)
  rw [xStar_mul_q_sum,q_inv]
  linear_combination -(q^6-q^4+q^2-2)/2 * q_pow_eight

theorem nZero_inv_polynomial : nZero⁻¹ = 1+q^2-q^6 := by
  apply mul_left_cancel₀ nZero_ne_zero
  rw [mul_inv_cancel₀ nZero_ne_zero,nZero,← q_two_sum]
  linear_combination -(q^4-2)*q_pow_eight

theorem q_pow_9 : q^9 = -q := by
  calc
    q^9 = (q^8)^1 * q^1 := by ring
    _ = -q := by rw [q_pow_eight]; norm_num

theorem q_pow_10 : q^10 = -q^2 := by
  calc
    q^10 = (q^8)^1 * q^2 := by ring
    _ = -q^2 := by rw [q_pow_eight]; norm_num

theorem q_pow_11 : q^11 = -q^3 := by
  calc
    q^11 = (q^8)^1 * q^3 := by ring
    _ = -q^3 := by rw [q_pow_eight]; norm_num

theorem q_pow_12 : q^12 = -q^4 := by
  calc
    q^12 = (q^8)^1 * q^4 := by ring
    _ = -q^4 := by rw [q_pow_eight]; norm_num

theorem q_pow_13 : q^13 = -q^5 := by
  calc
    q^13 = (q^8)^1 * q^5 := by ring
    _ = -q^5 := by rw [q_pow_eight]; norm_num

theorem q_pow_14 : q^14 = -q^6 := by
  calc
    q^14 = (q^8)^1 * q^6 := by ring
    _ = -q^6 := by rw [q_pow_eight]; norm_num

theorem q_pow_15 : q^15 = -q^7 := by
  calc
    q^15 = (q^8)^1 * q^7 := by ring
    _ = -q^7 := by rw [q_pow_eight]; norm_num

theorem q_pow_16 : q^16 = 1 := by
  calc
    q^16 = (q^8)^2 * q^0 := by ring
    _ = 1 := by rw [q_pow_eight]; norm_num

theorem q_pow_17 : q^17 = q := by
  calc
    q^17 = (q^8)^2 * q^1 := by ring
    _ = q := by rw [q_pow_eight]; norm_num

theorem q_pow_18 : q^18 = q^2 := by
  calc
    q^18 = (q^8)^2 * q^2 := by ring
    _ = q^2 := by rw [q_pow_eight]; norm_num

theorem q_pow_19 : q^19 = q^3 := by
  calc
    q^19 = (q^8)^2 * q^3 := by ring
    _ = q^3 := by rw [q_pow_eight]; norm_num

theorem q_pow_20 : q^20 = q^4 := by
  calc
    q^20 = (q^8)^2 * q^4 := by ring
    _ = q^4 := by rw [q_pow_eight]; norm_num

theorem q_pow_21 : q^21 = q^5 := by
  calc
    q^21 = (q^8)^2 * q^5 := by ring
    _ = q^5 := by rw [q_pow_eight]; norm_num

theorem q_pow_22 : q^22 = q^6 := by
  calc
    q^22 = (q^8)^2 * q^6 := by ring
    _ = q^6 := by rw [q_pow_eight]; norm_num

theorem q_pow_23 : q^23 = q^7 := by
  calc
    q^23 = (q^8)^2 * q^7 := by ring
    _ = q^7 := by rw [q_pow_eight]; norm_num

theorem q_pow_24 : q^24 = -1 := by
  calc
    q^24 = (q^8)^3 * q^0 := by ring
    _ = -1 := by rw [q_pow_eight]; norm_num

theorem q_pow_25 : q^25 = -q := by
  calc
    q^25 = (q^8)^3 * q^1 := by ring
    _ = -q := by rw [q_pow_eight]; norm_num

theorem q_pow_26 : q^26 = -q^2 := by
  calc
    q^26 = (q^8)^3 * q^2 := by ring
    _ = -q^2 := by rw [q_pow_eight]; norm_num

theorem q_pow_27 : q^27 = -q^3 := by
  calc
    q^27 = (q^8)^3 * q^3 := by ring
    _ = -q^3 := by rw [q_pow_eight]; norm_num

theorem q_pow_28 : q^28 = -q^4 := by
  calc
    q^28 = (q^8)^3 * q^4 := by ring
    _ = -q^4 := by rw [q_pow_eight]; norm_num

theorem q_pow_29 : q^29 = -q^5 := by
  calc
    q^29 = (q^8)^3 * q^5 := by ring
    _ = -q^5 := by rw [q_pow_eight]; norm_num

theorem q_pow_30 : q^30 = -q^6 := by
  calc
    q^30 = (q^8)^3 * q^6 := by ring
    _ = -q^6 := by rw [q_pow_eight]; norm_num

theorem q_pow_31 : q^31 = -q^7 := by
  calc
    q^31 = (q^8)^3 * q^7 := by ring
    _ = -q^7 := by rw [q_pow_eight]; norm_num

theorem q_pow_32 : q^32 = 1 := by
  calc
    q^32 = (q^8)^4 * q^0 := by ring
    _ = 1 := by rw [q_pow_eight]; norm_num

theorem q_pow_33 : q^33 = q := by
  calc
    q^33 = (q^8)^4 * q^1 := by ring
    _ = q := by rw [q_pow_eight]; norm_num

theorem q_pow_34 : q^34 = q^2 := by
  calc
    q^34 = (q^8)^4 * q^2 := by ring
    _ = q^2 := by rw [q_pow_eight]; norm_num

theorem q_pow_35 : q^35 = q^3 := by
  calc
    q^35 = (q^8)^4 * q^3 := by ring
    _ = q^3 := by rw [q_pow_eight]; norm_num

theorem q_pow_36 : q^36 = q^4 := by
  calc
    q^36 = (q^8)^4 * q^4 := by ring
    _ = q^4 := by rw [q_pow_eight]; norm_num

theorem q_pow_37 : q^37 = q^5 := by
  calc
    q^37 = (q^8)^4 * q^5 := by ring
    _ = q^5 := by rw [q_pow_eight]; norm_num

theorem q_pow_38 : q^38 = q^6 := by
  calc
    q^38 = (q^8)^4 * q^6 := by ring
    _ = q^6 := by rw [q_pow_eight]; norm_num

theorem q_pow_39 : q^39 = q^7 := by
  calc
    q^39 = (q^8)^4 * q^7 := by ring
    _ = q^7 := by rw [q_pow_eight]; norm_num

theorem q_pow_40 : q^40 = -1 := by
  calc
    q^40 = (q^8)^5 * q^0 := by ring
    _ = -1 := by rw [q_pow_eight]; norm_num

theorem q_pow_41 : q^41 = -q := by
  calc
    q^41 = (q^8)^5 * q^1 := by ring
    _ = -q := by rw [q_pow_eight]; norm_num

theorem q_pow_42 : q^42 = -q^2 := by
  calc
    q^42 = (q^8)^5 * q^2 := by ring
    _ = -q^2 := by rw [q_pow_eight]; norm_num

theorem q_pow_43 : q^43 = -q^3 := by
  calc
    q^43 = (q^8)^5 * q^3 := by ring
    _ = -q^3 := by rw [q_pow_eight]; norm_num

theorem q_pow_44 : q^44 = -q^4 := by
  calc
    q^44 = (q^8)^5 * q^4 := by ring
    _ = -q^4 := by rw [q_pow_eight]; norm_num

theorem q_pow_45 : q^45 = -q^5 := by
  calc
    q^45 = (q^8)^5 * q^5 := by ring
    _ = -q^5 := by rw [q_pow_eight]; norm_num

theorem q_pow_46 : q^46 = -q^6 := by
  calc
    q^46 = (q^8)^5 * q^6 := by ring
    _ = -q^6 := by rw [q_pow_eight]; norm_num

theorem q_pow_47 : q^47 = -q^7 := by
  calc
    q^47 = (q^8)^5 * q^7 := by ring
    _ = -q^7 := by rw [q_pow_eight]; norm_num

theorem q_pow_48 : q^48 = 1 := by
  calc
    q^48 = (q^8)^6 * q^0 := by ring
    _ = 1 := by rw [q_pow_eight]; norm_num

theorem q_pow_49 : q^49 = q := by
  calc
    q^49 = (q^8)^6 * q^1 := by ring
    _ = q := by rw [q_pow_eight]; norm_num

theorem q_pow_50 : q^50 = q^2 := by
  calc
    q^50 = (q^8)^6 * q^2 := by ring
    _ = q^2 := by rw [q_pow_eight]; norm_num

theorem q_pow_51 : q^51 = q^3 := by
  calc
    q^51 = (q^8)^6 * q^3 := by ring
    _ = q^3 := by rw [q_pow_eight]; norm_num

theorem q_pow_52 : q^52 = q^4 := by
  calc
    q^52 = (q^8)^6 * q^4 := by ring
    _ = q^4 := by rw [q_pow_eight]; norm_num

theorem q_pow_53 : q^53 = q^5 := by
  calc
    q^53 = (q^8)^6 * q^5 := by ring
    _ = q^5 := by rw [q_pow_eight]; norm_num

theorem q_pow_54 : q^54 = q^6 := by
  calc
    q^54 = (q^8)^6 * q^6 := by ring
    _ = q^6 := by rw [q_pow_eight]; norm_num

theorem q_pow_55 : q^55 = q^7 := by
  calc
    q^55 = (q^8)^6 * q^7 := by ring
    _ = q^7 := by rw [q_pow_eight]; norm_num

theorem q_pow_56 : q^56 = -1 := by
  calc
    q^56 = (q^8)^7 * q^0 := by ring
    _ = -1 := by rw [q_pow_eight]; norm_num

theorem q_pow_57 : q^57 = -q := by
  calc
    q^57 = (q^8)^7 * q^1 := by ring
    _ = -q := by rw [q_pow_eight]; norm_num

theorem q_pow_58 : q^58 = -q^2 := by
  calc
    q^58 = (q^8)^7 * q^2 := by ring
    _ = -q^2 := by rw [q_pow_eight]; norm_num

theorem q_pow_59 : q^59 = -q^3 := by
  calc
    q^59 = (q^8)^7 * q^3 := by ring
    _ = -q^3 := by rw [q_pow_eight]; norm_num

theorem q_pow_60 : q^60 = -q^4 := by
  calc
    q^60 = (q^8)^7 * q^4 := by ring
    _ = -q^4 := by rw [q_pow_eight]; norm_num

theorem q_pow_61 : q^61 = -q^5 := by
  calc
    q^61 = (q^8)^7 * q^5 := by ring
    _ = -q^5 := by rw [q_pow_eight]; norm_num

theorem q_pow_62 : q^62 = -q^6 := by
  calc
    q^62 = (q^8)^7 * q^6 := by ring
    _ = -q^6 := by rw [q_pow_eight]; norm_num

theorem q_pow_63 : q^63 = -q^7 := by
  calc
    q^63 = (q^8)^7 * q^7 := by ring
    _ = -q^7 := by rw [q_pow_eight]; norm_num

theorem q_pow_64 : q^64 = 1 := by
  calc
    q^64 = (q^8)^8 * q^0 := by ring
    _ = 1 := by rw [q_pow_eight]; norm_num

end PolynomialVacuumAlgebra

end OAI
