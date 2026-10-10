import OAI.NumberTheory.CubicMoment.Estimates.CubeErrorPowers

namespace OAI

/-! Elementary scales for the cube error of a bounded stopped row. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_half_inverse_third {b : ℝ} (hb : 0 < b) :
    (b/2)^(-(1/3:ℝ)) = (2:ℝ)^(1/3:ℝ)*b^(-(1/3:ℝ)) := by
  rw [Real.div_rpow hb.le (by norm_num),div_eq_mul_inv,
    ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  norm_num only [neg_neg]
  ring

lemma stopped_log_ratio {z R : ℝ} (hz : 0 < z) (k : ℕ)
    (hR : z^(k+1) ≤ R) : z/R ≤ 1/z^k := by
  have hRp : 0 < R := (pow_pos hz _).trans_le hR
  apply (div_le_div_iff₀ hRp (pow_pos hz k)).mpr
  simpa only [pow_succ,mul_comm,one_mul,mul_one] using hR

lemma stopped_cube_error_scale {A b z R C D M I : ℝ}
    (hA : 0 < A) (hb : 0 < b) (hz : 0 < z)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hI : 0 ≤ I)
    (k : ℕ) (hcut : A ≤ b^2/z^(3*k)) (hR : z^(k+1) ≤ R) :
    (C*A/(27*(b/2))+D*A^(2/3:ℝ)*(b/2)^(-(1/3:ℝ))/9*
        ((2*z/Real.log 2)/R))*(18*b*M)^2+
      (A^(2/3:ℝ)*(b/2)^(-(1/3:ℝ))/9*I)*(324*b^2*M^2*(z/Real.log 2)/R) ≤
      (24*C*M^2+(72*D+36*I)*(2:ℝ)^(1/3:ℝ)*M^2/Real.log 2)*
        A^(2/3:ℝ)*b^(5/3:ℝ)/z^k := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hRp : 0 < R := (pow_pos hz _).trans_le hR
  have hp : b^(-(1/3:ℝ))*b^2 = b^(5/3:ℝ) := by
    rw [←Real.rpow_natCast b 2,←Real.rpow_add hb]
    norm_num
  have hlattice : A*b ≤ A^(2/3:ℝ)*b^(5/3:ℝ)/z^k := by
    simpa only [zero_add,Nat.zero_add,pow_zero,mul_one] using
      cube_lattice_error_scale hA hb hz 0 k (by simpa using hcut)
  have he : (C*A/(27*(b/2))+D*A^(2/3:ℝ)*(b/2)^(-(1/3:ℝ))/9*
        ((2*z/Real.log 2)/R))*(18*b*M)^2+
      (A^(2/3:ℝ)*(b/2)^(-(1/3:ℝ))/9*I)*(324*b^2*M^2*(z/Real.log 2)/R) =
      (24*C*M^2)*(A*b)+
        ((72*D+36*I)*(2:ℝ)^(1/3:ℝ)*M^2/Real.log 2)*
          (A^(2/3:ℝ)*b^(5/3:ℝ))*(z/R) := by
    rw [stopped_half_inverse_third hb,←hp]
    field_simp
    ring
  rw [he]
  calc
    _ ≤ (24*C*M^2)*(A^(2/3:ℝ)*b^(5/3:ℝ)/z^k)+
        ((72*D+36*I)*(2:ℝ)^(1/3:ℝ)*M^2/Real.log 2)*
          (A^(2/3:ℝ)*b^(5/3:ℝ))*(1/z^k) := add_le_add
      (mul_le_mul_of_nonneg_left hlattice (by positivity))
      (mul_le_mul_of_nonneg_left (stopped_log_ratio hz k hR) (by positivity))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
