import OAI.NumberTheory.CubicMoment.Estimates.LowLogScale

namespace OAI

noncomputable section
namespace CubicFirstMoment

lemma low_diagonal_root_log_saving {A Z L Mα Mβ Ea Eb : ℝ}
    (hA : 0 < A) (hZ : 0 < Z) (hL : 0 < L)
    (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ) (ha : 0 ≤ Ea) (hb : 0 ≤ Eb)
    (j dα dβ a : ℕ) (hbound : A ≤ Z^2*L^(3*a))
    (hea : Ea ≤ Mα*A*L^dα) (heb : Eb ≤ Mβ*Z*L^dβ) :
    Real.sqrt (A/L^(a+2*j+dα+dβ))*Real.sqrt Ea*Real.sqrt Eb ≤
      Real.sqrt (Mα*Mβ)*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j := by
  let J := L^(a+2*j+dα+dβ)
  let R := Real.sqrt (A/J)*Real.sqrt Ea*Real.sqrt Eb
  let V := (A/J)*Eb
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hsq : ‖(R:ℂ)‖^2 ≤ Ea*V := by
    rw [Complex.norm_real,Real.norm_of_nonneg hR]
    dsimp [R,V]
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ A/J),Real.sq_sqrt ha,Real.sq_sqrt hb]
    exact le_of_eq (by ring)
  have hmass : V ≤ Mβ*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα) := by
    calc
      V ≤ (A/J)*(Mβ*Z*L^dβ) := mul_le_mul_of_nonneg_left heb (by positivity)
      _ = Mβ*(A*Z*L^dβ/L^(a+(2*j+dα)+dβ)) := by dsimp [J]; ring
      _ ≤ Mβ*(A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα)) :=
        mul_le_mul_of_nonneg_left (low_diagonal_log_scale hA hZ hL (2*j+dα) dβ a hbound) hMβ
      _ = _ := by ring
  have hh := bilinear_error_log_saving hMα hMβ hA hZ hL j dα ha hV hsq hea hmass
  simpa only [Complex.norm_real,Real.norm_of_nonneg hR] using hh

lemma low_remainder_root_log_saving {A Z L Mα M Ea : ℝ}
    (hA : 0 < A) (hZ : 0 < Z) (hL : 0 < L)
    (hMα : 0 ≤ Mα) (ha : 0 ≤ Ea) (j dα d D : ℕ)
    (hea : Ea ≤ Mα*A*L^dα) :
    (L^D)^2*Real.sqrt ((L^D)^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(D*(d+4)+(2*j+dα)))*
      Real.sqrt Ea ≤ Real.sqrt (Mα*M^2)*A^(5/6:ℝ)*Z^(5/6:ℝ)/L^j := by
  let Q := (L^D)^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(D*(d+4)+(2*j+dα))
  let R := (L^D)^2*Real.sqrt Q*Real.sqrt Ea
  let V := (L^D)^4*Q
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hsq : ‖(R:ℂ)‖^2 ≤ Ea*V := by
    rw [Complex.norm_real,Real.norm_of_nonneg hR]
    dsimp [R,V]
    rw [mul_pow,mul_pow,Real.sq_sqrt hQ,Real.sq_sqrt ha]
    exact le_of_eq (by ring)
  have hmass : V ≤ M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(2*j+dα) := by
    exact (low_remainder_log_scale hL.ne' d D (2*j+dα)).le
  have hh := bilinear_error_log_saving hMα (sq_nonneg M) hA hZ hL j dα ha hV hsq hea hmass
  simpa only [Complex.norm_real,Real.norm_of_nonneg hR] using hh

end CubicFirstMoment

end

end OAI
