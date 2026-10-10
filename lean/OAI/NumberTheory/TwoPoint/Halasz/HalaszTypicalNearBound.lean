import OAI.NumberTheory.TwoPoint.Halasz.HalaszNearEnergy

namespace OAI

/-! Near-center energy from a bound on the literal typical prefix,
without an additive density comparison. -/

namespace TwoPointCorrelations

open Finset MeasureTheory

lemma halasz_typical_near_bound (B : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (C D L M : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 1 ≤ L)
    (hcenter : ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B 0 k‖ ≤ C*(Real.exp (-2*M/5)+L^(-1/4:ℝ))*k)
    (hnear : ∀ u ∈ Set.Icc (-(L^(1/16:ℝ))) (L^(1/16:ℝ)), ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B u k-
        (halaszPowerPhase u k/(1+(-u:ℂ)*Complex.I))*halaszPhaseMean B 0 k‖ ≤
          (D*L^(-3/50:ℝ))*k) :
    (∫ u in -(L^(1/16:ℝ))..(L^(1/16:ℝ)), ‖mrtDyadicPolynomial B N u‖^2) ≤
      (100*Real.pi*C^2+100*D^2)*(Real.exp (-4*M/5)+L^(-1/32:ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hh := halasz_near_dyadic_energy B hN
    (C*(Real.exp (-2*M/5)+L^(-1/4:ℝ))) (D*L^(-3/50:ℝ)) (L^(1/16:ℝ))
    (by positivity) (by positivity) (by positivity) hcenter hnear
  apply hh.trans
  have he : Real.exp (-2*M/5)^2=Real.exp (-4*M/5) := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hp : (L^(-1/4:ℝ))^2 ≤ L^(-1/32:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hL0.le]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have ha : (C*(Real.exp (-2*M/5)+L^(-1/4:ℝ)))^2 ≤
      2*C^2*(Real.exp (-4*M/5)+L^(-1/32:ℝ)) := by
    have hsum : (Real.exp (-2*M/5)+L^(-1/4:ℝ))^2 ≤
        2*(Real.exp (-4*M/5)+L^(-1/32:ℝ)) := by
      nlinarith [sq_nonneg (Real.exp (-2*M/5)-L^(-1/4:ℝ))]
    have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg C)
    nlinarith
  have hb : L^(1/16:ℝ)*(D*L^(-3/50:ℝ))^2 ≤ D^2*L^(-1/32:ℝ) := by
    have hpow : L^(1/16:ℝ)*(L^(-3/50:ℝ))^2=L^(-23/400:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hL0.le,←Real.rpow_add hL0]
      norm_num
    calc
      _ = D^2*(L^(1/16:ℝ)*(L^(-3/50:ℝ))^2) := by ring
      _ = D^2*L^(-23/400:ℝ) := by rw [hpow]
      _  ≤  _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)) (sq_nonneg D)
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 50*Real.pi by positivity)
  have hb' := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ 100 by norm_num)
  have hde := mul_nonneg (sq_nonneg D) (Real.exp_pos (-4*M/5)).le
  nlinarith

end TwoPointCorrelations

end OAI
