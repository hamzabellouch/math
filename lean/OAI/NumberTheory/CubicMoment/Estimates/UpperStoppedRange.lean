import OAI.NumberTheory.CubicMoment.Decomposition.StoppedActualRange

namespace OAI

/-! The upper one-stage stopping range fits the high-height bilinear
estimate once κ is chosen inside its published power-width margin. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_upper_stopped_analytic_range {κ γ : ℝ}
    (hκ : 0 < κ) (hκsmall : κ < 1/12)
    (hmargin : 1 < (1/3-κ)*(3+γ)) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X/16 ≤ A*B → A*B ≤ 16*X →
      X^(1/3-κ) ≤ B → B ≤ X^(1/3-κ/2) →
      2*B^(3/2:ℝ) ≤ A ∧ A ≤ B^(2+γ) ∧ A ≤ B^3 ∧
      B^(1/50:ℝ) ≤ X^(1/100:ℝ) ∧ X^(1/2:ℝ) ≤ B^3 ∧
      (1/4:ℝ)*(1+Real.log X) ≤ 1+Real.log B := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_const_mul_rpow_le (by norm_num : (39/40:ℝ) < 1) 32,
    eventually_const_mul_rpow_le hmargin 16,
    eventually_const_mul_rpow_le
      (show (1:ℝ) < (1/3-κ)*4 by linarith) 16]
    with X hX hlower hupper hcube
  intro A B hlo hhi hBlo hBhi
  have hXp : 0 < X := zero_lt_one.trans hX
  have hBp : 0 < B := (Real.rpow_pos_of_pos hXp _).trans_le hBlo
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX.le (by linarith : 0 ≤ 1/3-κ)).trans hBlo
  have hB39 : B ≤ X^(39/100:ℝ) := hBhi.trans
    (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith))
  have hlow : 2*B^(3/2:ℝ) ≤ A := by
    have hp := Real.rpow_le_rpow hBp.le hB39 (by norm_num : (0:ℝ) ≤ 5/2)
    rw [←Real.rpow_mul hXp.le] at hp
    norm_num at hp
    have hbsmall : 32*B^(5/2:ℝ) ≤ X :=
      (mul_le_mul_of_nonneg_left hp (by norm_num)).trans
        (by simpa only [Real.rpow_one] using hlower)
    have he : B^(3/2:ℝ)*B = B^(5/2:ℝ) := by
      nth_rw 2 [←Real.rpow_one B]
      rw [←Real.rpow_add hBp]
      norm_num
    apply (mul_le_mul_iff_left₀ hBp).mp
    rw [mul_assoc,he]
    exact (show 2*B^(5/2:ℝ) ≤ X/16 by linarith only [hbsmall]).trans hlo
  have hγ3 : 0 ≤ 3+γ := by
    have hl : 0 < 1/3-κ := by linarith
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hl.le (le_of_not_ge hn)
    linarith
  have hAupper : A ≤ B^(2+γ) := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hBlo hγ3
    rw [←Real.rpow_mul hXp.le] at hp
    have hh : 16*X ≤ B^(3+γ) := by simpa only [Real.rpow_one] using hupper.trans hp
    apply (mul_le_mul_iff_left₀ hBp).mp
    have he : B^(2+γ)*B = B^(3+γ) := by
      nth_rw 2 [←Real.rpow_one B]
      rw [←Real.rpow_add hBp]
      congr 1
      ring
    rw [he]
    exact hhi.trans hh
  have hAcube : A ≤ B^3 := by
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hBlo 4
    rw [←Real.rpow_mul_natCast hXp.le] at hp
    have hh : 16*X ≤ B^4 := by simpa only [Real.rpow_one] using hcube.trans hp
    apply (mul_le_mul_iff_left₀ hBp).mp
    simpa only [pow_succ] using hhi.trans hh
  have hheight : B^(1/50:ℝ) ≤ X^(1/100:ℝ) := by
    apply (Real.rpow_le_rpow hBp.le hBhi (by norm_num : (0:ℝ) ≤ 1/50)).trans
    rw [←Real.rpow_mul hXp.le]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have hcubeH : X^(1/2:ℝ) ≤ B^3 := by
    apply le_trans _ (pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hBlo 3)
    rw [←Real.rpow_mul_natCast hXp.le]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hXp (1/3-κ)) hBlo
  rw [Real.log_rpow hXp] at hlog
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX.le
  refine ⟨hlow,hAupper,hAcube,hheight,hcubeH,?_⟩
  nlinarith

end CubicFirstMoment

end

end OAI
