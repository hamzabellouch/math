import OAI.NumberTheory.CubicMoment.Angular.AngularModelOuter

namespace OAI

/-! The two explicit cutoffs in the low-height Type-I argument.
Only elementary real power inequalities are used here. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_short_cutoff_power {X R p q : ℝ}
    (hX : 1 ≤ X) (hR : 0 ≤ R) (hRX : R ≤ X^p) :
    R^(3/2:ℝ)*(X^q)^(3/2:ℝ) ≤ X^((p+q)*(3/2:ℝ)) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  calc
    _ ≤ (X^p)^(3/2:ℝ)*(X^q)^(3/2:ℝ) := by gcongr
    _ = _ := by
      rw [←Real.rpow_mul hXp.le,←Real.rpow_mul hXp.le,←Real.rpow_add hXp]
      congr 1
      ring

lemma metaplectic_short_small_power {X R : ℝ}
    (hX : 1 ≤ X) (hR : 0 ≤ R) (hRX : R ≤ X^(2/5:ℝ)) :
    R^(3/2:ℝ)*(X^(13/100:ℝ))^(3/2:ℝ) ≤ X^(159/200:ℝ) := by
  convert metaplectic_short_cutoff_power (q := (13/100:ℝ)) hX hR hRX using 1
  norm_num

lemma metaplectic_short_large_power {X R : ℝ}
    (hX : 1 ≤ X) (hR : 0 ≤ R) (hRX : R ≤ X^(51/100:ℝ)) :
    R^(3/2:ℝ)*(X^(1/50:ℝ))^(3/2:ℝ) ≤ X^(159/200:ℝ) := by
  convert metaplectic_short_cutoff_power (q := (1/50:ℝ)) hX hR hRX using 1
  norm_num

lemma metaplectic_counting_small_power {X : ℝ} (hX : 1 ≤ X) :
    X*(X^(13/100:ℝ))^(-3/2:ℝ) = X^(161/200:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  rw [←Real.rpow_mul hXp.le]
  conv_lhs => lhs; rw [←Real.rpow_one X]
  rw [←Real.rpow_add hXp]
  norm_num

lemma metaplectic_large_length {X R U : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hRU : R*U = X)
    (hRX : X^(2/5:ℝ) ≤ R) : U ≤ X^(3/5:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have he : U = X/R := by rw [←hRU]; field_simp
  rw [he]
  calc
    _ ≤ X/X^(2/5:ℝ) := div_le_div_of_nonneg_left hXp.le
      (Real.rpow_pos_of_pos hXp _) hRX
    _ = _ := by
      conv_lhs => lhs; rw [←Real.rpow_one X]
      rw [←Real.rpow_sub hXp]
      norm_num

lemma metaplectic_large_sieve_power {X R U : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (_hU : 0 ≤ U) (hRU : R*U = X)
    (hRlo : X^(2/5:ℝ) ≤ R) (hRhi : R ≤ X^(51/100:ℝ)) :
    X*(R+U/(X^(1/50:ℝ))^3+(X/(X^(1/50:ℝ))^3)^(2/3:ℝ)) ≤
      3*X^(122/75:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hc : (X^(1/50:ℝ))^3 = X^(3/50:ℝ) := by
    rw [←Real.rpow_mul_natCast hXp.le]
    norm_num
  have hUhi := metaplectic_large_length hX hR hRU hRlo
  have hu : U/(X^(1/50:ℝ))^3 ≤ X^(27/50:ℝ) := by
    rw [hc]
    calc
      _ ≤ X^(3/5:ℝ)/X^(3/50:ℝ) := div_le_div_of_nonneg_right hUhi (by positivity)
      _ = _ := by rw [←Real.rpow_sub hXp]; norm_num
  have hx : (X/(X^(1/50:ℝ))^3)^(2/3:ℝ) = X^(47/75:ℝ) := by
    rw [hc]
    conv_lhs => lhs; lhs; rw [←Real.rpow_one X]
    rw [←Real.rpow_sub hXp,←Real.rpow_mul hXp.le]
    norm_num
  have hr' : R ≤ X^(47/75:ℝ) := hRhi.trans
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))
  have hu' : U/(X^(1/50:ℝ))^3 ≤ X^(47/75:ℝ) := hu.trans
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))
  calc
    _ ≤ X*(X^(47/75:ℝ)+X^(47/75:ℝ)+X^(47/75:ℝ)) := by
      rw [hx]
      gcongr
    _ = 3*(X^(1:ℝ)*X^(47/75:ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [←Real.rpow_add hXp]; norm_num

lemma metaplectic_large_sieve_fixed_support {X R U B : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hRU : R*U = X) (hRlo : X^(2/5:ℝ) ≤ R) (hRhi : R ≤ X^(51/100:ℝ)) :
    X*(2*R+8*B*U/(X^(1/50:ℝ))^3+
        (16*B*X/(X^(1/50:ℝ))^3)^(2/3:ℝ)) ≤
      (3*(2+8*B+(16*B)^(2/3:ℝ)))*X^(122/75:ℝ) := by
  let C : ℝ := 2+8*B+(16*B)^(2/3:ℝ)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hp : 0 ≤ (16*B)^(2/3:ℝ) := Real.rpow_nonneg (by positivity) _
  have hc2 : 2 ≤ C := by dsimp [C]; linarith
  have hc8 : 8*B ≤ C := by dsimp [C]; linarith
  have hc16 : (16*B)^(2/3:ℝ) ≤ C := by dsimp [C]; linarith
  have hx0 : 0 ≤ X := le_trans zero_le_one hX
  have hscale : (16*B*X/(X^(1/50:ℝ))^3)^(2/3:ℝ) =
      (16*B)^(2/3:ℝ)*(X/(X^(1/50:ℝ))^3)^(2/3:ℝ) := by
    rw [show 16*B*X/(X^(1/50:ℝ))^3 = (16*B)*(X/(X^(1/50:ℝ))^3) by ring,
      Real.mul_rpow (by positivity : 0 ≤ 16*B) (by positivity)]
  calc
    _ = X*(2*R+(8*B)*(U/(X^(1/50:ℝ))^3)+
        (16*B)^(2/3:ℝ)*(X/(X^(1/50:ℝ))^3)^(2/3:ℝ)) := by rw [hscale]; ring
    _ ≤ X*(C*R+C*(U/(X^(1/50:ℝ))^3)+C*(X/(X^(1/50:ℝ))^3)^(2/3:ℝ)) := by
      gcongr
    _ = C*(X*(R+U/(X^(1/50:ℝ))^3+(X/(X^(1/50:ℝ))^3)^(2/3:ℝ))) := by ring
    _ ≤ C*(3*X^(122/75:ℝ)) := mul_le_mul_of_nonneg_left
      (metaplectic_large_sieve_power hX hR hU hRU hRlo hRhi) hC0
    _ = _ := by dsimp [C]; ring

end CubicFirstMoment

end

end OAI
