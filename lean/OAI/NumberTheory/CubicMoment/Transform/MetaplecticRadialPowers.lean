import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCutoffPowers

namespace OAI

/-! The radial residue cutoff lies within the squarefree lattice cutoff,
and its elementary Euler tail has a power margin at the source scales. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_radial_cutoff_le_sqrt {X R U C B : ℝ}
    (hX : 1 ≤ X) (hR : 0 < R) (hU : 0 < U) (hRU : R*U = X)
    (hRhi : R ≤ X^(51/100:ℝ)) (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hChi : C ≤ X^(13/100:ℝ)) : C ≤ Real.sqrt (B*U) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hcR : C^2*R ≤ X := by
    calc
      _ ≤ (X^(13/100:ℝ))^2*X^(51/100:ℝ) :=
        mul_le_mul (pow_le_pow_left₀ hC hChi 2) hRhi hR.le (by positivity)
      _ = X^(77/100:ℝ) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_add hXp]
        norm_num
      _ ≤ X := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hX (show (77/100:ℝ) ≤ 1 by norm_num)
  have hcU : C^2 ≤ U := (mul_le_mul_iff_left₀ hR).mp (by simpa [hRU,mul_comm] using hcR)
  exact Real.le_sqrt_of_sq_le (hcU.trans (le_mul_of_one_le_left hU.le hB))

lemma metaplectic_radial_euler_power {X C : ℝ} (hX : 1 ≤ X)
    (hC : X^(1/50:ℝ) ≤ C) :
    X^(5/6:ℝ)*C^(-(99/100):ℝ)*X^(2/10000:ℝ) ≤ X^(41/50:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hc : X^(5/6:ℝ)*C^(-(99/100):ℝ)*X^(2/10000:ℝ) ≤
      X^(5/6:ℝ)*(X^(1/50:ℝ))^(-(99/100):ℝ)*X^(2/10000:ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXp _) hC (by norm_num))
      (by positivity)) (by positivity)
  apply hc.trans
  rw [←Real.rpow_mul hXp.le,←Real.rpow_add hXp,←Real.rpow_add hXp]
  exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

end CubicFirstMoment

end

end OAI
