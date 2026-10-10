import OAI.NumberTheory.CubicMoment.Estimates.PoissonTailPower

namespace OAI

/-! A small square divisor leaves a positive-power gap beyond the
effective-frequency cutoff. -/
noncomputable section
namespace CubicFirstMoment

lemma divisor_tail_lower_scale {L A D η : ℝ} (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hDhi : D ≤ L^(η/16)) (hA : L^(1-η/16) ≤ A) (hDp : 0 < D) :
    L^(1-η/4) ≤ A/D^3 := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hp : (L^(η/16))^3 = L^(3*η/16) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hLp.le]
    congr 1
    push_cast
    ring
  apply (le_div_iff₀ (pow_pos hDp 3)).mpr
  calc
    L^(1-η/4)*D^3 ≤ L^(1-η/4)*(L^(η/16))^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hDhi 3) (by positivity)
    _ = L^(1-η/16) := by rw [hp,← Real.rpow_add hLp]; congr 1; ring
    _ ≤ A := hA

lemma divisor_tail_upper_scale {L A D : ℝ} (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hAhi : A ≤ L^2) : A/D^2 ≤ L^2 :=
  (div_le_self hA (one_le_pow₀ hD)).trans hAhi

end CubicFirstMoment

end

end OAI
