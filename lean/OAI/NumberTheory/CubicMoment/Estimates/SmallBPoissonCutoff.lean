import OAI.NumberTheory.CubicMoment.Estimates.PoissonTailPower

namespace OAI

/-! A concrete dyadic cutoff lying inside the small-conductor range,
with a fixed power gap past the natural small-B Poisson scale. -/
noncomputable section
namespace CubicFirstMoment

lemma smallB_poisson_cutoff {Z : ℝ} (_hZ : 0 < Z) (hlarge : 16 ≤ Z^(3/4:ℝ)) :
    ∃ n : ℕ, Z^(3/4:ℝ)/32 ≤ (2:ℝ)^n ∧
      ∀ j : ℕ, j < n → 16*(2:ℝ)^j ≤ Z^(3/4:ℝ) := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near
    ((le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mpr (by simpa using hlarge))
    (by norm_num : (1:ℝ) < 2)
  refine ⟨n,?_,?_⟩
  · have hh := (div_lt_iff₀ (by norm_num : (0:ℝ) < 16)).mp hn'
    rw [pow_succ] at hh
    linarith
  · intro j hj
    have hp : (2:ℝ)^j ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hj.le
    have hn := (le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mp hn
    nlinarith

lemma smallB_poisson_cutoff_scale {Z A J : ℝ} (hZ : 1 ≤ Z)
    (hA : Z^(3/2:ℝ) ≤ A) (hJ : Z^(3/4:ℝ)/32 ≤ J) :
    1/(864*Z^2) ≤ A/(27*Z^2) ∧
      Z^(1/4:ℝ)/864 ≤ (A/(27*Z^2))*J := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have ha : 1 ≤ A := (Real.one_le_rpow hZ (by norm_num)).trans hA
  constructor
  · apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 864*Z^2)
      (by positivity : (0:ℝ) < 27*Z^2)).mpr
    nlinarith [sq_pos_of_pos hz]
  · have hmul := mul_le_mul hA hJ (by positivity : 0 ≤ Z^(3/4:ℝ)/32)
      (zero_le_one.trans ha)
    have hid : Z^(3/2:ℝ)*Z^(3/4:ℝ) = Z^(1/4:ℝ)*Z^2 := by
      rw [← Real.rpow_natCast Z 2,← Real.rpow_add hz,← Real.rpow_add hz]
      norm_num
    have hp : Z^(1/4:ℝ)*Z^2 ≤ 32*(A*J) := by
      rw [← mul_div_assoc,hid] at hmul
      linarith
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 864)).mpr
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hz)).mp
    calc
      _ = Z^(1/4:ℝ)*Z^2 := mul_comm _ _
      _ ≤ 32*(A*J) := hp
      _ = Z^2*((A/(27*Z^2))*J*864) := by field_simp; ring

end CubicFirstMoment

end

end OAI
