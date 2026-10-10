import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveMetricPowers

namespace OAI

/-! The chosen slow scale also gives the finite two-jet input budget for
the actual periodic primitive. -/
noncomputable section
namespace ClosedSurfaceR4.PrimitiveRealization

lemma slow_power_dominates_fast {z b : ℝ} {loss : ℕ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hb : 0 ≤ b) (hbl : b < 1/(1+(loss : ℝ))) :
    z ≤ (z^b)^loss := by
  have hbl' : b*(1+(loss : ℝ)) < 1 := (lt_div_iff₀ (by positivity)).mp hbl
  have hpow : b*(loss : ℝ) ≤ 1 := by nlinarith
  rw [← Real.rpow_mul_natCast hz.le]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hz hz1 hpow

lemma primitive_shifted_budget {z s P Q D : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hzs : z ≤ s)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (_hD : 0 ≤ D) :
    P+(z/s)*Q+D/z^2 ≤ (P+Q+D)/z^2 := by
  have hs : 0 < s := hz.trans_le hzs
  have hratio : z/s ≤ 1 := (div_le_one hs).mpr hzs
  have hbase : P+(z/s)*Q ≤ P+Q := by
    exact add_le_add le_rfl (mul_le_of_le_one_left hQ hratio)
  have hbase0 : 0 ≤ P+(z/s)*Q := add_nonneg hP (mul_nonneg (div_nonneg hz.le hs.le) hQ)
  have hzsq : z^2 ≤ 1 := by nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hz)).mpr
  calc
    (P+(z/s)*Q+D/z^2)*z^2 = (P+(z/s)*Q)*z^2+D := by field_simp
    _ ≤ P+(z/s)*Q+D := add_le_add (mul_le_of_le_one_right hbase0 hzsq) le_rfl
    _ ≤ P+Q+D := add_le_add hbase le_rfl

lemma primitive_normal_threshold {b ε : ℝ} {loss : ℕ} (hb : 0 ≤ b)
    (hbl : b < 1/(1+(loss : ℝ))) (hε : 0 < ε) (D : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ z : ℝ, 0 < z → z < η →
      D*z/(z^b)^loss < ε := by
  have hbl' : b*(1+(loss : ℝ)) < 1 := (lt_div_iff₀ (by positivity)).mp hbl
  have he : 0 < 1-b*(loss : ℝ) := by nlinarith
  obtain ⟨η,hη,hη1,hh⟩ := ExactCorrection.positive_power_threshold D (1-b*(loss : ℝ)) ε he hε
  refine ⟨η,hη,hη1,?_⟩
  intro z hz hzη
  have hid : D*z/(z^b)^loss = D*z^(1-b*(loss : ℝ)) := by
    rw [← Real.rpow_mul_natCast hz.le,Real.rpow_sub hz,Real.rpow_one,mul_div_assoc]
  rw [hid]
  exact hh z hz hzη

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
