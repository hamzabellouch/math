import OAI.NumberTheory.TwoPoint.Halasz.HalaszMomentInterpolation

namespace OAI

/-! Integer-power forms of the moment interpolation inequalities.
They avoid fractional powers in the final collision-absorption step. -/
namespace TwoPointCorrelations

open MeasureTheory

theorem halasz_holder_integer_power {d k : ℕ} (hk : 2≤k)
    (A B : (Fin d → AddCircle (1:ℝ)) → ℝ)
    (hA : Continuous A) (hB : Continuous B)
    (hA0 : ∀ x, 0≤A x) (hB0 : ∀ x, 0≤B x) :
    (∫ x, (A x)^(1-1/(k:ℝ))*(B x)^(1/(k:ℝ)) ∂halaszVinogradovHaar d)^k ≤
      (∫ x, A x ∂halaszVinogradovHaar d)^(k-1) *
        (∫ x, B x ∂halaszVinogradovHaar d) := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have hk1 : (1:ℝ)<k := by exact_mod_cast (by omega : 1<k)
  have hθ0 : 0<1-1/(k:ℝ) := by
    have : 1/(k:ℝ)<1 := (div_lt_one hk0).mpr hk1
    linarith
  have hθ1 : 1-1/(k:ℝ)<1 := by
    have := one_div_pos.mpr hk0
    linarith
  have h := halasz_torus_geometric_mean A B hA hB hA0 hB0 hθ0 hθ1
  simp only [sub_sub_cancel] at h
  have hI : 0≤∫ x, (A x)^(1-1/(k:ℝ))*(B x)^(1/(k:ℝ))
      ∂halaszVinogradovHaar d := integral_nonneg (fun x =>
    mul_nonneg (Real.rpow_nonneg (hA0 x) _) (Real.rpow_nonneg (hB0 x) _))
  have hAI : 0≤∫ x, A x ∂halaszVinogradovHaar d := integral_nonneg hA0
  have hBI : 0≤∫ x, B x ∂halaszVinogradovHaar d := integral_nonneg hB0
  have hexp : (1-1/(k:ℝ))*(k:ℝ)=((k-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤k)]
    push_cast
    field_simp
  have hpow := pow_le_pow_left₀ hI h k
  rw [mul_pow,← Real.rpow_mul_natCast hAI,← Real.rpow_mul_natCast hBI,
    hexp,one_div_mul_cancel hk0.ne',Real.rpow_natCast,Real.rpow_one] at hpow
  exact hpow

lemma halasz_collision_power_absorb {k : ℕ} (hk : 1≤k)
    {A B C : ℝ} (hA : 0<A)
    (h : A^k ≤ C^k*A^(k-1)*B) : A≤C^k*B := by
  have hp : 0<A^(k-1) := pow_pos hA _
  apply le_of_mul_le_mul_right _ hp
  calc
    A*A^(k-1) = A^k := by rw [← pow_succ',Nat.sub_add_cancel hk]
    _ ≤ C^k*A^(k-1)*B := h
    _ = (C^k*B)*A^(k-1) := by ring

end TwoPointCorrelations

end OAI
