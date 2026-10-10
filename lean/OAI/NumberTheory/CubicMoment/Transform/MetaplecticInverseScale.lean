import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimaryInverse

namespace OAI

/-! The exact amplitude and polynomial length range after angular
inverse completion. Each cube divisor contributes one inverse norm. -/
noncomputable section
namespace CubicFirstMoment

lemma norm_metaplectic_inverse_weight (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) :
    ‖(idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c‖ ≤ Real.sqrt (norm c) := by
  have h := norm_cubeInverseCompletionSeries_at_primary r ℓ t hc
  rwa [cubeInverseCompletionSeries_at_primary r ℓ t hc] at h

lemma metaplectic_inverse_sqrt_scale {U N : ℝ} (hU : 0 ≤ U) (hN : 0 < N) :
    Real.sqrt N*Real.sqrt (U/N^3) = Real.sqrt U/N := by
  have hn : Real.sqrt (N^3) = N*Real.sqrt N := by
    rw [show N^3 = N^2*N by ring,Real.sqrt_mul (sq_nonneg N),Real.sqrt_sq hN.le]
  rw [Real.sqrt_div hU,hn]
  field_simp [hN.ne',(Real.sqrt_pos.mpr hN).ne']

lemma metaplectic_inverse_weight_scale (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) {U : ℝ} (hU : 0 ≤ U) :
    ‖(idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c‖*
      Real.sqrt (U/norm c^3) ≤ Real.sqrt U/norm c := by
  calc
    _ ≤ Real.sqrt (norm c)*Real.sqrt (U/norm c^3) :=
      mul_le_mul_of_nonneg_right (norm_metaplectic_inverse_weight r ℓ t hc)
        (Real.sqrt_nonneg _)
    _ = _ := metaplectic_inverse_sqrt_scale hU (norm_pos_of_ne_zero (primary_ne_zero hc))

lemma metaplectic_inverse_length_range {Y U N B : ℝ}
    (hY : 1 ≤ Y) (hB : 0 ≤ B) (hUlo : Y^(-B) ≤ U) (hUhi : U ≤ Y^B)
    (hNlo : 1 ≤ N) (hNhi : N ≤ Y^B) :
    0 < U/N^3 ∧ Y^(-(4*B)) ≤ U/N^3 ∧ U/N^3 ≤ Y^(4*B) := by
  have hYp := zero_lt_one.trans_le hY
  have hUp := (Real.rpow_pos_of_pos hYp (-B)).trans_le hUlo
  have hNp := zero_lt_one.trans_le hNlo
  have hNcube : N^3 ≤ Y^(3*B) := by
    calc
      _ ≤ (Y^B)^3 := pow_le_pow_left₀ hNp.le hNhi 3
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hYp.le]; congr 1; ring
  refine ⟨div_pos hUp (pow_pos hNp 3),?_,?_⟩
  · apply (le_div_iff₀ (pow_pos hNp 3)).mpr
    calc
      _ ≤ Y^(-(4*B))*Y^(3*B) := mul_le_mul_of_nonneg_left hNcube (by positivity)
      _ = Y^(-B) := by rw [←Real.rpow_add hYp]; congr 1; ring
      _ ≤ U := hUlo
  · exact (div_le_self hUp.le (one_le_pow₀ hNlo)).trans
      (hUhi.trans (Real.rpow_le_rpow_of_exponent_le hY (by linarith)))

end CubicFirstMoment

end

end OAI
