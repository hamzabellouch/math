import OAI.NumberTheory.CubicMoment.Estimates.CommonWeightSum

namespace OAI

/-! The nonunit common-factor weight has a genuine roughness saving.
Its small-power cost is charged to the common factor itself, never to
an ambient coefficient length. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem rough_common_factor_weight_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Finset Eisenstein) (R : ℝ), 0 < R →
      (∀ a ∈ I, primary a ∧ R ≤ norm a) →
      (∑ a ∈ I, (2:ℝ)^(primaryPrimeFactors a).card*norm a^(-(5/3:ℝ))) ≤
        C*R^(-(1/6:ℝ)) := by
  obtain ⟨D,hD,hbound⟩ := prime_factor_power_small_bound (by norm_num : (0:ℝ) < 1/6)
  let Z := ∑' a : Eisenstein, norm a^(-(4/3:ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun a => Real.rpow_nonneg (norm_nonneg a) _)
  refine ⟨D*(1+Z),by positivity,?_⟩
  intro I R hR hI
  have hrow (a : Eisenstein) (ha : a ∈ I) :
      (2:ℝ)^(primaryPrimeFactors a).card*norm a^(-(5/3:ℝ)) ≤
        D*R^(-(1/6:ℝ))*norm a^(-(4/3:ℝ)) := by
    have hn := norm_pos_of_ne_zero (primary_ne_zero (hI a ha).1)
    calc
      _ ≤ (D*norm a^(1/6:ℝ))*norm a^(-(5/3:ℝ)) :=
        mul_le_mul_of_nonneg_right (hbound a (hI a ha).1) (by positivity)
      _ = D*norm a^(-(1/6:ℝ))*norm a^(-(4/3:ℝ)) := by
        rw [mul_assoc,←Real.rpow_add hn]
        rw [mul_assoc,←Real.rpow_add hn]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hR (hI a ha).2 (by norm_num)) hD.le) (by positivity)
  calc
    _ ≤ ∑ a ∈ I, D*R^(-(1/6:ℝ))*norm a^(-(4/3:ℝ)) := Finset.sum_le_sum hrow
    _ = (D*R^(-(1/6:ℝ)))*(∑ a ∈ I, norm a^(-(4/3:ℝ))) := (Finset.mul_sum _ _ _).symm
    _ ≤ (D*R^(-(1/6:ℝ)))*Z := mul_le_mul_of_nonneg_left
      ((summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).sum_le_tsum I
        (fun a _ => Real.rpow_nonneg (norm_nonneg a) _)) (by positivity)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hR.le (-(1/6:ℝ))]

end CubicFirstMoment

end

end OAI
