import OAI.Geometry.NodalSets.Elliptic.CorrugationWellBound

namespace OAI

namespace Yau.Geometry
open Real Set
open scoped ContDiff
noncomputable section

lemma corrugationSlope_le_amplitude {a R r : ℝ} (ha : 0 ≤ a)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hr : 0 ≤ r) : corrugationSlope a R r ≤ a := by
  by_cases hrR : r < R
  · calc
      corrugationSlope a R r ≤ a*r*1 :=
        mul_le_mul_of_nonneg_left (expNegInvGlue_le_one _) (mul_nonneg ha hr)
      _ ≤ a := by nlinarith
  · rw [corrugationSlope_zero hR0 (le_of_not_gt hrR)]
    exact ha

theorem exists_fixed_corrugation_slope : ∃ a C l₀ : ℝ,
    0 < a ∧ a ≤ 1 ∧ 0 < C ∧ 0 < l₀ ∧
    ContDiff ℝ ∞ (corrugationSlope a (1/4)) ∧
    (∀ r : ℝ, 0 ≤ r → 0 ≤ corrugationSlope a (1/4) r ∧ corrugationSlope a (1/4) r ≤ 1 ∧
      max (-(deriv (corrugationSlope a (1/4)) r)) 0 ≤ C*(corrugationSlope a (1/4) r)^((7:ℝ)/8) ∧
      corrugationSlope a (1/4) r * max (-(deriv (corrugationSlope a (1/4)) r)) 0 ≤ 1/(64*(1/4:ℝ))) ∧
    (∀ r ∈ Icc (1/16:ℝ) (1/8), l₀ ≤ corrugationSlope a (1/4) r) ∧
    (∀ r : ℝ, 1/4 ≤ r → corrugationSlope a (1/4) r = 0) := by
  obtain ⟨C,hC,hbound⟩ := corrugationSlope_fractional_bound
  let a := min 1 (1/(16*(C+1)))
  have ha : 0 < a := lt_min zero_lt_one (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  have haC : a*C ≤ 1/16 := by
    have ha' := min_le_right 1 (1/(16*(C+1)))
    have hm : a*(16*(C+1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp ha'
    nlinarith
  let l₀ := a*(1/16)*expNegInvGlue ((1/4:ℝ)^2-(1/8:ℝ)^2)
  have hl₀ : 0 < l₀ := mul_pos (mul_pos ha (by norm_num))
    (expNegInvGlue.pos_of_pos (by norm_num))
  refine ⟨a,C,l₀,ha,ha1,hC,hl₀,corrugationSlope_smooth _ _,?_,?_,?_⟩
  · intro r hr
    have hl := corrugationSlope_nonneg (R := (1/4:ℝ)) ha.le hr
    have hlu := corrugationSlope_le_one ha.le ha1 (by norm_num : 0 ≤ (1/4:ℝ)) (by norm_num) hr
    have hla := corrugationSlope_le_amplitude ha.le (by norm_num : 0 ≤ (1/4:ℝ)) (by norm_num) hr
    have hd := hbound a (1/4) r ha.le ha1 (by norm_num) (by norm_num) hr
    have hlq : (corrugationSlope a (1/4) r)^((7:ℝ)/8) ≤ 1 := Real.rpow_le_one hl hlu (by norm_num)
    have hdC : max (-(deriv (corrugationSlope a (1/4)) r)) 0 ≤ C := by nlinarith
    refine ⟨hl,hlu,hd,?_⟩
    calc
      corrugationSlope a (1/4) r * max (-(deriv (corrugationSlope a (1/4)) r)) 0 ≤ a*C := by gcongr
      _ ≤ 1/(64*(1/4:ℝ)) := by norm_num; exact haC
  · intro r hr
    have he : expNegInvGlue ((1/4:ℝ)^2-(1/8:ℝ)^2) ≤ expNegInvGlue ((1/4:ℝ)^2-r^2) :=
      expNegInvGlue.monotone (by nlinarith [hr.1,hr.2])
    have hn := expNegInvGlue.nonneg ((1/4:ℝ)^2-(1/8:ℝ)^2)
    change a*(1/16)*_ ≤ a*r*_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hr.1 ha.le) he hn
      (mul_nonneg ha.le (le_trans (by norm_num) hr.1))
  · intro r hr
    exact corrugationSlope_zero (by norm_num) hr

end
end Yau.Geometry

end OAI
