import OAI.Analysis.LpDimension.SymmetricMoments

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set
open scoped BigOperators Topology Matrix ENNReal NNReal
universe u

namespace SubpolynomialLp

lemma power_difference_epsilon (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ,
      abs (|a+b|^p-|a|^p) ≤ ε*|a|^p+C*|b|^p := by
  have hc : ContinuousAt (fun t : ℝ => |1+t|^p) 0 := by
    exact (continuousAt_const.add continuousAt_id).abs.rpow_const (Or.inr hp.le)
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousAt_iff.mp hc ε hε
  let C : ℝ := 1+(1+δ⁻¹)^p+(δ⁻¹)^p
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun a b => ?_⟩
  have ha0 : 0 ≤ |a|^p := Real.rpow_nonneg (abs_nonneg a) p
  have hb0 : 0 ≤ |b|^p := Real.rpow_nonneg (abs_nonneg b) p
  by_cases ha : a = 0
  · subst a
    simp only [zero_add, abs_zero, Real.zero_rpow hp.ne', sub_zero, mul_zero, zero_add,
      abs_of_nonneg hb0]
    have hC1 : 1 ≤ C := by
      have h₁ : 0 ≤ (1+δ⁻¹)^p := by positivity
      have h₂ : 0 ≤ (δ⁻¹)^p := by positivity
      dsimp [C]; linarith
    nlinarith
  have haa : 0 < |a| := abs_pos.mpr ha
  by_cases hb : |b| < δ*|a|
  · have hr : dist (b/a) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_div]
      exact (div_lt_iff₀ haa).mpr (by nlinarith)
    have hn := (hnear hr).le
    simp only [Real.dist_eq, add_zero, abs_one, Real.one_rpow] at hn
    have he : |a+b|^p = |a|^p*|1+b/a|^p := by
      rw [← Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← abs_mul]
      congr 2
      field_simp
    rw [he, show |a|^p*|1+b/a|^p-|a|^p = |a|^p*(|1+b/a|^p-1) by ring,
      abs_mul, abs_of_nonneg ha0]
    exact (mul_le_mul_of_nonneg_left hn ha0).trans (by nlinarith)
  · have hab : |a| ≤ δ⁻¹*|b| := by
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hδ).mpr
      nlinarith [le_of_not_gt hb]
    have hadd : |a+b| ≤ (1+δ⁻¹)*|b| := by
      have hh := abs_add_le a b
      nlinarith
    have haP := Real.rpow_le_rpow (abs_nonneg _) hab hp.le
    have hbP := Real.rpow_le_rpow (abs_nonneg _) hadd hp.le
    rw [Real.mul_rpow (by positivity) (abs_nonneg _)] at haP hbP
    have h := abs_sub (|a+b|^p) (|a|^p)
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), abs_of_nonneg ha0] at h
    dsimp [C]
    nlinarith

lemma rpow_le_constant_exp (p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → x^p ≤ C*Real.exp x := by
  obtain ⟨m,hm⟩ := exists_nat_ge p
  let C : ℝ := (m.factorial:ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun x hx => ?_⟩
  by_cases hx1 : x ≤ 1
  · have hpow : x^p ≤ 1 := by simpa only [Real.one_rpow] using Real.rpow_le_rpow hx hx1 hp
    have hex : 1 ≤ Real.exp x := Real.one_le_exp hx
    dsimp [C]
    have hf : 0 ≤ (m.factorial:ℝ) := by positivity
    nlinarith [Real.exp_pos x]
  · have hpow := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hm
    rw [Real.rpow_natCast] at hpow
    have hex := Real.pow_div_factorial_le_exp x hx m
    have hf : 0 < (m.factorial:ℝ) := by positivity
    have hmexp := (div_le_iff₀ hf).mp hex
    dsimp [C]
    have hex0 := Real.exp_pos x
    nlinarith

lemma symmetric_exp_quadratic (x : ℝ) (hx : |x| ≤ 1) :
    (Real.exp x+Real.exp (-x))/2 ≤ 1+x^2 := by
  have h₁ := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
  have h₂ := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := -x) (by simpa only [abs_neg] using hx))).2
  nlinarith

end SubpolynomialLp

end

end OAI
