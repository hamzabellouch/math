import OAI.NumberTheory.TwoPoint.Bounds.QualitativeSieveParameters

namespace OAI

/-! The literal CRT boundary error at the qualitative sieve cutoff. -/

namespace TwoPointCorrelations

lemma qualitative_sieve_boundary_cost (B : ℝ) (hpar : QualitativeSieveParameters B)
    (hB : 0 < B) (C₀ Y n : ℝ) (N : ℕ)
    (hC₀ : 0 ≤ C₀) (hC₃ : C₀ ≤ 3) (hY : 0 ≤ Y) (hn : 0 ≤ n)
    (hnY : n ≤ Y) (hYexp : Y ≤ Real.exp (qualitativeSieveLogCutoff B))
    (hN : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ N) :
    C₀ / (N : ℝ) * (2 * qualitativeSieveHalfOrder B + 1 : ℕ) *
      (n * Y + 1) ^ (2 * qualitativeSieveHalfOrder B) ≤ B ^ (-100 : ℝ) := by
  let X := qualitativeSieveLogCutoff B
  let A := B ^ (9999 / 10000 : ℝ)
  have hA : 0 < A := Real.rpow_pos_of_pos hB _
  have hXT : 1 ≤ X * Real.log B := by
    nlinarith only [hpar.cutoff_one, hpar.log_one]
  have hdom : 100000 * Real.log B ≤ A := by
    have hh := mul_le_mul_of_nonneg_right hpar.cutoff_one
      (show 0 ≤ Real.log B by linarith [hpar.log_one])
    nlinarith only [hh, hpar.cutoff_cost]
  have hA₄ : 4 ≤ A := by linarith [hpar.log_one]
  have hnum := sieve_boundary_numerator X (Real.log B) 1002 C₀ (n * Y + 1)
    (2 * qualitativeSieveHalfOrder B) hpar.cutoff_one hpar.log_one (by norm_num)
    hC₀ (by positivity) (sieve_base_le_exp X Y n hpar.cutoff_one hY hn hnY hYexp)
    hpar.order_small
  have hnumexp : Real.exp ((C₀ + 4 * 1002) * X * Real.log B) ≤ Real.exp (A / 4) := by
    apply Real.exp_le_exp.mpr
    have hcost : X * Real.log B ≤ A / 100000 := hpar.cutoff_cost
    have hXT₀ : 0 ≤ X * Real.log B := by linarith
    nlinarith only [hC₃, hC₀, hcost, hXT₀, hA]
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hdiv : 1 / (N : ℝ) ≤ 2 * Real.exp (-A) := by
    apply (div_le_iff₀ hNp).mpr
    have hh := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2 * Real.exp (-A) by positivity)
    have hc : (2 * Real.exp (-A)) * ((1 / 2 : ℝ) * Real.exp A) = 1 := by
      calc
        _ = Real.exp (-A) * Real.exp A := by ring
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    change (2 * Real.exp (-A)) * ((1 / 2 : ℝ) * Real.exp A) ≤ _ at hh
    rw [hc] at hh
    nlinarith only [hh]
  have he : 2 ≤ Real.exp (A / 4) := by
    linarith [Real.add_one_le_exp (A / 4)]
  calc
    _ = (C₀ * (2 * qualitativeSieveHalfOrder B + 1 : ℕ) *
        (n * Y + 1) ^ (2 * qualitativeSieveHalfOrder B)) * (1 / (N : ℝ)) := by ring
    _ ≤ Real.exp (A / 4) * (2 * Real.exp (-A)) := by
      exact mul_le_mul (hnum.trans hnumexp) hdiv (by positivity) (Real.exp_pos _).le
    _ ≤ Real.exp (A / 4) * (Real.exp (A / 4) * Real.exp (-A)) := by gcongr
    _ = Real.exp (-A / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-100 * Real.log B) := Real.exp_le_exp.mpr (by linarith only [hdom, hpar.log_one])
    _ = B ^ (-100 : ℝ) := by rw [Real.rpow_def_of_pos hB]; congr 1; ring

end TwoPointCorrelations

end OAI
