import OAI.Probability.SATComputability.RelaxedCandidates

namespace OAI

namespace FixedClauseThreshold.Computability

private theorem cubic_loss_bound {x d : ℝ} (hx : 0 ≤ x) (hd : 0 < d) :
    x^2 - d * x^3 / 2 ≤ 1 / d^2 := by
  have hp : (d*x)^2 - (d*x)^3 / 2 ≤ 1 := by
    have hs := mul_nonneg (sq_nonneg (d*x - 4/3))
      (show 0 ≤ d*x + 2/3 by positivity)
    nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith

theorem two_to_three_exp_replacement {x d : ℝ}
    (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) (hd : 0 < d) :
    x^2 - (1 - Real.exp (-d*x^3)) ≤ 1 / d^2 := by
  let z := d*x^3
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have he : Real.exp (-z) ≤ 1 / (1+z) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity : 0 < 1+z) (by
      simpa only [add_comm] using Real.add_one_le_exp z)
  have he' : Real.exp (-d*x^3) ≤ 1 / (1+z) := by
    simpa only [z, neg_mul] using he
  by_cases hz1 : z ≤ 1
  · have hlin : z / 2 ≤ 1 - Real.exp (-d*x^3) := by
      have ht : 1 / (1+z) ≤ 1-z/2 := by
        apply (div_le_iff₀ (by positivity : 0 < 1+z)).mpr
        nlinarith
      linarith
    have hc := cubic_loss_bound hx hd
    dsimp [z] at hlin
    linarith
  · have hlarge : 1 / (1+z) ≤ (1:ℝ)/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 1+z)).mpr
      linarith
    have hxx : x^2 ≤ (1:ℝ)/4 := by nlinarith
    have hpos : 0 ≤ 1 / d^2 := by positivity
    linarith

theorem two_to_three_replacement {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1/2)
    {d : ℕ} (hd : 0 < d) :
    x^2 - (1 - (1-x^3)^d) ≤ 1 / (d : ℝ)^2 := by
  have hbase : 0 ≤ 1-x^3 := by nlinarith [sq_nonneg x]
  have he : (1-x^3)^d ≤ Real.exp (-((d : ℝ)*x^3)) := by
    calc
      _ ≤ (Real.exp (-(x^3)))^d := by
        apply pow_le_pow_left₀ hbase
        have := Real.add_one_le_exp (-(x^3))
        linarith
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hr := two_to_three_exp_replacement hx hxhalf (show (0:ℝ) < d by exact_mod_cast hd)
  simp only [neg_mul] at hr
  linarith

end FixedClauseThreshold.Computability

end OAI
