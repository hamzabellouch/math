import OAI.Probability.FreeIsing.Energy.Attenuation

namespace OAI

noncomputable section

namespace Problem367

theorem one_sub_attenuation {theta : ℝ} (htheta : theta ^ 2 ≤ 1) (z : ℝ) :
    1 - responseAttenuation theta z =
      (1 - theta ^ 2) * Real.tanh z ^ 2 / (1 - theta ^ 2 * Real.tanh z ^ 2) := by
  unfold responseAttenuation
  have hden := ne_of_gt (attenuation_denominator_pos htheta z)
  apply (eq_div_iff hden).2
  rw [sub_mul, div_mul_cancel₀ _ hden]
  ring

theorem attenuation_le_one_sub {theta : ℝ} (htheta : theta ^ 2 ≤ 1) (z : ℝ) :
    responseAttenuation theta z ≤ 1 - (1 - theta ^ 2) * Real.tanh z ^ 2 := by
  have hden := attenuation_denominator_pos htheta z
  have hnum : 0 ≤ (1 - theta ^ 2) * Real.tanh z ^ 2 :=
    mul_nonneg (sub_nonneg.mpr htheta) (sq_nonneg _)
  have hdenle : 1 - theta ^ 2 * Real.tanh z ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg theta) (sq_nonneg (Real.tanh z))]
  have hquot : (1 - theta ^ 2) * Real.tanh z ^ 2 ≤
      (1 - theta ^ 2) * Real.tanh z ^ 2 / (1 - theta ^ 2 * Real.tanh z ^ 2) := by
    apply (le_div_iff₀ hden).2
    simpa using mul_le_mul_of_nonneg_left hdenle hnum
  rw [← one_sub_attenuation htheta z] at hquot
  linarith

theorem attenuation_sq_le {theta : ℝ} (htheta : theta ^ 2 ≤ 1) (z : ℝ) :
    responseAttenuation theta z ^ 2 ≤ responseAttenuation theta z := by
  have hp := responseAttenuation_pos htheta z
  have hl := responseAttenuation_le_one htheta z
  nlinarith [mul_nonneg (le_of_lt hp) (sub_nonneg.mpr hl)]

theorem attenuation_sq_le_one_sub {theta : ℝ} (htheta : theta ^ 2 ≤ 1) (z : ℝ) :
    responseAttenuation theta z ^ 2 ≤ 1 - (1 - theta ^ 2) * Real.tanh z ^ 2 :=
  (attenuation_sq_le htheta z).trans (attenuation_le_one_sub htheta z)

theorem attenuation_sq_le_exp {theta : ℝ} (htheta : theta ^ 2 ≤ 1) (z : ℝ) :
    responseAttenuation theta z ^ 2 ≤
      Real.exp (-(1 - theta ^ 2) * Real.tanh z ^ 2) := by
  refine (attenuation_sq_le_one_sub htheta z).trans ?_
  have h := Real.add_one_le_exp (-(1 - theta ^ 2) * Real.tanh z ^ 2)
  linarith

theorem prod_responseAttenuation_pos {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    {theta : ℝ} (htheta : theta ^ 2 ≤ 1) :
    0 < ∏ i ∈ s, responseAttenuation theta (z i) := by
  exact Finset.prod_pos (fun i _ => responseAttenuation_pos htheta (z i))

theorem prod_attenuation_le_one {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    {theta : ℝ} (htheta : theta ^ 2 ≤ 1) :
    ∏ i ∈ s, responseAttenuation theta (z i) ≤ 1 := by
  exact Finset.prod_le_one₀ (fun index _ => le_of_lt (responseAttenuation_pos htheta (z index)))
    (fun i _ => responseAttenuation_le_one htheta (z i))

theorem prod_attenuation_sq_le_exp {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    {theta : ℝ} (htheta : theta ^ 2 ≤ 1) :
    ∏ i ∈ s, responseAttenuation theta (z i) ^ 2 ≤
      Real.exp (-(1 - theta ^ 2) * ∑ i ∈ s, Real.tanh (z i) ^ 2) := by
  calc
    ∏ i ∈ s, responseAttenuation theta (z i) ^ 2 ≤
        ∏ i ∈ s, Real.exp (-(1 - theta ^ 2) * Real.tanh (z i) ^ 2) :=
      Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
        (fun i _ => attenuation_sq_le_exp htheta (z i))
    _ = Real.exp (∑ i ∈ s, -(1 - theta ^ 2) * Real.tanh (z i) ^ 2) :=
      (Real.exp_sum _ _).symm
    _ = _ := by rw [Finset.mul_sum]

end Problem367

end

end OAI
