import OAI.Probability.SwitchChain.SliceMoments
import OAI.Probability.SwitchChain.SliceBounds

namespace OAI

noncomputable section

namespace Problem315.SliceMoments
variable {V : Type*} [sectionDecidableEqV : DecidableEq V]

omit [DecidableEq V] in
theorem equalMean_pos (U : Finset V) (q : ℕ)
    (hN : 3 ≤ U.card) (hq : 1 ≤ q) (hqlt : q < U.card) :
    0 < equalMean U q := by
  apply SliceBounds.equalityProbability_pos (N := (U.card : ℝ))
    (q := (q : ℝ)) (r := (U.card : ℝ) - q)
  · exact_mod_cast hN
  · exact_mod_cast hq
  · have : (q : ℝ) + 1 ≤ U.card := by exact_mod_cast hqlt
    linarith
  · ring

omit [DecidableEq V] in
theorem equalMean_complement (U : Finset V) (q : ℕ) (hN : 2 ≤ U.card) :
    1 - equalMean U q =
      2 * (q : ℝ) * ((U.card : ℝ) - q) /
        ((U.card : ℝ) * ((U.card : ℝ) - 1)) := by
  apply SliceBounds.equalityProbability_complement
  · have : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
    linarith
  · ring

include sectionDecidableEqV in
theorem equalMean_lt_one (U : Finset V) (q : ℕ)
    (hN : 3 ≤ U.card) (hq : 1 ≤ q) (hqlt : q < U.card) :
    equalMean U q < 1 := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  have hNR : (3 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hqr : (q : ℝ) < U.card := by exact_mod_cast hqlt
  have hc := equalMean_complement U q (by omega)
  have hpos : 0 < 2 * (q : ℝ) * ((U.card : ℝ) - q) /
      ((U.card : ℝ) * ((U.card : ℝ) - 1)) := by
    exact div_pos (mul_pos (mul_pos (by norm_num) hqR) (sub_pos.mpr hqr))
      (mul_pos (by linarith) (by linarith))
  linarith

theorem normalized_linear_norm (U : Finset V) (q : ℕ)
    (hN : 3 ≤ U.card) (hq : 1 ≤ q) (hqlt : q < U.card)
    (u : V → ℝ) (hu : ∑ i ∈ U, u i = 0) :
    average U q (fun S =>
      (((2 * (q : ℝ) - U.card) * (∑ i ∈ U, u i * coord i S)) /
        Real.sqrt (equalMean U q * (1 - equalMean U q))) ^ 2) =
      (2 * (q : ℝ) - U.card)^2 / (2 * equalMean U q) *
        (∑ i ∈ U, (u i)^2) := by
  have hp := equalMean_pos U q hN hq hqlt
  have hplt := equalMean_lt_one U q hN hq hqlt
  have hpc : 0 ≤ equalMean U q * (1 - equalMean U q) := by positivity
  have hf : (fun S =>
      (((2 * (q : ℝ) - U.card) * (∑ i ∈ U, u i * coord i S)) /
        Real.sqrt (equalMean U q * (1 - equalMean U q))) ^ 2) =
      (fun S => ((2 * (q : ℝ) - U.card)^2 /
        (equalMean U q * (1 - equalMean U q))) *
        (∑ i ∈ U, u i * coord i S)^2) := by
    funext S
    rw [div_pow, mul_pow, Real.sq_sqrt hpc]
    ring
  rw [hf, average_mul_left,
    average_linear_sq_zero_sum U q (by omega) (Nat.le_of_lt hqlt) u hu]
  have hNR : (3 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hqr : (q : ℝ) < U.card := by exact_mod_cast hqlt
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hr0 : (U.card : ℝ) - q ≠ 0 := ne_of_gt (sub_pos.mpr hqr)
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : equalMean U q ≠ 0 := ne_of_gt hp
  rw [equalMean_complement U q (by omega)]
  field_simp

theorem normalized_linear_norm_le (U : Finset V) (q : ℕ)
    (hN : 3 ≤ U.card) (hq : 1 ≤ q) (hqlt : q < U.card)
    (u : V → ℝ) (hu : ∑ i ∈ U, u i = 0) :
    average U q (fun S =>
      (((2 * (q : ℝ) - U.card) * (∑ i ∈ U, u i * coord i S)) /
        Real.sqrt (equalMean U q * (1 - equalMean U q))) ^ 2) ≤
      (U.card : ℝ) / 2 * ((U.card : ℝ) - 2) *
        (∑ i ∈ U, (u i)^2) := by
  rw [normalized_linear_norm U q hN hq hqlt u hu]
  have hNR : (3 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hrR : (1 : ℝ) ≤ (U.card : ℝ) - q := by
    have : (q : ℝ) + 1 ≤ U.card := by exact_mod_cast hqlt
    linarith
  have hb := SliceBounds.linear_eigenvalue_le hNR hqR hrR (by ring)
  change (2 * (q : ℝ) - U.card)^2 /
    (2 * ((U.card : ℝ) - 2) * equalMean U q) ≤ (U.card : ℝ) / 2 at hb
  have hp := equalMean_pos U q hN hq hqlt
  have hd : 0 < 2 * ((U.card : ℝ) - 2) * equalMean U q :=
    mul_pos (mul_pos (by norm_num) (by linarith)) hp
  have hb' := (div_le_iff₀ hd).mp hb
  have hc : (2 * (q : ℝ) - U.card)^2 / (2 * equalMean U q) ≤
      (U.card : ℝ) / 2 * ((U.card : ℝ) - 2) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * equalMean U q)).2
    nlinarith
  exact mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun i _ => sq_nonneg (u i))

end Problem315.SliceMoments

end

end OAI
