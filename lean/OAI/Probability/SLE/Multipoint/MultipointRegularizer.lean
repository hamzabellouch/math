import Mathlib

namespace OAI

/-! Parameters and the two-ended regularizer in the multipoint radius
estimate, September 25 manuscript, Section 3. These bounds are uniform in
all target levels; completed factors can therefore be frozen separately. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge.Multipoint

def q (p : ℝ) : ℝ := min 1 p / 2

def eta (p : ℝ) : ℝ := (1 - q p) / (2 - q p)

def exponent (p : ℝ) : ℝ := (1 + eta p) / (1 - 2 * eta p)

def beta (a p : ℝ) : ℝ := min 1 (a / (4 * exponent p))

lemma q_pos {p : ℝ} (hp : 0 < p) : 0 < q p :=
  div_pos (lt_min zero_lt_one hp) (by norm_num)

lemma q_lt_one {p : ℝ} : q p < 1 := by
  have h := min_le_left (1 : ℝ) p
  dsimp [q]
  linarith

lemma q_lt_p {p : ℝ} (hp : 0 < p) : q p < p := by
  have h := min_le_right (1 : ℝ) p
  dsimp [q]
  linarith

lemma eta_pos {p : ℝ} : 0 < eta p := by
  exact div_pos (sub_pos.mpr q_lt_one) (by linarith [q_lt_one (p := p)])

lemma eta_lt_half {p : ℝ} (hp : 0 < p) : eta p < 1 / 2 := by
  rw [eta, div_lt_iff₀ (by linarith [q_lt_one (p := p)])]
  linarith [q_pos hp]

lemma eta_identity (p : ℝ) : eta p * (q p - 2) = q p - 1 := by
  have hn : 2 - q p ≠ 0 := ne_of_gt (by linarith [q_lt_one (p := p)])
  dsimp [eta]
  field_simp
  ring

lemma exponent_eq {p : ℝ} (hp : 0 < p) : exponent p = 3 / q p - 2 := by
  have hq := q_pos hp
  have hq2 : 2 - q p ≠ 0 := ne_of_gt (by linarith [q_lt_one (p := p)])
  have he : 1 - 2 * eta p ≠ 0 := ne_of_gt (by linarith [eta_lt_half hp])
  dsimp [exponent]
  apply (div_eq_iff he).mpr
  dsimp [eta]
  field_simp
  ring

lemma exponent_pos {p : ℝ} (hp : 0 < p) : 0 < exponent p := by
  exact div_pos (by linarith [eta_pos (p := p)]) (by linarith [eta_lt_half hp])

lemma beta_pos {a p : ℝ} (ha : 0 < a) (hp : 0 < p) : 0 < beta a p := by
  exact lt_min zero_lt_one (div_pos ha (mul_pos (by norm_num) (exponent_pos hp)))

lemma beta_le_one (a p : ℝ) : beta a p ≤ 1 := min_le_left _ _

lemma twice_exponent_beta_lt {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    2 * (exponent p * beta a p) < a := by
  have hM := exponent_pos hp
  have hb : beta a p ≤ a / (4 * exponent p) := min_le_right _ _
  have h := (le_div_iff₀ (by positivity : 0 < 4 * exponent p)).mp hb
  nlinarith

/-- The regulator equals one at either endpoint of an active interval. -/
def regulator (β U u : ℝ) : ℝ := Real.exp (-β * min u (U - u))

@[simp] lemma regulator_zero (β U : ℝ) (hU : 0 ≤ U) : regulator β U 0 = 1 := by
  simp [regulator, min_eq_left hU]

@[simp] lemma regulator_end (β U : ℝ) (hU : 0 ≤ U) : regulator β U U = 1 := by
  simp [regulator, min_eq_right hU]

lemma regulator_pos (β U u : ℝ) : 0 < regulator β U u := Real.exp_pos _

lemma regulator_le_one {β U u : ℝ} (hβ : 0 ≤ β) (hu : u ∈ Icc 0 U) :
    regulator β U u ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ)
    (le_min hu.1 (sub_nonneg.mpr hu.2))

lemma regulator_inv_power_le {β U u M : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M) :
    regulator β U u ^ (-M) ≤ Real.exp (M * β * u) := by
  rw [regulator, ← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (min_le_left u (U-u)) (mul_nonneg hM hβ)
  nlinarith

lemma pair_regulator_inv_power_le {β U V u v M : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M) :
    (regulator β U u * regulator β V v) ^ (-M) ≤ Real.exp (M * β * (u + v)) := by
  rw [Real.mul_rpow (regulator_pos _ _ _).le (regulator_pos _ _ _).le]
  calc
    _ ≤ Real.exp (M * β * u) * Real.exp (M * β * v) :=
      mul_le_mul (regulator_inv_power_le hβ hM) (regulator_inv_power_le hβ hM)
        (Real.rpow_nonneg (regulator_pos _ _ _).le _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma regulator_eq_left {β U u : ℝ} (hu : u ≤ U / 2) :
    regulator β U u = Real.exp (-β * u) := by
  rw [regulator, min_eq_left (by linarith)]

lemma regulator_eq_right {β U u : ℝ} (hu : U / 2 ≤ u) :
    regulator β U u = Real.exp (-β * (U-u)) := by
  rw [regulator, min_eq_right (by linarith)]

lemma regulator_reflect (β U u : ℝ) : regulator β U (U-u) = regulator β U u := by
  simp only [regulator, sub_sub_cancel, min_comm]

lemma regulator_continuous (β U : ℝ) : Continuous (regulator β U) := by
  exact Real.continuous_exp.comp (continuous_const.mul
    (continuous_id.min (continuous_const.sub continuous_id)))

/-- Exact total regulator cost, independent of the length of the active clock. -/
lemma integral_regulator {β U : ℝ} (hβ : 0 < β) (hU : 0 ≤ U) :
    (∫ u in (0 : ℝ)..U, regulator β U u) =
      2 / β * (1 - Real.exp (-β * U / 2)) := by
  have hi (a b : ℝ) : IntervalIntegrable (regulator β U) volume a b :=
    (regulator_continuous β U).intervalIntegrable _ _
  have he (a b : ℝ) :
      (∫ u in a..b, Real.exp (-β * u)) =
        (-β)⁻¹ * (Real.exp (-β * b) - Real.exp (-β * a)) := by
    rw [intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.mpr hβ.ne'),
      integral_exp]
    rfl
  have hleft : (∫ u in (0 : ℝ)..U/2, regulator β U u) =
      ∫ u in (0 : ℝ)..U/2, Real.exp (-β*u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ U/2)] at hu
    exact regulator_eq_left hu.2
  have hright : (∫ u in U/2..U, regulator β U u) =
      ∫ u in (0 : ℝ)..U/2, Real.exp (-β*u) := by
    calc
      _ = ∫ u in U/2..U, Real.exp (-β*(U-u)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le (by linarith : U/2 ≤ U)] at hu
        exact regulator_eq_right hu.1
      _ = _ := by
        change (∫ u in U/2..U, (fun v : ℝ => Real.exp (-β*v)) (U-u)) = _
        rw [intervalIntegral.integral_comp_sub_left (f := fun v : ℝ => Real.exp (-β*v)) U]
        congr 1 <;> ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (U/2)) (hi (U/2) U),
    hleft, hright, he]
  simp only [mul_zero, Real.exp_zero]
  field_simp [hβ.ne']
  ring

lemma integral_regulator_le {β U : ℝ} (hβ : 0 < β) (hU : 0 ≤ U) :
    (∫ u in (0 : ℝ)..U, regulator β U u) ≤ 2 / β := by
  rw [integral_regulator hβ hU]
  exact mul_le_of_le_one_right (by positivity) (by linarith [Real.exp_pos (-β * U / 2)])

/-- The deterministic pair-interaction allowance obtained by shells of
`max uᵢ uⱼ`; see the interaction integral in the manuscript. -/
def interactionBudget (a c : ℝ) : ℝ :=
  Real.exp (2*c) / (2*a*(1-Real.exp (2*c-a)))

lemma interactionBudget_pos {a c : ℝ} (ha : 0 < a) (hc : 2*c < a) :
    0 < interactionBudget a c := by
  unfold interactionBudget
  exact div_pos (Real.exp_pos _) (mul_pos (by positivity)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))))

lemma interaction_shell_series {a c : ℝ} (_ha : 0 < a) (hc : 2*c < a) :
    HasSum (fun k : ℕ => Real.exp (2*c*((k:ℝ)+1)) * Real.exp (-a*k) / (2*a))
      (interactionBudget a c) := by
  have hs := (hasSum_geometric_of_lt_one (Real.exp_pos (2*c-a)).le
    (Real.exp_lt_one_iff.mpr (by linarith : 2*c-a < 0))).mul_left
      (Real.exp (2*c)/(2*a))
  convert hs using 1
  · ext k
    rw [← Real.exp_nat_mul, div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  · simp only [interactionBudget, div_eq_mul_inv, mul_inv_rev]
    ring

lemma weighted_shell_sum_le {a c : ℝ} (ha : 0 < a) (hc : 2*c < a)
    (mass : ℕ → ℝ) (h0 : ∀ k, 0 ≤ mass k)
    (hmass : ∀ k : ℕ, mass k ≤ Real.exp (-a*k)/(2*a)) :
    Summable (fun k : ℕ => Real.exp (2*c*((k:ℝ)+1))*mass k) ∧
      (∑' k : ℕ, Real.exp (2*c*((k:ℝ)+1))*mass k) ≤ interactionBudget a c := by
  have hs := interaction_shell_series ha hc
  have hnonneg (k : ℕ) : 0 ≤ Real.exp (2*c*((k:ℝ)+1))*mass k :=
    mul_nonneg (Real.exp_pos _).le (h0 k)
  have hle (k : ℕ) : Real.exp (2*c*((k:ℝ)+1))*mass k ≤
      Real.exp (2*c*((k:ℝ)+1))*Real.exp (-a*k)/(2*a) := by
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left (hmass k) (Real.exp_pos _).le
  have hsum := Summable.of_nonneg_of_le hnonneg hle hs.summable
  exact ⟨hsum, hs.tsum_eq ▸ hsum.tsum_le_tsum hle hs.summable⟩

end SLEExactGauge.Multipoint

end

end OAI
