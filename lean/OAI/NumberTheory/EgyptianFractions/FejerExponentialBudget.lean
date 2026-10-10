import Mathlib

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337.FejerParameters

lemma exp_neg_cube (t : ℝ) : Real.exp (-t) ^ 3 = Real.exp (-3 * t) := by
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num

lemma exp_neg_inv_fourth (t : ℝ) : 1 / Real.exp (-t) ^ 4 = Real.exp (4 * t) := by
  rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
  congr 1
  norm_num

/-- The purely exponential input to automatic-modulus Fejer localization.
There is no restriction on a modulus or on the upper size of the frequency range. -/
lemma eventually_fejer_exponential_parameters (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w : ℝ in atTop,
      0 < Real.exp (-η * w) ∧
      Real.exp (-η * w) ≤ 1 / 65536 ∧
      Real.exp (-η * w) ^ 3 = Real.exp (-3 * η * w) ∧
      1 / Real.exp (-η * w) ^ 4 = Real.exp (4 * η * w) := by
  filter_upwards [eventually_ge_atTop (Real.log 65536 / η)] with w hw
  have hmul : Real.log 65536 ≤ η * w := by
    simpa only [mul_comm] using (div_le_iff₀ hη).mp hw
  have hsmall : Real.exp (-η * w) ≤ 1 / 65536 := by
    calc
      Real.exp (-η * w) ≤ Real.exp (-Real.log 65536) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 65536 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  refine ⟨Real.exp_pos _, hsmall, ?_, ?_⟩
  · rw [show -η * w = -(η * w) by ring,
      show -3 * η * w = -3 * (η * w) by ring]
    exact exp_neg_cube (η * w)
  · rw [show -η * w = -(η * w) by ring,
      show 4 * η * w = 4 * (η * w) by ring]
    exact exp_neg_inv_fourth (η * w)

/-- A small exponential arc has enough residue points and its Fejer smoothing
degree fits below the modulus, uniformly when `w ≤ log q`. -/
lemma eventually_fejer_budget_general (η : ℝ) (hη : 0 < η) (hη3 : η ≤ 1 / 3) :
    ∀ᶠ w : ℝ in atTop, ∀ q : ℕ, w ≤ Real.log (q : ℝ) →
      Real.exp (-η * w) ≤ 1 / 65536 ∧
      128 ≤ Real.exp (-η * w) * (q : ℝ) ∧
      ⌊1 / (64 * Real.exp (-η * w) ^ 3)⌋₊ ≤ q := by
  have hη1 : 0 < 1 - η := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (Real.log 65536 / η),
    eventually_ge_atTop (Real.log 128 / (1 - η))] with w hw1 hwsmall hwlarge
  intro q hwq
  have hw0 : 0 ≤ w := by linarith
  have hq : 0 < q := by
    by_contra h
    have hq0 : q = 0 := by omega
    simp only [hq0, Nat.cast_zero, Real.log_zero] at hwq
    linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hexpw : Real.exp w ≤ (q : ℝ) := by
    calc
      Real.exp w ≤ Real.exp (Real.log (q : ℝ)) := Real.exp_le_exp.mpr hwq
      _ = _ := Real.exp_log hqR
  have hδpos : 0 < Real.exp (-η * w) := Real.exp_pos _
  have hsmall : Real.exp (-η * w) ≤ 1 / 65536 := by
    have hmul : Real.log 65536 ≤ η * w := by
      simpa only [mul_comm] using (div_le_iff₀ hη).mp hwsmall
    calc
      Real.exp (-η * w) ≤ Real.exp (-Real.log 65536) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 65536 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hlarge : 128 ≤ Real.exp (-η * w) * (q : ℝ) := by
    have hmul : Real.log 128 ≤ (1 - η) * w := by
      simpa only [mul_comm] using (div_le_iff₀ hη1).mp hwlarge
    calc
      (128 : ℝ) = Real.exp (Real.log 128) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp ((1 - η) * w) := Real.exp_le_exp.mpr hmul
      _ = Real.exp (-η * w) * Real.exp w := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-η * w) * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hexpw hδpos.le
  have hprod : 1 ≤ Real.exp (-η * w) ^ 3 * Real.exp w := by
    calc
      (1 : ℝ) ≤ Real.exp ((1 - 3 * η) * w) :=
        Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hw0)
      _ = Real.exp (-η * w) ^ 3 * Real.exp w := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        norm_num
        ring
  have hdegree : 1 / (64 * Real.exp (-η * w) ^ 3) ≤ Real.exp w := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * Real.exp (-η * w) ^ 3)).mpr
    nlinarith
  exact ⟨hsmall, hlarge, Nat.floor_le_of_le (hdegree.trans hexpw)⟩

/-- The precise exponential budget for the paper's value `η = 1/10000`. -/
lemma eventually_fejer_budget :
    ∀ᶠ w : ℝ in atTop, ∀ q : ℕ, w ≤ Real.log (q : ℝ) →
      Real.exp (-(1 / 10000 : ℝ) * w) ≤ 1 / 65536 ∧
      128 ≤ Real.exp (-(1 / 10000 : ℝ) * w) * (q : ℝ) ∧
      ⌊1 / (64 * Real.exp (-(1 / 10000 : ℝ) * w) ^ 3)⌋₊ ≤ q := by
  exact eventually_fejer_budget_general (1 / 10000) (by norm_num) (by norm_num)

end Problem337.FejerParameters

end

end OAI
