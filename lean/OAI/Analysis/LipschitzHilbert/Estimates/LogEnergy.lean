import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-!
# Logarithmic energy and relative prediction deficits

The exact `p`-Lipschitz estimate for `log (1 + ‖x‖^p)` from §§9–10.
A fixed denominator then cancels from differences of log predictions,
so bounded off-path motion gives a deficit proportional to the path drop.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E]

def logEnergy (p : ℝ) (x : E) : ℝ := Real.log (1 + ‖x‖ ^ p)

theorem rpow_predecessor_le_one_add {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    x ^ (p - 1) ≤ 1 + x ^ p := by
  by_cases hx1 : x ≤ 1
  · have hpow := Real.rpow_le_one hx hx1 (sub_nonneg.mpr hp)
    exact hpow.trans (le_add_of_nonneg_right (Real.rpow_nonneg hx _))
  · have hpow := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) (show p - 1 ≤ p by linarith)
    exact hpow.trans (le_add_of_nonneg_left zero_le_one)

theorem hasDerivAt_scalar_logEnergy {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Real.log (1 + y ^ p))
      (p * x ^ (p - 1) / (1 + x ^ p)) x := by
  exact ((Real.hasDerivAt_rpow_const (Or.inr hp)).const_add 1).log
    (ne_of_gt (by positivity))

theorem scalar_logEnergy_derivative_bound {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    ‖deriv (fun y : ℝ => Real.log (1 + y ^ p)) x‖ ≤ p := by
  rw [(hasDerivAt_scalar_logEnergy hp hx).deriv, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx _)) (by positivity))]
  apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ p)).2
  exact mul_le_mul_of_nonneg_left (rpow_predecessor_le_one_add hp hx) (by linarith)

theorem scalar_logEnergy_lipschitz {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.log (1 + a ^ p) - Real.log (1 + b ^ p)| ≤ p * |a - b| := by
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hasDerivAt_scalar_logEnergy hp hx).differentiableAt)
    (fun x hx => scalar_logEnergy_derivative_bound hp hx) hb ha
  simpa only [Real.norm_eq_abs] using h

/-- The exact global logarithmic-energy Lipschitz estimate, requiring only
that the vectors lie in a normed additive group. -/
theorem logEnergy_lipschitz {p : ℝ} (hp : 1 ≤ p) (x y : E) :
    |logEnergy p x - logEnergy p y| ≤ p * ‖x - y‖ := by
  exact (scalar_logEnergy_lipschitz hp (norm_nonneg x) (norm_nonneg y)).trans
    (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by linarith))

/-- The prediction ratio with a fixed positive denominator. -/
def energyRatio (p denominator : ℝ) (x : E) : ℝ := (1 + ‖x‖ ^ p) / denominator

theorem energyRatio_pos {p denominator : ℝ} (hd : 0 < denominator) (x : E) :
    0 < energyRatio p denominator x := div_pos (by positivity) hd

theorem log_energyRatio_sub (p denominator : ℝ) (hd : 0 < denominator) (x y : E) :
    Real.log (energyRatio p denominator x) - Real.log (energyRatio p denominator y) =
      logEnergy p x - logEnergy p y := by
  rw [energyRatio, energyRatio, Real.log_div (by positivity) hd.ne',
    Real.log_div (by positivity) hd.ne']
  unfold logEnergy
  ring

theorem log_energyRatio_lipschitz {p denominator : ℝ} (hp : 1 ≤ p) (hd : 0 < denominator)
    (x y : E) :
    |Real.log (energyRatio p denominator x) - Real.log (energyRatio p denominator y)| ≤
      p * ‖x - y‖ := by
  rw [log_energyRatio_sub p denominator hd]
  exact logEnergy_lipschitz hp x y

/-- A value exceeding one and a bound on numerator motion force a pointwise
lower bound with the same motion factor. The fixed denominator is unrestricted. -/
theorem energyRatio_deficit_of_exceeds_one {p denominator M : ℝ}
    (hp : 1 ≤ p) (hd : 0 < denominator) (hM : 0 ≤ M) (x y : E)
    (hy : 1 < energyRatio p denominator y) (hmotion : ‖x - y‖ ≤ M) :
    max (1 - energyRatio p denominator x) 0 ≤ p * M := by
  have hlogs := log_energyRatio_lipschitz hp hd x y
  have hlogy : 0 < Real.log (energyRatio p denominator y) := Real.log_pos hy
  have hlogx := Real.log_le_sub_one_of_pos (energyRatio_pos hd x (p := p))
  have hmove := mul_le_mul_of_nonneg_left hmotion (show 0 ≤ p by linarith)
  apply max_le
  · have hdiff := (abs_le.mp hlogs).1
    linarith
  · exact mul_nonneg (by linarith) hM

/-- For a fixed path vector, off-path vectors of size at most `B` have diameter
at most `2B`; hence a model prediction exceeding one has deficit at most `2pB`. -/
theorem fixed_path_prediction_deficit {T : Type*} {p denominator B : ℝ}
    (hp : 1 ≤ p) (hd : 0 < denominator) (hB : 0 ≤ B)
    (Y : E) (Z : T → E) (hZ : ∀ t, ‖Z t‖ ≤ B)
    (hexceeds : ∃ t, 1 < energyRatio p denominator (Y + Z t)) (t : T) :
    max (1 - energyRatio p denominator (Y + Z t)) 0 ≤ 2 * p * B := by
  obtain ⟨s, hs⟩ := hexceeds
  have hmotion : ‖(Y + Z t) - (Y + Z s)‖ ≤ 2 * B := by
    rw [add_sub_add_left_eq_sub]
    exact (norm_sub_le _ _).trans (by linarith [hZ t, hZ s])
  have h := energyRatio_deficit_of_exceeds_one hp hd (by linarith : 0 ≤ 2 * B)
    (Y + Z t) (Y + Z s) hs hmotion
  convert h using 1
  ring

end LipschitzHilbert

end

end OAI
