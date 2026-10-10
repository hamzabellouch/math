import OAI.NumberTheory.JointDickman.Analysis.CharacterUnsmoothingBounds
import OAI.NumberTheory.JointDickman.Amplification.UnsmoothingPowerBound

namespace OAI

/-! # Removing Riesz smoothing from the character sums -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem squarefreeCharacterSum_log_bound {z C D : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q:ℝ) ≤ (Real.log x)^C → χ ≠ 1 →
        ‖squarefreeCharacterSum χ z x‖ ≤ K*x*(Real.log x)^(-D) := by
  let B := D+1
  let H := 2*B
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  obtain ⟨K,hK,hbound⟩ := squarefreeCharacterPrimitive_uniform_bound hz hz1 hC hH
  have hsmall := (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0:ℝ) < 1)).def zero_lt_one
  refine ⟨2+2*K, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)), hbound, hsmall]
    with x hx hlog hb hs
  intro q _ χ hq hn
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hp : 0 < (Real.log x)^B := Real.rpow_pos_of_pos hl0 _
  have hp1 : 1 ≤ (Real.log x)^B := Real.one_le_rpow hlog hB
  have hpx : (Real.log x)^B ≤ x := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl0.le _),
      Real.rpow_one, abs_of_pos hx0, one_mul] using hs
  let h := x/(Real.log x)^B
  have hh : 0 < h := div_pos hx0 hp
  have hh1 : 1 ≤ h := (le_div_iff₀ hp).mpr (by simpa using hpx)
  have hhx : h ≤ x := div_le_self hx0.le hp1
  let E := K*x^2*(Real.log x)^(-H)
  have he0 : ‖squarefreeCharacterPrimitive χ z x‖ ≤ E :=
    hb q χ hq hn x le_rfl (by linarith)
  have he1 : ‖squarefreeCharacterPrimitive χ z (x+h)‖ ≤ E :=
    hb q χ hq hn (x+h) (by linarith) (by linarith)
  have hdiff : ‖squarefreeCharacterPrimitive χ z (x+h)-squarefreeCharacterPrimitive χ z x-
      (h:ℂ)*squarefreeCharacterSum χ z x‖ ≤ h*(h+1) := by
    simpa only [Complex.ofReal_add, add_sub_cancel_left] using squarefreeCharacterPrimitive_difference χ hz hz1 hx0
      (show x ≤ x+h by linarith)
  have hsum := complex_norm_of_riesz_difference hh hdiff
  have hbalance := unsmoothing_power_bound (x := x) (l := Real.log x) (B := B)
    (β := -H) (γ := 0) (μ := -D) (C := K) (M := 2) hx0 hlog hK.le (by norm_num)
    (by dsimp [H,B]; linarith) (by dsimp [B]; linarith)
  calc
    _ ≤ h+1+(‖squarefreeCharacterPrimitive χ z (x+h)‖+
        ‖squarefreeCharacterPrimitive χ z x‖)/h := hsum
    _ ≤ 2*h+2*E/h := add_le_add (by linarith)
      (div_le_div_of_nonneg_right (by linarith) hh.le)
    _ ≤ (2+2*K)*x*(Real.log x)^(-D) := by
      simpa only [Real.rpow_zero, mul_one, h, E] using hbalance

end JointDickman

end OAI
