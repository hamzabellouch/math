import OAI.NumberTheory.Ostmann.QuadraticCenter.CutoffBounds
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericWitnessCosts

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_numeric_witness_scales :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      1 ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent → ∀ Y : ℝ,
      (Z:ℝ) ≤ Y → Real.log Y ≤ 7*Real.log Z →
      let K : ℝ := auxiliaryK Z z
      let epsilon := Real.exp (-K)
      let B := Real.exp (8*K)
      0 < epsilon ∧ epsilon ≤ 1 ∧ 1 ≤ B ∧
        B ≤ Y*(epsilon/(10*cutoffFourierBound)) ∧
        1024*(1+Real.log (2*Y)) ≤ (epsilon/(10*cutoffFourierBound))^2*B := by
  have hC := cutoffFourierBound_pos
  have hcost := eventually_auxiliary_exp_cost (10*cutoffFourierBound) 9 1
    (by positivity) (by norm_num) (by norm_num)
  have hlog := eventually_auxiliary_exp_dominates_log cutoffFourierBound hC
  filter_upwards [hcost,hlog] with T hcost hlog
  intro Z z hZ hZl hZu hz hzl hzu Y hZY hYlog K epsilon B
  have hZp : (0:ℝ)<Z := by exact_mod_cast hZ
  have hYp := hZp.trans_le hZY
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hc := hcost Z z hZ hZl hZu hz hzl hzu
  rw [Real.rpow_one] at hc
  have hcY := hc.trans hZY
  have hl := hlog Z z hZl hZu hz hzl hzu Y hYp hYlog
  refine ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (by linarith),
    Real.one_le_exp_iff.mpr (by positivity),?_,?_⟩
  · have hm := mul_le_mul_of_nonneg_right hcY
      (show 0 ≤ epsilon/(10*cutoffFourierBound) by positivity)
    have he : (10*cutoffFourierBound*Real.exp (9*K)) *
        (epsilon/(10*cutoffFourierBound)) = B := by
      dsimp [epsilon,B]
      calc
        _ = Real.exp (9*K)*Real.exp (-K) := by field_simp
        _ = Real.exp (9*K+-K) := (Real.exp_add _ _).symm
        _ = _ := by congr 1; ring
    change (10*cutoffFourierBound*Real.exp (9*K)) *
      (epsilon/(10*cutoffFourierBound)) ≤ _ at hm
    rw [he] at hm
    exact hm
  · have he : (epsilon/(10*cutoffFourierBound))^2*B =
        Real.exp (6*K)/(10*cutoffFourierBound)^2 := by
      dsimp [epsilon,B]
      rw [div_pow,div_mul_eq_mul_div,← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      congr 1
      ring
    rw [he]
    exact (le_div_iff₀ (sq_pos_of_pos (by positivity : 0<10*cutoffFourierBound))).mpr hl

end Ostmann.QuadraticCenter

end

end OAI
