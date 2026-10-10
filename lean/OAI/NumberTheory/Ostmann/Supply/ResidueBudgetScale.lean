import OAI.NumberTheory.Ostmann.Supply.ResidueRatio

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Preliminaries
open scoped BigOperators

theorem eventually_le_collisionScale_fourth :
    ∀ᶠ Q : ℕ in atTop, Q ≤ collisionScale 4 (Q^4) := by
  have hx : Tendsto (fun Q : ℕ => (Q:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlittle := isLittleO_log_rpow_rpow_atTop (5:ℕ) (show (0:ℝ)<1 by norm_num)
  have hbound := hlittle.bound (show (0:ℝ)<1/(4:ℝ)^5 by norm_num)
  filter_upwards [hx.eventually hbound,
    (Real.tendsto_log_atTop.comp hx).eventually_ge_atTop 1] with Q hsmall hlog
  change 1 ≤ Real.log (Q:ℝ) at hlog
  have hl : 0 < Real.log (Q:ℝ) := by linarith
  have hqn : 0 ≤ (Q:ℝ) := Nat.cast_nonneg _
  simp only [Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hl.le _), abs_of_nonneg hqn] at hsmall
  have hsqrt : Real.sqrt ((Q:ℝ)^4) = (Q:ℝ)^2 := by
    rw [show (Q:ℝ)^4=((Q:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  have hden : 0 < (4*Real.log (Q:ℝ))^5 := by positivity
  have hfrac : (Q:ℝ) ≤ (Q:ℝ)^2/(4*Real.log (Q:ℝ))^5 := by
    apply (le_div_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall ((by positivity) : 0 ≤ (4:ℝ)^5)
    have hh' : (4*Real.log (Q:ℝ))^5 ≤ (Q:ℝ) := by nlinarith [hh]
    simpa [pow_two] using mul_le_mul_of_nonneg_left hh' hqn
  unfold collisionScale
  simp only [Nat.cast_pow, hsqrt, Real.log_pow, Nat.cast_ofNat, Nat.reduceAdd]
  exact (Nat.le_floor_iff (div_nonneg (sq_nonneg _) hden.le)).mpr hfrac

theorem eventually_ratioWeightedSum_le (d : Decomposition) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Q : ℕ in atTop,
      ratioWeightedSum d Q ≤ C*Real.log (Real.log (Q:ℝ)) := by
  let C := collisionConstant 4*(Real.log 4+1)
  have hC : 0<C := mul_pos (collisionConstant_pos 4) (by positivity : 0<Real.log 4+1)
  refine ⟨C,hC,?_⟩
  have hpow : Tendsto (fun Q : ℕ => Q^4) atTop atTop := tendsto_pow_atTop (by decide)
  have hx : Tendsto (fun Q : ℕ => (Q:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hll := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hx)).eventually_ge_atTop 1
  filter_upwards [eventually_le_collisionScale_fourth,
    hpow.eventually (eventually_upperWindow_collision d),hll,
    (Real.tendsto_log_atTop.comp hx).eventually_ge_atTop 1] with Q hscale hcollision hloglog hlog
  change 1 ≤ Real.log (Q:ℝ) at hlog
  change 1 ≤ Real.log (Real.log (Q:ℝ)) at hloglog
  have hl : 0<Real.log (Q:ℝ) := by linarith
  have he : Real.log (Real.log ((Q^4:ℕ):ℝ)) = Real.log 4+Real.log (Real.log (Q:ℝ)) := by
    rw [Nat.cast_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact Real.log_mul (by norm_num) hl.ne'
  calc
    ratioWeightedSum d Q ≤ ratioWeightedSum d (collisionScale 4 (Q^4)) :=
      ratioWeightedSum_mono d hscale
    _ ≤ upperWindowCollision d (Q^4) := ratioWeightedSum_le_collision d _
    _ ≤ collisionConstant 4*Real.log (Real.log ((Q^4:ℕ):ℝ)) := hcollision.2.2
    _ ≤ C*Real.log (Real.log (Q:ℝ)) := by
      rw [he]
      have h4 := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
      have hh := mul_le_mul_of_nonneg_left hloglog h4
      dsimp [C]
      have hhC := mul_le_mul_of_nonneg_left hh (collisionConstant_pos 4).le
      nlinarith

end Ostmann.Supply

end

end OAI
