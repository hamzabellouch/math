import OAI.MeasureTheory.Falconer.Recursion.PlanarWeakDepth

namespace OAI

/-! The linear auxiliary-depth inequalities imply the exact multiplicative
budgets needed by the original planar graph obstruction. -/
namespace Falconer

 theorem planar_weak_parameters {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (Nmin : ℕ) :
    ∃ ε : ℝ, ∃ n0 : ℕ, 0 < ε ∧ 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∃ l : ℕ, l ≤ n ∧ Nmin ≤ n+2*l+10 ∧
      let W := Real.exp (ε*(n:ℝ)*Real.log 2)
      let M := (2:ℝ)^(l+2)
      let r := (1/2:ℝ)^l
      let S := Real.exp (γ*((n+2*l+10:ℕ):ℝ)*Real.log 2)
      1 ≤ W ∧ 1 ≤ M ∧ 0 < r ∧ r ≤ 1 ∧ (1/2:ℝ)^n ≤ r ∧
        W*r^(2*κ) ≤ (W⁻¹)^6/128 ∧ 4000000*(64*W^6)^5*M^6 ≤ S ∧
        ∀ P : ℝ, 0 < P → Real.log P ≤ (1-4*κ)*(n:ℝ)*Real.log 2 →
          Real.log (655*M*P) ≤ (1-κ)*((n+2*l+10:ℕ):ℝ)*Real.log 2 := by
  obtain ⟨ε,n0,hε,hn0,hdepth⟩ := planar_weak_depth hγ hκ hκ1 Nmin
  refine ⟨ε,n0,hε,hn0,?_⟩
  intro n hn
  obtain ⟨l,hln,hN,hsep,hbudget,hlog⟩ := hdepth n hn
  let W := Real.exp (ε*(n:ℝ)*Real.log 2)
  let M := (2:ℝ)^(l+2)
  let r := (1/2:ℝ)^l
  let S := Real.exp (γ*((n+2*l+10:ℕ):ℝ)*Real.log 2)
  have hW : 0 < W := Real.exp_pos _
  have hM : 0 < M := by dsimp [M]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hWlog : Real.log W = ε*(n:ℝ)*Real.log 2 := Real.log_exp _
  have hMlog : Real.log M = ((l:ℝ)+2)*Real.log 2 := by
    dsimp [M]
    rw [Real.log_pow]
    push_cast
    rfl
  have hrlog : Real.log r = -(l:ℝ)*Real.log 2 := by
    dsimp [r]
    rw [Real.log_pow,Real.log_div (by norm_num) (by norm_num),Real.log_one]
    ring
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hr1 : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hscale : (1/2:ℝ)^n ≤ r := pow_le_pow_of_le_one (by norm_num) (by norm_num) hln
  refine ⟨l,hln,hN,hW1,hM1,hr,hr1,hscale,?_,?_,?_⟩
  · apply (Real.log_le_log_iff (mul_pos hW (Real.rpow_pos_of_pos hr _)) (by positivity)).1
    change Real.log (W*r^(2*κ)) ≤ Real.log ((W⁻¹)^6/128)
    have hleft : Real.log (W*r^(2*κ)) = Real.log W+2*κ*Real.log r := by
      rw [Real.log_mul hW.ne' (Real.rpow_pos_of_pos hr _).ne',Real.log_rpow hr]
    have hright : Real.log ((W⁻¹)^6/128) = -6*Real.log W-Real.log 128 := by
      rw [Real.log_div (by positivity) (by norm_num),Real.log_pow,Real.log_inv]
      norm_num
    rw [hleft,hright,hWlog,hrlog]
    nlinarith only [hsep]
  · apply (Real.log_le_log_iff (by positivity) (Real.exp_pos _)).1
    change Real.log (4000000*(64*W^6)^5*M^6) ≤ _
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow,
      hWlog,hMlog,Real.log_exp]
    have hc : Real.log (4000000*(64:ℝ)^5) = Real.log 4000000+5*Real.log 64 := by
      rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
      norm_num
    rw [hc] at hbudget
    convert hbudget using 1; ring
  · intro P hP hPlog
    rw [Real.log_mul (mul_ne_zero (by norm_num) hM.ne') hP.ne',
      Real.log_mul (by norm_num) hM.ne',hMlog]
    linarith only [hlog,hPlog]

end Falconer

end OAI
