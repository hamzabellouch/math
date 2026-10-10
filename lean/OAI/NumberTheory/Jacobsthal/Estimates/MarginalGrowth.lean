import OAI.NumberTheory.Jacobsthal.Sieve.ExponentialMesh

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarginalGrowth

open _root_.Set _root_.Filter
open scoped Topology
open ExponentialMesh

noncomputable def factor (L κ w S : ℝ) : ℝ :=
  (1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*
    Real.exp (L*(1+S)^3*mesh κ w)*(1+20*mesh κ w)

theorem factor_pos (L κ w S : ℝ) : 0 < factor L κ w S := by
  have hm := mesh_pos κ w
  unfold factor
  positivity

theorem factor_exp_upper (L κ w S : ℝ) : factor L κ w S ≤
    Real.exp (Real.exp (-(κ/2)*Real.sqrt (Real.log w))+L*(1+S)^3*mesh κ w+20*mesh κ w) := by
  have hm := mesh_pos κ w
  have h1 : 1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ Real.exp (Real.exp (-(κ/2)*Real.sqrt (Real.log w))) := by
    simpa only [add_comm] using Real.add_one_le_exp (Real.exp (-(κ/2)*Real.sqrt (Real.log w)))
  have h2 : 1+20*mesh κ w ≤ Real.exp (20*mesh κ w) := by
    simpa only [add_comm] using Real.add_one_le_exp (20*mesh κ w)
  unfold factor
  rw [Real.exp_add,Real.exp_add]
  exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) h2 (by positivity) (by positivity)

theorem factor_power_bounded {A L κ : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hκ : 0 < κ) :
    ∀ᶠ w : ℝ in atTop, ∀ S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 → ∀ n : ℕ,
      (n:ℝ) ≤ A*(Real.log w)^3 → (factor L κ w S)^n ≤ 2 := by
  have ht := log_power_exp_tendsto (A*(21+8*L)) 12 (show 0 < κ/2 by positivity)
  filter_upwards [ht.eventually (eventually_lt_nhds (Real.log_pos (by norm_num : (1:ℝ) < 2))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with w hsmall hlog
  intro S hS hSP n hn
  let e := Real.exp (-(κ/2)*Real.sqrt (Real.log w))
  let τ := mesh κ w
  let a := e+L*(1+S)^3*τ+20*τ
  have hτ : 0 < τ := mesh_pos κ w
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hτe : τ ≤ e := by
    apply (mesh_upper κ w).trans
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_nonneg (Real.log w)]
  have hp3 : 1 ≤ (Real.log w)^3 := one_le_pow₀ hlog
  have hp9 : 1 ≤ (Real.log w)^9 := one_le_pow₀ hlog
  have he9 : e ≤ (Real.log w)^9*e := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp9 he
  have hSp : 1+S ≤ 2*(Real.log w)^3 := by linarith
  have hmid : L*(1+S)^3*τ ≤ 8*L*(Real.log w)^9*e := by
    calc
      _ ≤ (L*(2*(Real.log w)^3)^3)*e := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hSp 3) hL) hτe hτ.le (by positivity)
      _ = _ := by ring
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha : a ≤ (21+8*L)*(Real.log w)^9*e := by dsimp [a]; nlinarith
  have hna : (n:ℝ)*a ≤ (A*(21+8*L))*(Real.log w)^12*e := by
    calc
      _ ≤ (A*(Real.log w)^3)*((21+8*L)*(Real.log w)^9*e) := mul_le_mul hn ha ha0 (by positivity)
      _ = _ := by ring
  have hpow := pow_le_pow_left₀ (factor_pos L κ w S).le (factor_exp_upper L κ w S) n
  rw [← Real.exp_nat_mul] at hpow
  calc
    _ ≤ Real.exp ((n:ℝ)*a) := hpow
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (hna.trans hsmall.le)
    _ = _ := Real.exp_log (by norm_num)

end NumberTheoryLean.MarginalGrowth

end

end Erdos970

end OAI
