import Mathlib.Analysis.Complex.Exponential
import OAI.NumberTheory.Jacobsthal.Primes.PrimeGridGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ExponentialMesh

open _root_.Set _root_.Filter
open scoped Topology

noncomputable def mesh (κ w : ℝ) : ℝ := 1/(⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊:ℝ)

theorem mesh_pos (κ w : ℝ) : 0 < mesh κ w := by
  apply one_div_pos.mpr
  exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos (κ*Real.sqrt (Real.log w)))

theorem mesh_upper (κ w : ℝ) : mesh κ w ≤ Real.exp (-κ*Real.sqrt (Real.log w)) := by
  have h := one_div_le_one_div_of_le (Real.exp_pos (κ*Real.sqrt (Real.log w)))
    (Nat.le_ceil (Real.exp (κ*Real.sqrt (Real.log w))))
  have he : 1/Real.exp (κ*Real.sqrt (Real.log w)) = Real.exp (-κ*Real.sqrt (Real.log w)) := by
    rw [one_div,← Real.exp_neg]
    congr 1
    ring
  exact h.trans_eq he

theorem mesh_reciprocal (κ w : ℝ) : 1/mesh κ w = (⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊:ℝ) := by
  unfold mesh
  simp

theorem reciprocal_upper {κ : ℝ} (hκ : 0 ≤ κ) (w : ℝ) :
    1/mesh κ w ≤ 2*Real.exp (κ*Real.sqrt (Real.log w)) := by
  rw [mesh_reciprocal]
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (κ*Real.sqrt (Real.log w))).le
  have he : 1 ≤ Real.exp (κ*Real.sqrt (Real.log w)) := Real.one_le_exp_iff.mpr (by positivity)
  linarith

theorem mesh_le_one {κ : ℝ} (hκ : 0 ≤ κ) (w : ℝ) : mesh κ w ≤ 1 := by
  apply (mesh_upper κ w).trans
  apply Real.exp_le_one_iff.mpr
  nlinarith [Real.sqrt_nonneg (Real.log w)]

theorem half_sqrt_lower {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x/2 ≤ Real.sqrt ((1/2:ℝ)*x) := by
  apply (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt x/2) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity : 0 ≤ (1/2:ℝ)*x)]
  nlinarith [Real.sq_sqrt hx]

theorem prime_error_dominated {c κ w : ℝ} (hκ : 0 ≤ κ) (hc : 2*κ ≤ c) (hw : 0 ≤ Real.log w) :
    Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)) ≤ Real.exp (-κ*Real.sqrt (Real.log w)) := by
  have hc0 : 0 ≤ c := by linarith
  have hhalf := half_sqrt_lower hw
  have hmul := mul_le_mul_of_nonneg_left hhalf hc0
  have hcmp := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (Real.log w))
  apply Real.exp_le_exp.mpr
  nlinarith

theorem prime_error_over_mesh {c κ w : ℝ} (hκ : 0 ≤ κ) (hc : 4*κ ≤ c) (hw : 0 ≤ Real.log w) :
    Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/mesh κ w ≤
      2*Real.exp (-κ*Real.sqrt (Real.log w)) := by
  have hp := prime_error_dominated (c:=c) (κ:=2*κ) (by positivity) (by linarith) hw
  have hr := reciprocal_upper hκ w
  have hm := mesh_pos κ w
  calc
    _ = Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))*(1/mesh κ w) := by ring
    _ ≤ Real.exp (-(2*κ)*Real.sqrt (Real.log w))*(2*Real.exp (κ*Real.sqrt (Real.log w))) :=
      mul_le_mul hp hr (by positivity) (Real.exp_pos _).le
    _ = _ := by
      rw [show Real.exp (-(2*κ)*Real.sqrt (Real.log w))*(2*Real.exp (κ*Real.sqrt (Real.log w))) =
        2*(Real.exp (-(2*κ)*Real.sqrt (Real.log w))*Real.exp (κ*Real.sqrt (Real.log w))) by ring,
        ← Real.exp_add]
      congr 2
      ring

theorem log_pow_sqrt (n : ℕ) {w : ℝ} (hw : 0 ≤ Real.log w) :
    (Real.sqrt (Real.log w))^(2*n) = (Real.log w)^n := by
  rw [pow_mul,Real.sq_sqrt hw]

theorem log_power_exp_tendsto (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => C*(Real.log w)^n*Real.exp (-c*Real.sqrt (Real.log w))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => C*x^(2*n)*Real.exp (-c*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*n:ℕ):ℝ) c hc).const_mul C
    simpa only [Real.rpow_natCast,mul_zero,mul_assoc] using h
  apply Tendsto.congr' _ (hbase.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with w hw
  simp only [Function.comp_apply,log_pow_sqrt n hw]

theorem log_power_exp_absorption (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ w : ℝ in atTop, C*(Real.log w)^n*Real.exp (-c*Real.sqrt (Real.log w)) ≤
      Real.exp (-(c/2)*Real.sqrt (Real.log w)) := by
  have ht := log_power_exp_tendsto C n (show 0 < c/2 by positivity)
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))] with w hw
  calc
    _ = (C*(Real.log w)^n*Real.exp (-(c/2)*Real.sqrt (Real.log w)))*
        Real.exp (-(c/2)*Real.sqrt (Real.log w)) := by
      rw [show -c*Real.sqrt (Real.log w) = -(c/2)*Real.sqrt (Real.log w)+-(c/2)*Real.sqrt (Real.log w) by ring,
        Real.exp_add]
      ring
    _ ≤ 1*Real.exp (-(c/2)*Real.sqrt (Real.log w)) := mul_le_mul_of_nonneg_right hw.le (Real.exp_pos _).le
    _ = _ := one_mul _

theorem exp_increment {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x-1 ≤ 3*x := by
  have h := Real.abs_exp_sub_one_le (x:=x) (by rw [abs_of_nonneg hx]; exact hx1)
  rw [abs_of_nonneg hx] at h
  linarith [le_abs_self (Real.exp x-1)]

end NumberTheoryLean.ExponentialMesh

end

end Erdos970

end OAI
