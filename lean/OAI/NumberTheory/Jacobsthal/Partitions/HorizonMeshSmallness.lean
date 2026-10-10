import OAI.NumberTheory.Jacobsthal.Estimates.UniformFailureBudget
import OAI.NumberTheory.Jacobsthal.Sieve.ExponentialMesh

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.HorizonMeshSmallness

open _root_.Set _root_.Filter
open scoped Topology
open UniformFailureBudget ExponentialMesh

theorem horizon_mesh_smallness {A D κ : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hκ : 0 < κ) :
    ∀ᶠ w : ℝ in atTop, ∀ S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 → ∀ N : ℕ,
      (N:ℝ) ≤ A*(Real.log w)^3 →
      2*mesh κ w ≤ 1 ∧ 4*(N:ℝ)*mesh κ w ≤ 1 ∧ D*(1+S)^3*mesh κ w ≤ 1 ∧
        upperDisplacement S (mesh κ w) N+mesh κ w ≤ 1 := by
  filter_upwards [log_power_exp_absorption 2 0 hκ,
    log_power_exp_absorption (4*A) 3 hκ,
    log_power_exp_absorption (8*D) 9 hκ,
    log_power_exp_absorption (24*A+1) 6 hκ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with w htwo hclockB hparentB hupperB hlog
  intro S hS hSP N hNP
  let x := Real.log w
  let e := Real.exp (-κ*Real.sqrt (Real.log w))
  let τ := mesh κ w
  have hx : 1 ≤ x := hlog
  have hx0 : 0 ≤ x := by linarith
  have hx3 : 1 ≤ x^3 := one_le_pow₀ hx
  have hx6 : 1 ≤ x^6 := one_le_pow₀ hx
  have hSp : S+1 ≤ 2*x^3 := by change S ≤ x^3 at hSP; linarith
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hτ : 0 < τ := mesh_pos κ w
  have hτe : τ ≤ e := mesh_upper κ w
  have hsmall : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [Real.sqrt_nonneg (Real.log w)]
  have htwo' : 2*τ ≤ 1 := by
    have ht : 2*e ≤ Real.exp (-(κ/2)*Real.sqrt (Real.log w)) := by
      simpa only [pow_zero,mul_one] using htwo
    exact (mul_le_mul_of_nonneg_left hτe (by norm_num)).trans (ht.trans hsmall)
  have hclock : 4*(N:ℝ)*τ ≤ 1 := by
    calc
      _ ≤ (4*(A*x^3))*e := mul_le_mul (by nlinarith : 4*(N:ℝ) ≤ 4*(A*x^3)) hτe hτ.le (by positivity)
      _ = (4*A)*x^3*e := by ring
      _ ≤ _ := hclockB.trans hsmall
  have hparent : D*(1+S)^3*τ ≤ 1 := by
    calc
      _ ≤ (D*(2*x^3)^3)*e := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith : 1+S ≤ 2*x^3) 3) hD)
        hτe hτ.le (by positivity)
      _ = (8*D)*x^9*e := by ring
      _ ≤ _ := hparentB.trans hsmall
  have hU : upperDisplacement S τ N ≤ 24*A*x^6*e := by
    have hexp := exp_increment (show 0 ≤ 4*(N:ℝ)*τ by positivity) hclock
    have hNmul : 12*(N:ℝ)*τ ≤ 12*(A*x^3)*e :=
      mul_le_mul (by nlinarith : 12*(N:ℝ) ≤ 12*(A*x^3)) hτe hτ.le (by positivity)
    calc
      _ ≤ (S+1)*(12*(N:ℝ)*τ) := by
        unfold upperDisplacement
        apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ S+1)
        nlinarith
      _ ≤ (2*x^3)*(12*(A*x^3)*e) := mul_le_mul hSp hNmul (by positivity) (by positivity)
      _ = _ := by ring
  have he6 : e ≤ x^6*e := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx6 he
  have hUpper : upperDisplacement S τ N+τ ≤ 1 := by
    calc
      _ ≤ (24*A+1)*x^6*e := by nlinarith
      _ ≤ _ := hupperB.trans hsmall
  exact ⟨htwo',hclock,hparent,hUpper⟩

end NumberTheoryLean.HorizonMeshSmallness

end

end Erdos970

end OAI
