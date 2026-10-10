import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real

namespace OAI

namespace SiegelZeros


namespace SiegelZerosAwei.W46

noncomputable def masterRHS (S₁ S₂ M U C C_H ell delta L m k : ℝ) : ℝ :=
  3 / 4 * (1 + S₂ / S₁) +
    (C + 1 / 2 * (1 + S₂ / S₁)) * (ell / L) +
    C * delta * (L / ell) +
    (C_H + (1 + S₂ / S₁) * k) / L +
    (C * M * U + 1 / 2 * M * m) / (S₁ * L)

theorem master_identity
    (S₁ S₂ M U C C_H ell delta L m k : ℝ)
    (hS : S₁ ≠ 0) (hL : L ≠ 0) (hell : ell ≠ 0) :
    masterRHS S₁ S₂ M U C C_H ell delta L m k =
      1 + ((M / 2 * m + (S₁ + S₂) * (3 / 4 * L + 1 / 2 * ell + k)) -
        (S₁ * (L - C * ell - C * (delta * (L ^ 2) / ell) - C_H) - C * M * U)) /
          (S₁ * L) := by
  unfold masterRHS
  field_simp [hS, hL, hell]
  ring

theorem master_from_real_bounds
    (S₁ S₂ M U C C_H ell delta L n m k B : ℝ)
    (hS : 0 < S₁) (hL : 0 < L) (hell : 0 < ell)
    (hn : n = 3 / 4 * L)
    (harch : B ≤ M / 2 * m + (S₁ + S₂) * (n + 1 / 2 * ell + k))
    (hfinite : S₁ * (L - C * ell - C * (delta * (L ^ 2) / ell) - C_H) -
      C * M * U ≤ B) :
    1 ≤ masterRHS S₁ S₂ M U C C_H ell delta L m k := by
  rw [master_identity S₁ S₂ M U C C_H ell delta L m k
    (ne_of_gt hS) (ne_of_gt hL) (ne_of_gt hell)]
  have hcomp := hfinite.trans harch
  rw [hn] at hcomp
  have hdiff := sub_nonneg.mpr hcomp
  have hquot := div_nonneg hdiff (le_of_lt (mul_pos hS hL))
  linarith

theorem master_from_log_bounds
    (S₁ S₂ M U N C C_H ell delta B : ℝ)
    (hS : 0 < S₁) (hU : 1 < U) (hell : 0 < ell)
    (hn : Real.log N = 3 / 4 * Real.log U)
    (harch : B ≤ M / 2 * Real.log M +
      (S₁ + S₂) * (Real.log N + 1 / 2 * ell + Real.log 8))
    (hfinite : S₁ * (Real.log U - C * ell -
      C * (delta * ((Real.log U) ^ 2) / ell) - C_H) - C * M * U ≤ B) :
    1 ≤ 3 / 4 * (1 + S₂ / S₁) +
      (C + 1 / 2 * (1 + S₂ / S₁)) * (ell / Real.log U) +
      C * delta * (Real.log U / ell) +
      (C_H + (1 + S₂ / S₁) * Real.log 8) / Real.log U +
      (C * M * U + 1 / 2 * M * Real.log M) / (S₁ * Real.log U) := by
  exact master_from_real_bounds S₁ S₂ M U C C_H ell delta
    (Real.log U) (Real.log N) (Real.log M) (Real.log 8) B
    hS (Real.log_pos hU) hell hn harch hfinite





theorem log_three_quarters_power (N : ℝ) (hN : 0 < N) :
    Real.log N = 3 / 4 * Real.log (N ^ (4 / 3 : ℝ)) := by
  rw [Real.log_rpow hN]
  ring

theorem master_from_power_scale
    (S₁ S₂ M N q C C_H delta B : ℝ)
    (hS : 0 < S₁) (hN : 1 < N) (hq : 1 < q)
    (harch : B ≤ M / 2 * Real.log M +
      (S₁ + S₂) * (Real.log N + 1 / 2 * Real.log q + Real.log 8))
    (hfinite : S₁ * (Real.log (N ^ (4 / 3 : ℝ)) - C * Real.log q -
      C * (delta * ((Real.log (N ^ (4 / 3 : ℝ))) ^ 2) / Real.log q) - C_H) -
      C * M * N ^ (4 / 3 : ℝ) ≤ B) :
    1 ≤ masterRHS S₁ S₂ M (N ^ (4 / 3 : ℝ)) C C_H (Real.log q) delta
      (Real.log (N ^ (4 / 3 : ℝ))) (Real.log M) (Real.log 8) := by
  exact master_from_log_bounds S₁ S₂ M (N ^ (4 / 3 : ℝ)) N C C_H
    (Real.log q) delta B hS (Real.one_lt_rpow hN (by norm_num))
    (Real.log_pos hq) (log_three_quarters_power N (by linarith)) harch hfinite

end SiegelZerosAwei.W46



open Filter
open scoped Topology

namespace SiegelZerosAwei.W50

theorem one_le_allowances_of_eventual_master
    {ι : Type*} {l : Filter ι} [NeBot l]
    (a b e₁ e₂ e₃ : ι → ℝ) (A B : ℝ)
    (hmaster : ∀ᶠ n in l, 1 ≤ a n + b n + e₁ n + e₂ n + e₃ n)
    (ha : ∀ᶠ n in l, a n ≤ A) (hb : ∀ᶠ n in l, b n ≤ B)
    (he₁ : Tendsto e₁ l (𝓝 0)) (he₂ : Tendsto e₂ l (𝓝 0))
    (he₃ : Tendsto e₃ l (𝓝 0)) : 1 ≤ A + B := by
  have hlimit : Tendsto (fun n => A + B + (e₁ n + e₂ n + e₃ n)) l
      (𝓝 (A + B)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add ((he₁.add he₂).add he₃))
  apply ge_of_tendsto hlimit
  filter_upwards [hmaster, ha, hb] with n hm hnA hnB
  linarith

theorem false_of_eventual_master_allowances
    {ι : Type*} {l : Filter ι} [NeBot l]
    (a b e₁ e₂ e₃ : ι → ℝ)
    (hmaster : ∀ᶠ n in l, 1 ≤ a n + b n + e₁ n + e₂ n + e₃ n)
    (ha : ∀ᶠ n in l, a n ≤ 13 / 16) (hb : ∀ᶠ n in l, b n ≤ 1 / 16)
    (he₁ : Tendsto e₁ l (𝓝 0)) (he₂ : Tendsto e₂ l (𝓝 0))
    (he₃ : Tendsto e₃ l (𝓝 0)) : False := by
  have h := one_le_allowances_of_eventual_master a b e₁ e₂ e₃
    (13 / 16) (1 / 16) hmaster ha hb he₁ he₂ he₃
  norm_num at h

theorem second_term_eventually_le
    {ι : Type*} {l : Filter ι} (r t : ι → ℝ) (C t₀ : ℝ)
    (hr : ∀ᶠ n in l, r n ≤ 1 / 12)
    (htnonneg : ∀ᶠ n in l, 0 ≤ t n)
    (ht : Tendsto t l (𝓝 t₀))
    (hallow : (C + 13 / 24) * t₀ < 1 / 16) :
    ∀ᶠ n in l, (C + 1 / 2 * (1 + r n)) * t n ≤ 1 / 16 := by
  have hlimit : Tendsto (fun n => (C + 13 / 24) * t n) l
      (𝓝 ((C + 13 / 24) * t₀)) := tendsto_const_nhds.mul ht
  have hevent := hlimit.eventually_lt_const hallow
  filter_upwards [hr, htnonneg, hevent] with n hnr hnt hnlimit
  have hcoef : C + 1 / 2 * (1 + r n) ≤ C + 13 / 24 := by linarith
  exact (mul_le_mul_of_nonneg_right hcoef hnt).trans hnlimit.le

theorem false_of_master_ratio_limit
    {ι : Type*} {l : Filter ι} [NeBot l]
    (r t e₁ e₂ e₃ : ι → ℝ) (C t₀ : ℝ)
    (hmaster : ∀ᶠ n in l,
      1 ≤ 3 / 4 * (1 + r n) + (C + 1 / 2 * (1 + r n)) * t n +
        e₁ n + e₂ n + e₃ n)
    (hr : ∀ᶠ n in l, r n ≤ 1 / 12)
    (htnonneg : ∀ᶠ n in l, 0 ≤ t n)
    (ht : Tendsto t l (𝓝 t₀))
    (hallow : (C + 13 / 24) * t₀ < 1 / 16)
    (he₁ : Tendsto e₁ l (𝓝 0)) (he₂ : Tendsto e₂ l (𝓝 0))
    (he₃ : Tendsto e₃ l (𝓝 0)) : False := by
  apply false_of_eventual_master_allowances
    (fun n => 3 / 4 * (1 + r n))
    (fun n => (C + 1 / 2 * (1 + r n)) * t n)
    e₁ e₂ e₃ hmaster
  · filter_upwards [hr] with n hn
    linarith
  · exact second_term_eventually_le r t C t₀ hr htnonneg ht hallow
  · exact he₁
  · exact he₂
  · exact he₃

theorem false_of_exact_master
    {ι : Type*} {l : Filter ι} [NeBot l]
    (S₁ S₂ M U ell delta L m : ι → ℝ) (C C_H k t₀ : ℝ)
    (hmaster : ∀ᶠ n in l,
      1 ≤ W46.masterRHS (S₁ n) (S₂ n) (M n) (U n) C C_H
        (ell n) (delta n) (L n) (m n) k)
    (hr : ∀ᶠ n in l, S₂ n / S₁ n ≤ 1 / 12)
    (htnonneg : ∀ᶠ n in l, 0 ≤ ell n / L n)
    (ht : Tendsto (fun n => ell n / L n) l (𝓝 t₀))
    (hallow : (C + 13 / 24) * t₀ < 1 / 16)
    (he₁ : Tendsto (fun n => C * delta n * (L n / ell n)) l (𝓝 0))
    (he₂ : Tendsto (fun n => (C_H + (1 + S₂ n / S₁ n) * k) / L n) l (𝓝 0))
    (he₃ : Tendsto (fun n =>
      (C * M n * U n + 1 / 2 * M n * m n) / (S₁ n * L n)) l (𝓝 0)) :
    False := by
  exact false_of_master_ratio_limit (fun n => S₂ n / S₁ n)
    (fun n => ell n / L n) _ _ _ C t₀ hmaster hr htnonneg ht hallow he₁ he₂ he₃

end SiegelZerosAwei.W50


end SiegelZeros

end OAI
