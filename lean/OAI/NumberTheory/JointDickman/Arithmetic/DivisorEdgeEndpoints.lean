import OAI.NumberTheory.JointDickman.Amplification.NonzeroGraphAtoms
import Mathlib.RingTheory.Coprime.Lemmas

namespace OAI

/-! # The actual integer endpoints of a divisor-graph edge -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- Forward reindexing at the actual natural quotients, for either sign
of the lag. The shifted endpoint is positive automatically. -/
theorem natural_divisor_edge_endpoints {a b c m : ℕ} {j : ℤ}
    (hc : 0 < c) (ha : c ∣ a*m+1) (hb : c ∣ b*m+1)
    (he : (a : ℤ)-b = j*c) :
    ((b*((a*m+1)/c) : ℕ) : ℤ)+j = ((a*((b*m+1)/c) : ℕ) : ℤ) := by
  have hqa : (c : ℤ)*((a*m+1)/c : ℕ) = (a : ℤ)*m+1 := by
    exact_mod_cast Nat.mul_div_cancel' ha
  have hqb : (c : ℤ)*((b*m+1)/c : ℕ) = (b : ℤ)*m+1 := by
    exact_mod_cast Nat.mul_div_cancel' hb
  change (b : ℤ)*(((a*m+1)/c : ℕ) : ℤ)+j =
    (a : ℤ)*(((b*m+1)/c : ℕ) : ℤ)
  apply mul_left_cancel₀ (show (c : ℤ) ≠ 0 by exact_mod_cast (ne_of_gt hc))
  linear_combination (b : ℤ)*hqa - (a : ℤ)*hqb - he

/-- The inverse congruence reconstructs a nonnegative multiplier. It uses
only coprimality with the lag and positivity of the endpoint. -/
theorem natural_divisor_edge_inverse {a b c n : ℕ} {j : ℤ}
    (ha : 0 < a) (hc : 0 < c) (hn : 0 < n) (hb : b ∣ n)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    (hdiv : (a : ℤ) ∣ (n : ℤ)+j) :
    ∃! m : ℕ, c*(n/b) = a*m+1 := by
  have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hb hn
  have hnb : b*(n/b) = n := Nat.mul_div_cancel' hb
  have hcop' : IsCoprime (a : ℤ) j := by
    have h := hcop.isCoprime
    exact h.of_isCoprime_of_dvd_right Int.dvd_natAbs_self
  have hd' : (a : ℤ) ∣ (b : ℤ)*((n/b : ℕ) : ℤ)+j := by
    have hid : (b : ℤ)*((n/b : ℕ) : ℤ) = n := by exact_mod_cast hnb
    rwa [hid]
  obtain ⟨m,hm⟩ := (divisor_edge_iff he hcop').mpr hd'
  have hnq : 0 < n/b := Nat.div_pos (Nat.le_of_dvd hn hb) hb0
  have hmul : 0 ≤ (a : ℤ)*m := by
    have hcz : (1 : ℤ) ≤ (c : ℤ)*((n/b : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_pos hc hnq
    linarith
  have hm0 : 0 ≤ m := nonneg_of_mul_nonneg_right hmul (by exact_mod_cast ha)
  refine ⟨m.toNat,?_,?_⟩
  · have heq : (c : ℤ)*((n/b : ℕ) : ℤ) = (a : ℤ)*(m.toNat : ℤ)+1 := by
      simpa only [Int.toNat_of_nonneg hm0] using hm
    exact_mod_cast heq
  · intro m' hm'
    apply Nat.eq_of_mul_eq_mul_left ha
    have hmnat : c*(n/b) = a*m.toNat+1 := by
      have heq : (c : ℤ)*((n/b : ℕ) : ℤ) = (a : ℤ)*(m.toNat : ℤ)+1 := by
        simpa only [Int.toNat_of_nonneg hm0] using hm
      exact_mod_cast heq
    omega

/-- Fixed-multiplier invariance identifies each original centered label
with its new graph endpoint. This holds simultaneously for all coefficients. -/
theorem centered_binLabel_graph_endpoints {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (μ : ℂ) (B : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ D ∈ (auxiliaryPrimes B).powerset,
      ∀ E ∈ (auxiliaryPrimes B).powerset, ∀ a m : ℕ,
      (∏ p ∈ D, p) ∣ a*m+1 →
      movingBinLabel J k z N (a*m+1)-μ =
        movingBinLabel J k z N ((∏ p ∈ E, p)*((a*m+1)/(∏ p ∈ D, p)))-μ := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (binLabel_auxiliary_multipliers J hJ k hk z B)] with N hN
  intro D hD E hE a m hdiv
  have hquot : (∏ p ∈ D, p)*((a*m+1)/(∏ p ∈ D, p)) = a*m+1 :=
    Nat.mul_div_cancel' hdiv
  have hc := hN D hD ((a*m+1)/(∏ p ∈ D, p))
  have hb := hN E hE ((a*m+1)/(∏ p ∈ D, p))
  change binLabel _ z (a*m+1)-μ = binLabel _ z _-μ
  rw [hquot] at hc
  rw [hc,hb]

end JointDickman

end OAI
