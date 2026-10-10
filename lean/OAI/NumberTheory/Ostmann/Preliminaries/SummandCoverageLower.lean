import OAI.NumberTheory.Ostmann.Preliminaries.SummandSizePrimeBand
import OAI.NumberTheory.Ostmann.Preliminaries.SummandTails

namespace OAI

/-! # The counting lower bound from prime coverage -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem EventuallyPrimeSumset.prime_coverage_card {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N₀ : ℕ, ∀ N : ℕ,
      (Nat.primesLE N).card ≤ N₀ + (summandPrefix A N).card * (summandPrefix B N).card := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨N₀, ?_⟩
  intro N
  let U := (Nat.primesLE N).filter fun p => N₀ ≤ p
  let V := (Nat.primesLE N).filter fun p => ¬ N₀ ≤ p
  have hV : V.card ≤ N₀ := by
    have hsub : V ⊆ Finset.range N₀ := by
      intro p hp
      exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hp).2; omega)
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hU : U.card ≤ (summandPrefix A N).card * (summandPrefix B N).card := by
    have hsub : U ⊆ ((summandPrefix A N) ×ˢ (summandPrefix B N)).image (fun ab => ab.1 + ab.2) := by
      intro p hp
      obtain ⟨hpN, hpprime⟩ := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
      obtain ⟨a, ha, b, hb, hab⟩ :=
        mem_sumset.mp ((hN p (Finset.mem_filter.mp hp).2).mpr hpprime)
      refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨?_, ?_⟩, hab⟩
      · exact (mem_summandPrefix A N a).mpr ⟨ha, by omega⟩
      · exact (mem_summandPrefix B N b).mpr ⟨hb, by omega⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans_eq (Finset.card_product _ _))
  have hsplit := Finset.card_filter_add_card_filter_not (s := Nat.primesLE N) (fun p => N₀ ≤ p)
  change U.card + V.card = (Nat.primesLE N).card at hsplit
  omega

 theorem EventuallyPrimeSumset.coverage_product_lower {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) / (4 * Real.log (N : ℝ)) ≤
      ((summandPrefix A N).card : ℝ) * (summandPrefix B N).card := by
  obtain ⟨N₀, hcoverage⟩ := h.prime_coverage_card
  have htheta := tendsto_natCast_atTop_atTop.eventually
    (actual_theta_relative_small (by norm_num : (0 : ℝ) < 1 / 2))
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).const_mul_left
    (N₀ : ℝ)).bound (by norm_num : (0 : ℝ) < 1 / 4)
  have hsmallN := tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [htheta, hsmallN, eventually_ge_atTop (2 : ℕ)] with N hθ hs hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hNp : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have herr : (N₀ : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) / 4 := by
    simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hNp,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N₀) hlog.le), one_div, div_eq_mul_inv, one_mul, mul_comm] using hs
  have hsum : Chebyshev.theta (N : ℝ) ≤ (Nat.primesLE N).card * Real.log (N : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      _ ≤ ∑ _p ∈ Nat.primesLE N, Real.log (N : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos)
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).1)
      _ = _ := by simp
  have hc : ((Nat.primesLE N).card : ℝ) ≤ N₀ +
      ((summandPrefix A N).card : ℝ) * (summandPrefix B N).card := by exact_mod_cast hcoverage N
  have hmul := mul_le_mul_of_nonneg_right hc hlog.le
  rw [abs_le] at hθ
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log (N : ℝ))).mpr
  nlinarith

end Ostmann

end OAI
