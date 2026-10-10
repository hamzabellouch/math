import OAI.NumberTheory.Ostmann.Supply.TailSieveParameters

namespace OAI

/-! # The collision budget on the band used in Proposition 5.1 -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_logLogPrimeBand_subset_collision_cutoff :
    ∀ᶠ L : ℝ in atTop,
      logLogPrimeBand L ⊆ Nat.primesLE (tailCollisionCutoff (Real.exp L)) := by
  have hsmall := eventual_affine_log_le_rpow 5 (Real.log 2) (1 / 4) 1
    (by norm_num) (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at hsmall
  filter_upwards [Real.tendsto_exp_atTop.eventually hsmall,
    Real.tendsto_exp_atTop.eventually (eventual_tailCollisionCutoff 0),
    eventually_ge_atTop (30 : ℝ)] with L hsmall hcut hL
  intro p hp
  obtain ⟨hpp, _, hpu⟩ := logLogPrimeBand_mem hp
  have hfour : 4 ≤ Real.exp ((1 / 10 : ℝ) * L) := by
    linarith [Real.add_one_le_exp ((1 / 10 : ℝ) * L)]
  have hprod := mul_le_mul_of_nonneg_left hfour (Real.exp_nonneg ((9 / 10 : ℝ) * L))
  rw [← Real.exp_add] at hprod
  have hex : (9 / 10 : ℝ) * L + (1 / 10 : ℝ) * L = L := by ring
  rw [hex] at hprod
  have hQ := tailCollisionCutoff_bounds (Real.exp L) hcut.1 hcut.2.1
  have hlog : Real.log p ≤ Real.log (tailCollisionCutoff (Real.exp L) : ℝ) := by
    linarith [hQ.2.2]
  have hQpos : (0 : ℝ) < tailCollisionCutoff (Real.exp L) := by exact_mod_cast hQ.1
  have hpQ : (p : ℝ) ≤ tailCollisionCutoff (Real.exp L) :=
    (Real.log_le_log_iff (by exact_mod_cast hpp.pos) hQpos).mp hlog
  exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpQ, hpp⟩

theorem EventuallyPrimeSumset.tail_band_collision_budget
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      (∑ p ∈ logLogPrimeBand L, Real.log p * tailCollisionDefect A N p
        (summandTail A (summandTailCutoff (Real.exp L)) X)
        (summandTail B (summandTailCutoff (Real.exp L)) X)
        (fun _ => 1 / ((summandTail A (summandTailCutoff (Real.exp L)) X).card : ℝ))
        (fun _ => 1 / ((summandTail B (summandTailCutoff (Real.exp L)) X).card : ℝ))) ≤
        20 * L + (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a) := by
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  refine ⟨a, ha, ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually hlarge,
    Real.tendsto_exp_atTop.eventually (eventual_tailCollisionCutoff N),
    eventual_logLogPrimeBand_subset_collision_cutoff] with L hlarge hcut hsub
  intro X hX
  obtain ⟨hsa, hsb, _, _, _⟩ := hlarge X hX
  have hb := uniform_tail_collision_bound hA hB N (summandTailCutoff (Real.exp L)) X
    a (Real.exp L) C ha hcut.1 hcut.2.1 hX hcut.2.2
    (fun p hp => hN p (Nat.prime_of_mem_primesLE hp))
    (by simpa only [positiveSummandTail_card] using hsa)
    (by simpa only [negativeSummandTail_card] using hsb) hM
  rw [Real.log_exp] at hb
  apply le_trans _ (by convert hb using 1; ring)
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro p hp _
  apply mul_nonneg (Real.log_natCast_nonneg p)
  apply collisionDefect_nonneg
  · exact tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos
  · exact tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos
      (hN p (Nat.prime_of_mem_primesLE hp))
  · exact (tailSupport_card_add_complement A N p).le

end Ostmann

end OAI
