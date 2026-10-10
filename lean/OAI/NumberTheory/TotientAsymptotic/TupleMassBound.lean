import OAI.NumberTheory.TotientAsymptotic.LargestPrimeCount

namespace OAI

/-! Tuple counts controlled by arithmetic mass. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma tupleValue_eq_head {R : ℕ} (p : ℕ) (ζ : PrefixDatum R) :
    tupleValue (TotientTuple.mk p ζ) = (p-1)*(ζ.d*∏ i, (ζ.primes i-1)) := by
  unfold tupleValue tuplePrimes
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

lemma basic_prefix_denominator_pos {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)}
    (hPH : P H ≤ H) (hζ : IsPrefixDatum x H ζ) :
    0 < ζ.d*∏ i, (ζ.primes i-1) := by
  have hp := basic_prefix_data_positive hPH hζ
  exact Nat.mul_pos hp.1 (Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (hp.2 i).one_lt))

lemma tupleFinset_card_eq_sum_fibers {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    (tupleFinset x H t).card = ∑ ζ ∈ prefixDataFinset x H,
      ((tupleFinset x H t).filter (fun τ => τ.tail = ζ)).card := by
  rw [Finset.sum_card_fiberwise_eq_card_filter (tupleFinset x H t)
    (prefixDataFinset x H) TotientTuple.tail]
  congr 1
  symm
  apply Finset.filter_eq_self.mpr
  intro τ hτ
  exact mem_prefixDataFinset.mpr ((mem_tupleFinset hPH).mp hτ).2.2.1

/-- Uniform at both common endpoints: an arbitrary smaller endpoint can only
reduce the largest-prime fibers. -/
theorem tuple_count_le_mass : ∀ᶠ x : ℝ in atTop, ∀ H : ℕ, P H ≤ H →
    ∀ t : ℝ, t ≤ x → ( (tupleFinset x H t).card : ℝ) ≤
      (10*x/Real.log x)*M x H (fun _ => 1) := by
  filter_upwards [largest_prime_count_upper, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro H hPH t ht
  rw [tupleFinset_card_eq_sum_fibers hPH, Nat.cast_sum, mass_eq_sum_prefixData, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ζ hζ
  have hz := mem_prefixDataFinset.mp hζ
  rw [tuple_fiber_card, ite_eq_left hz]
  let D := ζ.d*∏ i, (ζ.primes i-1)
  let Q := (Finset.range (⌊t⌋₊+2)).filter (fun p : ℕ => p.Prime ∧ x^(9/10 : ℝ) ≤ p ∧
    (tupleValue (TotientTuple.mk p ζ) : ℝ) ≤ t)
  have hD : 0 < D := basic_prefix_denominator_pos hPH hz
  have hb := hx D hD Q (by
    intro p hp
    obtain ⟨_, hprime, hlo, hval⟩ := Finset.mem_filter.mp hp
    refine ⟨hprime, hlo, ?_⟩
    rw [tupleValue_eq_head] at hval
    exact hval.trans ht)
  change (Q.card : ℝ) ≤ _
  apply hb.trans_eq
  dsimp [D]
  push_cast
  field_simp

end TotientAsymptotic

end

end OAI
