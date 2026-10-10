import OAI.NumberTheory.EgyptianFractions.MarkedCleanup
import OAI.NumberTheory.EgyptianFractions.LengthBasic
import OAI.NumberTheory.EgyptianFractions.EgyptianExistence
import OAI.NumberTheory.EgyptianFractions.DivisorCounting
import OAI.NumberTheory.EgyptianFractions.CountingPadding
import OAI.NumberTheory.EgyptianFractions.MarkerCoverage
import OAI.NumberTheory.EgyptianFractions.DenominatorBound
import OAI.NumberTheory.EgyptianFractions.FiniteBox
import OAI.NumberTheory.EgyptianFractions.CountingUpper
import OAI.NumberTheory.EgyptianFractions.OddPrimorial
import OAI.NumberTheory.EgyptianFractions.CountingTransfer

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- Appending the complementary unit fraction and cleaning repetitions preserves an odd multiple. -/
theorem marked_multiple_at_minimal_length (Q : ℕ) (hQ : Odd Q) (hQone : 1 < Q) :
    ∃ n : Fin (egyptianLength (Q - 1) Q + 1) → ℕ,
      IsOneExpansion n ∧ ∃ i, Q ∣ n i := by
  have hpos : 1 ≤ Q - 1 := by omega
  have hlt : Q - 1 < Q := by omega
  obtain ⟨n, hn⟩ := egyptianLength_attained_of_exists
    (exists_strict_unit_fraction_sum (Q - 1) Q hpos hlt)
  apply marked_cleanup_exact_length hQ hQone (Fin.cons Q n)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp; omega
    · simpa using (show 1 ≤ n j from (hn.1 j).trans' (by omega))
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hn.2.2]
    have hQzero : (Q : ℚ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
    rw [Nat.cast_sub (by omega : 1 ≤ Q)]
    push_cast
    field_simp
    ring
  · exact ⟨0, by simp⟩

/-- The length of the cleaned marked expansion is bounded by the uniform maximum. -/
theorem marked_multiple_length_le_max (Q : ℕ) (hQ : Odd Q) (hQone : 1 < Q) :
    ∃ k : ℕ, ∃ n : Fin k → ℕ, IsOneExpansion n ∧ (∃ i, Q ∣ n i) ∧
      k ≤ maxEgyptianLength Q + 1 := by
  obtain ⟨n, hn, hm⟩ := marked_multiple_at_minimal_length Q hQ hQone
  refine ⟨egyptianLength (Q - 1) Q + 1, n, hn, hm, ?_⟩
  exact Nat.add_le_add_right (egyptianLength_le_max (by omega) (by omega)) 1

/-- Tuple form of divisor branching, avoiding conversion choices in the counting assembly. -/
theorem divisor_branching_from_tuple {k : ℕ} (n : Fin k → ℕ)
    (hn : IsOneExpansion n) (i : Fin k)
    (hfinite : (OneExpansions (k + 1)).Finite) :
    (n i).divisors.card ≤ F (k + 1) + 1 + 2 * (k - 1) := by
  classical
  let s := Finset.univ.image n
  have hcard : s.card = k := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hn.2.1.injective, Finset.card_univ,
      Fintype.card_fin]
  have his : n i ∈ s := by simp [s]
  have hpos : ∀ d ∈ s, 1 ≤ d := by
    intro d hd
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
    exact hn.1 j
  have hsum : (∑ d ∈ s, (1 : ℚ) / d) = 1 := by
    dsimp [s]
    rw [Finset.sum_image (fun i _ j _ h => hn.2.1.injective h)]
    exact hn.2.2
  have hfinite' : (OneExpansions (s.card + 1)).Finite := by rw [hcard]; exact hfinite
  have hc := divisor_branching_lower_bound s (n i) his hpos hsum hfinite'
  rw [hcard] at hc
  omega

/-- Branching on the marked multiple counts at least as many divisors as the marker itself. -/
theorem divisor_branching_from_odd_marker {Q k : ℕ} (hQ : Odd Q) (hQone : 1 < Q)
    (n : Fin k → ℕ) (hn : IsOneExpansion n) (hm : ∃ i, Q ∣ n i)
    (hfinite : (OneExpansions (k + 1)).Finite) :
    3 ≤ k ∧ Q.divisors.card ≤ F (k + 1) + 1 + 2 * (k - 1) := by
  obtain ⟨i, hi⟩ := hm
  have hmi : 3 ≤ n i := odd_marker_denominator_ge_three hQ hQone (hn.1 i) hi
  have hDi : n i ∈ D k := ⟨by omega, n, hn, i, rfl⟩
  refine ⟨marker_length_ge_three hDi, ?_⟩
  have hcard : Q.divisors.card ≤ (n i).divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd (by have := hn.1 i; omega) hi)
  exact hcard.trans (divisor_branching_from_tuple n hn i hfinite)

/-- A short odd-marked expansion supplies a lower bound for the number of expansions one term longer. -/
theorem counting_from_uniform_max (Q : ℕ) (hQ : Odd Q) (hQone : 1 < Q)
    (hfinite : ∀ k, (OneExpansions k).Finite) :
    ∃ ell : ℕ, 4 ≤ ell ∧ ell ≤ maxEgyptianLength Q + 2 ∧
      Q.divisors.card ≤ F ell + 2 * ell := by
  obtain ⟨k, n, hn, hm, hk⟩ := marked_multiple_length_le_max Q hQ hQone
  obtain ⟨hkthree, hcount⟩ := divisor_branching_from_odd_marker hQ hQone n hn hm (hfinite _)
  refine ⟨k + 1, by omega, by omega, ?_⟩
  omega

/-- Exponential divisor counts eventually absorb the loss from the finitely many collisions. -/
theorem eventually_collision_budget (B : ℝ) (hB : 0 < B) :
    ∀ᶠ r : ℕ in atTop, 2 * B * Real.log (r : ℝ) ≤ (2 ^ (r - 1) : ℕ) := by
  have hlim : Tendsto (fun r : ℕ => (r : ℝ) / (2 : ℝ) ^ r) atTop (nhds 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2))
  have hsmall : ∀ᶠ r : ℕ in atTop, (r : ℝ) / (2 : ℝ) ^ r < 1 / (4 * B) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with r hr hrone
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hlog : Real.log (r : ℝ) ≤ r := Real.log_le_self (le_of_lt hrpos)
  have hcross := (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ r)
    (by positivity : (0 : ℝ) < 4 * B)).mp hr
  have heq : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    nth_rw 1 [show r = (r - 1) + 1 by omega]
    rw [pow_succ]
    ring
  push_cast
  rw [heq] at hcross
  nlinarith

/-- Uniform logarithmic lengths and an odd many-divisor supply yield exponentially branching short lengths. -/
theorem short_counting_lengths_of_uniform_upper
    (hfinite : ∀ k, (OneExpansions k).Finite)
    (hupper : ∃ c : ℝ, 0 < c ∧ ∀ᶠ Q : ℕ in atTop,
      (maxEgyptianLength Q : ℝ) ≤ c * Real.log (Real.log (Q : ℝ)))
    (hsupply : ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℕ in atTop,
      ∃ Q : ℕ, Odd Q ∧ 1 < Q ∧ 2 ^ r ≤ Q.divisors.card ∧
        Real.log (Real.log (Q : ℝ)) ≤ C * Real.log (r : ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ r : ℕ in atTop,
      ∃ ell : ℕ, 2 ≤ ell ∧ (ell : ℝ) ≤ B * Real.log (r : ℝ) ∧
        2 ^ (r - 1) ≤ F ell := by
  obtain ⟨c, hc, hupper⟩ := hupper
  obtain ⟨C, hC, hsupply⟩ := hsupply
  obtain ⟨Q0, hQ0⟩ := eventually_atTop.mp hupper
  let B : ℝ := c * C + 2
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  have hlog : ∀ᶠ r : ℕ in atTop, 1 ≤ Real.log (r : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hsupply, eventually_collision_budget B hB, hlog,
    eventually_ge_atTop Q0, eventually_ge_atTop 1] with r hr hbudget hlogr hrQ0 hrone
  obtain ⟨Q, hQodd, hQone, hdivisors, hlogQ⟩ := hr
  have hrQ : r ≤ Q := by
    have hp := Nat.lt_two_pow_self (n := r)
    have hd := Nat.card_divisors_le_self Q
    omega
  obtain ⟨ell, helfour, hell, hcount⟩ := counting_from_uniform_max Q hQodd hQone hfinite
  have hmax := hQ0 Q (hrQ0.trans hrQ)
  have hellR : (ell : ℝ) ≤ B * Real.log (r : ℝ) := by
    have hell' : (ell : ℝ) ≤ maxEgyptianLength Q + 2 := by exact_mod_cast hell
    have hmul := mul_le_mul_of_nonneg_left hlogQ hc.le
    dsimp [B]
    nlinarith
  refine ⟨ell, by omega, hellR, ?_⟩
  have hlossR : (2 * ell : ℕ) ≤ (2 ^ (r - 1) : ℕ) := by
    have hreal : (2 : ℝ) * ell ≤ (2 ^ (r - 1) : ℕ) := by nlinarith
    exact_mod_cast hreal
  have hexp : 2 ^ r = 2 ^ (r - 1) * 2 := by
    nth_rw 1 [show r = (r - 1) + 1 by omega]
    rw [pow_succ]
  rw [hexp] at hdivisors
  omega

/-- The odd-primorial many-divisor input is unconditional, so only the main uniform upper
bound remains in the short-counting-length construction. -/
theorem short_counting_lengths_of_main_upper
    (hupper : ∃ c : ℝ, 0 < c ∧ ∀ᶠ Q : ℕ in atTop,
      (maxEgyptianLength Q : ℝ) ≤ c * Real.log (Real.log (Q : ℝ))) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ r : ℕ in atTop,
      ∃ ell : ℕ, 2 ≤ ell ∧ (ell : ℝ) ≤ B * Real.log (r : ℝ) ∧
        2 ^ (r - 1) ≤ F ell := by
  apply short_counting_lengths_of_uniform_upper
  · intro k
    exact (finite_ncard_le_egyptian_box k (OneExpansions k)
      (fun n hn => hn.1) (fun n hn => one_expansion_denominator_bound n hn)).1
  · exact hupper
  · refine ⟨4, by norm_num, ?_⟩
    filter_upwards [eventually_odd_primorial_supply] with r hr
    obtain ⟨Q, hQone, hQodd, hcount, hsize⟩ := hr
    exact ⟨Q, hQodd, hQone, hcount, hsize⟩

/-- The counting order theorem follows from the main uniform upper bound alone;
this route does not use the quantitative prescribed-denominator construction. -/
theorem counting_order_of_main_upper
    (hupper : ∃ c : ℝ, 0 < c ∧ ∀ᶠ Q : ℕ in atTop,
      (maxEgyptianLength Q : ℝ) ≤ c * Real.log (Real.log (Q : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k0 : ℕ,
      ∀ k : ℕ, k0 ≤ k →
        c * (k : ℝ) ≤ Real.log (Real.log (F k : ℝ)) ∧
        Real.log (Real.log (F k : ℝ)) ≤ C * (k : ℝ) := by
  have hbox (k : ℕ) : (OneExpansions k).Finite ∧ F k ≤ k ^ (2 ^ k - 1) :=
    finite_ncard_le_egyptian_box k (OneExpansions k)
      (fun n hn => hn.1) (fun n hn => one_expansion_denominator_bound n hn)
  obtain ⟨B, hB, hsupply⟩ := short_counting_lengths_of_main_upper hupper
  have hmono : ∀ i j : ℕ, 2 ≤ i → i ≤ j → F i ≤ F j := by
    intro i j hi hij
    exact CountingPadding.F_le_of_le (fun k => (hbox k).1) hi hij
  have hlower := counting_lower_transfer F hB hmono hsupply
  refine ⟨1 / (2 * B), 3, by positivity, by norm_num, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hlower, eventually_ge_atTop 2] with k hk hk2
  exact ⟨hk, counting_loglog_upper_of_box F (fun k => (hbox k).2) k hk2⟩

end Problem337

end

end OAI
