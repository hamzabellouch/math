import OAI.NumberTheory.TotientAsymptotic.LargestPrimeCount

namespace OAI

/-! The quarter-power prime interval used in Ford’s global counting argument.
Chebyshev's library theorem suffices for the upper bound; no PNT input is used here. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The largest-prime restriction makes the logarithm of every nonempty
counting interval comparable to `log x`, uniformly in its integer denominator. -/
theorem quarter_prime_count_upper :
    ∀ᶠ x : ℝ in atTop, ∀ D : ℕ, 0 < D → ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ x^(1/4 : ℝ) ≤ p ∧ ((p-1)*D : ℕ) ≤ x) →
      (Q.card : ℝ) ≤ 32*x/((D : ℝ)*Real.log x) := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ)<1))
  have ht : Tendsto (fun x : ℝ => x^(1/4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ), ht.eventually (eventually_ge_atTop Y₀)] with x hx hxp
  intro D hD Q hQ
  have hD' : (0 : ℝ)<D := by exact_mod_cast hD
  have hx0 : 0<x := zero_lt_one.trans hx
  have hlogx : 0<Real.log x := Real.log_pos hx
  by_cases hne : Q.Nonempty
  · let Y := 1+x/D
    have hpY (p : ℕ) (hp : p ∈ Q) : (p : ℝ) ≤ Y := by
      have hh := hQ p hp
      have hpn := hh.1.one_lt.le
      have hval : ((p : ℝ)-1)*D ≤ x := by
        exact_mod_cast hh.2.2
      change _ ≤ 1+x/D
      have hh' := (le_div_iff₀ hD').mpr hval
      linarith
    obtain ⟨p, hp⟩ := hne
    have hlY : x^(1/4 : ℝ) ≤ Y := (hQ p hp).2.1.trans (hpY p hp)
    have hY0 : 0<Y := by dsimp [Y]; positivity
    have hYlarge : Y₀ ≤ Y := hxp.trans hlY
    have hlogY : (1/4 : ℝ)*Real.log x ≤ Real.log Y := by
      have hh := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hlY
      rw [Real.log_rpow hx0] at hh
      linarith
    have hlogYpos : 0<Real.log Y := lt_of_lt_of_le (by positivity) hlogY
    have hDx : (D : ℝ) ≤ x := by
      have hh := (hQ p hp).2.2
      have hp2 := (hQ p hp).1.two_le
      have hp1 : 1 ≤ p-1 := by omega
      have hnat : D ≤ (p-1)*D := by simpa only [one_mul] using Nat.mul_le_mul_right D hp1
      exact (by exact_mod_cast hnat : (D : ℝ) ≤ ((p-1)*D : ℕ)).trans hh
    have hYupper : Y ≤ 2*x/D := by
      change 1+x/D ≤ _
      have hone : (1 : ℝ) ≤ x/D := (le_div_iff₀ hD').mpr (by simpa using hDx)
      have he : 2*x/D = 2*(x/D) := by ring
      rw [he]
      linarith
    have hsub : Q ⊆ Nat.primesLE ⌊Y⌋₊ := by
      intro q hq
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hpY q hq), (hQ q hq).1⟩
    have hcard : (Q.card : ℝ) ≤ Nat.primeCounting ⌊Y⌋₊ := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Nat.primesLE_card_eq_primeCounting _)
    have hc : Real.log 4+1 ≤ (3 : ℝ) := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
    calc
      _ ≤ (Real.log 4+1)*Y/Real.log Y := hcard.trans (hY₀ Y hYlarge)
      _ ≤ (3*(2*x/D))/((1/4 : ℝ)*Real.log x) := by
        apply div_le_div₀ (by positivity)
          ((mul_le_mul_of_nonneg_right hc hY0.le).trans (mul_le_mul_of_nonneg_left hYupper (by norm_num)))
          (by positivity) hlogY
      _ ≤ 32*x/((D : ℝ)*Real.log x) := by
        field_simp
        nlinarith
  · have hz : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hz, Finset.card_empty, Nat.cast_zero]
    positivity

end TotientAsymptotic

end

end OAI
