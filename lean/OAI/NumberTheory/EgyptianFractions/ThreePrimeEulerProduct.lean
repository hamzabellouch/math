import OAI.NumberTheory.EgyptianFractions.ThreePrimeSingularSeries

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The standard ternary local Euler factor, extended by one at nonprimes. -/
def ternaryEulerFactor (u p : ℕ) : ℝ :=
  if p.Prime then
    if p ∣ u then 1 - 1 / ((p : ℝ) - 1) ^ 2
    else 1 + 1 / ((p : ℝ) - 1) ^ 3
  else 1

lemma ternaryEulerFactor_add_three (u n : ℕ) :
    ternaryEulerFactor u (n + 3) = 1 + threePrimeOddPerturbation u n := by
  have heq : ((n + 3 : ℕ) : ℝ) - 1 = (n : ℝ) + 2 := by push_cast; ring
  unfold ternaryEulerFactor threePrimeOddPerturbation
  rw [heq]
  split_ifs <;> ring

lemma ternaryEulerFactor_two (u : ℕ) :
    ternaryEulerFactor u 2 = if Odd u then 2 else 0 := by
  unfold ternaryEulerFactor
  norm_num only [Nat.prime_two, ite_true, Nat.cast_ofNat]
  by_cases h : 2 ∣ u
  · have hn : ¬ Odd u := fun ho =>
      (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h)
    norm_num [h, hn]
  · have ho : Odd u := Nat.not_even_iff_odd.mp
      (fun he => h (even_iff_two_dvd.mp he))
    norm_num [h, ho]

lemma ternaryEulerFactor_prefix (u : ℕ) :
    (∏ p ∈ Finset.range 3, ternaryEulerFactor u p) = if Odd u then 2 else 0 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have h0 : ternaryEulerFactor u 0 = 1 := by simp [ternaryEulerFactor, Nat.not_prime_zero]
  have h1 : ternaryEulerFactor u 1 = 1 := by simp [ternaryEulerFactor]
  rw [h0, h1, one_mul, one_mul, ternaryEulerFactor_two]

lemma ternaryEulerFactor_tail_multipliable (u : ℕ) :
    Multipliable (fun n : ℕ => ternaryEulerFactor u (n + 3)) := by
  exact (threePrimeOddFactors_multipliable u).congr
    (fun n => (ternaryEulerFactor_add_three u n).symm)

lemma ternaryEulerFactor_multipliable (u : ℕ) :
    Multipliable (ternaryEulerFactor u) :=
  (ternaryEulerFactor_tail_multipliable u).comp_nat_add

/-- The shifted odd-prime definition is exactly the conventional Euler
product, including the vanishing local factor at two for even inputs. -/
theorem threePrimeSingularSeries_eq_euler_tprod (u : ℕ) :
    threePrimeSingularSeries u = ∏' p : ℕ, ternaryEulerFactor u p := by
  calc
    threePrimeSingularSeries u = (if Odd u then 2 else 0) *
        ∏' n : ℕ, ternaryEulerFactor u (n + 3) := by
      unfold threePrimeSingularSeries
      congr 1
      exact tprod_congr (fun n => (ternaryEulerFactor_add_three u n).symm)
    _ = (∏ p ∈ Finset.range 3, ternaryEulerFactor u p) *
        ∏' n : ℕ, ternaryEulerFactor u (n + 3) := by rw [ternaryEulerFactor_prefix]
    _ = ∏' p : ℕ, ternaryEulerFactor u p :=
      (ternaryEulerFactor_tail_multipliable u).prod_mul_tprod_nat_mul'

/-- Removing the factors equal to one at nonprimes recovers the usual
prime-indexed singular series. This identity is valid for all natural inputs. -/
theorem threePrimeSingularSeries_eq_prime_tprod (u : ℕ) :
    threePrimeSingularSeries u = ∏' p : {p : ℕ // p.Prime},
      (if p.val ∣ u then 1 - 1 / ((p.val : ℝ) - 1) ^ 2
       else 1 + 1 / ((p.val : ℝ) - 1) ^ 3) := by
  have hs : Function.mulSupport (ternaryEulerFactor u) ⊆ {p : ℕ | p.Prime} := by
    intro p hp
    by_contra hn
    change ¬ p.Prime at hn
    exact hp (by simp [ternaryEulerFactor, hn])
  rw [threePrimeSingularSeries_eq_euler_tprod,
    ← tprod_subtype_eq_of_mulSupport_subset hs]
  apply tprod_congr
  intro p
  have hp : Nat.Prime (p : ℕ) := p.property
  simp only [ternaryEulerFactor, hp, ite_true]

lemma threePrimeSingularSeries_eq_zero_of_even {u : ℕ} (hu : Even u) :
    threePrimeSingularSeries u = 0 := by
  have hn : ¬ Odd u := fun ho => Nat.not_even_iff_odd.mpr ho hu
  simp [threePrimeSingularSeries, hn]

end Problem337

end

end OAI
