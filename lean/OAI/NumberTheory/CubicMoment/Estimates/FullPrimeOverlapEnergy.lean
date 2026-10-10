import OAI.NumberTheory.CubicMoment.Estimates.PairOverlapEnergy

namespace OAI

/-! A shared prime in two rough prime products saves its norm in the
quadratic coefficient mass. This uses actual quotient lattice counts. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_noncoprime_degree {R D L : ℝ} (hR : 1 ≤ R)
    (hD : 0 < D) (hL : 0 < L) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hprod : (∏ i, X i) = L)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) {a : Eisenstein}
    (ha : a ∈ fullSquarefreePrimeSupport R W X e) :
    (((fullSquarefreePrimeSupport R W X e).filter (fun b => ¬IsCoprime a b)).card:ℝ) ≤
      18*R^Fintype.card ι*(Fintype.card ι:ℝ)*L/D := by
  have hp := fullSquarefreePrimeSupport_primary R W X e ha
  have hS (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R W X e) :
      b ≠ 0 ∧ norm b ≤ R^Fintype.card ι*L := by
    refine ⟨primary_ne_zero (fullSquarefreePrimeSupport_primary R W X e hb).1,?_⟩
    simpa only [hprod] using
      (fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp hb).1).2
  have hpn (p : Eisenstein) (hpa : p ∈ primaryPrimeFactors a) : D ≤ norm p := by
    obtain ⟨i,hi⟩ := fullPrime_prime_divisor_coordinate R W X
      (primaryPrimeFactor_spec hp.1 hpa).1 (primaryPrimeFactor_spec hp.1 hpa).2
      (Finset.mem_filter.mp ha).1
    have hw := ((fullPrimeSupport_mem_iff W X hX hhi i p).mp hi).2
    have hr : 1 ≤ norm p/X i := le_of_not_gt (fun h => hw (hlo i _ h))
    exact (hrough i).le.trans (by simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hr)
  have hcard : ((primaryPrimeFactors a).card:ℝ) ≤ (Fintype.card ι:ℝ) := by
    exact_mod_cast primeProduct_primeFactors_card _ (fullPrimeSupport_prime R W X)
      (Finset.mem_filter.mp ha).1
  calc
    _ ≤ (primaryPrimeFactors a).card*(18*(R^Fintype.card ι*L)/D) :=
      noncoprime_row_card_le _ (by positivity) hD hS hp.1 hp.2 hpn
    _ ≤ (Fintype.card ι:ℝ)*(18*(R^Fintype.card ι*L)/D) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem fullPrime_overlap_energy {R D L : ℝ} (hR : 1 ≤ R)
    (hD : 0 < D) (hL : 0 < L) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hprod : (∏ i, X i) = L)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) :
    (∑ a ∈ fullSquarefreePrimeSupport R W X e, ∑ b ∈ fullSquarefreePrimeSupport R W X e,
      if ¬IsCoprime a b then ‖fullPrimeCoefficient R W X a‖*‖fullPrimeCoefficient R W X b‖ else 0) ≤
      (18*R^Fintype.card ι*(Fintype.card ι:ℝ)*L/D)*
        ∑ a ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X a‖^2 := by
  convert (symmetric_pair_energy_le (fullSquarefreePrimeSupport R W X e)
    (fun a b => ¬IsCoprime a b) (fun _ _ _ _ => not_congr isCoprime_comm)
    (fun a => ‖fullPrimeCoefficient R W X a‖)
    (18*R^Fintype.card ι*(Fintype.card ι:ℝ)*L/D)
    (fun _ ha => by
      convert fullPrime_noncoprime_degree hR hD hL W X hX hprod hlo hhi hrough e ha using 1
      congr 2
      ext b
      simp only [Finset.mem_filter])) using 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> rfl

end CubicFirstMoment

end

end OAI
