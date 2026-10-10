import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedQuadraticInverse
import OAI.NumberTheory.Ostmann.QuadraticCenter.RationalApproximationLift

namespace OAI

/-! # Weighted quadratic witnesses supply the common-center lifts -/

namespace Ostmann

open scoped BigOperators

/-- Multiplying the inverse denominator by the actual quadratic coefficient
produces precisely the phase witness used by the common-center argument. -/
theorem weighted_quadratic_phase_witness (w : ℕ → ℂ) (β δ : ℝ)
    (N c Amax : ℕ) (θ : ℝ) (hN : 0 < N) (hc : 0 < c)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hscale : 512 * (1 + 2 * Real.log (N : ℝ)) ≤ δ ^ 3 * N)
    (hlarge : discreteVariation w N * (δ * N) <
      ‖∑ j ∈ Finset.range N, w j * realQuadraticPhase ((c : ℝ) * θ) β j‖)
    (hA : 1024 * (c : ℝ) / δ ^ 2 ≤ Amax) :
    ∃ a ∈ Finset.Icc 1 Amax, ∃ b : ℤ,
      |(a : ℝ) * θ - b| ≤
        1024 * (1 + 2 * Real.log (N : ℝ)) / (δ ^ 4 * (N : ℝ) ^ 2) := by
  obtain ⟨q, hq, hqbound, happrox⟩ := weighted_quadratic_inverse w ((c : ℝ) * θ) β δ N
    hN hδ hδ1 hscale hlarge
  let a := q * c
  have ha : 0 < a := Nat.mul_pos hq hc
  have habound : (a : ℝ) ≤ Amax := by
    have hh := mul_le_mul_of_nonneg_right hqbound (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
    have heq : (1024 / δ ^ 2) * (c : ℝ) = 1024 * c / δ ^ 2 := by ring
    rw [heq] at hh
    exact (show (a : ℝ) ≤ 1024 * c / δ ^ 2 by exact_mod_cast hh).trans hA
  refine ⟨a, Finset.mem_Icc.mpr ⟨ha, by exact_mod_cast habound⟩,
    round ((q : ℝ) * ((c : ℝ) * θ)), ?_⟩
  convert happrox using 1
  congr 2
  dsimp [a]
  push_cast
  ring

/-- With the already constructed tuple residue and product modulus, the
weighted witness gives the bounded simultaneous integer lift. -/
theorem weighted_quadratic_tuple_lift (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {k : ℕ} (e : Fin k ↪ P) (w : ℕ → ℂ) (β δ : ℝ)
    (N c Amax H : ℕ) (tM : ℤ) (t : ℕ → ℤ)
    (hN : 0 < N) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hscale : 512 * (1 + 2 * Real.log (N : ℝ)) ≤ δ ^ 3 * N)
    (hlarge : discreteVariation w N * (δ * N) <
      ‖∑ j ∈ Finset.range N, w j *
        realQuadraticPhase ((c : ℝ) * ((tM : ℝ) / primeTupleProduct P e)) β j‖)
    (hA : 1024 * (c : ℝ) / δ ^ 2 ≤ Amax)
    (hH : (primeTupleProduct P e : ℝ) *
      (1024 * (1 + 2 * Real.log (N : ℝ)) / (δ ^ 4 * (N : ℝ) ^ 2)) ≤ H)
    (ht : ∀ i, ((e i).1 : ℤ) ∣ tM - t (e i).1) :
    ∃ a ∈ Finset.Icc 1 Amax, ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
      ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1 := by
  obtain ⟨a, ha, b, hab⟩ := weighted_quadratic_phase_witness w β δ N c Amax
    ((tM : ℝ) / primeTupleProduct P e) hN hc hδ hδ1 hscale hlarge hA
  obtain ⟨n, hn, hnt⟩ := approximationLift_tuple P hprime e a H tM b t _ hab hH ht
  exact ⟨a, ha, n, hn, hnt⟩

end Ostmann

end OAI
