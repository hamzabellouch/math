import OAI.NumberTheory.EgyptianFractions.EightProductConductor
import OAI.NumberTheory.EgyptianFractions.RationalDivisorLift
import OAI.NumberTheory.EgyptianFractions.RationalDivisorSupplyAlgebra

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A conductor collision bound for an indexed family of positive divisors
gives an eight-term rational supply of the modulus. Repeated samples are
allowed; no primality assumption is made on the modulus. -/
theorem rational_divisor_sum_eight_of_collision
    {q P : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℕ) (ha : ∀ i, 0 < a i) (had : ∀ i, a i ∣ P)
    (hcollision : ∀ d : ℕ, 2 ≤ d → d ∣ q →
      (CompositeSpectral.remainderCollisionCount a d : ℝ) ≤
        (Fintype.card ι : ℝ) ^ 2 / (d : ℝ) ^ ((7 : ℝ) / 8)) :
    HasRationalDivisorSum (P ^ 2) (q : ℚ) 8 := by
  obtain ⟨u, v, hu⟩ :=
    CompositeSpectral.eight_products_of_collision_rpow_bound a hcollision (0 : ZMod q)
  obtain ⟨t, ht, he, hsum⟩ := rational_divisor_sum_of_zmod_zero
    (by norm_num : 0 < 8) (NeZero.pos q)
    (fun i => a (u i)) (fun i => a (v i))
    (fun i => ha (u i)) (fun i => ha (v i))
    (fun i => had (u i)) (fun i => had (v i)) hu
  exact hasRationalDivisorSum_of_common_denominator
    (fun i => a (u i) * a (v i)) ht he hsum.symm

/-- The exact divisor-list specialization of the indexed collision criterion.
The collision count retains each natural divisor once, even if residues
coincide. Nonzero `P` supplies the index `1`, including the boundary `P = 1`. -/
theorem rational_divisor_sum_eight_of_divisor_collision
    {q P : ℕ} [NeZero q] (hP : P ≠ 0)
    (hcollision : ∀ d : ℕ, 2 ≤ d → d ∣ q →
      (CompositeSpectral.remainderCollisionCount
        (fun i : P.divisors => (i : ℕ)) d : ℝ) ≤
        (P.divisors.card : ℝ) ^ 2 / (d : ℝ) ^ ((7 : ℝ) / 8)) :
    HasRationalDivisorSum (P ^ 2) (q : ℚ) 8 := by
  classical
  let : Nonempty P.divisors := ⟨⟨1, Nat.mem_divisors.mpr ⟨one_dvd P, hP⟩⟩⟩
  apply rational_divisor_sum_eight_of_collision (fun i : P.divisors => (i : ℕ))
    (fun i => Nat.pos_of_mem_divisors i.property)
    (fun i => Nat.dvd_of_mem_divisors i.property)
  simpa only [Fintype.card_coe] using hcollision

end Problem337

end

end OAI
