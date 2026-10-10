import OAI.NumberTheory.EgyptianFractions.DenseModularPair
import OAI.NumberTheory.EgyptianFractions.RationalSupplyScaling
import OAI.NumberTheory.EgyptianFractions.RationalDivisorSupplyBridge

namespace OAI
noncomputable section

namespace Problem337

/-- A supply on more than two thirds of an initial interval gives supply for
every smaller positive integer at twice the original budget. The multiplier
is removed by changing only the rational summands' denominators. -/
theorem rational_divisor_supply_of_two_thirds
    (K B N : ℕ) (G : Finset ℕ) (hG : G ⊆ Finset.Icc 1 N)
    (hcard : 2 * N < 3 * G.card)
    (hgood : ∀ u ∈ G, HasRationalDivisorSum K (u : ℚ) B) :
    ∀ s : ℕ, 1 ≤ s → s ≤ N → HasRationalDivisorSum K (s : ℚ) (2 * B) := by
  intro s hs hsN
  obtain ⟨u, hu, v, hv, hdiv⟩ := exists_pair_dvd_sum_of_two_thirds G N s hs hsN hG hcard
  have hu1 := (Finset.mem_Icc.mp (hG hu)).1
  obtain ⟨d, hd⟩ := hdiv
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    rw [hd0, Nat.mul_zero] at hd
    omega
  have hrep : HasRationalDivisorSum K ((d * s : ℕ) : ℚ) (B + B) := by
    rw [Nat.mul_comm d s, ← hd, Nat.cast_add]
    exact (hgood u hu).add (hgood v hv)
  simpa only [two_mul] using hrep.of_nat_multiple hdpos

/-- Complement-cardinality version: fewer than a third of the initial interval
may be exceptional. Good elements outside that interval are irrelevant. -/
theorem rational_divisor_supply_of_third_exception
    (K B N : ℕ) (G : Finset ℕ)
    (hbad : 3 * (Finset.Icc 1 N \ G).card < N)
    (hgood : ∀ u ∈ G, HasRationalDivisorSum K (u : ℚ) B) :
    ∀ s : ℕ, 1 ≤ s → s ≤ N → HasRationalDivisorSum K (s : ℚ) (2 * B) := by
  classical
  apply rational_divisor_supply_of_two_thirds K B N (Finset.Icc 1 N ∩ G)
  · exact Finset.inter_subset_left
  · have hsplit := Finset.card_sdiff_add_card_inter (Finset.Icc 1 N) G
    have hN : (Finset.Icc 1 N).card = N := by simp
    rw [hN] at hsplit
    omega
  · intro u hu
    exact hgood u (Finset.mem_inter.mp hu).2

/-- The sharper finite density completion in the canonical marked-grouping
interface. This does not supply the density or the good-modulus estimates. -/
theorem marked_rational_supply_of_third_exception
    (m K B : ℕ) (G : Finset ℕ)
    (hbad : 3 * (Finset.Icc 1 (m ^ 4) \ G).card < m ^ 4)
    (hgood : ∀ u ∈ G, HasRationalDivisorSum K (u : ℚ) B) :
    HasRationalDivisorSupply m K (2 * B) := by
  exact rational_divisor_supply_bridge
    (rational_divisor_supply_of_third_exception K B (m ^ 4) G hbad hgood)

end Problem337

end

end OAI
