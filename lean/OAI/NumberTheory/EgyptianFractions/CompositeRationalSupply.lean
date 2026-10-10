import OAI.NumberTheory.EgyptianFractions.RationalSupplyScaling
import OAI.NumberTheory.EgyptianFractions.RationalDivisorSupplyBridge
import OAI.NumberTheory.EgyptianFractions.DensePairing

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Multiplication convolves the two positive lists. Numerators divide the
product of the original supplies, and the term budgets multiply. -/
theorem HasRationalDivisorSum.mul {K L B C : ℕ} {x y : ℚ}
    (hx : HasRationalDivisorSum K x B) (hy : HasRationalDivisorSum L y C) :
    HasRationalDivisorSum (K * L) (x * y) (B * C) := by
  obtain ⟨k, hk, e, t, het, hsum⟩ := hx
  obtain ⟨l, hl, f, u, hfu, hsum'⟩ := hy
  let E : Fin (k * l) ≃ Fin k × Fin l := finProdFinEquiv.symm
  refine ⟨k * l, Nat.mul_le_mul hk hl,
    (fun i => e (E i).1 * f (E i).2),
    (fun i => t (E i).1 * u (E i).2), ?_, ?_⟩
  · intro i
    exact ⟨Nat.mul_pos (het _).1 (hfu _).1,
      Nat.mul_dvd_mul (het _).2.1 (hfu _).2.1,
      Nat.mul_pos (het _).2.2 (hfu _).2.2⟩
  · simp only [Nat.cast_mul, mul_div_mul_comm]
    rw [E.sum_comp (fun z : Fin k × Fin l =>
      ((e z.1 : ℚ) / t z.1) * ((f z.2 : ℚ) / u z.2))]
    rw [Fintype.sum_prod_type]
    dsimp only
    rw [← Fintype.sum_mul_sum, hsum, hsum']

/-- Taking powers is therefore available without any primality requirement. -/
theorem HasRationalDivisorSum.pow {K B : ℕ} {x : ℚ}
    (h : HasRationalDivisorSum K x B) (r : ℕ) :
    HasRationalDivisorSum (K ^ r) (x ^ r) (B ^ r) := by
  induction r with
  | zero =>
      simpa using hasRationalDivisorSum_of_dvd (K := 1) (s := 1)
        (by omega) (dvd_refl 1)
  | succ r ih =>
      simpa only [pow_succ] using ih.mul h

/-- A dense supply on a single interval gives supply for every smaller positive
integer. First represent its largest multiple below the endpoint as a sum of
two good integers, then divide by the multiplier. No finite exceptional range
or additional factorial factor is required for this completion step. -/
theorem rational_divisor_supply_of_dense_set
    (K B N : ℕ) (G : Finset ℕ) (hN : 4 < N)
    (hbad : ((Finset.Icc 1 N \ G).card : ℝ) ≤ (N : ℝ) / 8)
    (hgood : ∀ u ∈ G, HasRationalDivisorSum K (u : ℚ) B) :
    ∀ s : ℕ, 1 ≤ s → s ≤ N → HasRationalDivisorSum K (s : ℚ) (2 * B) := by
  intro s hs hsN
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsNR : (s : ℝ) ≤ N := by exact_mod_cast hsN
  let a : ℕ := ⌊(N : ℝ) / s⌋₊
  have ha : 0 < a := by
    have hratio : (1 : ℝ) ≤ (N : ℝ) / s :=
      (le_div_iff₀ hsR).mpr (by simpa using hsNR)
    have hfloor : 1 ≤ a := Nat.le_floor (by simpa using hratio)
    omega
  obtain ⟨hlo, hhi⟩ := floor_multiple_bounds hsR hsNR
  have hlo' : (N : ℝ) / 2 ≤ (a * s : ℕ) := by
    simpa only [Nat.cast_mul, a] using hlo
  have hhi' : ((a * s : ℕ) : ℝ) ≤ (N : ℝ) := by
    simpa only [Nat.cast_mul, a] using hhi
  obtain ⟨u, hu, v, hv, huv⟩ := dense_pairing_real (N : ℝ) G (a * s)
    (by exact_mod_cast hN) hlo' hhi' (by simpa using hbad)
  have hadd : HasRationalDivisorSum K ((a * s : ℕ) : ℚ) (B + B) := by
    simpa only [← Nat.cast_add, huv] using (hgood u hu).add (hgood v hv)
  simpa only [two_mul] using hadd.of_nat_multiple ha

/-- Dense composite-modulus supply can be fed directly to the canonical list
interface used in marked grouping. The density and good-modulus supply remain
explicit arithmetic hypotheses. -/
theorem marked_rational_supply_of_dense_set
    (m K B : ℕ) (G : Finset ℕ) (hm : 2 ≤ m)
    (hbad : ((Finset.Icc 1 (m ^ 4) \ G).card : ℝ) ≤ (m : ℝ) ^ 4 / 8)
    (hgood : ∀ u ∈ G, HasRationalDivisorSum K (u : ℚ) B) :
    HasRationalDivisorSupply m K (2 * B) := by
  apply rational_divisor_supply_bridge
  apply rational_divisor_supply_of_dense_set K B (m ^ 4) G
  · have hh := Nat.pow_le_pow_left hm 4
    norm_num at hh
    omega
  · simpa only [Nat.cast_pow] using hbad
  · exact hgood

end Problem337

end

end OAI
