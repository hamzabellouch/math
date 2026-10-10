import OAI.NumberTheory.EgyptianFractions.DivisorEnergyNesting
import OAI.NumberTheory.EgyptianFractions.CompositeSupplySize
import OAI.NumberTheory.EgyptianFractions.ReducedCollisionFourier
import OAI.NumberTheory.EgyptianFractions.CollisionCounting

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A finite natural list has the same collision count whether residues are
represented by remainders or by elements of `ZMod`. -/
theorem indexed_divisor_collision_eq (P q : ℕ) [NeZero q] :
    indexedResidueCollisionCount (fun d : ↥P.divisors => (d.val : ZMod q)) =
      (collisionPairs P.divisors (fun d => d % q)).card := by
  classical
  simp only [indexedResidueCollisionCount, collisionPairs, Finset.card_filter,
    Fintype.sum_prod_type, Finset.sum_product]
  simp_rw [ZMod.natCast_eq_natCast_iff']
  exact (Finset.sum_coe_sort P.divisors (fun a : ℕ =>
    ∑ b : ↥P.divisors, if a % q = b.val % q then 1 else 0)).trans
      (Finset.sum_congr rfl (fun a ha =>
        Finset.sum_coe_sort P.divisors (fun b : ℕ => if a % q = b % q then 1 else 0)))

/-- Exact normalized energy of the complete divisor list. -/
theorem divisorResidueEnergy_eq_collision_quotient (P q : ℕ) [NeZero q] :
    divisorResidueEnergy P q =
      ((collisionPairs P.divisors (fun d => d % q)).card : ℝ) /
        (P.divisors.card : ℝ)^2 := by
  unfold divisorResidueEnergy
  simp_rw [div_pow]
  rw [← Finset.sum_div, sum_sq_residue_fiber_card,
    indexed_divisor_collision_eq]
  simp only [Fintype.card_coe]

namespace CompositeSupply

/-- A global, total predicate independent of any later ambient supply range.
The strict energy inequality is encoded without division or typeclass data. -/
def BadModulus (d : ℕ) : Prop :=
  2 ≤ d ∧ (base d).Coprime d ∧
    ((base d).divisors.card : ℝ)^2 <
      (d : ℝ)^(7 / 8 : ℝ) *
        ((collisionPairs (base d).divisors (fun a => a % d)).card : ℝ)

lemma divisor_card_pos (u : ℕ) : 0 < ((base u).divisors.card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr
    (show (base u).divisors.Nonempty from
      ⟨1, Nat.one_mem_divisors.mpr (base_pos u).ne'⟩)

lemma badModulus_iff_energy {d : ℕ} [NeZero d] :
    BadModulus d ↔ 2 ≤ d ∧ (base d).Coprime d ∧
      1 / (d : ℝ)^(7 / 8 : ℝ) < divisorResidueEnergy (base d) d := by
  rw [divisorResidueEnergy_eq_collision_quotient]
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hpow : 0 < (d : ℝ)^(7 / 8 : ℝ) := Real.rpow_pos_of_pos hd _
  have hc : 0 < ((base d).divisors.card : ℝ)^2 := pow_pos (divisor_card_pos d) 2
  unfold BadModulus
  rw [div_lt_div_iff₀ hpow hc]
  simp only [one_mul]
  ring_nf

/-- All bad moduli in a dyadic block have a large energy already in its
smaller, fixed divisor pool. This is the input for collision double counting. -/
lemma badModulus_fixed_base_energy {D d : ℕ} [NeZero d]
    (hD : 0 < D) (hDd : D ≤ d) (hd : BadModulus d) :
    1 / (d : ℝ)^(7 / 8 : ℝ) < divisorResidueEnergy (base D) d := by
  have he := (badModulus_iff_energy.mp hd).2.2
  exact he.trans_le (divisorResidueEnergy_le_of_dvd_squarefree
    (base_dvd_mono hD hDd) (base_squarefree d) hd.2.1)

/-- Collision-count version of the fixed-pool implication, ready for the
finite exceptional-modulus theorem. -/
lemma badModulus_fixed_base_collisions {D d : ℕ} [NeZero d]
    (hD : 0 < D) (hDd : D ≤ d) (hd : BadModulus d) :
    ((base D).divisors.card : ℝ)^2 ≤
      (d : ℝ)^(7 / 8 : ℝ) *
        ((collisionPairs (base D).divisors (fun a => a % d)).card : ℝ) := by
  have he := badModulus_fixed_base_energy hD hDd hd
  rw [divisorResidueEnergy_eq_collision_quotient] at he
  have hdp : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hpow : 0 < (d : ℝ)^(7 / 8 : ℝ) := Real.rpow_pos_of_pos hdp _
  have hc : 0 < ((base D).divisors.card : ℝ)^2 := pow_pos (divisor_card_pos D) 2
  have h := (div_lt_div_iff₀ hpow hc).mp he
  nlinarith

/-- The same global bad modulus satisfies the logarithmic roughness
condition needed in any smaller dyadic block. -/
lemma badModulus_prime_lower {D d p : ℕ} (hD : 2 ≤ D) (hDd : D ≤ d)
    (hd : BadModulus d) (hp : p.Prime) (hpd : p ∣ d) :
    Real.log (2 * (D : ℝ)) ≤ (p : ℝ) := by
  have hnot : ¬ p ∣ base d := by
    intro hpP
    have hh := Nat.dvd_gcd hpP hpd
    rw [hd.2.1] at hh
    exact hp.not_dvd_one hh
  apply (Real.log_le_log (by positivity : (0 : ℝ) < 2 * D)
    (show 2 * (D : ℝ) ≤ 2 * (d : ℝ) by exact_mod_cast Nat.mul_le_mul_left 2 hDd)).trans
  exact log_double_le_prime_of_not_dvd d p (hD.trans hDd) hp hnot

/-- Outside the global bad set, every conductor dividing a modulus coprime
to the ambient pool has the required ambient-pool energy bound. -/
lemma ambient_energy_le_of_not_bad {Y q d : ℕ} [NeZero d]
    (hq : 0 < q) (hqY : q ≤ Y) (hdq : d ∣ q)
    (hc : (base Y).Coprime q) (hnd : ¬ BadModulus d) (hd : 2 ≤ d) :
    divisorResidueEnergy (base Y) d ≤ 1 / (d : ℝ)^(7 / 8 : ℝ) := by
  have hdpos : 0 < d := by omega
  have hdY : d ≤ Y := (Nat.le_of_dvd hq hdq).trans hqY
  have hbase : base d ∣ base Y := base_dvd_mono hdpos hdY
  have hcY : (base Y).Coprime d := hc.coprime_dvd_right hdq
  have hcd : (base d).Coprime d := hcY.coprime_dvd_left hbase
  have hsmall : divisorResidueEnergy (base d) d ≤ 1 / (d : ℝ)^(7 / 8 : ℝ) := by
    by_contra h
    exact hnd (badModulus_iff_energy.mpr ⟨hd, hcd, lt_of_not_ge h⟩)
  exact (divisorResidueEnergy_le_of_dvd_squarefree hbase
    (base_squarefree Y) hcY).trans hsmall

/-- The same ambient estimate in the unnormalized form used by the
finite eight-product criterion. -/
lemma ambient_collisions_le_of_not_bad {Y q d : ℕ} [NeZero d]
    (hq : 0 < q) (hqY : q ≤ Y) (hdq : d ∣ q)
    (hc : (base Y).Coprime q) (hnd : ¬ BadModulus d) (hd : 2 ≤ d) :
    ((collisionPairs (base Y).divisors (fun a => a % d)).card : ℝ) ≤
      ((base Y).divisors.card : ℝ)^2 / (d : ℝ)^(7 / 8 : ℝ) := by
  have he := ambient_energy_le_of_not_bad hq hqY hdq hc hnd hd
  rw [divisorResidueEnergy_eq_collision_quotient] at he
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hpow : 0 < (d : ℝ)^(7 / 8 : ℝ) := Real.rpow_pos_of_pos hdp _
  have hcard : 0 < ((base Y).divisors.card : ℝ)^2 := pow_pos (divisor_card_pos Y) 2
  apply (le_div_iff₀ hpow).mpr
  have hh := (div_le_div_iff₀ hcard hpow).mp he
  nlinarith

/-- Every nontrivial conductor of a modulus coprime to the ambient pool
starts beyond the logarithmic cutoff. -/
lemma log_le_conductor {Y q d : ℕ} (hc : (base Y).Coprime q)
    (hdq : d ∣ q) (hd : 2 ≤ d) : Real.log (Y : ℝ) ≤ (d : ℝ) := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hnot : ¬ p ∣ base Y := by
    intro hpP
    have hcommon := Nat.dvd_gcd hpP (hpd.trans hdq)
    rw [hc] at hcommon
    exact hp.not_dvd_one hcommon
  exact (log_le_prime_of_not_dvd Y p hp hnot).trans
    (by exact_mod_cast Nat.le_of_dvd (by omega : 0 < d) hpd)

end CompositeSupply
end Problem337

end

end OAI
