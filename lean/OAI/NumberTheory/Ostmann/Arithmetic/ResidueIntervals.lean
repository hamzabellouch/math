import OAI.NumberTheory.Ostmann.Construction.GiantDiscreteTransport

namespace OAI

/-! # Exact residue decompositions of the original giant sums -/

namespace Ostmann
open scoped BigOperators Classical

def reducedResidues (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => a.Coprime q)

theorem reducedResidues_card_le (q : ℕ) : (reducedResidues q).card ≤ q := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range q)

theorem prime_mod_mem_reducedResidues (q p : ℕ) (hq : 0 < q) (hp : p.Prime) (hqp : q < p) :
    p % q ∈ reducedResidues q := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), ?_⟩
  have hc : p.Coprime q := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hq hqp)
  rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec]
  exact hc.symm

theorem sum_residue_indicator (q : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a < q)
    (p : ℕ) (hp : p % q ∈ S) (z : ℂ) :
    (∑ a ∈ S, if Nat.ModEq q p a then z else 0) = z := by
  rw [Finset.sum_eq_single (p % q)]
  · simp only [Nat.ModEq, Nat.mod_mod, ite_true]
  · intro a ha hne
    have hnot : ¬ Nat.ModEq q p a := by
      intro h
      have he : p % q = a := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hS a ha)] using h
      exact hne he.symm
    simp only [hnot, ite_false]
  · exact fun hn => (hn hp).elim

theorem complexPrimeInterval_residues (q : ℕ) (hq : 0 < q) (u v : ℝ)
    (hlarge : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, p.Prime → q < p)
    (f : ℝ → ℂ) :
    complexPrimeInterval 1 0 u v f =
      ∑ a ∈ reducedResidues q, complexPrimeInterval q a u v f := by
  unfold complexPrimeInterval
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · simp only [hprime, true_and, Nat.modEq_one, ite_true]
    exact (sum_residue_indicator q (reducedResidues q)
      (fun a ha => Finset.mem_range.mp (Finset.mem_filter.mp ha).1) p
      (prime_mod_mem_reducedResidues q p hq hprime (hlarge p hp hprime)) _).symm
  · simp only [hprime, false_and, ite_false, Finset.sum_const_zero]

theorem complexIntegerInterval_residues (q : ℕ) (hq : 0 < q) (u v J : ℝ) (f : ℝ → ℂ) :
    complexIntegerInterval 1 0 u v J f =
      ∑ a ∈ Finset.range q, complexIntegerInterval q a u v J f := by
  unfold complexIntegerInterval integerResidueAtom
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Nat.modEq_one, ite_true, apply_ite, Complex.ofReal_zero, mul_zero]
  exact (sum_residue_indicator q (Finset.range q) (fun a ha => Finset.mem_range.mp ha) p
    (Finset.mem_range.mpr (Nat.mod_lt _ hq)) _).symm

theorem complexPrimeInterval_finset_sum {A : Type*} (S : Finset A)
    (q a : ℕ) (u v : ℝ) (f : A → ℝ → ℂ) :
    complexPrimeInterval q a u v (fun y => ∑ i ∈ S, f i y) =
      ∑ i ∈ S, complexPrimeInterval q a u v (f i) := by
  unfold complexPrimeInterval
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp only [Finset.sum_mul, Finset.sum_const_zero]

theorem reciprocalPrimeInterval_le_exp (q a : ℕ) (u v : ℝ) :
    reciprocalPrimeInterval q a (Real.exp u) (Real.exp v) ≤ Real.exp (v - u) := by
  calc
    _ ≤ ∑ _p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, Real.exp (-u) := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      · have hp0 : (0 : ℝ) < p := (Real.exp_pos u).trans (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hp).1)
        have hlog : Real.exp (-Real.log (p : ℝ)) = (p : ℝ)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log hp0]
        rw [← hlog]
        exact Real.exp_le_exp.mpr (neg_le_neg (log_mem_of_mem_exp_interval hp).1.le)
      · exact (Real.exp_pos _).le
    _ = ((⌊Real.exp v⌋₊ - ⌊Real.exp u⌋₊ : ℕ) : ℝ) * Real.exp (-u) := by simp
    _ ≤ Real.exp v * Real.exp (-u) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add, sub_eq_add_neg]

end Ostmann

end OAI
