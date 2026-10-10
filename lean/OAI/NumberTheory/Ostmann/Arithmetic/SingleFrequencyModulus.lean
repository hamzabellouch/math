import OAI.NumberTheory.Ostmann.Arithmetic.SingleFrequencyTree

namespace OAI

/-! # The modulus attached to one fixed frequency history -/

namespace Ostmann

open scoped BigOperators Classical

/-- The product includes every internal frequency and every leaf frequency,
with multiplicity, exactly as in the residue-precision argument. -/
def historyFrequencyProduct (S : Finset ℤ) : (n : ℕ) → FrequencyTree S n → ℕ
  | 0, s => (show S from s).val.natAbs
  | n + 1, t => (t.1 : ℤ).natAbs * historyFrequencyProduct S n t.2.1 *
      historyFrequencyProduct S n t.2.2

def historyFrequencyModulus (S : Finset ℤ) (n k : ℕ) (t : FrequencyTree S n) : ℕ :=
  historyFrequencyProduct S n t ^ (k + 2)

theorem historyFrequencyProduct_pos (S : Finset ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (n : ℕ) (t : FrequencyTree S n) : 0 < historyFrequencyProduct S n t := by
  induction n with
  | zero => exact Int.natAbs_pos.mpr (hS _ t.property)
  | succ n ih =>
      exact Nat.mul_pos
        (Nat.mul_pos (Int.natAbs_pos.mpr (hS _ t.1.property)) (ih _)) (ih _)

theorem historyFrequencyModulus_pos (S : Finset ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (n k : ℕ) (t : FrequencyTree S n) : 0 < historyFrequencyModulus S n k t :=
  pow_pos (historyFrequencyProduct_pos S hS n t) _

theorem historyFrequencyProduct_le (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s.natAbs ≤ N) (n : ℕ) (t : FrequencyTree S n) :
    historyFrequencyProduct S n t ≤ N ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simpa [historyFrequencyProduct] using hS _ t.property
  | succ n ih =>
    have he : 2 ^ (n + 1 + 1) - 1 = 1 + (2 ^ (n + 1) - 1) + (2 ^ (n + 1) - 1) := by
      have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    calc
      _ ≤ N * N ^ (2 ^ (n + 1) - 1) * N ^ (2 ^ (n + 1) - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (hS _ t.1.property) (ih _)) (ih _)
      _ = _ := by rw [he]; simp only [pow_add, pow_one]

theorem historyFrequencyModulus_le (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s.natAbs ≤ N) (n k : ℕ) (t : FrequencyTree S n) :
    historyFrequencyModulus S n k t ≤ N ^ ((2 ^ (n + 1) - 1) * (k + 2)) := by
  simpa only [historyFrequencyModulus, pow_mul] using
    Nat.pow_le_pow_left (historyFrequencyProduct_le S N hS n t) (k + 2)

theorem history_root_dvd_frequencyProduct (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n) :
    ((frequencyRoot n t : S) : ℤ).natAbs ∣ historyFrequencyProduct S n t := by
  cases n with
  | zero =>
      change t.val.natAbs ∣ t.val.natAbs
      exact dvd_rfl
  | succ n =>
      change (t.1 : ℤ).natAbs ∣ (t.1 : ℤ).natAbs * _ * _
      exact dvd_mul_of_dvd_left (dvd_mul_right (t.1 : ℤ).natAbs _) _

theorem singleFrequencySplitList_root_mem (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (f : NodeFrequencies) (hf : f ∈ singleFrequencySplitList S n t) : f.root ∈ S := by
  induction n with
  | zero => simp [singleFrequencySplitList] at hf
  | succ n ih =>
    simp only [singleFrequencySplitList, List.mem_cons, List.mem_append] at hf
    rcases hf with rfl | hf | hf
    · exact t.1.property
    · exact ih _ hf
    · exact ih _ hf

theorem singleTreeNodeFrequencies_root_mem (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (j : ℕ) (hj : j < 2 ^ n - 1) : (singleTreeNodeFrequencies S n t j).root ∈ S := by
  apply singleFrequencySplitList_root_mem S n t
  have hj' : j < (singleFrequencySplitList S n t).length := by
    simpa only [singleFrequencySplitList_length] using hj
  rw [singleTreeNodeFrequencies, List.getD_eq_getElem _ _ hj']
  exact List.getElem_mem hj'

theorem history_node_dvd_frequencyProduct (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (f : NodeFrequencies) (hf : f ∈ singleFrequencySplitList S n t) :
    f.root.natAbs ∣ historyFrequencyProduct S n t := by
  induction n with
  | zero => simp [singleFrequencySplitList] at hf
  | succ n ih =>
    simp only [singleFrequencySplitList, List.mem_cons, List.mem_append] at hf
    rcases hf with rfl | hf | hf
    · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (ih _ hf) _) _
    · exact dvd_mul_of_dvd_right (ih _ hf) _

theorem history_node_dvd_frequencyModulus (S : Finset ℤ) (n k : ℕ) (t : FrequencyTree S n)
    (f : NodeFrequencies) (hf : f ∈ singleFrequencySplitList S n t) :
    f.root.natAbs ∣ historyFrequencyModulus S n k t :=
  (history_node_dvd_frequencyProduct S n t f hf).trans (dvd_pow_self _ (by omega))

/-- All actual primes exceed the frequency range. Consequently they are
units for the full history modulus, including its precision exponent. -/
theorem prime_coprime_historyFrequencyModulus (S : Finset ℤ) (N p : ℕ)
    (hp : p.Prime) (hpN : N < p)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (n k : ℕ) (t : FrequencyTree S n) :
    p.Coprime (historyFrequencyModulus S n k t) := by
  have hfreq (s : S) : p.Coprime (s : ℤ).natAbs := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hpos : 0 < (s : ℤ).natAbs := Int.natAbs_pos.mpr (hS _ s.property).1
    have hle := Nat.le_of_dvd hpos hd
    have hbound := (hS _ s.property).2
    omega
  have hprod : p.Coprime (historyFrequencyProduct S n t) := by
    induction n with
    | zero => exact hfreq t
    | succ n ih => exact (hfreq t.1).mul_right (ih t.2.1) |>.mul_right (ih t.2.2)
  exact hprod.pow_right (k + 2)

theorem historyFrequencyModulus_le_exp (S : Finset ℤ) (N n k : ℕ) (C m : ℝ)
    (hS : ∀ s ∈ S, s.natAbs ≤ N) (hN : (N : ℝ) ≤ Real.exp (C * m))
    (t : FrequencyTree S n) :
    (historyFrequencyModulus S n k t : ℝ) ≤
      Real.exp (((2 ^ (n + 1) - 1) * (k + 2) : ℕ) * (C * m)) := by
  calc
    _ ≤ (N : ℝ) ^ ((2 ^ (n + 1) - 1) * (k + 2)) := by
      exact_mod_cast historyFrequencyModulus_le S N hS n k t
    _ ≤ Real.exp (C * m) ^ ((2 ^ (n + 1) - 1) * (k + 2)) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hN _
    _ = _ := (Real.exp_nat_mul _ _).symm

end Ostmann

end OAI
