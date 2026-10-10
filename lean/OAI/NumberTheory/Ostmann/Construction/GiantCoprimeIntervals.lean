import OAI.NumberTheory.Ostmann.Construction.GiantCoprimeRemoval
import OAI.NumberTheory.Ostmann.Arithmetic.ResidueIntervals

namespace OAI

/-! # The top coprimality error on the literal giant interval laws -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def giantPrimes (u v : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊).filter Nat.Prime

theorem complexPrimeInterval_primeSum (u v : ℝ) (f : ℝ → ℂ) :
    complexPrimeInterval 1 0 u v f =
      ∑ p ∈ giantPrimes u v, ((p : ℝ)⁻¹ : ℂ) * f (Real.log p) := by
  simp only [complexPrimeInterval, giantPrimes, Finset.sum_filter, Nat.modEq_one, and_true]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime <;> simp only [hp, ite_true, ite_false, mul_comm]

theorem reciprocalPrimeInterval_primeSum (u v : ℝ) :
    reciprocalPrimeInterval 1 0 (Real.exp u) (Real.exp v) =
      ∑ p ∈ giantPrimes u v, (p : ℝ)⁻¹ := by
  simp only [reciprocalPrimeInterval, giantPrimes, Finset.sum_filter, Nat.modEq_one, and_true]

theorem prime_pair_naturalSum (u v r s : ℝ) (F : ℕ → ℕ → ℂ) :
    complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v
      (fun x => F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) =
      ∑ q ∈ giantPrimes r s, ((q : ℝ)⁻¹ : ℂ) *
        ∑ p ∈ giantPrimes u v, ((p : ℝ)⁻¹ : ℂ) * F p q := by
  rw [complexPrimeInterval_primeSum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_filter.mp hq).2.pos
  rw [Real.exp_log hq0, Nat.floor_natCast, complexPrimeInterval_primeSum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  rw [Real.exp_log hp0, Nat.floor_natCast]

theorem mixed_pair_naturalSum (u v r s J : ℝ) (F : ℕ → ℕ → ℂ) :
    complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J
      (fun x => F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) =
      ∑ q ∈ giantPrimes r s, ((q : ℝ)⁻¹ : ℂ) *
        ∑ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, (Real.exp (-J) : ℂ) * F p q := by
  rw [complexPrimeInterval_primeSum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_filter.mp hq).2.pos
  rw [Real.exp_log hq0, Nat.floor_natCast]
  congr 1
  unfold complexIntegerInterval integerResidueAtom
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by
    have h := (Finset.mem_Ioc.mp hp).1
    have hpNat : 0 < p := Nat.zero_le _ |>.trans_lt h
    exact_mod_cast hpNat
  dsimp only
  rw [Real.exp_log hp0, Nat.floor_natCast]
  simp only [Nat.modEq_one, ite_true, mul_comm]

theorem prime_pair_coprime_removal (u v r s : ℝ) (F : ℕ → ℕ → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ p ∈ giantPrimes u v, ∀ q ∈ giantPrimes r s, ‖F p q‖ ≤ K) :
    ‖complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
        if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ else 0)) -
      complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
        F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))‖ ≤
      K * Real.exp (-u) * reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp s) := by
  rw [prime_pair_naturalSum u v r s (fun p q => if p.Coprime q then F p q else 0),
    prime_pair_naturalSum u v r s F, reciprocalPrimeInterval_primeSum]
  simp only [← Complex.ofReal_inv]
  apply weighted_prime_coprime_removal
    (giantPrimes u v) (giantPrimes r s) (fun p => (p : ℝ)⁻¹) (fun q => (q : ℝ)⁻¹)
    (fun _ hp => (Finset.mem_filter.mp hp).2) (fun _ hq => (Finset.mem_filter.mp hq).2)
    (fun _ _ => by positivity) (fun _ _ => by positivity) _ (Real.exp_pos _).le _ F K hK hF
  intro p hp
  have hpI := (Finset.mem_filter.mp hp).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  rw [← Real.exp_log hp0, ← Real.exp_neg]
  exact Real.exp_le_exp.mpr (neg_le_neg (log_mem_of_mem_exp_interval hpI).1.le)

theorem mixed_pair_coprime_removal (u v r s J : ℝ) (F : ℕ → ℕ → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      ∀ q ∈ giantPrimes r s, ‖F p q‖ ≤ K) :
    ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
        if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ else 0)) -
      complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
        F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))‖ ≤
      K * Real.exp (v - J) * Real.exp (-r) *
        reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp s) := by
  rw [mixed_pair_naturalSum u v r s J (fun p q => if p.Coprime q then F p q else 0),
    mixed_pair_naturalSum u v r s J F, reciprocalPrimeInterval_primeSum]
  simp only [← Complex.ofReal_inv]
  refine (weighted_integer_prime_coprime_removal
    (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊) (giantPrimes r s)
    (fun _ => Real.exp (-J)) (fun q => (q : ℝ)⁻¹) ⌊Real.exp v⌋₊
    (fun _ hq => (Finset.mem_filter.mp hq).2)
    (fun p hp => Nat.zero_le _ |>.trans_lt (Finset.mem_Ioc.mp hp).1)
    (fun _ hp => (Finset.mem_Ioc.mp hp).2)
    (fun _ _ => (Real.exp_pos _).le) (fun _ _ => by positivity)
    _ (Real.exp_pos _).le (fun _ _ => le_rfl) F K hK hF).trans ?_
  have hsum : (∑ q ∈ giantPrimes r s, (q : ℝ)⁻¹ / q) ≤
      Real.exp (-r) * ∑ q ∈ giantPrimes r s, (q : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_filter.mp hq).2.pos
    have hi : (q : ℝ)⁻¹ ≤ Real.exp (-r) := by
      rw [← Real.exp_log hq0, ← Real.exp_neg]
      exact Real.exp_le_exp.mpr (neg_le_neg (log_mem_of_mem_exp_interval (Finset.mem_filter.mp hq).1).1.le)
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ (q : ℝ)⁻¹)
  have hN : (⌊Real.exp v⌋₊ : ℝ) ≤ Real.exp v := Nat.floor_le (Real.exp_pos _).le
  calc
    _ ≤ K * Real.exp (-J) * Real.exp v *
        (Real.exp (-r) * ∑ q ∈ giantPrimes r s, (q : ℝ)⁻¹) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hN (by positivity)) hsum
        (Finset.sum_nonneg fun q _ => by positivity) (by positivity)
    _ = _ := by rw [Real.exp_sub, Real.exp_neg]; ring

end Ostmann

end OAI
