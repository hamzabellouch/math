import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeSetQuadratic

namespace OAI

/-! # The original positive periodic amplification weight -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def amplificationWeight (Q : Finset ℕ)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) : ℝ :=
  ∏ p ∈ Q, (1 + (1 / 16 : ℝ) * centeredDensity (D p) (n : ZMod p))

theorem amplificationWeight_pos (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    0 < amplificationWeight Q D n := by
  apply Finset.prod_pos
  intro p hp
  let : NeZero p := ⟨(hQ p hp).ne_zero⟩
  have hh := (abs_le.mp (centeredDensity_abs_le (D p) (n : ZMod p))).1
  linarith

theorem amplificationWeight_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    amplificationWeight Q D n ≤ (17 / 16 : ℝ) ^ Q.card := by
  unfold amplificationWeight
  calc
    _ ≤ ∏ _p ∈ Q, (17 / 16 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        let : NeZero p := ⟨(hQ p hp).ne_zero⟩
        have hh := (abs_le.mp (centeredDensity_abs_le (D p) (n : ZMod p))).1
        linarith
      · intro p hp
        let : NeZero p := ⟨(hQ p hp).ne_zero⟩
        have hh := (abs_le.mp (centeredDensity_abs_le (D p) (n : ZMod p))).2
        linarith
    _ = _ := by rw [Finset.prod_const]

theorem amplificationWeight_lower (Q : Finset ℕ)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ)
    (hD : ∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3)
    (hn : ∀ p ∈ Q, (n : ZMod p) ∈ D p) :
    (49 / 48 : ℝ) ^ Q.card ≤ amplificationWeight Q D n := by
  rw [amplificationWeight, ← Finset.prod_const]
  apply Finset.prod_le_prod₀ (fun _ _ => by norm_num)
  intro p hp
  have hd := hD p hp
  rw [centeredDensity, ite_eq_left (hn p hp)]
  linarith

theorem exp_le_amplificationWeight (Q : Finset ℕ)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ)
    (hD : ∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3)
    (hn : ∀ p ∈ Q, (n : ZMod p) ∈ D p) :
    Real.exp ((Q.card : ℝ) / 50) ≤ amplificationWeight Q D n := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 49 / 48)
  have hlog : (1 / 50 : ℝ) ≤ Real.log (49 / 48) := by norm_num at hh ⊢; linarith
  apply le_trans _ (amplificationWeight_lower Q D n hD hn)
  calc
    _ ≤ Real.exp ((Q.card : ℝ) * Real.log (49 / 48)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) Q.card]
    _ = (49 / 48 : ℝ) ^ Q.card := by
      simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 49 / 48)] using
        Real.exp_nat_mul (Real.log (49 / 48)) Q.card

noncomputable def primeDivisorDensity (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) : ZMod U.toList.prod → ℂ :=
  if hU : U ⊆ Q then
    let : NeZero U.toList.prod :=
      ⟨(prime_list_prod_pos U.toList (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
    (densityCRTList U.toList
      (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
      (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D).value
  else fun _ => 0

theorem primeDivisorDensity_intCast (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (hU : U ⊆ Q) (n : ℤ) :
    primeDivisorDensity Q hQ D U (n : ZMod U.toList.prod) =
      ∏ p ∈ U, (centeredDensity (D p) (n : ZMod p) : ℂ) := by
  rw [primeDivisorDensity, dite_eq_left hU]
  simpa using densityCRTList_intCast U.toList
    (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
    (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D n

/-- Exact divisor expansion, with the same CRT density functions as those
already used in the Fourier coefficient construction. -/
theorem amplificationWeight_expansion (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    (amplificationWeight Q D n : ℂ) =
      ∑ U ∈ Q.powerset, (1 / 16 : ℂ) ^ U.card *
        primeDivisorDensity Q hQ D U (n : ZMod U.toList.prod) := by
  unfold amplificationWeight
  push_cast
  simp_rw [add_comm (1 : ℂ)]
  rw [Finset.prod_add_one]
  apply Finset.sum_congr rfl
  intro U hU
  rw [primeDivisorDensity_intCast Q hQ D U (Finset.mem_powerset.mp hU) n,
    Finset.prod_mul_distrib, Finset.prod_const]

end Ostmann

end OAI
