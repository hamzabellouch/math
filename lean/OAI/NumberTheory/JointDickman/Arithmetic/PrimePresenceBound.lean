import OAI.NumberTheory.JointDickman.Arithmetic.PrimePresencePhase
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSubsetTail
import OAI.NumberTheory.JointDickman.Amplification.FiniteProductTail

namespace OAI

/-! # An elementary middle-frequency bound for rough prime weights -/
namespace JointDickman
open Finset TwoPointCorrelations

lemma prime_presence_coefficient_mass (P : Finset ℕ) (z : ℕ → ℂ)
    (hz : ∀ p ∈ P, ‖z p‖ ≤ 1) :
    (∑ D ∈ P.powerset, ‖∏ p ∈ D, (z p-1)‖/(∏ p ∈ D, (p:ℝ))) ≤
      Real.exp (2*∑ p ∈ P, 1/(p:ℝ)) := by
  have he : (∑ D ∈ P.powerset, ‖∏ p ∈ D, (z p-1)‖/(∏ p ∈ D, (p:ℝ))) =
      ∏ p ∈ P, (1+‖z p-1‖/(p:ℝ)) := by
    simp_rw [norm_prod,← prod_div_distrib]
    exact (prod_one_add _).symm
  rw [he]
  apply (prod_one_add_le_exp_sum P (fun p => ‖z p-1‖/(p:ℝ))
    (fun p _ => by positivity)).trans
  apply Real.exp_le_exp.mpr
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hb : ‖z p-1‖ ≤ 2 := by
    have hh := norm_sub_le (z p) 1
    norm_num only [norm_one] at hh
    linarith [hz p hp]
  simpa only [mul_one_div] using div_le_div_of_nonneg_right hb (Nat.cast_nonneg p)

lemma prime_presence_coefficient_bound (P D : Finset ℕ) (hDP : D ⊆ P)
    (z : ℕ → ℂ) (hz : ∀ p ∈ P, ‖z p‖ ≤ 1) {J : ℕ} (hD : D.card ≤ J) :
    ‖∏ p ∈ D, (z p-1)‖ ≤ (2:ℝ)^J := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _p ∈ D, (2:ℝ) := prod_le_prod₀ (fun _ _ => norm_nonneg _) (by
      intro p hp
      have hh := norm_sub_le (z p) 1
      norm_num only [norm_one] at hh
      linarith [hz p (hDP hp)])
    _ = (2:ℝ)^D.card := by simp
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hD

lemma power_phase_divisor_bound (t : ℝ) (N d : ℕ) (hd : 0 < d)
    {Y : ℝ} (hY : 0 ≤ Y) :
    ‖∑ m ∈ Icc 1 (N/d), halaszPowerPhase t m‖ ≤
      (2*(N:ℝ)/(1+|t|)+9*(1+|t|)*Y)/(d:ℝ) +
        if Y < (d:ℝ) then (N:ℝ)/d else 0 := by
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd
  have hp : 0 < 1+|t| := by positivity
  have hA : 0 ≤ 2*(N:ℝ)/(1+|t|)+9*(1+|t|)*Y := by positivity
  by_cases hs : (d:ℝ) ≤ Y
  · rw [ite_eq_right (not_lt_of_ge hs),add_zero]
    have hb := power_phase_sum_bound t ((N:ℝ)/d) (by positivity)
    rw [Nat.floor_div_eq_div] at hb
    apply hb.trans
    have hq : 1 ≤ Y/(d:ℝ) := (le_div_iff₀ hd0).mpr (by simpa using hs)
    calc
      _ ≤ 2*((N:ℝ)/d)/(1+|t|)+9*(1+|t|)*(Y/d) := by
        nlinarith [mul_le_mul_of_nonneg_left hq (show 0 ≤ 9*(1+|t|) by positivity)]
      _ = _ := by ring
  · rw [ite_eq_left (lt_of_not_ge hs)]
    have hb : ‖∑ m ∈ Icc 1 (N/d), halaszPowerPhase t m‖ ≤ (N:ℝ)/d := by
      calc
        _ ≤ ∑ m ∈ Icc 1 (N/d), ‖halaszPowerPhase t m‖ := norm_sum_le _ _
        _ = (N/d:ℕ) := by simp
        _ ≤ _ := Nat.cast_div_le
    exact hb.trans (le_add_of_nonneg_left (div_nonneg hA hd0.le))

/-- A finite, uniform oscillatory estimate. Its inputs are the literal
prime set and the cardinality bound for products below the cutoff. -/
theorem primePresence_phase_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℂ) (hz : ∀ p ∈ P, ‖z p‖ ≤ 1) (t : ℝ) (N J : ℕ)
    {Y : ℝ} (hY : 0 ≤ Y)
    (hcard : ∀ D ∈ boundedPrimeSubsets P N, D.card ≤ J) :
    ‖halaszPhaseMean (primePresence P z) t N‖ ≤
      (2*(N:ℝ)/(1+|t|)+9*(1+|t|)*Y)*Real.exp (2*∑ p ∈ P, 1/(p:ℝ)) +
        (N:ℝ)*2^J*primeSubsetTail P Y N := by
  classical
  let A := 2*(N:ℝ)/(1+|t|)+9*(1+|t|)*Y
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let B := boundedPrimeSubsets P N
  let w (D : Finset ℕ) := ‖∏ p ∈ D, (z p-1)‖/(∏ p ∈ D, (p:ℝ))
  have hterm (D : Finset ℕ) (hD : D ∈ B) :
      ‖(∏ p ∈ D, (z p-1))*halaszPowerPhase t (∏ p ∈ D, (p:ℝ))*
        ∑ m ∈ Icc 1 (N/(∏ p ∈ D, p)), halaszPowerPhase t m‖ ≤
      A*w D+(if Y < ∏ p ∈ D, (p:ℝ) then (N:ℝ)*w D else 0) := by
    have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp =>
      (hP p (mem_powerset.mp (mem_filter.mp hD).1 hp)).pos)
    have hb := mul_le_mul_of_nonneg_left (power_phase_divisor_bound t N _ hd hY)
      (norm_nonneg (∏ p ∈ D, (z p-1)))
    rw [norm_mul,norm_mul,halasz_power_phase_norm,mul_one]
    apply hb.trans_eq
    rw [Nat.cast_prod]
    dsimp only [A,w]
    split_ifs <;> ring
  have hmass : (∑ D ∈ B, w D) ≤ Real.exp (2*∑ p ∈ P, 1/(p:ℝ)) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by dsimp [w]; positivity)).trans
      (prime_presence_coefficient_mass P z hz)
  have htail : (∑ D ∈ B, if Y < ∏ p ∈ D, (p:ℝ) then (N:ℝ)*w D else 0) ≤
      (N:ℝ)*2^J*primeSubsetTail P Y N := by
    rw [← sum_filter]
    have he : B.filter (fun D : Finset ℕ => Y < ∏ p ∈ D, (p:ℝ)) =
        P.powerset.filter (fun D : Finset ℕ =>
          Y < (∏ p ∈ D, (p:ℝ)) ∧ (∏ p ∈ D, (p:ℝ)) ≤ N) := by
      ext D
      simp only [B,boundedPrimeSubsets,mem_filter,mem_powerset]
      rw [← Nat.cast_le (α := ℝ)]
      simp only [Nat.cast_prod]
      tauto
    rw [he,primeSubsetTail,mul_sum]
    apply sum_le_sum
    intro D hD
    have hDP := mem_powerset.mp (mem_filter.mp hD).1
    have hDB : D ∈ B := mem_filter.mpr ⟨(mem_filter.mp hD).1,by
      have hh : ((∏ p ∈ D, p : ℕ):ℝ) ≤ N := by
        simpa only [Nat.cast_prod] using (mem_filter.mp hD).2.2
      exact_mod_cast hh⟩
    have hb := prime_presence_coefficient_bound P D hDP z hz (hcard D hDB)
    dsimp [w]
    calc
      _ ≤ (N:ℝ)*((2:ℝ)^J/(∏ p ∈ D, (p:ℝ))) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (by positivity)) (Nat.cast_nonneg N)
      _ = _ := by ring
  rw [primePresence_phase_expansion P hP]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum hterm).trans
  rw [sum_add_distrib,← mul_sum]
  exact add_le_add (mul_le_mul_of_nonneg_left hmass hA) htail

end JointDickman

end OAI
