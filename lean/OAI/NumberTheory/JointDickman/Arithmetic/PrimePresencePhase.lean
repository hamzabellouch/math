import OAI.NumberTheory.JointDickman.Arithmetic.PrimeGeneratingMean
import OAI.NumberTheory.JointDickman.Amplification.NearCofactorMean

namespace OAI

/-! # Oscillatory divisor expansion for prime-presence weights -/
namespace JointDickman
open Finset TwoPointCorrelations

noncomputable def primePresence (P : Finset ℕ) (z : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∏ p ∈ P, if p ∣ n then z p else 1

theorem primePresence_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℂ) (n : ℕ) :
    primePresence P z n = ∑ D ∈ P.powerset,
      if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, (z p-1) else 0 := by
  classical
  have he (p : ℕ) : (if p ∣ n then z p else 1) =
      1 + (if p ∣ n then z p-1 else 0) := by split_ifs <;> simp
  simp_rw [primePresence,he]
  rw [prod_one_add]
  apply sum_congr rfl
  intro D hD
  rw [prod_ite_zero]
  simp only [primeProduct_dvd_iff D (fun p hp => hP p (mem_powerset.mp hD hp))]

theorem sum_Icc_dvd_reindex {M : Type*} [AddCommMonoid M]
    {d : ℕ} (hd : 0 < d) (N : ℕ) (F : ℕ → M) :
    (∑ n ∈ Icc 1 N, if d ∣ n then F n else 0) =
      ∑ m ∈ Icc 1 (N/d), F (d*m) := by
  classical
  rw [← sum_filter]
  apply sum_bij (fun n _ => n/d)
  · intro n hn
    obtain ⟨hn,hdn⟩ := mem_filter.mp hn
    have hp : 0 < n := (mem_Icc.mp hn).1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hp hdn) hd,
      Nat.div_le_div_right (mem_Icc.mp hn).2⟩
  · intro n hn m hm he
    have hdn := (mem_filter.mp hn).2
    have hdm := (mem_filter.mp hm).2
    simpa only [Nat.mul_div_cancel' hdn,Nat.mul_div_cancel' hdm] using congrArg (d*·) he
  · intro m hm
    obtain ⟨hm1,hmN⟩ := mem_Icc.mp hm
    refine ⟨d*m,mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith,
      by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmN⟩,
      dvd_mul_right d m⟩,Nat.mul_div_cancel_left m hd⟩
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

theorem primePresence_phase_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    halaszPhaseMean (primePresence P z) t N =
      ∑ D ∈ boundedPrimeSubsets P N,
        (∏ p ∈ D, (z p-1))*halaszPowerPhase t (∏ p ∈ D, (p:ℝ))*
          ∑ m ∈ Icc 1 (N/(∏ p ∈ D, p)), halaszPowerPhase t m := by
  classical
  have he : halaszPhaseMean (primePresence P z) t N =
      ∑ D ∈ P.powerset,
        (∏ p ∈ D, (z p-1))*halaszPowerPhase t (∏ p ∈ D, (p:ℝ))*
          ∑ m ∈ Icc 1 (N/(∏ p ∈ D, p)), halaszPowerPhase t m := by
    simp only [halaszPhaseMean,primePresence_expansion P hP z,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro D hD
    have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp => (hP p (mem_powerset.mp hD hp)).pos)
    have hi : (∑ n ∈ Icc 1 N,
        (if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, (z p-1) else 0)*halaszPowerPhase t n) =
        ∑ n ∈ Icc 1 N, if (∏ p ∈ D, p) ∣ n then
          (∏ p ∈ D, (z p-1))*halaszPowerPhase t n else 0 := by
      apply sum_congr rfl
      intro n _
      split_ifs <;> simp
    rw [hi,sum_Icc_dvd_reindex hd,mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [Nat.cast_mul,halasz_power_phase_mul t _ _ (by exact_mod_cast hd)
      (by exact_mod_cast (mem_Icc.mp hm).1),Nat.cast_prod,mul_assoc]
  rw [he]
  symm
  apply sum_subset (filter_subset _ _)
  intro D hDP hD
  have hd : N < ∏ p ∈ D, p := by
    exact lt_of_not_ge (fun h => hD (mem_filter.mpr ⟨hDP,h⟩))
  simp only [Nat.div_eq_of_lt hd,show Icc 1 (0:ℕ) = ∅ by decide,sum_empty,mul_zero]

lemma power_phase_sum_bound (t : ℝ) (x : ℝ) (hx : 0 ≤ x) :
    ‖∑ m ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t m‖ ≤
      2*x/(1+|t|)+9*(1+|t|) := by
  have he := halasz_power_phase_sum_real t x hx
  have hm : ‖(x:ℂ)*halaszPowerPhase t x/(1+(-t:ℂ)*Complex.I)‖ ≤ 2*x/(1+|t|) := by
    rw [mul_div_assoc,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx]
    calc
      _ ≤ x*(2/(1+|t|)) := mul_le_mul_of_nonneg_left (halasz_phase_factor_decay t x) hx
      _ = _ := by ring
  exact (norm_le_norm_sub_add _ _).trans
    ((add_le_add he hm).trans_eq (_root_.add_comm _ _))

end JointDickman

end OAI
