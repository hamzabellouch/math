import OAI.NumberTheory.TwoPointCorrelations.MRTAmplificationPower

namespace OAI

/-! Real short-prime bins, as used in the Ramaré decomposition, fit the
integer endpoint mixed-moment theorem without moving any prime. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_real_prime_bin_subset (P : Finset ℕ) {Y : ℝ}
    (hbin : ∀ p ∈ P, Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y) :
    P ⊆ Icc ⌈Y⌉₊ (2 * ⌈Y⌉₊) := by
  intro p hp
  refine mem_Icc.mpr ⟨Nat.ceil_le.mpr (hbin p hp).1, ?_⟩
  have hh : (p : ℝ) ≤ 2 * (⌈Y⌉₊ : ℝ) :=
    (hbin p hp).2.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil Y) (by norm_num))
  exact_mod_cast hh

lemma mrt_real_prime_bin_ceil {Y : ℝ} (hY : 1 < Y) :
    1 < ⌈Y⌉₊ ∧ Y ≤ (⌈Y⌉₊ : ℝ) ∧ (⌈Y⌉₊ : ℝ) ≤ 2 * Y ∧
      Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log Y + Real.log 2 := by
  have hY0 : 0 < Y := by linarith
  have hlo : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
  have hhi : (⌈Y⌉₊ : ℝ) ≤ 2 * Y := by
    have hh := Nat.ceil_lt_add_one hY0.le
    linarith
  refine ⟨Nat.lt_ceil.mpr (by simpa using hY), hlo, hhi, ?_⟩
  calc
    _ ≤ Real.log (2 * Y) := Real.log_le_log (hY0.trans_le hlo) hhi
    _ = _ := by rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY0.ne']; ring

theorem mrt_real_short_class_cofactor_energy (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y : ℝ} (hY : 1 < Y)
    (hbin : ∀ p ∈ P, Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y)
    {N : ℕ} (hN : 0 < N) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial P
      (fun p => a p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      (16 * Real.exp 10 *
        (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
          ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2) /
        V ^ (2 * mrtAmplificationOrder ⌈Y⌉₊ u) := by
  exact mrt_short_class_cofactor_energy_chosen P Q hP
    (mrt_real_prime_bin_ceil hY).1 hN
    (mrt_real_prime_bin_subset P hbin) a ha F hF hu hT hV hE hlarge

end TwoPointCorrelations

end OAI
