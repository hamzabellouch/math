import Mathlib.Data.Nat.GCD.BigOperators
import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructionTestBounds

namespace OAI

/-! # A nonzero common modulus constructed from the actual small frequencies -/

namespace Ostmann

def historyFrequencyBase (frequencies : List ℤ) : ℕ := (frequencies.map Int.natAbs).prod

def historyFrequencyPeriod (frequencies : List ℤ) (degree : ℕ) : ℕ :=
  historyFrequencyBase frequencies ^ degree

theorem historyFrequencyBase_pos (frequencies : List ℤ)
    (h : ∀ s ∈ frequencies, s ≠ 0) : 0 < historyFrequencyBase frequencies := by
  induction frequencies with
  | nil => simp [historyFrequencyBase]
  | cons s rest ih =>
    simp only [historyFrequencyBase, List.map_cons, List.prod_cons]
    exact Nat.mul_pos (Int.natAbs_pos.mpr (h s (by simp)))
      (ih (fun t ht => h t (by simp [ht])))

theorem historyFrequencyPeriod_pos (frequencies : List ℤ) (degree : ℕ)
    (h : ∀ s ∈ frequencies, s ≠ 0) : 0 < historyFrequencyPeriod frequencies degree :=
  pow_pos (historyFrequencyBase_pos frequencies h) degree

theorem frequency_dvd_historyFrequencyBase (frequencies : List ℤ) (s : ℤ)
    (hs : s ∈ frequencies) : s ∣ (historyFrequencyBase frequencies : ℤ) := by
  apply Int.dvd_natCast.mpr
  exact List.dvd_prod (List.mem_map.mpr ⟨s, hs, rfl⟩)

theorem prime_coprime_historyFrequencyPeriod (frequencies : List ℤ) (degree p : ℕ)
    (hp : p.Prime) (hsmall : ∀ s ∈ frequencies, 0 < s.natAbs ∧ s.natAbs < p) :
    p.Coprime (historyFrequencyPeriod frequencies degree) := by
  apply Nat.Coprime.pow_right
  apply Nat.coprime_list_prod_right_iff.mpr
  intro n hn
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hn
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (hsmall s hs).1 (hsmall s hs).2)

theorem constructed_history_test_period {σ : Type*} (steps : List (HistoryPivotStep σ))
    (frequencies : List ℤ) (C : ℕ) (hC : 1 ≤ C)
    (hsteps : ∀ step ∈ steps, step.s ∈ frequencies)
    (hsize : ∀ step ∈ steps, step.left.length + step.right.length + 4 ≤ C)
    (s : ℤ) (hs : s ∈ frequencies) (F : HistoryFormula σ)
    (hF : F ∈ reconstructionTests steps HistoryFormula.prime) :
    F.cleared.denominator * s ∣
      (historyFrequencyPeriod frequencies (C ^ steps.length + 1) : ℤ) := by
  simpa only [historyFrequencyPeriod, Nat.cast_pow] using
    reconstructionTests_prime_period steps (historyFrequencyBase frequencies) s C hC
      (fun step hstep => frequency_dvd_historyFrequencyBase frequencies step.s (hsteps step hstep))
      hsize (frequency_dvd_historyFrequencyBase frequencies s hs) F hF

theorem constructed_history_test_period_of_dvd {σ : Type*} (steps : List (HistoryPivotStep σ))
    (frequencies : List ℤ) (C : ℕ) (hC : 1 ≤ C)
    (hsteps : ∀ step ∈ steps, step.s ∈ frequencies)
    (hsize : ∀ step ∈ steps, step.left.length + step.right.length + 4 ≤ C)
    (s : ℤ) (hs : s ∣ (historyFrequencyBase frequencies : ℤ)) (F : HistoryFormula σ)
    (hF : F ∈ reconstructionTests steps HistoryFormula.prime) :
    F.cleared.denominator * s ∣
      (historyFrequencyPeriod frequencies (C ^ steps.length + 1) : ℤ) := by
  simpa only [historyFrequencyPeriod, Nat.cast_pow] using
    reconstructionTests_prime_period steps (historyFrequencyBase frequencies) s C hC
      (fun step hstep => frequency_dvd_historyFrequencyBase frequencies step.s (hsteps step hstep))
      hsize hs F hF

theorem historyFrequencyPeriod_le (frequencies : List ℤ) (V degree : ℕ)
    (hV : ∀ s ∈ frequencies, s.natAbs ≤ V) :
    historyFrequencyPeriod frequencies degree ≤ V ^ (frequencies.length * degree) := by
  have hb : historyFrequencyBase frequencies ≤ V ^ frequencies.length := by
    induction frequencies with
    | nil => simp [historyFrequencyBase]
    | cons s rest ih =>
      simp only [historyFrequencyBase, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      exact (Nat.mul_le_mul (hV s (by simp))
        (ih (fun t ht => hV t (by simp [ht])))).trans_eq (Nat.mul_comm _ _)
  exact (Nat.pow_le_pow_left hb degree).trans_eq (pow_mul V frequencies.length degree).symm

theorem constructed_history_test_period_of_length {σ : Type*}
    (steps : List (HistoryPivotStep σ)) (frequencies : List ℤ) (C N : ℕ) (hC : 1 ≤ C)
    (hlen : steps.length ≤ N) (hsteps : ∀ step ∈ steps, step.s ∈ frequencies)
    (hsize : ∀ step ∈ steps, step.left.length + step.right.length + 4 ≤ C)
    (s : ℤ) (hs : s ∣ (historyFrequencyBase frequencies : ℤ)) (F : HistoryFormula σ)
    (hF : F ∈ reconstructionTests steps HistoryFormula.prime) :
    F.cleared.denominator * s ∣ (historyFrequencyPeriod frequencies (C ^ N + 1) : ℤ) := by
  have hd := constructed_history_test_period_of_dvd steps frequencies C hC hsteps hsize s hs F hF
  simp only [historyFrequencyPeriod, Nat.cast_pow] at hd ⊢
  exact hd.trans (pow_dvd_pow _ (Nat.add_le_add_right (pow_le_pow_right₀ hC hlen) 1))

end Ostmann

end OAI
