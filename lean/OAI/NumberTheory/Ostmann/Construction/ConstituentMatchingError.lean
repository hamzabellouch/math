import OAI.NumberTheory.Ostmann.Construction.ScheduledMatchingError
import OAI.NumberTheory.Ostmann.Construction.RoundedEnergyCutoffs

namespace OAI

/-! # The matched error with its actual constituent counts and frequency cutoff -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem transferFrequencyRange_card_exp_bound (V : ℕ) (C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hV : (V : ℝ) ≤ Real.exp (C * (1 + M))) :
    ((transferFrequencyRange V).card : ℝ) ≤ Real.exp ((C + Real.log 3) * (1 + M)) := by
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have he : 1 ≤ Real.exp (C * (1 + M)) := Real.one_le_exp (by positivity)
  calc
    _ = 2 * (V : ℝ) + 1 := by rw [card_transferFrequencyRange]; push_cast; rfl
    _ ≤ 3 * Real.exp (C * (1 + M)) := by linarith
    _ = Real.exp (Real.log 3 + C * (1 + M)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem eventual_constituent_matching_error {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (s C H T z α c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (size : I → ℕ) (Smax : ℕ) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hM : 0 ≤ M) (_hML : M ≤ z * L) (_hSM : (Smax : ℝ) ≤ s * (1 + M))
      (V : ℕ → ℕ) (_hV : Monotone V) (_hVn : (V n : ℝ) ≤ Real.exp (C * (1 + M)))
      (Sbad : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
      (Q : (Σ a, Fin (size a)) → Finset ℕ)
      (_hQinv : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M))),
      (Sbad.card : ℝ) * (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 *
        (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) *
        Real.exp (-c * Real.exp (α * L)) ≤ Real.exp (-T * M) := by
  let a : ℝ := (3 ^ n * Fintype.card I : ℕ) * s
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hCr : 0 ≤ C + Real.log 3 := add_nonneg hC (Real.log_nonneg (by norm_num))
  filter_upwards [eventual_scheduled_matching_error n a (C + Real.log 3) H T z α c
    ha hCr hH hT hz hα hc] with L hL
  intro size Smax hsize M hM hML hSM V hV hVn Sbad Q hQinv
  let J := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n
  have hcard : (Fintype.card J : ℝ) ≤ a * (1 + M) := by
    have hh := constituent_retained_card_le role size n Smax hsize
    rw [Fintype.card_sum] at hh
    have hh' : Fintype.card J ≤ 3 ^ n * Fintype.card I * Smax := by dsimp [J]; omega
    calc
      _ ≤ ((3 ^ n * Fintype.card I : ℕ) : ℝ) * (Smax : ℝ) := by exact_mod_cast hh'
      _ ≤ ((3 ^ n * Fintype.card I : ℕ) : ℝ) * (s * (1 + M)) :=
        mul_le_mul_of_nonneg_left hSM (by positivity)
      _ = _ := by dsimp [a]; ring
  exact hL J M V Sbad
    (fun h => (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹)
    hM hML hcard hV (transferFrequencyRange_card_exp_bound _ C M hC hM hVn)
    (fun _ => by positivity) (fun _ => hQinv _)

end Ostmann

end OAI
