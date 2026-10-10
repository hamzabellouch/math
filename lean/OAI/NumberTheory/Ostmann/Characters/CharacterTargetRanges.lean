import OAI.NumberTheory.Ostmann.Characters.CharacterInitialProduct
import OAI.NumberTheory.Ostmann.Construction.FillerTargetScale

namespace OAI

/-! # The exact pivot and filler targets lie in the tested late-shell range -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterPivotTarget_sum (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) :
    (∑ j, characterPivotTarget k J a Δ j) = (pivotTargets k J a Δ).sum := by
  let v := pivotTargets k J a Δ
  have hlen : v.length = k := by simp [v, pivotTargets, backwardTargets_length, pivotCoefficients]
  have hlist : List.ofFn (fun j : Fin k => characterPivotTarget k J a Δ j) = v := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  rw [← List.sum_ofFn, hlist]

theorem character_constructed_target_ranges (k : ℕ) (hk : 0 < k) (J τ Δ₀ : ℝ)
    (a : Fin k → Bool → ℝ) (Δ : Fin k → ℝ)
    (hτ : 0 < τ) (hJlo : τ / 2 ≤ J) (hJhi : J ≤ 4 * τ)
    (ha : ∀ j, 0 ≤ a j false + a j true ∧ a j false + a j true ≤ 4 * τ)
    (hΔ : ∀ j, 0 ≤ Δ j ∧ Δ j ≤ (2 : ℝ) ^ j.val * τ / 4)
    (hΔ₀ : 0 ≤ Δ₀ ∧ Δ₀ ≤ τ / 4) :
    let TP := characterPivotTarget k J (fun j => a j false + a j true) Δ
    let TF := characterFillerTarget (1000 * (4 : ℝ) ^ k * τ) Δ₀ J TP a
    ∀ j : Option (Fin k), (2 : ℝ) ^ (k - 1) * τ / 4 ≤ j.elim TF TP ∧
      j.elim TF TP ≤ 600 * (4 : ℝ) ^ k * τ := by
  intro TP TF j
  have ht := pivotTargets_bounds k hk J τ (fun j => a j false + a j true) Δ
    hτ hJlo hJhi ha hΔ
  cases j with
  | some j =>
    have hm : TP j ∈ pivotTargets k J (fun j => a j false + a j true) Δ := List.getElem_mem _
    have hb := ht.2.2 _ hm
    exact ⟨hb.1, hb.2.trans (by
      nlinarith only [show 0 ≤ (4 : ℝ) ^ k * τ by positivity])⟩
  | none =>
    have hf := constructed_fillerTarget_bounds k hk J τ Δ₀ (fun j => a j false + a j true) Δ
      hτ hJlo hJhi ha hΔ hΔ₀
    have he : TF = fillerTarget k τ Δ₀ J (∑ j, (a j false + a j true))
        (pivotTargets k J (fun j => a j false + a j true) Δ).sum := by
      change characterFillerTarget _ _ _ _ _ = _
      unfold characterFillerTarget fillerTarget
      rw [characterPivotTarget_sum]
      ring
    rw [← he] at hf
    change (2 : ℝ) ^ k * τ ≤ TF ∧ TF ≤ 501 * (4 : ℝ) ^ k * τ at hf
    change (2 : ℝ) ^ (k - 1) * τ / 4 ≤ TF ∧ TF ≤ 600 * (4 : ℝ) ^ k * τ
    have hp : (2 : ℝ) ^ (k - 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    constructor
    · have hh := mul_le_mul_of_nonneg_right hp hτ.le
      have hn : 0 ≤ (2 : ℝ) ^ k * τ := by positivity
      nlinarith only [hh, hn, hf.1]
    · exact hf.2.trans (by
        nlinarith only [show 0 ≤ (4 : ℝ) ^ k * τ by positivity])

end Ostmann

end OAI
