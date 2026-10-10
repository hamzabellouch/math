import Mathlib.Data.List.OfFn
import OAI.NumberTheory.Ostmann.Construction.BackwardTargets

namespace OAI

/-! # Positive pivot targets at the required logarithmic scale -/

namespace Ostmann

def pivotCoefficients (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) : List ℝ :=
  List.ofFn (fun i => (2 : ℝ) ^ i.val * J + a i - Δ i)

def pivotTargets (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) : List ℝ :=
  backwardTargets (pivotCoefficients k J a Δ)

theorem pivotTargets_recurrence (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) (i : Fin k) :
    (pivotTargets k J a Δ)[i.val]'(by
      simpa only [pivotTargets, backwardTargets_length, pivotCoefficients,
        List.length_ofFn] using i.isLt) =
      (2 : ℝ) ^ i.val * J + a i - Δ i +
        ((pivotTargets k J a Δ).drop (i.val + 1)).sum := by
  have hi : i.val < (pivotCoefficients k J a Δ).length := by
    simpa only [pivotCoefficients, List.length_ofFn] using i.isLt
  simpa [pivotTargets, pivotCoefficients] using
    backwardTargets_get (pivotCoefficients k J a Δ) i.val hi

theorem pivotCoefficient_bounds (k : ℕ) (J τ : ℝ) (a Δ : Fin k → ℝ)
    (hτ : 0 < τ) (hJlo : τ / 2 ≤ J) (hJhi : J ≤ 4 * τ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 4 * τ)
    (hΔ : ∀ i, 0 ≤ Δ i ∧ Δ i ≤ (2 : ℝ) ^ i.val * τ / 4) (i : Fin k) :
    (2 : ℝ) ^ i.val * τ / 4 ≤ (2 : ℝ) ^ i.val * J + a i - Δ i ∧
      (2 : ℝ) ^ i.val * J + a i - Δ i ≤ 8 * (2 : ℝ) ^ k * τ := by
  have hpow : (0 : ℝ) < 2 ^ i.val := by positivity
  have hpow1 : (1 : ℝ) ≤ 2 ^ i.val := one_le_pow₀ (by norm_num)
  have hpowk : (2 : ℝ) ^ i.val ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) i.isLt.le
  have hjl := mul_le_mul_of_nonneg_left hJlo hpow.le
  have hjh := mul_le_mul_of_nonneg_left hJhi hpow.le
  have hτpow := mul_le_mul_of_nonneg_right hpow1 hτ.le
  have hτpowk := mul_le_mul_of_nonneg_right hpowk hτ.le
  constructor <;> nlinarith [ha i, hΔ i]

theorem pivotTargets_bounds (k : ℕ) (hk : 0 < k) (J τ : ℝ) (a Δ : Fin k → ℝ)
    (hτ : 0 < τ) (hJlo : τ / 2 ≤ J) (hJhi : J ≤ 4 * τ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 4 * τ)
    (hΔ : ∀ i, 0 ≤ Δ i ∧ Δ i ≤ (2 : ℝ) ^ i.val * τ / 4) :
    (pivotTargets k J a Δ).length = k ∧
      (pivotTargets k J a Δ).sum ≤ 8 * (4 : ℝ) ^ k * τ ∧
      ∀ T ∈ pivotTargets k J a Δ,
        (2 : ℝ) ^ (k - 1) * τ / 4 ≤ T ∧ T ≤ 8 * (4 : ℝ) ^ k * τ := by
  let cs := pivotCoefficients k J a Δ
  have hcslen : cs.length = k := by simp [cs, pivotCoefficients]
  have hcsne : cs ≠ [] := by intro h; have := congrArg List.length h; simp [hcslen] at this; omega
  have hcs : ∀ c ∈ cs, 0 ≤ c ∧ c ≤ 8 * (2 : ℝ) ^ k * τ := by
    dsimp [cs, pivotCoefficients]
    rw [List.forall_mem_ofFn_iff]
    intro i
    have h := pivotCoefficient_bounds k J τ a Δ hτ hJlo hJhi ha hΔ i
    exact ⟨(by positivity : 0 ≤ (2 : ℝ) ^ i.val * τ / 4).trans h.1, h.2⟩
  have he : (2 : ℝ) ^ k * 2 ^ k = (4 : ℝ) ^ k := by rw [← mul_pow]; norm_num
  have hmaxpos : 0 ≤ 8 * (2 : ℝ) ^ k * τ := by positivity
  have hsum : (backwardTargets cs).sum ≤ 8 * (4 : ℝ) ^ k * τ := by
    have h := backwardTargets_sum_upper cs (8 * (2 : ℝ) ^ k * τ) (fun c hc => (hcs c hc).2)
    rw [hcslen] at h
    have heq : (8 * (2 : ℝ) ^ k * τ) * (2 : ℝ) ^ k = 8 * (4 : ℝ) ^ k * τ := by
      calc
        _ = 8 * ((2 : ℝ) ^ k * 2 ^ k) * τ := by ring
        _ = _ := by rw [he]
    rw [← heq]
    nlinarith
  have hlast : (2 : ℝ) ^ (k - 1) * τ / 4 ≤ cs.getLast hcsne := by
    have heq := List.getLast_ofFn (f := fun i : Fin k => (2 : ℝ) ^ i.val * J + a i - Δ i)
      (show List.ofFn (fun i : Fin k => (2 : ℝ) ^ i.val * J + a i - Δ i) ≠ [] from hcsne)
    have hb := (pivotCoefficient_bounds k J τ a Δ hτ hJlo hJhi ha hΔ
      ⟨k - 1, by omega⟩).1
    exact hb.trans_eq heq.symm
  refine ⟨(backwardTargets_length cs).trans hcslen, hsum, ?_⟩
  intro T hT
  have hT' : T ∈ backwardTargets cs := hT
  refine ⟨hlast.trans (backwardTargets_lower_last cs hcsne (fun c hc => (hcs c hc).1) T hT'), ?_⟩
  exact (List.single_le_sum (backwardTargets_nonneg cs (fun c hc => (hcs c hc).1)) T hT').trans hsum

end Ostmann

end OAI
