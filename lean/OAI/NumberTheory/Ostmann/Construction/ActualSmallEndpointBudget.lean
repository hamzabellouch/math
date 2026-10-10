import OAI.NumberTheory.Ostmann.Construction.SmallEndpointBudget
import OAI.NumberTheory.Ostmann.Preliminaries.LargeSummandTails

namespace OAI

/-! # The small-endpoint error for the original summand prefixes -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

 theorem EventuallyPrimeSumset.small_endpoint_budget (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ M : ℝ, 0 ≤ M → M ≤ Real.exp (Real.exp L / 100) →
      Real.log X * M *
        (((summandPrefix A (summandTailCutoff (Real.exp L))).card : ℝ) *
            (summandPrefix B X).card +
          ((summandPrefix A X).card : ℝ) *
            (summandPrefix B (summandTailCutoff (Real.exp L))).card) ≤
        (X : ℝ) * Real.exp (-D * L) := by
  obtain ⟨a, C, _, hC, N₀, hcounts⟩ := hsize A B hA hB h
  let K := max N₀ 2
  filter_upwards [eventual_small_endpoint_error C D,
    Real.tendsto_exp_atTop.eventually_ge_atTop (2 * ((K : ℝ) + 2)),
    eventually_ge_atTop (1 : ℝ)] with L herror hbig hL
  intro X hX M hM hMupper
  let T := Real.exp L
  let lo := summandTailCutoff T
  have hT : 1 ≤ T := Real.one_le_exp (by linarith)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hKexp : (K : ℝ) ≤ Real.exp (9 * T / 10) := by
    have he := Real.add_one_le_exp (9 * T / 10)
    change 2 * ((K : ℝ) + 2) ≤ T at hbig
    linarith
  have hKlo : K ≤ lo := Nat.le_floor hKexp
  have hloUpper : (lo : ℝ) ≤ Real.exp (9 * T / 10) := Nat.floor_le (Real.exp_nonneg _)
  have hloX : lo ≤ X := by
    have he : Real.exp (9 * T / 10) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
    have hh := hloUpper.trans he
    change (X : ℝ) = Real.exp T at hX
    rw [← hX] at hh
    exact_mod_cast hh
  have hNlo : N₀ ≤ lo := (le_max_left _ _).trans hKlo
  have h2lo : 2 ≤ lo := (le_max_right _ _).trans hKlo
  have hcntlo := hcounts lo hNlo h2lo
  have hcntX := hcounts X (hNlo.trans hloX) (h2lo.trans hloX)
  have hsqrtX : Real.sqrt (X : ℝ) = Real.exp (T / 2) := by
    rw [hX]
    change Real.sqrt (Real.exp T) = _
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have hlogX : Real.log X = T := by rw [hX, Real.log_exp]
  have hfullA : ((summandPrefix A X).card : ℝ) ≤ C * Real.exp (T / 2) * T ^ 2 := by
    simpa only [hsqrtX, hlogX] using hcntX.2.1
  have hfullB : ((summandPrefix B X).card : ℝ) ≤ C * Real.exp (T / 2) * T ^ 2 := by
    simpa only [hsqrtX, hlogX] using hcntX.2.2.2
  have hsmallA := hcntlo.2.1.trans (sqrt_log_prefix_bound C T hC.le hT lo (by omega) hloUpper)
  have hsmallB := hcntlo.2.2.2.trans (sqrt_log_prefix_bound C T hC.le hT lo (by omega) hloUpper)
  have hcard := endpoint_count_product_bound C T
    (summandPrefix A lo).card (summandPrefix B lo).card
    (summandPrefix A X).card (summandPrefix B X).card hC.le
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hsmallA hsmallB hfullA hfullB
  change M ≤ Real.exp (T / 100) at hMupper
  rw [hlogX]
  calc
    _ ≤ T * Real.exp (T / 100) * (2 * C ^ 2 * Real.exp (19 * T / 20) * T ^ 4) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hMupper (by positivity)
      · exact hcard
      · positivity
      · positivity
    _ = 2 * C ^ 2 * Real.exp ((24 / 25 : ℝ) * T) * Real.exp (5 * L) := by
      have hpow : T ^ 5 = Real.exp (5 * L) := by
        dsimp [T]
        rw [← Real.exp_nat_mul]
        norm_num
      have he : Real.exp (T / 100) * Real.exp (19 * T / 20) =
          Real.exp ((24 / 25 : ℝ) * T) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = 2 * C ^ 2 * (Real.exp (T / 100) * Real.exp (19 * T / 20)) * T ^ 5 := by ring
        _ = _ := by rw [he, hpow]
    _ ≤ _ := by simpa only [hX] using herror

end Ostmann

end OAI
