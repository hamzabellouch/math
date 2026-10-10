import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.NumberTheory.Ostmann.Characters.CharacterWordSupport

namespace OAI

/-! # Rates for the actual tail count and top-word bin count -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_character_tail_count_rate (a β D : ℝ) (ha : 0 < a) (hβ : 0 ≤ β) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ) (T : ℝ) (E : Finset ℕ),
      L ≤ m → 0 < T → Real.log T ≤ β * L + D →
      a * Real.exp (T / 2) / T ^ 3 ≤ E.card →
      Real.sqrt (Real.exp T) * Real.exp (-(3 * β + 1) * m) ≤ E.card := by
  have he : ∀ᶠ L : ℝ in atTop, Real.exp (-L) ≤ a * Real.exp (-3 * D) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually_le_const (by positivity)
  filter_upwards [he] with L he m T E hLm hT hlog hE
  apply le_trans _ hE
  have hp : T ^ 3 ≤ Real.exp (3 * (β * L + D)) := by
    calc
      T ^ 3 = Real.exp (3 * Real.log T) := by
        rw [show (3 : ℝ) = (3 : ℕ) from rfl, Real.exp_nat_mul, Real.exp_log hT]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hcoef : 0 ≤ 3 * β + 1 := by linarith
  have hexp : Real.exp (-(3 * β + 1) * m) * T ^ 3 ≤ a := by
    calc
      _ ≤ Real.exp (-(3 * β + 1) * L) * Real.exp (3 * (β * L + D)) :=
        mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) hp (by positivity) (by positivity)
      _ = Real.exp (-L) * Real.exp (3 * D) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1; ring
      _ ≤ (a * Real.exp (-3 * D)) * Real.exp (3 * D) :=
        mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = a := by rw [mul_assoc, ← Real.exp_add]; simp
  have hs : Real.sqrt (Real.exp T) = Real.exp (T / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1; ring
  rw [hs]
  apply (le_div_iff₀ (pow_pos hT 3)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg (T / 2))]

theorem eventual_character_bin_count (β D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ τ : ℝ, 1 ≤ τ → Real.log τ ≤ β * L + D →
      (Fintype.card (Fin (⌊4 * τ⌋₊ + 1)) : ℝ) ≤ Real.exp ((β + 1) * L) := by
  filter_upwards [eventually_ge_atTop (D + Real.log 5)] with L hL τ hτ hlog
  have hc := wordLogBin_count τ hτ
  have hpos : (0 : ℝ) < Fintype.card (Fin (⌊4 * τ⌋₊ + 1)) := by simp only [Fintype.card_fin]; positivity
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr (by nlinarith only [hc, hlog, hL])

/-- The endpoint tests can be extended outside their selected finite set
without strengthening any premise about actual endpoints. -/
noncomputable def characterEndpointExtension (E : Finset ℕ) (x₀ : ℕ)
    (G : ℕ → ℕ → ℂ) (x p : ℕ) : ℂ := if x ∈ E then G x p else G x₀ p

@[simp] theorem characterEndpointExtension_of_mem (E : Finset ℕ) (x₀ : ℕ)
    (G : ℕ → ℕ → ℂ) {x : ℕ} (hx : x ∈ E) (p : ℕ) :
    characterEndpointExtension E x₀ G x p = G x p := ite_eq_left hx

theorem characterEndpointExtension_property (E : Finset ℕ) (x₀ : ℕ) (hx₀ : x₀ ∈ E)
    (G : ℕ → ℕ → ℂ) (A : (ℕ → ℂ) → Prop)
    (h : ∀ x ∈ E, A (G x)) :
    ∀ x, A (characterEndpointExtension E x₀ G x) := by
  intro x
  by_cases hx : x ∈ E
  · have he : characterEndpointExtension E x₀ G x = G x := by
      funext p
      exact ite_eq_left hx
    rw [he]
    exact h x hx
  · have he : characterEndpointExtension E x₀ G x = G x₀ := by
      funext p
      exact ite_eq_right hx
    rw [he]
    exact h x₀ hx₀

end Ostmann

end OAI
