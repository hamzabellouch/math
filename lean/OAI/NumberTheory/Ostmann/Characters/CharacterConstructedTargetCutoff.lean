import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.NumberTheory.Ostmann.Characters.CharacterConstructedTargets

namespace OAI

/-! # Constructed pivot targets lie below the comparison prime cutoff -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

theorem eventual_exp_linear_allowance (β γ D A c : ℝ) (hgap : β < γ)
    (hβ : 0 ≤ β) (hA : 0 ≤ A) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ τ y : ℝ, 0 < τ →
      Real.log τ ≤ β * L + D → y ≤ A * τ → y + c ≤ Real.exp (γ * L) := by
  have hlim : Tendsto (fun L : ℝ => Real.exp (-(γ - β) * L)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (sub_pos.mpr hgap))
  have hsmall := hlim.eventually_le_const (by positivity : 0 < (A * Real.exp D + c + 1)⁻¹)
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with L hsmall hL τ y hτ hlog hy
  have ht : τ ≤ Real.exp (β * L + D) := by
    simpa only [Real.exp_log hτ] using Real.exp_le_exp.mpr hlog
  have hcoef : (A * Real.exp D + c) * Real.exp (-(γ - β) * L) ≤ 1 := by
    have hp : 0 < A * Real.exp D + c + 1 := by positivity
    have hh := mul_le_mul_of_nonneg_left hsmall (le_of_lt hp)
    rw [mul_inv_cancel₀ (ne_of_gt hp)] at hh
    have he := Real.exp_nonneg (-(γ - β) * L)
    nlinarith only [hh, he]
  have he : 1 ≤ Real.exp (β * L) := Real.one_le_exp_iff.mpr (mul_nonneg hβ hL)
  have hrat : Real.exp (-(γ - β) * L) * Real.exp (γ * L) = Real.exp (β * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    y + c ≤ A * Real.exp (β * L + D) + c * Real.exp (β * L) := by
      exact add_le_add (hy.trans (mul_le_mul_of_nonneg_left ht hA))
        (by nlinarith only [he, hc])
    _ = (A * Real.exp D + c) * Real.exp (β * L) := by rw [Real.exp_add]; ring
    _ = (A * Real.exp D + c) *
        (Real.exp (-(γ - β) * L) * Real.exp (γ * L)) := by rw [hrat]
    _ ≤ Real.exp (γ * L) := by
      nlinarith only [mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg (γ * L))]

/-- The cutoff is uniform over the selected anchors, bin and original floor length. -/
theorem eventual_constructed_character_target_cutoff (k : ℕ) (hk : 0 < k)
    (B z α β βg c : ℝ) (hB : 0 ≤ B) (hz : 1 ≤ z) (hα : 0 < α)
    (hβ : 0 ≤ β) (hβg : β < βg) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ (U τ J : ℝ) (m : ℕ) (a : Fin k → Bool → ℕ),
      α * L ≤ U → U ≤ β * L → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 → 0 < τ →
      (m : ℝ) ≤ z * L → τ / 2 ≤ J → J ≤ 4 * τ →
      (∀ j, (a j false : ℝ) + a j true ≤ 4 * τ) →
      ∀ j, characterPivotTarget k J (fun j => (a j false : ℝ) + a j true)
        (fun j => characterPivotGap B z m j.val) j + c ≤ Real.exp (βg * L) := by
  filter_upwards [eventual_character_target_gaps k B z α hB hz hα,
    eventual_exp_linear_allowance β βg (2 * (k : ℝ) / 10000)
      (600 * (4 : ℝ) ^ k) c hβg hβ (by positivity) hc] with L hgap hcut
  intro U τ J m a hUL hUβ hUτ hτU hτ hm hJlo hJhi ha j
  have hτlo : Real.exp (α * L) ≤ τ := by
    exact (Real.exp_le_exp.mpr (hUL.trans hUτ)).trans_eq (Real.exp_log hτ)
  have hg := hgap m τ (Nat.cast_nonneg _) hm hτlo
  have hr := character_constructed_target_ranges k hk J τ (characterBaseGap B z m)
    (fun j b => (a j b : ℝ)) (fun j => characterPivotGap B z m j.val)
    hτ hJlo hJhi (fun j => ⟨by positivity, ha j⟩)
    (fun j => hg.2.2 j.val j.isLt) ⟨hg.1, hg.2.1⟩ (some j)
  exact hcut τ _ hτ (by linarith only [hUβ, hτU]) hr.2

end Ostmann

end OAI
