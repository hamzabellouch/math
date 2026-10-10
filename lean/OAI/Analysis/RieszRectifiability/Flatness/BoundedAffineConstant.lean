import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzKernel

namespace OAI

/-!
# Bounded affine functions are constant

A nonzero linear part grows along a suitable ray, contradicting any global
bound on its affine translate. Density of volume-almost-everywhere sets extends
an almost-everywhere affine bound to every point, so a bounded function that is
almost everywhere affine is almost everywhere constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter

theorem bounded_affine_linear_part_zero {d : ℕ} (c : ℝ)
    (L : Ambient d →L[ℝ] ℝ) (M : ℝ) (hb : ∀ x, |c + L x| ≤ M) : L = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change L x = 0
  by_contra hx
  let t : ℝ := (M + |c| + 1) / L x
  have hvalue : L (t • x) = M + |c| + 1 := by
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ _ hx
  have hle := (le_abs_self (c + L (t • x))).trans (hb (t • x))
  rw [hvalue] at hle
  linarith [neg_abs_le c]

theorem ae_bounded_affine_is_constant {d : ℕ} (f : Ambient d → ℝ)
    (M : ℝ) (hb : ∀ x, |f x| ≤ M) (c : ℝ) (L : Ambient d →L[ℝ] ℝ)
    (heq : ∀ᵐ x ∂volume, f x = c + L x) :
    L = 0 ∧ ∀ᵐ x ∂volume, f x = c := by
  have haeb : ∀ᵐ x ∂volume, |c + L x| ≤ M := by
    filter_upwards [heq] with x hx
    rw [← hx]
    exact hb x
  have hclosed : IsClosed {x : Ambient d | |c + L x| ≤ M} :=
    isClosed_le (continuous_const.add L.continuous).abs continuous_const
  have hs := (Measure.dense_of_ae haeb).closure_eq
  rw [hclosed.closure_eq] at hs
  have hbound (x : Ambient d) : |c + L x| ≤ M := by
    have hx : x ∈ {x : Ambient d | |c + L x| ≤ M} := by
      rw [hs]
      exact mem_univ x
    exact hx
  have hzero := bounded_affine_linear_part_zero c L M hbound
  refine ⟨hzero, ?_⟩
  simpa only [hzero, zero_apply, add_zero] using! heq

end

end RieszRectifiability

end OAI
