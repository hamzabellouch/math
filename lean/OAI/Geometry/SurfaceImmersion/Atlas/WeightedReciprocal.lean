import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

namespace OAI

/-! Polynomial weighted bounds for the reciprocal operations occurring in
metric inversion and normal reconstruction. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDerivWithin_inv (j : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) x‖ =
      (j.factorial : ℝ)*‖x⁻¹‖^(j+1) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have h := iteratedDerivWithin_one_div j isOpen_compl_singleton
    (show x ∈ ({0}ᶜ : Set ℝ) from hx)
  simp only [one_div] at h
  rw [h,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Real.norm_natCast,norm_zpow]
  have he : (-1-(j : ℤ)) = -((j+1 : ℕ) : ℤ) := by omega
  rw [he,zpow_neg,zpow_natCast,← inv_pow,← norm_inv]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both the input size and inverse denominator enter polynomially at each
fixed derivative order. There is no compact-range hypothesis. -/
theorem WeightedBound.inv_real {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} {f : E → ℝ}
    (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hf : ContDiffOn ℝ ∞ f U) (hne : ∀ x ∈ U, f x ≠ 0)
    (hInv : ∀ x ∈ U, ‖(f x)⁻¹‖ ≤ K) (hb : WeightedBound U s m C f) :
    WeightedBound U s m ((m.factorial : ℝ)^2*K^(m+1)*C^m) (fun x => (f x)⁻¹) := by
  have hV : UniqueDiffOn ℝ ({0}ᶜ : Set ℝ) := isOpen_compl_singleton.uniqueDiffOn
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) ({0}ᶜ) :=
    contDiffOn_id.inv (fun x hx => hx)
  have hD : 0 ≤ (m.factorial : ℝ)*K^(m+1) := by positivity
  have hd : ∀ j ≤ m, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) (f x)‖ ≤
        (m.factorial : ℝ)*K^(m+1) := by
    intro j hj x hx
    rw [norm_iteratedFDerivWithin_inv j (hne x hx)]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hj
    · exact (pow_le_pow_left₀ (norm_nonneg _) (hInv x hx) _).trans
        (pow_le_pow_right₀ hK (by omega))
    · positivity
    · positivity
  have hh := hb.comp hU hV hs hC hD hf hg (fun x hx => hne x hx) hd
  convert hh using 1 <;> first | rfl | ring

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
