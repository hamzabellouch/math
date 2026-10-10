import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitContour

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open Complex Set MeasureTheory
open scoped Interval SchwartzMap

theorem smooth_vertical_edge_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : 𝓢(ℝ, ℂ)) {X σ lo hi B C : ℝ}
    (hX : 0 < X) (hB : 0 ≤ B) (_hC : 0 ≤ C) (hlohi : lo ≤ hi)
    (hlog : ∀ t ∈ Icc lo hi, ‖logDeriv χ.LFunction ((σ:ℂ)+t*Complex.I)‖ ≤ B)
    (hker : ∀ t ∈ Icc lo hi, ‖mellin (ρ:ℝ→ℂ) ((σ:ℂ)+t*Complex.I)‖ ≤ C) :
    ‖Erdos970.VIntegral (characterSmoothIntegrand ρ χ X) σ lo hi‖ ≤
      B*C*X^σ*(hi-lo) := by
  rw [Erdos970.VIntegral, norm_smul, norm_I, one_mul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := lo) (b := hi) (C := B*C*X^σ)
    (f := fun t : ℝ => characterSmoothIntegrand ρ χ X ((σ:ℂ)+t*Complex.I)) (fun t ht => by
      have ht' : t ∈ Icc lo hi := uIcc_of_le hlohi ▸ uIoc_subset_uIcc ht
      rw [norm_characterSmoothIntegrand ρ χ hX]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hlog t ht') (hker t ht') (norm_nonneg _) hB)
        (Real.rpow_nonneg hX.le _))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hlohi)] using h

theorem smooth_horizontal_edge_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : 𝓢(ℝ, ℂ)) {X left right y B C : ℝ}
    (hX : 1 ≤ X) (hB : 0 ≤ B) (hC : 0 ≤ C) (hlr : left ≤ right)
    (hlog : ∀ x ∈ Icc left right, ‖logDeriv χ.LFunction ((x:ℂ)+y*Complex.I)‖ ≤ B)
    (hker : ∀ x ∈ Icc left right, ‖mellin (ρ:ℝ→ℂ) ((x:ℂ)+y*Complex.I)‖ ≤ C) :
    ‖Erdos970.HIntegral (characterSmoothIntegrand ρ χ X) left right y‖ ≤
      B*C*X^right*(right-left) := by
  unfold Erdos970.HIntegral
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := left) (b := right) (C := B*C*X^right)
    (f := fun x : ℝ => characterSmoothIntegrand ρ χ X ((x:ℂ)+y*Complex.I)) (fun x hx => by
      have hx' : x ∈ Icc left right := uIcc_of_le hlr ▸ uIoc_subset_uIcc hx
      rw [norm_characterSmoothIntegrand ρ χ hXp]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero]
      exact mul_le_mul
        (mul_le_mul (hlog x hx') (hker x hx') (norm_nonneg _) hB)
        (Real.rpow_le_rpow_of_exponent_le hX hx'.2) (Real.rpow_nonneg hXp.le _) (mul_nonneg hB hC))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hlr)] using h

end Ostmann.Dirichlet

end

end OAI
