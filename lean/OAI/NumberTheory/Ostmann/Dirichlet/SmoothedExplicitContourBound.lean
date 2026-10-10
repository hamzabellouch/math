import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitEdgeBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open Complex Set MeasureTheory
open scoped Topology BigOperators SchwartzMap

theorem norm_contourFactor_le_one : ‖(1 : ℂ)/(2*(Real.pi:ℂ)*Complex.I)‖ ≤ 1 := by
  simp only [norm_div, norm_one, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, norm_I, mul_one]
  apply (div_le_one (by positivity)).mpr
  linarith [Real.pi_gt_three]

theorem norm_character_smooth_le_zeroSum_edges {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : 𝓢(ℝ, ℂ))
    {X left right lo hi : ℝ} (hX : 0 < X) (hleft : 0 < left)
    (hright : 1 < right) (hlr : left ≤ right) (hlohi : lo ≤ hi)
    (hboundary : ∀ p ∈ Erdos970.RectangleBorder ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I),
      χ.LFunction p ≠ 0) :
    ‖∑' n : ℕ, χ n*(ArithmeticFunction.vonMangoldt n:ℂ)*ρ ((n:ℝ)/X)‖ ≤
      (∑ p ∈ zerosInRectangle χ hχ ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I),
        (zeroMultiplicity χ p:ℝ)*X^p.re*‖mellin (ρ:ℝ→ℂ) p‖) +
      ‖Erdos970.VIntegral (characterSmoothIntegrand ρ χ X) left lo hi‖ +
      ‖Erdos970.HIntegral (characterSmoothIntegrand ρ χ X) left right lo‖ +
      ‖Erdos970.HIntegral (characterSmoothIntegrand ρ χ X) left right hi‖ +
      ‖∫ t in Iic lo, characterSmoothIntegrand ρ χ X ((right:ℂ)+t*Complex.I)‖ +
      ‖∫ t in Ici hi, characterSmoothIntegrand ρ χ X ((right:ℂ)+t*Complex.I)‖ := by
  let F := characterSmoothIntegrand ρ χ X
  have hsum : ‖∑ p ∈ zerosInRectangle χ hχ ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I),
      (zeroMultiplicity χ p:ℂ)*smoothExplicitKernel ρ X p‖ ≤
      ∑ p ∈ zerosInRectangle χ hχ ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I),
        (zeroMultiplicity χ p:ℝ)*X^p.re*‖mellin (ρ:ℝ→ℂ) p‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    simp only [smoothExplicitKernel, norm_mul, Complex.norm_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hX]
    exact (by ring : _ = _).le
  rw [character_smooth_five_edges χ hχ ρ hX hleft hright hlr hlohi hboundary]
  have hedge := norm_add_le
    (Erdos970.VIntegral F left lo hi - Erdos970.HIntegral F left right lo +
      Erdos970.HIntegral F left right hi + Complex.I*(∫ t in Iic lo, F ((right:ℂ)+t*Complex.I)))
    (Complex.I*(∫ t in Ici hi, F ((right:ℂ)+t*Complex.I)))
  have hedge2 := norm_add_le
    (Erdos970.VIntegral F left lo hi - Erdos970.HIntegral F left right lo +
      Erdos970.HIntegral F left right hi) (Complex.I*(∫ t in Iic lo, F ((right:ℂ)+t*Complex.I)))
  have hedge3 := norm_add_le
    (Erdos970.VIntegral F left lo hi - Erdos970.HIntegral F left right lo)
    (Erdos970.HIntegral F left right hi)
  have hedge4 := norm_sub_le (Erdos970.VIntegral F left lo hi) (Erdos970.HIntegral F left right lo)
  simp only [norm_mul, norm_I, one_mul] at hedge hedge2
  calc
    _ ≤ ‖-(∑ p ∈ zerosInRectangle χ hχ ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I),
        (zeroMultiplicity χ p:ℂ)*smoothExplicitKernel ρ X p)‖ +
      ‖(1/(2*(Real.pi:ℂ)*Complex.I)) *
        (Erdos970.VIntegral F left lo hi - Erdos970.HIntegral F left right lo +
          Erdos970.HIntegral F left right hi + Complex.I*(∫ t in Iic lo, F ((right:ℂ)+t*Complex.I)) +
          Complex.I*(∫ t in Ici hi, F ((right:ℂ)+t*Complex.I)))‖ := norm_add_le _ _
    _ ≤ (∑ p ∈ zerosInRectangle χ hχ ((left:ℂ)+lo*Complex.I) ((right:ℂ)+hi*Complex.I),
        (zeroMultiplicity χ p:ℝ)*X^p.re*‖mellin (ρ:ℝ→ℂ) p‖) +
      ‖Erdos970.VIntegral F left lo hi - Erdos970.HIntegral F left right lo +
          Erdos970.HIntegral F left right hi + Complex.I*(∫ t in Iic lo, F ((right:ℂ)+t*Complex.I)) +
          Complex.I*(∫ t in Ici hi, F ((right:ℂ)+t*Complex.I))‖ := by
        rw [norm_neg, norm_mul]
        exact add_le_add hsum (mul_le_of_le_one_left (norm_nonneg _) norm_contourFactor_le_one)
    _ ≤ _ := by linarith

end Ostmann.Dirichlet

end

end OAI
