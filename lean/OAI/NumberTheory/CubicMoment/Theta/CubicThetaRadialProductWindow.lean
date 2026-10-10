import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialTypeIIntegral
import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductWindow

namespace OAI

/-! Apply the constructed radial mean to the literal product window.
The bounded dilation of its inner smooth weight is retained exactly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicTheta_radial_productTypeICutoffWindow_bound
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    (B M : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (P : Finset Eisenstein) (α : Eisenstein → ℂ)
        (X R U T H X₀ : ℝ),
        1 ≤ R → 1 ≤ U → R*U = X → 1 ≤ Real.log X → Real.log X ≤ T →
        0 < X₀ →
        ((R ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
          (R ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+ρ))) →
        (∀ r ∈ P, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ P, ‖α r‖) ≤ A*R*(Real.log X)^B →
        ‖productTypeICutoffWindow w P α W 0 (Real.exp hW.radius) X U H T X₀‖ ≤
          C*X^(5/6-min (1/100) (3*κ/16))+E*X^(5/6:ℝ)/(Real.log X)^M := by
  have hV := hW.logDilate (Real.log 2) (Real.log_nonneg (by norm_num))
  obtain ⟨C,E,hC,hE,hbound⟩ := cubicTheta_radial_typeI_height_integral hMV hMean0 hV hκ hρ B M hA
  refine ⟨2*C,2*E,by positivity,by positivity,?_⟩
  intro w P α X R U T H X₀ hR hU hRU hlog hLT hX₀ hrange hP hmass
  obtain ⟨v,hv⟩ := productTypeICutoffWindow_dilate hW w P α 0 hR
    (zero_lt_one.trans_le hU) hRU hP
  rw [hv, typeICutoffWindow_endpoints hV v P α 0 (zero_lt_one.trans_le hU)
    (zero_lt_one.trans_le (hlog.trans hLT)) hX₀ H]
  have h₁ := hbound v P α R U T H X₀ hR hU (by simpa only [hRU] using hlog)
    (by simpa only [hRU] using hLT) (by simpa only [hRU] using hrange) hP
    (by simpa only [hRU] using hmass)
  have h₂ := hbound v P α R U T H (2*X₀) hR hU (by simpa only [hRU] using hlog)
    (by simpa only [hRU] using hLT) (by simpa only [hRU] using hrange) hP
    (by simpa only [hRU] using hmass)
  rw [hRU] at h₁ h₂
  apply (norm_sub_le _ _).trans
  exact (add_le_add h₁ h₂).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
