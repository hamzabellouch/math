import OAI.NumberTheory.CubicMoment.Estimates.TypeIHeightRanges
import OAI.NumberTheory.CubicMoment.Estimates.HeightIntegralMajorant
import OAI.NumberTheory.CubicMoment.Estimates.HeightEndpointRegularity

namespace OAI

/-! The literal Type-I height integral is bounded by the published-input
mean estimates, with the outer norm phase and interval endpoint retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def typeIHeightIntegral {γ : Type*} (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ) (ℓ : ℤ) (U H T X₀ : ℝ) : ℂ :=
  (T:ℂ)⁻¹*∫ t : ℝ,
    (localizedEndpointWeight H T t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
      ∑ r ∈ S, (α r*normTwist t r)*metaplecticAngularSmoothSum r ℓ (W (w r)) U t

lemma typeIHeightIntegral_le_mean {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (ℓ : ℤ) {U T : ℝ} (hU : 0 < U) (hT : 0 < T)
    (H X₀ : ℝ) :
    ‖typeIHeightIntegral w S α W ℓ U H T X₀‖ ≤
      dyadicHeightMean (fun t => ∑ r ∈ S,
        ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖) T := by
  apply normalized_dyadic_integral_majorant
  · apply continuous_finsetSum
    intro r _
    exact continuous_const.mul
      (continuous_metaplecticAngularSmoothSum_of_cutoff r ℓ (W (w r)) hU
        (le_refl (Real.exp hW.radius*U)) (hW.upper_support (w r))).norm
  · exact hT
  · intro t
    rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
    exact localizedEndpointWeight_norm_le H hT t
  · intro t ht
    rw [localizedEndpointWeight_zero H hT t ht,zero_mul]
  · intro t
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro r _
    simp only [norm_mul,norm_normTwist,mul_one,le_refl]

lemma metaplecticAngularSmoothSum_zero_mode (r : Eisenstein) (W : ℝ → ℂ) (U t : ℝ) :
    metaplecticAngularSmoothSum r 0 W U t = metaplecticSmoothSum r W U t := by
  unfold metaplecticAngularSmoothSum metaplecticSmoothSum
  apply tsum_congr
  intro u
  rw [theta_zero,mul_one,mellinPhase_eq_cpow
    (norm_pos_of_ne_zero (primary_ne_zero u.property))]

theorem radial_typeI_height_integral
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hGrowth : MetaplecticPolynomialGrowth F) (hHB : MetaplecticMeanSquare F)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    (B M : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ)
        (R U T H X₀ : ℝ), 1 ≤ R → 1 ≤ U → 1 ≤ Real.log (R*U) →
        Real.log (R*U) ≤ T →
        ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
          (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
        (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^B →
        ‖typeIHeightIntegral w S α W 0 U H T X₀‖ ≤
          C*(R*U)^(5/6-min (1/100) (3*κ/16))+
            E*(R*U)^(5/6:ℝ)/(Real.log (R*U))^M := by
  obtain ⟨C,E,hC,hE,hbound⟩ := typeI_selected_height_ranges hW hF hGrowth
    hHB hκ hρ B M hA
  refine ⟨C,E,hC,hE,?_⟩
  intro w S α R U T H X₀ hR hU hlog hLT hrange hS hmass
  apply (typeIHeightIntegral_le_mean hW w S α 0 (zero_lt_one.trans_le hU)
    (zero_lt_one.trans_le (hlog.trans hLT)) H X₀).trans
  simpa only [metaplecticAngularSmoothSum_zero_mode,dyadicHeightMean,neg_mul] using
    hbound w S α R U T hR hU hlog hLT hrange hS hmass

theorem angular_typeI_height_integral
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    (B : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ (mpos mneg : ℕ) (C : ℝ), 2 ≤ mpos ∧ 2 ≤ mneg ∧ 0 ≤ C ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ)
        (R U T H X₀ : ℝ), 1 ≤ R → 1 ≤ U → max 2 (Real.exp hW.radius) ≤ R*U →
        1 ≤ T → T ≤ (R*U)^2 →
        ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
          (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
        (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^B →
        AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mpos:ℝ)-1/2)) →
        AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mpos:ℝ)-1/2)) →
        AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mneg:ℝ)-1/2)) →
        AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mneg:ℝ)-1/2)) →
        ‖typeIHeightIntegral w S α W ℓ U H T X₀‖ ≤
          C*(R*U)^(5/6-min (1/100) (3*κ/16)) := by
  obtain ⟨mp,mn,C,hmp,hmn,hC,hbound⟩ := angular_typeI_selected_height_ranges
    hV hMV hMV0 hW ℓ hℓ hκ hρ B hA
  refine ⟨mp,mn,C,hmp,hmn,hC,?_⟩
  intro w S α R U T H X₀ hR hU hsize hT hTX hrange hS hmass hgmp hgpp hgmn hgpn
  apply (typeIHeightIntegral_le_mean hW w S α ℓ (zero_lt_one.trans_le hU)
    (zero_lt_one.trans_le hT) H X₀).trans
  simpa only [dyadicHeightMean,neg_mul] using
    hbound w S α R U T hR hU hsize hT hTX hrange hS hmass hgmp hgpp hgmn hgpn

end CubicFirstMoment

end

end OAI
