import OAI.NumberTheory.CubicMoment.Estimates.HeightConvolution
import OAI.NumberTheory.CubicMoment.Estimates.MellinSignedIntegration

namespace OAI

/-! The two Poisson row signs under an independent arithmetic height
average, with the exact Fourier-to-arithmetic Jacobian. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_continuous_normMellin_signed_height_integral (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (R : ℝ) (H : Finset Eisenstein) (e : Eisenstein) (u ρ : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    Continuous (fun t => ∫ s : ℝ,
      ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
      ((fullStructuredHeightMass R H 1 e ℓ (u+t) W X (2*Real.pi*s)+
        fullStructuredHeightMass R H 1 e ℓ (u+t) W X (-(2*Real.pi*s)))/2)) := by
  let G := fullStructuredHeightMass R H 1 e ℓ 0 W X
  let A := arithmeticMellinCoefficient M hM V hV hV' ρ
  obtain ⟨B,_hB,hB⟩ := fullStructuredHeightMass_bounded R H 1 e ℓ 0 W X
  have hb (t : ℝ) : ‖G t‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (fullStructuredHeightMass_nonneg R H 1 e ℓ 0 W X t)]
    exact hB t
  have hgc : Continuous G := continuous_fullStructuredHeightMass R H 1 e ℓ 0 W X
  have hac : Continuous A := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hai : Integrable A := arithmeticMellinCoefficient_integrable M hM V hV hV' ρ
  have hp := continuous_height_convolution hac.norm hai.norm hgc hb u
  have hn := continuous_height_convolution (hac.comp continuous_neg).norm hai.norm.comp_neg hgc hb u
  have hc := (hp.add hn).const_mul ((4*Real.pi)⁻¹)
  apply hc.congr
  intro t
  rw [normMellin_signed_height_integral M hM V hV hV' R H 1 e ℓ (u+t) W X ρ]
  have ht (s : ℝ) : fullStructuredHeightMass R H 1 e ℓ (u+t) W X s = G (t+u+s) := by
    simp only [G,fullStructuredHeightMass,add_zero,add_comm,add_left_comm]
  simp only [ht,A,Pi.add_apply,Function.comp_apply,add_comm t u]
  ring

lemma angular_normMellin_signed_height_average (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (R : ℝ) (H : Finset Eisenstein) (e : Eisenstein) (u ρ : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    dyadicHeightMean (fun t => ∫ s : ℝ,
      ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
      ((fullStructuredHeightMass R H 1 e ℓ (u+t) W X (2*Real.pi*s)+
        fullStructuredHeightMass R H 1 e ℓ (u+t) W X (-(2*Real.pi*s)))/2)) T =
    (dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖arithmeticMellinCoefficient M hM V hV hV' ρ s‖*
          fullStructuredHeightMass R H 1 e ℓ 0 W X (t+u+s)) T+
      dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖arithmeticMellinCoefficient M hM V hV hV' ρ (-s)‖*
          fullStructuredHeightMass R H 1 e ℓ 0 W X (t+u+s)) T)/(4*Real.pi) := by
  let G := fullStructuredHeightMass R H 1 e ℓ 0 W X
  let A := arithmeticMellinCoefficient M hM V hV hV' ρ
  let P := fun t => ∫ s : ℝ, ‖A s‖*G (t+u+s)
  let N := fun t => ∫ s : ℝ, ‖A (-s)‖*G (t+u+s)
  have htranslate (t s : ℝ) : fullStructuredHeightMass R H 1 e ℓ (u+t) W X s =
      G (t+u+s) := by
    simp only [G,fullStructuredHeightMass,add_zero,add_comm,add_left_comm]
  have he (t : ℝ) : (∫ s : ℝ,
      ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
      ((fullStructuredHeightMass R H 1 e ℓ (u+t) W X (2*Real.pi*s)+
        fullStructuredHeightMass R H 1 e ℓ (u+t) W X (-(2*Real.pi*s)))/2)) =
        (4*Real.pi)⁻¹*(P t+N t) := by
    rw [normMellin_signed_height_integral M hM V hV hV' R H 1 e ℓ (u+t) W X ρ]
    simp only [htranslate,P,N,A]
    ring
  obtain ⟨B,_hB,hB⟩ := fullStructuredHeightMass_bounded R H 1 e ℓ 0 W X
  have hb (t : ℝ) : ‖G t‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (fullStructuredHeightMass_nonneg R H 1 e ℓ 0 W X t)]
    exact hB t
  have hgc : Continuous G := continuous_fullStructuredHeightMass R H 1 e ℓ 0 W X
  have hac : Continuous A := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hai : Integrable A := arithmeticMellinCoefficient_integrable M hM V hV hV' ρ
  have hp {a b : ℝ} (hab : a ≤ b) : IntervalIntegrable P volume a b :=
    intervalIntegrable_height_convolution hac.norm hai.norm hgc hb u hab
  have hn {a b : ℝ} (hab : a ≤ b) : IntervalIntegrable N volume a b :=
    intervalIntegrable_height_convolution (hac.comp continuous_neg).norm hai.norm.comp_neg hgc hb u hab
  simp_rw [he]
  rw [dyadicHeightMean_const_mul,dyadicHeightMean_add_of_integrable T
    (hp (by linarith)) (hp (by linarith)) (hn (by linarith)) (hn (by linarith))]
  change (4*Real.pi)⁻¹*(dyadicHeightMean P T+dyadicHeightMean N T) = _
  ring

end CubicFirstMoment

end

end OAI
