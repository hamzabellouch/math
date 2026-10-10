import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierProfileGram
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialMeanIntegral

namespace OAI

/-! Exact mass of a compact cusp Fourier source and its height scaling. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaHorizontalFourier_character_self (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter h)=
      ((volume : Measure ℂ).real cubicThetaHorizontalCell:ℂ) := by
  unfold cubicThetaHorizontalFourierCoefficient
  simp_rw [cubicThetaHorizontalCharacter_unit]
  rw [setIntegral_const,Complex.real_smul,mul_one]

theorem cubicThetaFourierProfile_inner_self (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) :
    inner ℂ (cubicThetaFourierProfileL2 h W hW) (cubicThetaFourierProfileL2 h W hW)=
      ((volume : Measure ℂ).real cubicThetaHorizontalCell:ℂ)*
        ∫ v in Ioi (2:ℝ),star (W v)*W v/(v:ℂ)^3 := by
  rw [cubicThetaFourierProfile_gram,cubicThetaCuspFourierTest_pairing,
    cubicThetaHorizontalFourier_character_self,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  ring

lemma cubicThetaWeightSquareIntegral_scale (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ)) :
    (∫ v in Ioi (0:ℝ),star (W (r*v))*W (r*v)/(v:ℂ)^3)=
      (r:ℂ)^2*∫ v in Ioi (0:ℝ),star (W v)*W v/(v:ℂ)^3 := by
  let g : ℝ → ℂ := fun v => star (W v)*W v/(v:ℂ)^3
  have he : (fun v => star (W (r*v))*W (r*v)/(v:ℂ)^3)=
      (fun v => (r:ℂ)^3*g (r*v)) := by
    funext v
    dsimp only [g]
    rw [Complex.ofReal_mul,mul_pow]
    have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
    by_cases hv : v=0
    · simp [hv]
    · have hvC : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv
      field_simp
  rw [he,integral_const_mul,integral_comp_mul_left_Ioi g 0 hr,mul_zero]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  dsimp only [g]
  field_simp

theorem cubicThetaFourierProfile_scale_norm_sq (h k : Eisenstein)
    (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ),W v=0)
    (hV : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r hr W v=0) :
    ‖cubicThetaFourierProfileL2 k (cubicThetaRadialWeightScale r hr W) hV‖^2=
      r^2*‖cubicThetaFourierProfileL2 h W hW‖^2 := by
  have hs : inner ℂ
      (cubicThetaFourierProfileL2 k (cubicThetaRadialWeightScale r hr W) hV)
      (cubicThetaFourierProfileL2 k (cubicThetaRadialWeightScale r hr W) hV)=
      (r:ℂ)^2*inner ℂ (cubicThetaFourierProfileL2 h W hW) (cubicThetaFourierProfileL2 h W hW) := by
    rw [cubicThetaFourierProfile_inner_self,cubicThetaFourierProfile_inner_self]
    have hz (V : C_c(ℝ,ℂ)) (hV : ∀ v≤(2:ℝ),V v=0) :
        (∫ v in Ioi (2:ℝ),star (V v)*V v/(v:ℂ)^3)=
          ∫ v in Ioi (0:ℝ),star (V v)*V v/(v:ℂ)^3 := by
      simpa only [mul_div_assoc,div_mul_eq_mul_div] using
        cubicThetaRadialIntegral_zero_extension V hV (fun v => V v)
    rw [hz _ hV,hz _ hW]
    change _*((∫ v in Ioi (0:ℝ),star (W (r*v))*W (r*v)/(v:ℂ)^3))=_
    rw [cubicThetaWeightSquareIntegral_scale r hr W]
    ring
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at hs
  apply Complex.ofReal_injective
  push_cast
  exact hs

end CubicFirstMoment

end

end OAI
