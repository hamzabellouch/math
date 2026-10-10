import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramKernelCompact
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialWeightScaling

namespace OAI

/-! Exact archimedean scaling of the diagonal prime-power Gram kernels.
The denominator transforms by c/a; all frequencies and radial factors are retained. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadius_divide {a : ℂ} (ha : a≠0) (z : ℂ) (v : ℝ) :
    cubicThetaRadius (z/a,v/‖a‖)=cubicThetaRadius (z,v)/Complex.normSq a := by
  have hn : ‖a‖≠0 := norm_ne_zero_iff.mpr ha
  simp only [cubicThetaRadius,Complex.normSq_div,div_pow,Complex.normSq_eq_norm_sq a]
  rw [add_div]

lemma cubicThetaInversion_double_scale {a c : ℂ} (ha : a≠0) (hc : c≠0)
    {z : ℂ} {v : ℝ} (hv : 0<v) :
    (a*(cubicThetaInversion c (z/a,v/‖a‖)).1,
      ‖a‖*(cubicThetaInversion c (z/a,v/‖a‖)).2)=
      cubicThetaInversion (c/a) (z,v) := by
  have hn : ‖a‖≠0 := norm_ne_zero_iff.mpr ha
  have hna : Complex.normSq a≠0 := (Complex.normSq_pos.mpr ha).ne'
  have hnc : Complex.normSq c≠0 := (Complex.normSq_pos.mpr hc).ne'
  have hr : cubicThetaRadius (z,v)≠0 := (cubicThetaRadius_pos hv).ne'
  have hrC : (cubicThetaRadius (z,v):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  have hstar : star a≠0 := star_ne_zero.mpr ha
  have hN : (Complex.normSq a:ℂ)=a*star a := by
    rw [Complex.normSq_eq_norm_sq,Complex.ofReal_pow,Complex.star_def,Complex.mul_conj']
  apply Prod.ext
  · simp only [cubicThetaInversion,cubicThetaRadius_divide ha]
    push_cast
    rw [hN]
    field_simp
    rw [star_div₀,div_mul_cancel₀ _ hstar]
  · simp only [cubicThetaInversion,cubicThetaRadius_divide ha,Complex.normSq_div]
    rw [Complex.normSq_eq_norm_sq a]
    field_simp

lemma cubicThetaGramInversionKernel_scale (a h k : Eisenstein) (ha : a≠0)
    (V : C_c(ℝ,ℂ)) {c : ℂ} (hc : c≠0) {z : ℂ} {v : ℝ} (hv : 0<v) :
    cubicThetaGramInversionKernel (a*h) (a*k)
      (cubicThetaRadialWeightScale ‖(a:ℂ)‖
        (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) V) c (z/(a:ℂ)) (v/‖(a:ℂ)‖)=
      cubicThetaGramInversionKernel h k V (c/(a:ℂ)) z v := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  have hs := cubicThetaInversion_double_scale haC hc (z:=z) hv
  have hsz := congrArg Prod.fst hs
  have hsv := congrArg Prod.snd hs
  dsimp only at hsz hsv
  unfold cubicThetaGramInversionKernel
  have haz : (a:ℂ)*(z/(a:ℂ))=z := by field_simp
  rw [cubicThetaHorizontalCharacter_mul_index,cubicThetaHorizontalCharacter_mul_index,haz]
  change star (cubicThetaHorizontalCharacter h z)*
    V (‖(a:ℂ)‖*(cubicThetaInversion c (z/(a:ℂ),v/‖(a:ℂ)‖)).2)*
      cubicThetaHorizontalCharacter k ((a:ℂ)*(cubicThetaInversion c (z/(a:ℂ),v/‖(a:ℂ)‖)).1)=_
  rw [hsz,hsv]

end CubicFirstMoment

end

end OAI
