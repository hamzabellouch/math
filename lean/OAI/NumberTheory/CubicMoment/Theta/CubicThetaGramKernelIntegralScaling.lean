import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramKernelScaling

namespace OAI

/-! The real and complex Jacobians cancel exactly in the normalized
prime-power archimedean Gram integral. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaGramKernel_integral_scale (a h k : Eisenstein) (ha : a≠0)
    (V : C_c(ℝ,ℂ)) {c : ℂ} (hc : c≠0) {v : ℝ} (hv : 0<v) :
    (∫ z,cubicThetaGramInversionKernel (a*h) (a*k)
      (cubicThetaRadialWeightScale ‖(a:ℂ)‖ (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) V)
      c z (v/‖(a:ℂ)‖))=
      (norm a)⁻¹ • ∫ z,cubicThetaGramInversionKernel h k V (c/(a:ℂ)) z v := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  have he (z : ℂ) := cubicThetaGramInversionKernel_scale a h k ha V hc (z:=(a:ℂ)*z) hv
  have hz (z : ℂ) : (a:ℂ)*z/(a:ℂ)=z := by field_simp
  simp only [hz] at he
  simp_rw [he]
  have ht := integral_complexMul (a:ℂ) haC
    (fun z => cubicThetaGramInversionKernel h k V (c/(a:ℂ)) z v)
  exact ht

def cubicThetaArchimedeanGram (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    (c : ℂ) (ε : ℝ) : ℂ :=
  ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*∫ z,cubicThetaGramInversionKernel h k V c z v

theorem cubicThetaArchimedeanGram_scale (a h k : Eisenstein) (ha : a≠0)
    (W V : C_c(ℝ,ℂ)) {c : ℂ} (hc : c≠0) {ε : ℝ} (hε : 0<ε) :
    cubicThetaArchimedeanGram (a*h) (a*k)
      (cubicThetaRadialWeightScale ‖(a:ℂ)‖ (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W)
      (cubicThetaRadialWeightScale ‖(a:ℂ)‖ (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) V)
      c (ε/‖(a:ℂ)‖)=
      cubicThetaArchimedeanGram h k W V (c/(a:ℂ)) ε := by
  let r := ‖(a:ℂ)‖
  have hr : 0<r := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  have hn : norm a=r^2 := Complex.normSq_eq_norm_sq (a:ℂ)
  let F : ℝ → ℂ := fun v => star (W v)/(v:ℂ)^3*
    ∫ z,cubicThetaGramInversionKernel h k V (c/(a:ℂ)) z v
  have he : cubicThetaArchimedeanGram (a*h) (a*k)
      (cubicThetaRadialWeightScale r hr W) (cubicThetaRadialWeightScale r hr V) c (ε/r)=
      ∫ v in Ioi (ε/r),(r:ℂ)*F (r*v) := by
    unfold cubicThetaArchimedeanGram
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hv0 : 0<v := (div_pos hε hr).trans hv
    have hs := cubicThetaGramKernel_integral_scale a h k ha V hc (v:=r*v) (mul_pos hr hv0)
    have hrv : r*v/r=v := by field_simp
    change (∫ z,cubicThetaGramInversionKernel (a*h) (a*k) (cubicThetaRadialWeightScale r hr V)
      c z (r*v/r))=_ at hs
    rw [hrv] at hs
    dsimp only [F]
    change star (W (r*v))/(v:ℂ)^3*_= _
    rw [hs,Complex.real_smul,hn]
    have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hvC : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv0.ne'
    push_cast
    field_simp
  rw [he,integral_const_mul,integral_comp_mul_left_Ioi F (ε/r) hr]
  have hre : r*(ε/r)=ε := by field_simp
  rw [hre,Complex.real_smul]
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  rw [←mul_assoc,mul_inv_cancel₀ hrC,one_mul]
  rfl

end CubicFirstMoment

end

end OAI
