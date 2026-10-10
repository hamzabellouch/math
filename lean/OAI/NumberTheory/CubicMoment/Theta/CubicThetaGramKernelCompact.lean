import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramRowKernel
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierSmooth

namespace OAI

/-! The archimedean inversion kernel in every nonzero row is a genuine
compactly supported smooth function of the horizontal variable. -/
noncomputable section
open Set
open scoped CompactlySupported ContDiff SchwartzMap
namespace CubicFirstMoment

lemma cubicThetaGramInversionKernel_support (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    {c : ℂ} (hc : c≠0) {δ v : ℝ} (hδ : 0<δ) (hv : 0<v)
    (hV : ∀ t≤δ,V t=0) :
    Function.support (fun z => cubicThetaGramInversionKernel h k V c z v)⊆
      Metric.closedBall 0 (Real.sqrt (v/(Complex.normSq c*δ))) := by
  intro z hz
  have hval : V (cubicThetaInversion c (z,v)).2≠0 := by
    intro he
    exact hz (by simp only [cubicThetaGramInversionKernel,he,mul_zero,zero_mul])
  have hh : δ<(cubicThetaInversion c (z,v)).2 :=
    lt_of_not_ge (fun he => hval (hV _ he))
  have hcpos : 0<Complex.normSq c := Complex.normSq_pos.mpr hc
  have hD : 0<Complex.normSq c*cubicThetaRadius (z,v) :=
    mul_pos hcpos (cubicThetaRadius_pos hv)
  change δ<v/(Complex.normSq c*cubicThetaRadius (z,v)) at hh
  have hm := (lt_div_iff₀ hD).mp hh
  have hn : ‖z‖^2≤v/(Complex.normSq c*δ) := by
    apply (le_div_iff₀ (mul_pos hcpos hδ)).mpr
    unfold cubicThetaRadius at hm
    dsimp only at hm
    rw [Complex.normSq_eq_norm_sq z] at hm
    nlinarith [mul_nonneg (mul_nonneg hcpos.le hδ.le) (sq_nonneg v)]
  rw [Metric.mem_closedBall,dist_zero_right]
  exact Real.le_sqrt_of_sq_le hn

lemma cubicThetaGramInversionKernel_compact (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    {c : ℂ} (hc : c≠0) {δ v : ℝ} (hδ : 0<δ) (hv : 0<v)
    (hV : ∀ t≤δ,V t=0) :
    HasCompactSupport (fun z => cubicThetaGramInversionKernel h k V c z v) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 _)
    (cubicThetaGramInversionKernel_support h k V hc hδ hv hV)

lemma cubicThetaInversion_horizontal_smooth {c : ℂ} (hc : c≠0) {v : ℝ} (hv : 0<v) :
    ContDiff ℝ ∞ (fun z : ℂ => cubicThetaInversion c (z,v)) := by
  have he : (fun z : ℂ => cubicThetaInversion c (z,v))=
      (fun z => cubicThetaMobius (cubicThetaInversionMatrix c hc) (z,v)) :=
    funext (fun _ => (cubicThetaMobius_inversion hc hv).symm)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (cubicThetaMobius_contDiffAt (cubicThetaInversionMatrix c hc) (p:=(z,v)) hv).comp z
    (contDiffAt_id.prodMk contDiffAt_const)

lemma cubicThetaGramInversionKernel_smooth (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {c : ℂ} (hc : c≠0) {v : ℝ} (hv : 0<v) :
    ContDiff ℝ ∞ (fun z => cubicThetaGramInversionKernel h k V c z v) := by
  have hM := cubicThetaInversion_horizontal_smooth hc hv
  have hstar : ContDiff ℝ ∞ (fun z => star (cubicThetaHorizontalCharacter h z)) := by
    simpa only [Function.comp_def,Complex.star_def,Complex.conjCLE_apply] using
      Complex.conjCLE.contDiff.comp (cubicThetaHorizontalCharacter_contDiff h)
  exact (hstar.mul (hsm.comp hM.snd)).mul
    ((cubicThetaHorizontalCharacter_contDiff k).comp hM.fst)

def cubicThetaGramKernelSchwartz (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {c : ℂ} (hc : c≠0) {δ v : ℝ}
    (hδ : 0<δ) (hv : 0<v) (hV : ∀ t≤δ,V t=0) : 𝓢(ℂ,ℂ) :=
  (cubicThetaGramInversionKernel_compact h k V hc hδ hv hV).toSchwartzMap
    (cubicThetaGramInversionKernel_smooth h k V hsm hc hv)

end CubicFirstMoment

end

end OAI
