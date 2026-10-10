import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! A smooth ambient radial contraction, fixed outside the larger disk.
It supplies the local shrinking step for analytic Jordan caps. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def radialShrinkFactor (t a b r : ℝ) : ℝ :=
  t+(1-t)*Real.smoothTransition ((r^2-a^2)/(b^2-a^2))

def radialShrink (t a b : ℝ) (z : ℂ) : ℂ :=
  radialShrinkFactor t a b ‖z‖ • z

lemma radialShrinkFactor_pos {t a b r : ℝ} (ht : 0<t) (ht1 : t≤1) :
    0<radialShrinkFactor t a b r := by
  unfold radialShrinkFactor
  have := mul_nonneg (sub_nonneg.mpr ht1) (Real.smoothTransition.nonneg ((r^2-a^2)/(b^2-a^2)))
  linarith

lemma radialShrinkFactor_monotone {t a b : ℝ} (ht1 : t≤1) (ha : 0<a) (hab : a<b) :
    MonotoneOn (radialShrinkFactor t a b) (Ici 0) := by
  have hden : 0<b^2-a^2 := by nlinarith
  intro r hr s hs hrs
  unfold radialShrinkFactor
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht1)
  apply Real.smoothTransition.monotone
  apply div_le_div_of_nonneg_right _ hden.le
  have hr0 : 0≤r := hr
  have hs0 : 0≤s := hs
  nlinarith

lemma radialShrinkRadius_strictMono {t a b : ℝ} (ht : 0<t) (ht1 : t≤1)
    (ha : 0<a) (hab : a<b) :
    StrictMonoOn (fun r => radialShrinkFactor t a b r*r) (Ici 0) := by
  intro r hr s hs hrs
  calc
    radialShrinkFactor t a b r*r < radialShrinkFactor t a b r*s :=
      mul_lt_mul_of_pos_left hrs (radialShrinkFactor_pos ht ht1)
    _ ≤ radialShrinkFactor t a b s*s := mul_le_mul_of_nonneg_right
      (radialShrinkFactor_monotone ht1 ha hab hr hs hrs.le) hs

lemma radialShrink_norm {t a b : ℝ} (ht : 0<t) (ht1 : t≤1) (z : ℂ) :
    ‖radialShrink t a b z‖=radialShrinkFactor t a b ‖z‖*‖z‖ := by
  rw [radialShrink,norm_smul,Real.norm_eq_abs,abs_of_pos (radialShrinkFactor_pos ht ht1)]

lemma radialShrink_inner {t a b : ℝ} (ha : 0<a) (hab : a<b) {z : ℂ} (hz : ‖z‖≤a) :
    radialShrink t a b z=t • z := by
  have hden : 0<b^2-a^2 := by nlinarith
  have harg : (‖z‖^2-a^2)/(b^2-a^2)≤0 := div_nonpos_of_nonpos_of_nonneg
    (by nlinarith [norm_nonneg z]) hden.le
  simp only [radialShrink,radialShrinkFactor,Real.smoothTransition.zero_of_nonpos harg,
    mul_zero,add_zero]

lemma radialShrink_outer {t a b : ℝ} (ha : 0<a) (hab : a<b) {z : ℂ} (hz : b≤‖z‖) :
    radialShrink t a b z=z := by
  have hden : 0<b^2-a^2 := by nlinarith
  have harg : 1≤(‖z‖^2-a^2)/(b^2-a^2) := (le_div_iff₀ hden).mpr (by nlinarith)
  simp only [radialShrink,radialShrinkFactor,Real.smoothTransition.one_of_one_le harg,mul_one]
  have he : t+(1-t)=1 := by ring
  rw [he,one_smul]

lemma radialShrink_contDiff (t a b : ℝ) : ContDiff ℝ ∞ (radialShrink t a b) := by
  have hs : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖^2) := by
    simp only [Complex.sq_norm,Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  exact (contDiff_const.add (contDiff_const.mul
    (Real.smoothTransition.contDiff.comp ((hs.sub contDiff_const).div_const _)))).smul contDiff_id

lemma radialShrink_injective {t a b : ℝ} (ht : 0<t) (ht1 : t≤1)
    (ha : 0<a) (hab : a<b) : Injective (radialShrink t a b) := by
  intro z w he
  have hn : ‖z‖=‖w‖ := (radialShrinkRadius_strictMono ht ht1 ha hab).injOn
    (norm_nonneg z) (norm_nonneg w) (by simpa only [radialShrink_norm ht ht1] using congrArg norm he)
  change radialShrinkFactor t a b ‖z‖ • z=radialShrinkFactor t a b ‖w‖ • w at he
  rw [hn] at he
  exact (smul_right_injective _ (radialShrinkFactor_pos ht ht1).ne') he

lemma radialShrink_surjective {t a b : ℝ} (_ht : 0<t) (_ht1 : t≤1)
    (ha : 0<a) (hab : a<b) : Surjective (radialShrink t a b) := by
  intro y
  by_cases hy : y=0
  · subst y
    exact ⟨0,by simp [radialShrink]⟩
  have hypos : 0<‖y‖ := norm_pos_iff.mpr hy
  by_cases hyb : b≤‖y‖
  · exact ⟨y,radialShrink_outer ha hab hyb⟩
  have hb : 0<b := ha.trans hab
  have hc : Continuous (fun r => radialShrinkFactor t a b r*r) := by
    unfold radialShrinkFactor
    fun_prop
  have hbval : radialShrinkFactor t a b b*b=b := by
    have hd : b^2-a^2≠0 := by nlinarith
    simp [radialShrinkFactor,hd]
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc hb.le hc.continuousOn
    (show ‖y‖∈Icc (radialShrinkFactor t a b 0*0) (radialShrinkFactor t a b b*b) by
      rw [mul_zero,hbval];exact ⟨hypos.le,le_of_lt (lt_of_not_ge hyb)⟩)
  change radialShrinkFactor t a b r*r=‖y‖ at he
  have hrpos : 0<r := by
    by_contra hn
    have hz : r=0 := le_antisymm (le_of_not_gt hn) hr.1
    rw [hz,mul_zero] at he
    exact hypos.ne' he.symm
  refine ⟨(r/‖y‖) • y,?_⟩
  have hn : ‖(r/‖y‖) • y‖=r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hrpos hypos),div_mul_cancel₀ _ hypos.ne']
  unfold radialShrink
  rw [hn,smul_smul]
  have hfac : radialShrinkFactor t a b r*(r/‖y‖)=1 := by
    rw [←mul_div_assoc,he,div_self hypos.ne']
  rw [hfac,one_smul]

def smoothRadialShrinkHomeomorph {t a b : ℝ} (ht : 0<t) (ht1 : t≤1)
    (ha : 0<a) (hab : a<b) : ℂ ≃ₜ ℂ := by
  let e := Equiv.ofBijective (radialShrink t a b)
    ⟨radialShrink_injective ht ht1 ha hab,radialShrink_surjective ht ht1 ha hab⟩
  have hc := (radialShrink_contDiff t a b).continuous
  have he : (fun z : ℂ => z)=ᶠ[cocompact ℂ] radialShrink t a b := by
    filter_upwards [(isCompact_closedBall (0:ℂ) b).compl_mem_cocompact] with z hz
    have hz' : b<‖z‖ := by
      simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hz
    exact (radialShrink_outer ha hab hz'.le).symm

  have hp : IsProperMap (radialShrink t a b) :=
    isProperMap_iff_tendsto_cocompact.mpr ⟨hc,tendsto_id.congr' he⟩
  exact e.toHomeomorphOfContinuousClosed hc hp.isClosedMap

end CircleDomainRigidity

end

end OAI
