import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactCuspSupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCutoff
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspHardy

namespace OAI

/-! Actual compact smooth sections, pulled into a cusp and conjugated
by logarithmic height, are genuine compact radial test functions. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaCuspCutoffSection (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) (v : ℝ) : ℂ :=
  cubicThetaCuspCutoff v*cubicThetaSectionFunction F
    (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))

def cubicThetaCuspLogSection (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-t):ℂ)*cubicThetaCuspCutoffSection δ F z (Real.exp t)

lemma cubicThetaCuspLogSection_contDiff (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) : ContDiff ℝ ∞ (cubicThetaCuspLogSection δ F z) := by
  have hM : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaMobius (cubicThetaFullComplex δ) (z,Real.exp t)) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact (cubicThetaMobius_contDiffAt _ (Real.exp_pos t)).comp t
      (contDiffAt_const.prodMk Real.contDiff_exp.contDiffAt)
  have hF : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,Real.exp t))) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    have hpos := cubicThetaMobius_height_pos (cubicThetaFullComplex δ)
      (p:=(z,Real.exp t)) (Real.exp_pos t)
    have hFpoint : ContDiffAt ℝ ∞ (cubicThetaSectionFunction F)
        (cubicThetaMobius (cubicThetaFullComplex δ) (z,Real.exp t)) :=
      F.property.1.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hpos)
    exact ContDiffAt.comp (g:=cubicThetaSectionFunction F)
      (f:=fun t : ℝ => cubicThetaMobius (cubicThetaFullComplex δ) (z,Real.exp t))
      t hFpoint hM.contDiffAt
  have he : ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (-t):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_id.neg)
  exact he.mul ((cubicThetaCuspCutoff_smooth.comp Real.contDiff_exp).mul hF)

lemma cubicThetaCuspLogSection_compact (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) : HasCompactSupport (cubicThetaCuspLogSection δ F z) := by
  obtain ⟨C,_,hC⟩ := cubicThetaSmoothTests_cusp_function_support F
  let D := max C 2
  have hD : 0<D := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_right _ _)
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=0) (b:=Real.log D))
  intro t ht
  by_contra hout
  have hout' : t<0 ∨ Real.log D<t := by simpa only [mem_Icc,not_and_or,not_le] using hout
  apply ht
  rcases hout' with ht | ht
  · have hv : Real.exp t≤1 := Real.exp_le_one_iff.mpr ht.le
    simp only [cubicThetaCuspLogSection,cubicThetaCuspCutoffSection,
      cubicThetaCuspCutoff_zero hv,zero_mul,mul_zero]
  · have hv : D<Real.exp t := (Real.log_lt_iff_lt_exp hD).mp ht
    have hz := hC δ z (Real.exp t) (Real.exp_pos t) (lt_of_le_of_lt (le_max_left _ _) hv)
    simp only [cubicThetaCuspLogSection,cubicThetaCuspCutoffSection,hz,mul_zero]

lemma cubicThetaCuspLogSection_lift (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaLogLift (cubicThetaCuspLogSection δ F z) v=cubicThetaCuspCutoffSection δ F z v := by
  unfold cubicThetaLogLift cubicThetaCuspLogSection
  rw [Real.exp_log hv,Real.exp_neg,Real.exp_log hv]
  have hv' : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  push_cast
  field_simp

end CubicFirstMoment

end

end OAI
