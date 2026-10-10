import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionDifferential
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalL2

namespace OAI

/-! The genuine differential energy descends to a continuous function
on the quotient. Compact smooth sections have compactly supported
gradient norm, hence square-integrable gradient. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSectionEnergy_continuous (F : cubicThetaSmoothTests) :
    Continuous (cubicThetaSectionEnergy F) := by
  have hd : Continuous (fun p : CubicThetaPoint =>
      fderiv ℝ (cubicThetaSectionFunction F) p.val) :=
    (F.property.1.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by simp)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  unfold cubicThetaSectionEnergy cubicThetaTangentEnergy cubicThetaSectionDifferential
  apply ((continuous_snd.comp continuous_subtype_val).pow 2).mul
  apply continuous_finsetSum
  intro i hi
  exact ((hd.clm_apply continuous_const).norm).pow 2

def cubicThetaQuotientEnergy (F : cubicThetaSmoothTests) (q : CubicThetaQuotient) : ℝ :=
  cubicThetaSectionEnergy F (cubicThetaQuotientLift q)

lemma cubicThetaQuotientEnergy_apply (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaQuotientEnergy F (cubicThetaQuotientMap p)=cubicThetaSectionEnergy F p := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaQuotientEnergy
  rw [← hg,cubicThetaSectionEnergy_invariant]

lemma cubicThetaQuotientEnergy_continuous (F : cubicThetaSmoothTests) :
    Continuous (cubicThetaQuotientEnergy F) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaQuotientEnergy F ∘ cubicThetaQuotientMap=cubicThetaSectionEnergy F :=
    funext (cubicThetaQuotientEnergy_apply F)
  rw [he]
  exact cubicThetaSectionEnergy_continuous F

lemma cubicThetaSectionDifferential_eq_zero (F : CubicThetaSection) (p : CubicThetaPoint)
    (hp : cubicThetaQuotientMap p∉tsupport (cubicThetaSectionNorm F)) :
    cubicThetaSectionDifferential F p=0 := by
  have hzero := notMem_tsupport_iff_eventuallyEq.mp hp
  have htarget : p.val∈cubicThetaPointInclusion.target := by
    rw [cubicThetaPointInclusion_target]
    exact p.property
  have hinv : cubicThetaPointInclusion.symm p.val=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  have hmap : ContinuousAt (fun y => cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)) p.val :=
    cubicThetaQuotientMap_open.continuous.continuousAt.comp
      (cubicThetaPointInclusion.symm.continuousAt htarget)
  have hmap' : Tendsto (fun y => cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))
      (𝓝 p.val) (𝓝 (cubicThetaQuotientMap p)) := by
    have he := congrArg (fun r : CubicThetaPoint => 𝓝 (cubicThetaQuotientMap r)) hinv
    exact he ▸ hmap.tendsto
  have he : cubicThetaSectionFunction F =ᶠ[𝓝 p.val] (fun _ => (0:ℂ)) := by
    filter_upwards [hzero.comp_tendsto hmap'] with y hy
    change cubicThetaSectionNorm F (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))=0 at hy
    rw [cubicThetaSectionNorm_apply] at hy
    exact norm_eq_zero.mp hy
  have hd : fderiv ℝ (cubicThetaSectionFunction F) p.val=0 := by
    rw [he.fderiv_eq]
    exact fderiv_const_apply (0:ℂ)
  ext u
  simp only [cubicThetaSectionDifferential,hd,ContinuousLinearMap.zero_comp,zero_apply]

lemma cubicThetaQuotientEnergy_compact (F : cubicThetaSmoothTests) :
    HasCompactSupport (cubicThetaQuotientEnergy F) := by
  apply F.property.2.mono'
  intro q hq
  by_contra hn
  have hp : cubicThetaQuotientMap (cubicThetaQuotientLift q)∉tsupport (cubicThetaSectionNorm F) := by
    rwa [cubicThetaQuotientLift_map]
  have hd := cubicThetaSectionDifferential_eq_zero F (cubicThetaQuotientLift q) hp
  apply hq
  simp only [cubicThetaQuotientEnergy,cubicThetaSectionEnergy,hd,
    cubicThetaTangentEnergy,zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero,mul_zero]

def cubicThetaQuotientGradientNorm (F : cubicThetaSmoothTests) : CubicThetaQuotient → ℝ :=
  fun q => Real.sqrt (cubicThetaQuotientEnergy F q)

lemma cubicThetaQuotientGradientNorm_memLp (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaQuotientGradientNorm F) 2 cubicThetaQuotientMeasure :=
  (cubicThetaQuotientEnergy_continuous F).sqrt.memLp_of_hasCompactSupport
    ((cubicThetaQuotientEnergy_compact F).comp_left (g:=Real.sqrt) Real.sqrt_zero)

end CubicFirstMoment

end

end OAI
