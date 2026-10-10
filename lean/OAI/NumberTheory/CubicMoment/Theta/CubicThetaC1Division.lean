import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1L2

namespace OAI

/-! Divide a compact C1 section by a continuous invariant scalar
which is smooth and nonzero near its support. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaSectionFunction_zero_eventually (F : CubicThetaSection)
    {y : ℂ × ℝ} (hy : 0<y.2)
    (hq : cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)∉tsupport (cubicThetaSectionNorm F)) :
    cubicThetaSectionFunction F=ᶠ[𝓝 y] (fun _ => (0:ℂ)) := by
  have ht : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  have hm := cubicThetaQuotientMap_open.continuous.continuousAt.comp
    (cubicThetaPointInclusion.symm.continuousAt ht)
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hq).comp_tendsto hm
  filter_upwards [hz] with z hz
  change cubicThetaSectionNorm F (cubicThetaQuotientMap (cubicThetaPointInclusion.symm z))=0 at hz
  rw [cubicThetaSectionNorm_apply] at hz
  exact norm_eq_zero.mp hz

def cubicThetaSectionDivide (F : CubicThetaSection) (D : CubicThetaQuotient → ℝ)
    (hD : Continuous D) (hn : ∀ q∈tsupport (cubicThetaSectionNorm F), D q≠0) :
    CubicThetaSection := by
  let f := fun p : CubicThetaPoint => F.val p/(D (cubicThetaQuotientMap p):ℂ)
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro p
    by_cases hd : D (cubicThetaQuotientMap p)=0
    · have hout : cubicThetaQuotientMap p∉tsupport (cubicThetaSectionNorm F) :=
        fun h => hn _ h hd
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hout).comp_tendsto
        cubicThetaQuotientMap_open.continuous.continuousAt
      have hzf : f=ᶠ[𝓝 p] (fun _ => (0:ℂ)) := by
        filter_upwards [hz] with r hr
        change cubicThetaSectionNorm F (cubicThetaQuotientMap r)=0 at hr
        rw [cubicThetaSectionNorm_apply] at hr
        dsimp only [f]
        rw [norm_eq_zero.mp hr,zero_div]
      exact continuousAt_const.congr_of_eventuallyEq hzf
    · exact F.val.continuous.continuousAt.div
        (Complex.continuous_ofReal.comp (hD.comp cubicThetaQuotientMap_open.continuous)).continuousAt
        (by exact_mod_cast hd)
  exact ⟨⟨f,hf⟩,by
    intro g p
    change F.val (g • p)/(D (cubicThetaQuotientMap (g • p)):ℂ)=
      cubicThetaKubotaValue g*(F.val p/(D (cubicThetaQuotientMap p):ℂ))
    rw [cubicThetaQuotient_covering.map_smul,F.property g p]
    ring⟩

lemma cubicThetaSectionDivide_norm_support (F : CubicThetaSection) (D : CubicThetaQuotient → ℝ)
    (hD : Continuous D) (hn : ∀ q∈tsupport (cubicThetaSectionNorm F), D q≠0) :
    tsupport (cubicThetaSectionNorm (cubicThetaSectionDivide F D hD hn))⊆
      tsupport (cubicThetaSectionNorm F) := by
  apply closure_minimal _ isClosed_closure
  intro q hq
  by_contra h
  have hnorm : cubicThetaSectionNorm F q=0 := image_eq_zero_of_notMem_tsupport h
  have hz := norm_eq_zero.mp hnorm
  apply hq
  change ‖F.val (cubicThetaQuotientLift q)/(D (cubicThetaQuotientMap (cubicThetaQuotientLift q)):ℂ)‖=0
  rw [hz,zero_div,norm_zero]

lemma cubicThetaSectionDivide_compact (F : CubicThetaSection) (D : CubicThetaQuotient → ℝ)
    (hD : Continuous D) (hn : ∀ q∈tsupport (cubicThetaSectionNorm F), D q≠0)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaSectionDivide F D hD hn)) :=
  hc.of_isClosed_subset isClosed_closure (cubicThetaSectionDivide_norm_support F D hD hn)

lemma cubicThetaSectionDivide_regular (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (D : CubicThetaQuotient → ℝ) (hD : Continuous D)
    (hn : ∀ q∈tsupport (cubicThetaSectionNorm F), D q≠0)
    (hDs : ContDiffOn ℝ 1 (fun y => D (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)))
      {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaSectionDivide F D hD hn))
      {y : ℂ × ℝ | 0<y.2} := by
  intro y hy
  by_cases hd : D (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))=0
  · have hout : cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)∉tsupport (cubicThetaSectionNorm F) :=
      fun h => hn _ h hd
    have hhout : cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)∉
        tsupport (cubicThetaSectionNorm (cubicThetaSectionDivide F D hD hn)) :=
      fun h => hout (cubicThetaSectionDivide_norm_support F D hD hn h)
    exact (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ × ℝ => (0:ℂ)) y).congr_of_eventuallyEq
      (cubicThetaSectionFunction_zero_eventually _ hy hhout) |>.contDiffWithinAt
  · have hnb := (isOpen_lt continuous_const continuous_snd).mem_nhds hy
    have hfAt := hF.contDiffAt hnb
    have hdAt := Complex.ofRealCLM.contDiff.contDiffAt.comp y ((hDs.contDiffAt hnb).inv hd)
    change ContDiffWithinAt ℝ 1
      (fun z => cubicThetaSectionFunction F z /
        (D (cubicThetaQuotientMap (cubicThetaPointInclusion.symm z)):ℂ)) _ y
    simpa only [div_eq_mul_inv,Function.comp_apply,Pi.inv_apply,
      Complex.ofRealCLM_apply,Complex.ofReal_inv] using (hfAt.mul hdAt).contDiffWithinAt

end CubicFirstMoment

end

end OAI
