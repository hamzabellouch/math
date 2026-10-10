import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateEnergyClosure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPoincareLocalization
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreSections

namespace OAI

/-! Localize a C1 section by one actual arithmetic core profile.
The periodized result is its scalar bump cutoff and lies in the energy graph. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaC1Localization_regular {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiff ℝ 1 (cubicThetaTestLocalization φ F) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y.2
  · exact (hφ.contDiffOn.mul hF).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)
  · have hout : y∉tsupport (cubicThetaTestLocalization φ F) :=
      fun h => hy (hp (tsupport_mul_subset_left h))
    exact (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ × ℝ => (0:ℂ)) y).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hout)

def cubicThetaC1CoreFunction (c : CubicThetaQuotient) (F : CubicThetaSection) (y : ℂ × ℝ) : ℂ :=
  cubicThetaCoreProfile c y*(cubicThetaCoreProfile c y*cubicThetaSectionFunction F y)

lemma cubicThetaC1CoreFunction_support (c : CubicThetaQuotient) (F : CubicThetaSection) :
    tsupport (cubicThetaC1CoreFunction c F)⊆tsupport (cubicThetaCoreProfile c) :=
  tsupport_mul_subset_left

lemma cubicThetaC1CoreFunction_compact (c : CubicThetaQuotient) (F : CubicThetaSection) :
    HasCompactSupport (cubicThetaC1CoreFunction c F) := (cubicThetaCoreProfile_compact c).mul_right

lemma cubicThetaC1CoreFunction_regular (c : CubicThetaQuotient) (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiff ℝ 1 (cubicThetaC1CoreFunction c F) :=
  (cubicThetaCoreProfile_contDiff c).of_le (by simp) |>.mul
    (cubicThetaC1Localization_regular ((cubicThetaCoreProfile_contDiff c).of_le (by simp))
      (cubicThetaCoreProfile_support_positive c) F hF)

def cubicThetaCoreSquare (c : CubicThetaQuotient) : C(CubicThetaQuotient,ℂ) :=
  ⟨fun q => (cubicThetaCoreBump c q:ℂ)^2,
    (Complex.continuous_ofReal.comp (cubicThetaCoreBump c).continuous).pow 2⟩

lemma cubicThetaC1CoreFunction_periodization (c : CubicThetaQuotient) (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    let g := cubicThetaC1CoreFunction c F
    let hg := cubicThetaC1CoreFunction_regular c F hF
    let hc := cubicThetaC1CoreFunction_compact c F
    let hp := (cubicThetaC1CoreFunction_support c F).trans (cubicThetaCoreProfile_support_positive c)
    cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc hp)=
      cubicThetaSectionCutoff (cubicThetaCoreSquare c) F := by
  intro g hg hc hp
  let e := cubicThetaCoveringChart (cubicThetaQuotientLift c)
  have hψs : tsupport (cubicThetaCoordinateSeed g hg.continuous hc hp)⊆e.source := by
    intro p hps
    obtain ⟨y,hy,rfl⟩ := cubicThetaCoordinateSeed_support g hg.continuous hc hp hps
    have ht := cubicThetaCoreProfile_support_target c (cubicThetaC1CoreFunction_support c F hy)
    exact ht.2
  have hb : Function.support (cubicThetaCoreSquare c)⊆e.target := by
    intro q hq
    have hb : cubicThetaCoreBump c q≠0 := by
      intro hz
      apply hq
      simp only [cubicThetaCoreSquare,ContinuousMap.coe_mk,hz,Complex.ofReal_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact ((cubicThetaCoreBump c).support_subset_source hb).1
  apply cubicThetaPoincare_localization_eq _ e (cubicThetaCoveringChart_coe _) hψs F (cubicThetaCoreSquare c) hb
  intro p hps
  change cubicThetaCoreProfile c p.val*(cubicThetaCoreProfile c p.val*cubicThetaSectionFunction F p.val)=_
  rw [cubicThetaCoreSeed_eq_bump c hps,cubicThetaSectionFunction_apply F p.property]
  change (cubicThetaCoreBump c (cubicThetaQuotientMap p):ℂ)*
    ((cubicThetaCoreBump c (cubicThetaQuotientMap p):ℂ)*F.val p)=_
  dsimp only [cubicThetaCoreSquare,ContinuousMap.coe_mk]
  ring

lemma cubicThetaC1CoreFunction_mem_energy (c : CubicThetaQuotient) (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaCoordinateData (cubicThetaC1CoreFunction_regular c F hF)
      (cubicThetaC1CoreFunction_compact c F)
      ((cubicThetaC1CoreFunction_support c F).trans (cubicThetaCoreProfile_support_positive c))∈
      cubicThetaGlobalEnergySpace := by
  apply cubicThetaCoordinateData_mem_energy _ _ _ (cubicThetaCoveringChart (cubicThetaQuotientLift c))
    (cubicThetaCoveringChart_coe _)
  rintro p ⟨y,hy,rfl⟩
  exact (cubicThetaCoreProfile_support_target c (cubicThetaC1CoreFunction_support c F hy)).2

end CubicFirstMoment

end

end OAI
