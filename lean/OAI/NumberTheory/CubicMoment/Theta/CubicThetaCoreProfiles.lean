import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreBumps
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionLocalization

namespace OAI

/-! The compact core cutoffs become actual smooth Euclidean chart
profiles, with support entirely at positive height. -/
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
namespace CubicFirstMoment

def cubicThetaCoreProfile (c : CubicThetaQuotient) (y : ℂ × ℝ) : ℂ :=
  ((cubicThetaCoreBump c).toContDiffBump y:ℝ)

lemma cubicThetaCoreProfile_contDiff (c : CubicThetaQuotient) :
    ContDiff ℝ ∞ (cubicThetaCoreProfile c) :=
  Complex.ofRealCLM.contDiff.comp (cubicThetaCoreBump c).toContDiffBump.contDiff

lemma cubicThetaCoreProfile_compact (c : CubicThetaQuotient) :
    HasCompactSupport (cubicThetaCoreProfile c) :=
  (cubicThetaCoreBump c).toContDiffBump.hasCompactSupport.comp_left
    (g:=fun r : ℝ => (r:ℂ)) (by simp)

lemma cubicThetaQuotientChart_target_positive (c : CubicThetaQuotient) :
    (cubicThetaQuotientChart c).target ⊆ {y : ℂ × ℝ | 0<y.2} := by
  intro y hy
  change y∈cubicThetaPointInclusion.target ∧ _ at hy
  rw [cubicThetaPointInclusion_target] at hy
  exact hy.1

lemma cubicThetaCoreProfile_support_target (c : CubicThetaQuotient) :
    tsupport (cubicThetaCoreProfile c) ⊆ (cubicThetaQuotientChart c).target := by
  have hs : tsupport (cubicThetaCoreProfile c) ⊆ tsupport (cubicThetaCoreBump c).toContDiffBump := by
    apply closure_mono
    intro y hy hz
    apply hy
    change ((cubicThetaCoreBump c).toContDiffBump y:ℂ)=0
    rw [hz]
    rfl
  intro y hy
  have hb := hs hy
  rw [ContDiffBump.tsupport_eq] at hb
  have ht := (cubicThetaCoreBump c).closedBall_subset ⟨hb,⟨y,rfl⟩⟩
  have ht' : y∈(cubicThetaQuotientChart c).target := by
    simp only [extChartAt_target,modelWithCornersSelf_coe_symm,Set.preimage_id_eq,
      modelWithCornersSelf_coe,Set.range_id,Set.inter_univ,id_eq] at ht
    change y∈(cubicThetaQuotientChart c).target at ht
    exact ht
  exact ht'

lemma cubicThetaCoreProfile_support_positive (c : CubicThetaQuotient) :
    tsupport (cubicThetaCoreProfile c) ⊆ {y : ℂ × ℝ | 0<y.2} :=
  (cubicThetaCoreProfile_support_target c).trans (cubicThetaQuotientChart_target_positive c)

lemma cubicThetaCoreProfile_section_memLp (c : CubicThetaQuotient) (F : CubicThetaSection) :
    MemLp (cubicThetaLocalizedSection (cubicThetaCoreProfile c) F) 2
      (volume : Measure (ℂ × ℝ)) :=
  cubicThetaLocalizedSection_memLp (cubicThetaCoreProfile_contDiff c).continuous
    (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c) F

end CubicFirstMoment

end

end OAI
