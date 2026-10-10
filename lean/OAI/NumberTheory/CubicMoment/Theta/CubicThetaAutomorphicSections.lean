import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientCharts
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaCharacter
import Mathlib.Topology.ContinuousMap.Algebra

namespace OAI

/-! Continuous sections with the actual cubic multiplier. Their norm
descends to the arithmetic quotient, and quotient cutoffs localize them. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaAutomorphicSections : Submodule ℂ C(CubicThetaPoint,ℂ) where
  carrier := {F | ∀ g : cubicThetaPrincipalGroup, ∀ p : CubicThetaPoint,
    F (g • p)=cubicThetaKubotaValue g*F p}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG g p
    change F (g • p)+G (g • p)=cubicThetaKubotaValue g*(F p+G p)
    rw [hF,hG]
    ring
  smul_mem' := by
    intro c F hF g p
    change c*F (g • p)=cubicThetaKubotaValue g*(c*F p)
    rw [hF]
    ring

abbrev CubicThetaSection := cubicThetaAutomorphicSections

def cubicThetaSectionNorm (F : CubicThetaSection) (q : CubicThetaQuotient) : ℝ :=
  ‖F.val (cubicThetaQuotientLift q)‖

lemma cubicThetaSectionNorm_apply (F : CubicThetaSection) (p : CubicThetaPoint) :
    cubicThetaSectionNorm F (cubicThetaQuotientMap p)=‖F.val p‖ := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaSectionNorm
  rw [← hg,F.property g p,norm_mul,cubicThetaKubotaValue_norm,one_mul]

lemma cubicThetaSectionNorm_continuous (F : CubicThetaSection) :
    Continuous (cubicThetaSectionNorm F) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaSectionNorm F ∘ cubicThetaQuotientMap=fun p => ‖F.val p‖ :=
    funext (cubicThetaSectionNorm_apply F)
  rw [he]
  exact F.val.continuous.norm

def cubicThetaSectionCutoff (ψ : C(CubicThetaQuotient,ℂ)) (F : CubicThetaSection) :
    CubicThetaSection :=
  ⟨⟨fun p => ψ (cubicThetaQuotientMap p)*F.val p,
    (ψ.continuous.comp cubicThetaQuotientMap_open.continuous).mul F.val.continuous⟩,by
      intro g p
      change ψ (cubicThetaQuotientMap (g • p))*F.val (g • p)=
        cubicThetaKubotaValue g*(ψ (cubicThetaQuotientMap p)*F.val p)
      rw [cubicThetaQuotient_covering.map_smul g,F.property g p]
      ring⟩

lemma cubicThetaSectionCutoff_norm (ψ : C(CubicThetaQuotient,ℂ)) (F : CubicThetaSection)
    (q : CubicThetaQuotient) :
    cubicThetaSectionNorm (cubicThetaSectionCutoff ψ F) q=‖ψ q‖*cubicThetaSectionNorm F q := by
  unfold cubicThetaSectionNorm
  change ‖ψ (cubicThetaQuotientMap (cubicThetaQuotientLift q))*F.val (cubicThetaQuotientLift q)‖=_
  rw [cubicThetaQuotientLift_map,norm_mul]

lemma cubicThetaSectionCutoff_compact (ψ : C(CubicThetaQuotient,ℂ)) (F : CubicThetaSection)
    (hψ : HasCompactSupport ψ) : HasCompactSupport (cubicThetaSectionNorm (cubicThetaSectionCutoff ψ F)) := by
  have hnorm : HasCompactSupport (fun q => ‖ψ q‖) :=
    hψ.comp_left (g:=fun z : ℂ => ‖z‖) (by simp)
  have he : cubicThetaSectionNorm (cubicThetaSectionCutoff ψ F)=
      fun q => ‖ψ q‖*cubicThetaSectionNorm F q := funext (cubicThetaSectionCutoff_norm ψ F)
  rw [he]
  exact hnorm.mul_right

end CubicFirstMoment

end

end OAI
