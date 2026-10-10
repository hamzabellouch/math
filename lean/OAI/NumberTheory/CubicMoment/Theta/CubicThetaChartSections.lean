import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPoincareSmooth
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreProfiles

namespace OAI

/-! A compact Euclidean chart profile gives a genuine compact smooth
section. On its covering sheet the periodization is exactly the seed. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveSeed_compact {φ : ℂ × ℝ → ℂ}
    (hc : HasCompactSupport φ) (hpos : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) :
    HasCompactSupport (fun p : CubicThetaPoint => φ p.val) := by
  have hinc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hK := hc.image_of_continuousOn (hinc.mono hpos)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro p hp
  refine ⟨p.val,subset_tsupport φ hp,?_⟩
  exact cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)

def cubicThetaCoreSeed (c : CubicThetaQuotient) : C_c(CubicThetaPoint,ℂ) :=
  ⟨⟨fun p => cubicThetaCoreProfile c p.val,
    (cubicThetaCoreProfile_contDiff c).continuous.comp continuous_subtype_val⟩,
    cubicThetaPositiveSeed_compact (cubicThetaCoreProfile_compact c)
      (cubicThetaCoreProfile_support_positive c)⟩

lemma cubicThetaCoreSeed_contDiffOn (c : CubicThetaQuotient) :
    ContDiffOn ℝ ∞ (fun y => cubicThetaCoreSeed c (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2} := by
  apply (cubicThetaCoreProfile_contDiff c).contDiffOn.congr
  intro y hy
  change cubicThetaCoreProfile c (cubicThetaPointInclusion.symm y).val=cubicThetaCoreProfile c y
  congr 1
  exact cubicThetaPointInclusion.right_inv (by rwa [cubicThetaPointInclusion_target])

lemma cubicThetaPoincareSection_on_sheet (ψ : C_c(CubicThetaPoint,ℂ))
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hs : Function.support ψ ⊆ e.source) {p : CubicThetaPoint} (hp : p∈e.source) :
    (cubicThetaPoincareSection ψ).val p=ψ p := by
  have hz : ∀ g : cubicThetaPrincipalGroup, g≠1 → cubicThetaPoincareTerm ψ g p=0 := by
    intro g hg
    have hgp : g • p∉Function.support ψ := by
      intro h
      have heq : e (g • p)=e p := by
        rw [he,cubicThetaQuotient_covering.map_smul]
      have hf : g • p=p := e.injOn (hs h) hp heq
      exact hg (cubicThetaPrincipal_fixed_eq_one g p hf)
    have hz : ψ (g • p)=0 := by simpa only [Function.mem_support,not_not] using hgp
    simp only [cubicThetaPoincareTerm,hz,mul_zero]
  change (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)=ψ p
  rw [finsum_eq_single _ 1 hz]
  simp [cubicThetaPoincareTerm,cubicThetaKubotaValue]

end CubicFirstMoment

end

end OAI
