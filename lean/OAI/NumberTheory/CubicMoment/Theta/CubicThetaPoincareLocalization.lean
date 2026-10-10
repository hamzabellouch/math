import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateSectionSupport

namespace OAI

/-! A seed in one covering sheet periodizes to the corresponding
invariant cutoff of the original section, including its cubic multiplier. -/
noncomputable section
open Set
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoincare_localization_eq (ψ : C_c(CubicThetaPoint,ℂ))
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hψs : tsupport ψ⊆e.source) (F : CubicThetaSection) (b : C(CubicThetaQuotient,ℂ))
    (hb : Function.support b⊆e.target)
    (hψ : ∀ p∈e.source, ψ p=b (cubicThetaQuotientMap p)*F.val p) :
    cubicThetaPoincareSection ψ=cubicThetaSectionCutoff b F := by
  let T := cubicThetaPoincareSection ψ
  let G := cubicThetaSectionCutoff b F
  have hn (q : CubicThetaQuotient) : cubicThetaSectionNorm (T-G) q=0 := by
    by_cases hq : q∈e.target
    · let p := e.symm q
      have hp : p∈e.source := e.map_target hq
      have hqp : cubicThetaQuotientMap p=q := by rw [← he]; exact e.right_inv hq
      rw [← hqp,cubicThetaSectionNorm_apply]
      change ‖(cubicThetaPoincareSection ψ).val p-b (cubicThetaQuotientMap p)*F.val p‖=0
      rw [cubicThetaPoincareSection_on_sheet ψ e he (subset_tsupport ψ |>.trans hψs) hp,
        hψ p hp,sub_self,norm_zero]
    · have hout : q∉tsupport (cubicThetaSectionNorm T) := by
        intro h
        obtain ⟨p,hp,hpq⟩ := cubicThetaPoincareSection_norm_support ψ h
        have ht := e.map_source (hψs hp)
        rw [he,hpq] at ht
        exact hq ht
      have hz := image_eq_zero_of_notMem_tsupport hout
      have hb0 : b q=0 := Function.notMem_support.mp (fun h => hq (hb h))
      change ‖T.val (cubicThetaQuotientLift q)-
        b (cubicThetaQuotientMap (cubicThetaQuotientLift q))*F.val (cubicThetaQuotientLift q)‖=0
      rw [cubicThetaQuotientLift_map,hb0,zero_mul,sub_zero]
      exact hz
  ext p
  have h := hn (cubicThetaQuotientMap p)
  rw [cubicThetaSectionNorm_apply] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp h)

end CubicFirstMoment

end

end OAI
