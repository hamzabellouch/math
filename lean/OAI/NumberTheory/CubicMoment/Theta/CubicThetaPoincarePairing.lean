import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateSectionSupport

namespace OAI

/-! The cubic multiplier cancels in the pairing of a periodized seed
with an actual automorphic section. The resulting sum is locally finite. -/
noncomputable section
open Set
open scoped BigOperators CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoincare_pairing_point (ψ : C_c(CubicThetaPoint,ℂ))
    (F : CubicThetaSection) (p : CubicThetaPoint) :
    cubicThetaSectionPairing (cubicThetaPoincareSection ψ) F (cubicThetaQuotientMap p)=
      ∑' g : cubicThetaPrincipalGroup, star (ψ (g • p))*F.val (g • p) := by
  classical
  let S := {g : cubicThetaPrincipalGroup | g • p∈tsupport ψ}
  have hS : S.Finite := (cubicTheta_compact_translates_locallyFinite ψ.hasCompactSupport).point_finite p
  let A := hS.toFinset
  have ht : Function.support (fun g => cubicThetaPoincareTerm ψ g p)⊆A := by
    intro g hg
    apply hS.mem_toFinset.mpr
    apply subset_tsupport ψ
    intro hz
    exact hg (by simp only [cubicThetaPoincareTerm,hz,mul_zero])
  have hu : Function.support (fun g : cubicThetaPrincipalGroup => star (ψ (g • p))*F.val (g • p))⊆A := by
    intro g hg
    apply hS.mem_toFinset.mpr
    apply subset_tsupport ψ
    intro hz
    exact hg (by simp only [hz,star_zero,zero_mul])
  rw [cubicThetaSectionPairing_apply,RCLike.inner_apply,mul_comm]
  change star (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)*F.val p=_
  rw [finsum_eq_sum_of_support_subset _ ht,tsum_eq_sum (fun b hb => by by_contra hn; exact hb (hu hn)),star_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g hg
  rw [F.property g p]
  simp only [cubicThetaPoincareTerm,star_mul,star_star]
  ring

end CubicFirstMoment

end

end OAI
