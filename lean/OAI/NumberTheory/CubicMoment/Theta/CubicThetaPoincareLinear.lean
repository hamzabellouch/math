import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateSectionSupport

namespace OAI

/-! Finite-support additivity of the actual periodization. -/
noncomputable section
open Set
open scoped BigOperators CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoincareSection_sub (ψ φ : C_c(CubicThetaPoint,ℂ)) :
    cubicThetaPoincareSection (ψ-φ)=cubicThetaPoincareSection ψ-cubicThetaPoincareSection φ := by
  ext p
  change (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm (ψ-φ) g p)=
    (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)-
      ∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm φ g p
  have h (g : cubicThetaPrincipalGroup) : cubicThetaPoincareTerm (ψ-φ) g p=
      cubicThetaPoincareTerm ψ g p-cubicThetaPoincareTerm φ g p := by
    change star (cubicThetaKubotaValue g)*(ψ (g • p)-φ (g • p))=_
    exact mul_sub _ _ _
  simp_rw [h]
  exact finsum_sub_distrib (cubicThetaPoincareTerm_locallyFinite ψ |>.point_finite p)
    (cubicThetaPoincareTerm_locallyFinite φ |>.point_finite p)

end CubicFirstMoment

end

end OAI
