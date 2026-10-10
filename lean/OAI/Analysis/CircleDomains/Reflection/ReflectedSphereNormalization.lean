import OAI.Analysis.CircleDomains.Reflection.ReflectedLimitHolomorphic
import OAI.Analysis.CircleDomains.Topology.PlaneHomeomorphFromSphere
import OAI.Analysis.CircleDomains.Modulus.MobiusNormalization

namespace OAI

/-! Normalize the pole of the actual conjugated reflection to infinity.
The result is an actual plane homeomorphism. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

def reflectedSphere (D : AnalyticReflectionData C) (i : I) : Sphere ≃ₜ Sphere :=
  D.principal.onePointCongr.symm.trans
    ((roundDiskReflection (D.center i) (D.radius i) (D.radius_pos i)).trans
      (D.principal.onePointCongr.trans Complex.conjCLE.toHomeomorph.onePointCongr))

lemma reflectedSphere_pole (D : AnalyticReflectionData C) (i : I) :
    D.reflectedSphere i (D.principal (D.center i) : Sphere)=OnePoint.infty := by
  change Complex.conjCLE.toHomeomorph.onePointCongr (D.principal.onePointCongr
    (roundDiskReflection (D.center i) (D.radius i) (D.radius_pos i)
      (D.principal.onePointCongr.symm (D.principal (D.center i) : Sphere))))=_
  change Complex.conjCLE.toHomeomorph.onePointCongr (D.principal.onePointCongr
    (roundDiskReflection (D.center i) (D.radius i) (D.radius_pos i)
      (D.principal.symm (D.principal (D.center i)) : Sphere)))=_
  rw [D.principal.symm_apply_apply,roundDiskReflection_center]
  rfl

lemma reflectedSphere_infty (D : AnalyticReflectionData C) (i : I) :
    D.reflectedSphere i OnePoint.infty=(star (D.principal (D.center i)) : ℂ) := by
  change Complex.conjCLE.toHomeomorph.onePointCongr (D.principal.onePointCongr
    (roundDiskReflection (D.center i) (D.radius i) (D.radius_pos i) OnePoint.infty))=_
  rw [roundDiskReflection_infty]
  rfl

lemma reflectedSphere_coe (D : AnalyticReflectionData C) (i : I) {z : ℂ}
    (hz : z≠D.principal (D.center i)) :
    D.reflectedSphere i (z : Sphere)=(D.reflectedLimit i z : Sphere) := by
  have hi : D.principal.symm z≠D.center i := by
    intro h
    exact hz ((D.principal.apply_symm_apply z).symm.trans (congrArg D.principal h))
  change Complex.conjCLE.toHomeomorph.onePointCongr (D.principal.onePointCongr
    (roundDiskReflection (D.center i) (D.radius i) (D.radius_pos i)
      (D.principal.symm z : Sphere)))=_
  rw [roundDiskReflection_coe (D.center i) (D.radius_pos i) hi]
  rfl

def poleParameter (D : AnalyticReflectionData C) (i : I) : Sphere ≃ₜ Sphere :=
  CannonMobius.inversion.trans (affineSphere 1 (D.principal (D.center i)) one_ne_zero)

lemma poleParameter_infty (D : AnalyticReflectionData C) (i : I) :
    D.poleParameter i OnePoint.infty=(D.principal (D.center i) : Sphere) := by
  change affineSphere 1 _ one_ne_zero (CannonMobius.inversion OnePoint.infty)=_
  rw [show CannonMobius.inversion OnePoint.infty=(0:ℂ) from CannonMobius.inv_infty,affineSphere_coe]
  simp

lemma poleParameter_zero (D : AnalyticReflectionData C) (i : I) :
    D.poleParameter i (0:ℂ)=OnePoint.infty := by
  change affineSphere 1 _ one_ne_zero (CannonMobius.inversion (0:ℂ))=_
  rw [show CannonMobius.inversion (0:ℂ)=OnePoint.infty from CannonMobius.inv_zero]
  rfl

lemma poleParameter_coe (D : AnalyticReflectionData C) (i : I) {z : ℂ} (hz : z≠0) :
    D.poleParameter i (z : Sphere)=(D.principal (D.center i)+z⁻¹ : ℂ) := by
  change affineSphere 1 _ one_ne_zero (CannonMobius.inversion (z : Sphere))=_
  rw [show CannonMobius.inversion (z : Sphere)=(z⁻¹ : ℂ) from CannonMobius.inv_coe hz,
    affineSphere_coe]
  simp [add_comm]

lemma poleNormalized_fixes_infty (D : AnalyticReflectionData C) (i : I) :
    (D.poleParameter i |>.trans (D.reflectedSphere i)) OnePoint.infty=OnePoint.infty := by
  change D.reflectedSphere i (D.poleParameter i OnePoint.infty)=_
  rw [D.poleParameter_infty,D.reflectedSphere_pole]

def poleNormalized (D : AnalyticReflectionData C) (i : I) : ℂ ≃ₜ ℂ :=
  spherePlaneHomeomorph ((D.poleParameter i).trans (D.reflectedSphere i))
    (D.poleNormalized_fixes_infty i)

lemma poleNormalized_zero (D : AnalyticReflectionData C) (i : I) :
    D.poleNormalized i 0=star (D.principal (D.center i)) := by
  apply OnePoint.coe_injective
  rw [show (D.poleNormalized i 0 : Sphere)=D.reflectedSphere i (D.poleParameter i (0:ℂ)) from
    coe_spherePlaneMap _ (D.poleNormalized_fixes_infty i) 0,D.poleParameter_zero,D.reflectedSphere_infty]

lemma poleNormalized_coe (D : AnalyticReflectionData C) (i : I) {z : ℂ} (hz : z≠0) :
    D.poleNormalized i z=D.reflectedLimit i (D.principal (D.center i)+z⁻¹) := by
  apply OnePoint.coe_injective
  rw [show (D.poleNormalized i z : Sphere)=D.reflectedSphere i (D.poleParameter i (z : Sphere)) from
    coe_spherePlaneMap _ (D.poleNormalized_fixes_infty i) z,D.poleParameter_coe i hz,D.reflectedSphere_coe i]
  exact add_ne_left.mpr (inv_ne_zero hz)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
