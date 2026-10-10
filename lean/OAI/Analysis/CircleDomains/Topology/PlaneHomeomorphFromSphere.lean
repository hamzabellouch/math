import OAI.Analysis.CircleDomains.Topology.PrincipalSphereCharts
import OAI.Analysis.CircleDomains.Modulus.SphericalChartCost

namespace OAI

/-! Restrict an actual sphere homeomorphism fixing infinity to its finite
plane chart. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def spherePlaneMap (e : Sphere ≃ₜ Sphere) (_he : e OnePoint.infty=OnePoint.infty) (z : ℂ) : ℂ :=
  finiteCoord (e (z : Sphere))

lemma spherePlaneMap_finite (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty=OnePoint.infty) (z : ℂ) :
    e (z : Sphere)≠OnePoint.infty := by
  intro h
  exact OnePoint.coe_ne_infty z (e.injective (h.trans he.symm))

lemma coe_spherePlaneMap (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty=OnePoint.infty) (z : ℂ) :
    (spherePlaneMap e he z : Sphere)=e (z : Sphere) :=
  CannonMobius.coe_coordinate (spherePlaneMap_finite e he z)

lemma spherePlaneMap_continuous (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty=OnePoint.infty) :
    Continuous (spherePlaneMap e he) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (CannonMobius.continuousAt_coordinate (spherePlaneMap_finite e he z)).comp_of_eq
    ((e.continuous.comp OnePoint.continuous_coe).continuousAt) rfl

lemma sphereHomeomorph_symm_infty (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty=OnePoint.infty) :
    e.symm OnePoint.infty=OnePoint.infty := by
  apply e.injective
  rw [e.apply_symm_apply,he]

def spherePlaneHomeomorph (e : Sphere ≃ₜ Sphere) (he : e OnePoint.infty=OnePoint.infty) : ℂ ≃ₜ ℂ where
  toFun := spherePlaneMap e he
  invFun := spherePlaneMap e.symm (sphereHomeomorph_symm_infty e he)
  left_inv := by
    intro z
    apply OnePoint.coe_injective
    rw [coe_spherePlaneMap,coe_spherePlaneMap,e.symm_apply_apply]
  right_inv := by
    intro z
    apply OnePoint.coe_injective
    rw [coe_spherePlaneMap,coe_spherePlaneMap,e.apply_symm_apply]
  continuous_toFun := spherePlaneMap_continuous e he
  continuous_invFun := spherePlaneMap_continuous e.symm _

end CircleDomainRigidity

end

end OAI
