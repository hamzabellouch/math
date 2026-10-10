import Mathlib
import OAI.Geometry.Cannon.Modulus.Ambient
import OAI.Geometry.Cannon.Conformal.Chart
import OAI.Geometry.Cannon.Modulus.SqDiffNormDiff

namespace OAI

section
noncomputable section
namespace CannonRadialWitness
open Set Metric Topology CannonMobius
open scoped OnePoint

lemma trace_preconnected {S : Set Sphere} (hS : IsPreconnected S) (hinf : ∞∉S) :
    IsPreconnected (((↑) : ℂ → Sphere) ⁻¹' S) := by
  apply OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
  have he : ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' S)=S := by
    apply image_preimage_eq_of_subset
    intro y hy
    exact OnePoint.ne_infty_iff_exists.mp (fun he=>hinf (he ▸ hy))
  rwa [he]

theorem spherical_two_center_band {S : Set Sphere} (hS : IsPreconnected S)
    {x p q : ℂ} {y : Sphere} (hx : (x:Sphere)∈S) (hy : y∈S)
    {R η : ℝ} (hR : 0<R) (hpq : dist p q=R) (hxp : dist x p≤R)
    (hη : 0≤η) (hη1 : η≤1) (hxy : 102*η*R^2<dist (x:Sphere) y^2) :
    ∃ c : ℂ,(c=p ∨ c=q) ∧ ∃ a b : ℝ,0≤a ∧ a≤b ∧ b≤3*R ∧ b-a=η*R ∧
      ∃ u∈S,∃ v∈S,u∈((↑) '' closedBall c a : Set Sphere) ∧
        v∉((↑) '' ball c b : Set Sphere) := by
  by_cases hinf : ∞∈S
  · refine ⟨p,Or.inl rfl,R,R+η*R,hR.le,?_,?_,by ring,(x:Sphere),hx,∞,hinf,⟨x,hxp,rfl⟩,?_⟩
    · nlinarith
    · nlinarith
    · rintro ⟨z,_hz,he⟩
      exact OnePoint.coe_ne_infty z he
  · obtain ⟨y',rfl⟩:=OnePoint.ne_infty_iff_exists.mp (show y≠∞ from fun he=>hinf (he ▸ hy))
    have hxy' : 102*η*R^2<dist x y'^2 := by
      apply hxy.trans_le
      exact pow_le_pow_left₀ dist_nonneg (coe_dist_le x y') 2
    obtain ⟨c,hc,a,b,ha,hab,hb,hw,u,hu,v,hv,hu',hv'⟩:=two_center_band_scaled
      (trace_preconnected hS hinf) hx hy hR hpq hxp hη hη1 hxy'
    refine ⟨c,hc,a,b,ha,hab,hb,hw,(u:Sphere),hu,(v:Sphere),hv,⟨u,hu',rfl⟩,?_⟩
    rintro ⟨z,hz,hez⟩
    have hzv : z=v:=OnePoint.coe_injective hez
    subst z
    exact not_lt_of_ge hv' hz

lemma continuum_point_at_radius {S : Set Sphere} (hS : IsPreconnected S)
    {p : ℂ} (hp : (p:Sphere)∈S) (hinf : ∞∈S) {R : ℝ} (hR : 0≤R) :
    ∃ q : ℂ,(q:Sphere)∈S ∧ dist p q=R := by
  let f : C(Sphere,Sphere):=ContinuousMap.id Sphere
  have h1 : f (p:Sphere)∈((↑) '' closedBall p R : Set Sphere):=⟨p,mem_closedBall_self hR,rfl⟩
  have h2 : f ∞∉((↑) '' ball p R : Set Sphere) := by
    rintro ⟨z,_hz,he⟩
    exact OnePoint.coe_ne_infty z he
  obtain ⟨x,hx,z,hz,hzx⟩:=CannonCarrierCharging.spherical_radial_level_preimage f S hS p hp hinf h1 h2 R ⟨le_rfl,le_rfl⟩
  refine ⟨z,?_,?_⟩
  · exact hzx ▸ hx
  · simpa only [mem_sphere,dist_comm] using hz
end CannonRadialWitness

end
end

end OAI
