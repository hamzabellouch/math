import Mathlib
import OAI.Geometry.Cannon.Conformal.AnalyticFixInftyAffine
import OAI.Geometry.Cannon.Modulus.Quad

namespace OAI

section
noncomputable section
namespace CannonMobius
open Set Metric Topology CannonGeneralizedDisk
open scoped OnePoint

lemma affine_region (q : Quad) (a b : ℂ) (ha : a≠0) :
    affine a b ha '' q.region=(q.affine a b).region := by
  have hf (p : Sphere) : affine a b ha p∈(q.affine a b).region ↔ p∈q.region := by
    induction p using OnePoint.rec with
    | infty => simp only [affine_infty,Quad.mem_region_infty,Quad.affine]
    | coe z => simpa only [affine_coe,Quad.mem_region_coe] using q.affine_mem_iff a b ha z
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact (hf p).mpr hp
  · intro hx
    refine ⟨(affine a b ha).symm x,?_,(affine a b ha).apply_symm_apply x⟩
    apply (hf _).mp
    simpa only [Homeomorph.apply_symm_apply] using hx

lemma inversion_region (q : Quad) : inversion '' q.region=q.inv.region := by
  have hf (p : Sphere) : inversion p∈q.inv.region ↔ p∈q.region := by
    induction p using OnePoint.rec with
    | infty =>
      change q.inv.value 0<0 ↔ q.A<0
      simp [Quad.value,Quad.inv]
    | coe z =>
      by_cases hz : z=0
      · subst z
        change inv ((0:ℂ):Sphere)∈q.inv.region ↔ ((0:ℂ):Sphere)∈q.region
        rw [inv_zero]
        simp [Quad.region,Quad.value,Quad.inv]
      · simpa only [show inversion (z:Sphere)=(z⁻¹:ℂ) from inv_coe hz,
          Quad.mem_region_coe] using q.inv_mem_iff hz
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact (hf p).mpr hp
  · intro hx
    refine ⟨inversion.symm x,?_,inversion.apply_symm_apply x⟩
    apply (hf _).mp
    simpa only [Homeomorph.apply_symm_apply] using hx

theorem biholomorphic_region (N : Sphere ≃ₜ Sphere) (hN : N∈biholomorphic)
    (q : Quad) (hq : 0<q.discr) :
    ∃ q' : Quad,0<q'.discr ∧ N '' q.region=q'.region := by
  rcases biholomorphic_normal_form N hN with ⟨a,b,ha,rfl⟩|⟨p,a,b,ha,rfl⟩
  · refine ⟨q.affine a b,?_,affine_region q a b ha⟩
    rw [Quad.affine_discr]
    exact mul_pos (Complex.normSq_pos.mpr ha) hq
  · refine ⟨(q.affine a b).inv.affine 1 p,?_,?_⟩
    · rw [Quad.affine_discr,Quad.inv_discr,Quad.affine_discr]
      simpa only [Complex.normSq_one,one_mul] using mul_pos (Complex.normSq_pos.mpr ha) hq
    · rw [←affine_region (q.affine a b).inv 1 p one_ne_zero,
        ←inversion_region (q.affine a b),←affine_region q a b ha]
      rw [Set.image_image,Set.image_image]
      rfl

end CannonMobius

end
end

end OAI
