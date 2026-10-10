import Mathlib
import OAI.Geometry.Cannon.Conformal.ClosureCoeBall
import OAI.Geometry.Cannon.Modulus.TangentDiskMeet

namespace OAI

section
noncomputable section
namespace CannonMobius
open Set Metric Topology CannonTileTopology
open scoped OnePoint

theorem finite_packing_at_vertex {ν : Type*} (z : ν → ℂ) (r : ν → ℝ)
    (hr : ∀ j,0<r j) (hsep : ∀ i j,i≠j → r i+r j≤dist (z i) (z j))
    (N : Sphere ≃ₜ Sphere) (hN : N∈biholomorphic) (pole : ν)
    (hpole : N (z pole:Sphere)=∞) :
    ∃ c : {j : ν // j≠pole} → ℂ,∃ t : {j : ν // j≠pole} → ℝ,
      (∀ j,0<t j) ∧
      (∀ j,N '' ((↑) '' ball (z j.val) (r j.val) : Set Sphere)=(↑) '' ball (c j) (t j)) ∧
      (∀ j,N '' ((↑) '' closedBall (z j.val) (r j.val) : Set Sphere)=(↑) '' closedBall (c j) (t j)) ∧
      Pairwise (fun i j=>Disjoint (ball (c i) (t i)) (ball (c j) (t j))) := by
  have hex (j : {j : ν // j≠pole}) : ∃ c : ℂ,∃ t : ℝ,0<t ∧
      N '' ((↑) '' ball (z j.val) (r j.val) : Set Sphere)=(↑) '' ball c t ∧
      N '' ((↑) '' closedBall (z j.val) (r j.val) : Set Sphere)=(↑) '' closedBall c t := by
    apply biholomorphic_finite_disk N hN (z j.val) (hr j.val)
    rintro ⟨p,⟨q,hq,rfl⟩,hep⟩
    have hqpole : q=z pole:=OnePoint.coe_injective (N.injective (hep.trans hpole.symm))
    subst q
    have hs:=hsep pole j.val j.property.symm
    have hq':=mem_closedBall.mp hq
    linarith [hr pole]
  choose c t ht hb hc using hex
  refine ⟨c,t,ht,hb,hc,?_⟩
  intro i j hij
  have hn : i.val≠j.val:=fun h=>hij (Subtype.ext h)
  have hd:=packing_balls_disjoint z r hsep hn
  have hd':=hd.image OnePoint.coe_injective.injOn (subset_univ _) (subset_univ _)
  have hd'':=hd'.image N.injective.injOn (subset_univ _) (subset_univ _)
  rw [hb i,hb j] at hd''
  exact hd''.of_image
end CannonMobius

end
end

end OAI
