import Mathlib
import OAI.Geometry.Cannon.Conformal.SphereTile

namespace OAI

section
section
section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

theorem normalize_packing_centers {ν : Type*}
    (z : ν → ℂ) (r : ν → ℝ) (hr : ∀ v,0<r v)
    (hsep : ∀ u v,u≠v → r u+r v≤dist (z u) (z v))
    (b : Fin 3 → ν) (hb : Function.Injective b) :
    ∃ N : Sphere ≃ₜ Sphere,N∈biholomorphic ∧
      (∀ i,N ((z (b i):ℂ):Sphere)=std i) ∧
      (∀ v,IsOpen (N '' ((↑) '' ball (z v) (r v) : Set Sphere))) ∧
      Pairwise (fun u v=>Disjoint (N '' ((↑) '' ball (z u) (r u) : Set Sphere))
        (N '' ((↑) '' ball (z v) (r v) : Set Sphere))) ∧
      (∀ v,∃ i j : Fin 3,i≠j ∧
        std i∉N '' ((↑) '' ball (z v) (r v) : Set Sphere) ∧
        std j∉N '' ((↑) '' ball (z v) (r v) : Set Sphere)) := by
  have hz : Function.Injective z := by
    intro u v huv
    by_contra hne
    have hh:=hsep u v hne
    rw [huv,dist_self] at hh
    linarith [hr u,hr v]
  let t : Triple:=⟨fun i=>(z (b i):Sphere),OnePoint.coe_injective.comp (hz.comp hb)⟩
  obtain ⟨M,hM,hMt⟩:=exists_triple_normalizer t
  let N : Sphere ≃ₜ Sphere:=M.symm
  have hN (i : Fin 3) : N (z (b i):Sphere)=std i := by
    have H : M (std i)=(z (b i):Sphere):=congrArg (fun t : Triple=>t.val i) hMt
    dsimp only [N]
    rw [←H,M.symm_apply_apply]
  have hout {v : ν} {i : Fin 3} (hi : b i≠v) :
      std i∉N '' ((↑) '' ball (z v) (r v) : Set Sphere) := by
    rintro ⟨_,⟨w,hw,rfl⟩,hew⟩
    have hcoe : (w:Sphere)=(z (b i):Sphere):=N.injective (hew.trans (hN i).symm)
    have hew : w=z (b i):=OnePoint.coe_injective hcoe
    rw [hew] at hw
    have hh:=hsep (b i) v hi
    have hh':=mem_ball.mp hw
    linarith [hr (b i)]
  refine ⟨N,biholomorphic.inv_mem hM,hN,?_,?_,?_⟩
  · intro v
    exact N.isOpenMap _ (OnePoint.isOpenMap_coe _ isOpen_ball)
  · intro u v huv
    apply disjoint_left.mpr
    rintro q ⟨_,⟨w,hwu,rfl⟩,hwq⟩ ⟨_,⟨w',hwv,rfl⟩,hwq'⟩
    have heq : w=w' := OnePoint.coe_injective (N.injective (hwq.trans hwq'.symm))
    subst w'
    have h1:=mem_ball.mp hwu
    have h2:=mem_ball.mp hwv
    have ht:=dist_triangle (z u) w (z v)
    rw [dist_comm (z u) w] at ht
    have hh:=hsep u v huv
    linarith
  · intro v
    have hx : ∃ i j : Fin 3,i≠j ∧ b i≠v ∧ b j≠v := by
      by_cases h0 : b 0=v
      · refine ⟨1,2,by decide,?_,?_⟩ <;> intro h
        · have hh:=hb (h.trans h0.symm)
          exact (by decide : (1:Fin 3)≠0) hh
        · have hh:=hb (h.trans h0.symm)
          exact (by decide : (2:Fin 3)≠0) hh
      · by_cases h1 : b 1=v
        · refine ⟨0,2,by decide,h0,?_⟩
          intro h
          have hh:=hb (h.trans h1.symm)
          exact (by decide : (2:Fin 3)≠1) hh
        · exact ⟨0,1,by decide,h0,h1⟩
    obtain ⟨i,j,hij,hi,hj⟩:=hx
    exact ⟨i,j,hij,hout hi,hout hj⟩
end CannonMobius

end
end
end
end

end OAI
