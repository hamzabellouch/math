import Mathlib
import OAI.Geometry.Cannon.Conformal.AffineRegion
import OAI.Geometry.Cannon.Modulus.CompleteSquare

namespace OAI

section
noncomputable section
namespace CannonMobius
open Set Metric Topology CannonGeneralizedDisk
open scoped OnePoint

lemma closure_coe_ball (a : ℂ) {r : ℝ} (hr : 0<r) :
    closure ((↑) '' ball a r : Set Sphere)=(↑) '' closedBall a r := by
  apply subset_antisymm
  · exact closure_minimal (image_mono ball_subset_closedBall)
      (((isCompact_closedBall a r).image OnePoint.continuous_coe).isClosed)
  · rw [←closure_ball a hr.ne']
    exact image_closure_subset_closure_image OnePoint.continuous_coe

theorem biholomorphic_finite_disk (N : Sphere ≃ₜ Sphere) (hN : N∈biholomorphic)
    (a : ℂ) {r : ℝ} (hr : 0<r)
    (hpole : ∞∉N '' ((↑) '' closedBall a r : Set Sphere)) :
    ∃ a' : ℂ,∃ r' : ℝ,0<r' ∧
      N '' ((↑) '' ball a r : Set Sphere)=((↑) '' ball a' r' : Set Sphere) ∧
      N '' ((↑) '' closedBall a r : Set Sphere)=((↑) '' closedBall a' r' : Set Sphere) := by
  have hq : 0<(disk a r).discr:=by rw [disk_discr]; exact sq_pos_of_pos hr
  have hfinite : ∃ q' : Quad,0<q'.A ∧ 0<q'.discr ∧
      N '' (disk a r).region=q'.region := by
    rcases biholomorphic_normal_form N hN with ⟨α,β,hα,rfl⟩|⟨p,α,β,hα,rfl⟩
    · refine ⟨(disk a r).affine α β,by norm_num [Quad.affine,disk],?_,
        affine_region _ α β hα⟩
      rw [Quad.affine_discr]
      exact mul_pos (Complex.normSq_pos.mpr hα) hq
    · let w : ℂ:=-β/α
      have hw : α*w+β=0 := by
        dsimp only [w]
        rw [mul_div_cancel₀ (-β) hα,neg_add_cancel]
      have hmap : (affine 1 p one_ne_zero*inversion*affine α β hα) (w:Sphere)=∞ := by
        change affine 1 p one_ne_zero (inv (affine α β hα (w:Sphere)))=∞
        rw [affine_coe,hw,inv_zero,affine_infty]
      have hwr : r<dist w a := by
        by_contra hn
        exact hpole ⟨(w:Sphere),⟨w,mem_closedBall.mpr (le_of_not_gt hn),rfl⟩,hmap⟩
      have hval : 0<(disk a r).value w := by
        rw [disk_value]
        nlinarith [dist_nonneg (x:=w) (y:=a)]
      have hC : 0<((disk a r).affine α β).C := by
        have he:=Quad.affine_value (disk a r) α β w
        rw [hw] at he
        have he' : ((disk a r).affine α β).C=Complex.normSq α*(disk a r).value w := by
          simpa [Quad.value] using he
        rw [he']
        exact mul_pos (Complex.normSq_pos.mpr hα) hval
      refine ⟨((disk a r).affine α β).inv.affine 1 p,hC,?_,?_⟩
      · rw [Quad.affine_discr,Quad.inv_discr,Quad.affine_discr]
        simpa only [Complex.normSq_one,one_mul] using
          mul_pos (Complex.normSq_pos.mpr hα) hq
      · rw [←affine_region ((disk a r).affine α β).inv 1 p one_ne_zero,
          ←inversion_region ((disk a r).affine α β),←affine_region (disk a r) α β hα]
        rw [Set.image_image,Set.image_image]
        rfl
  obtain ⟨q',hA,hq',he⟩:=hfinite
  obtain ⟨a',r',hr',hreg⟩:=q'.finite_disk hA hq'
  rw [disk_region a hr,hreg] at he
  refine ⟨a',r',hr',he,?_⟩
  rw [←closure_coe_ball a hr,←closure_coe_ball a' hr',N.image_closure,he]

end CannonMobius

end
end

end OAI
