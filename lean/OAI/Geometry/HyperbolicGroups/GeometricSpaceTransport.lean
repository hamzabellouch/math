import Mathlib
import OAI.Geometry.HyperbolicGroups.Basic

namespace OAI

section


/-! Isometric transport of the literal CAT(0) comparison and geometric actions,
including the universe lift required by the unchanged main statement. -/
noncomputable section
open Set
namespace HyperbolicObstruction
universe u v w
variable {X : Type v} {Y : Type w} [MetricSpace X] [MetricSpace Y]

lemma CATZero.of_isometryEquiv (e : X ≃ᵢ Y) (h : CATZero Y) : CATZero X := by
  intro x y
  obtain ⟨γ,hγ,hcmp⟩:=h (e x) (e y)
  refine ⟨fun t => e.symm (γ t),⟨?_,?_,?_⟩,?_⟩
  · change e.symm (γ 0)=x
    rw [hγ.1,e.symm_apply_apply]
  · change e.symm (γ 1)=y
    rw [hγ.2.1,e.symm_apply_apply]
  · intro s hs t ht
    rw [e.symm.dist_eq,hγ.2.2 s hs t ht,e.dist_eq]
  · intro z t ht
    have hh:=hcmp (e z) t ht
    rw [e.dist_eq,e.dist_eq,e.dist_eq] at hh
    rwa [←e.dist_eq z (e.symm (γ t)),e.apply_symm_apply]

namespace GeometricAction
variable {G : Type*} [Group G]

def spaceTransport (e : X ≃ᵢ Y) (A : GeometricAction G Y) : GeometricAction G X where
  act := {
    toFun := fun g => (e.trans (A.act g)).trans e.symm
    map_one' := by
      apply IsometryEquiv.ext
      intro x
      simp
    map_mul' := by
      intro a b
      apply IsometryEquiv.ext
      intro x
      simp [IsometryEquiv.mul_apply] }
  proper C hC := by
    apply (A.proper (e '' C) (hC.image e.continuous)).subset
    rintro g ⟨x,hx,hgx⟩
    refine ⟨e x,mem_image_of_mem e hx,?_⟩
    refine ⟨e.symm (A.act g (e x)),hgx,?_⟩
    exact e.apply_symm_apply _
  cocompact := by
    obtain ⟨C,hC,hcover⟩:=A.cocompact
    refine ⟨e.symm '' C,hC.image e.symm.continuous,?_⟩
    intro x
    obtain ⟨g,y,hy,hgy⟩:=hcover (e x)
    refine ⟨g,e.symm y,mem_image_of_mem e.symm hy,?_⟩
    change e.symm (A.act g (e (e.symm y)))=x
    rw [e.apply_symm_apply,hgy,e.symm_apply_apply]
end GeometricAction

def uliftIsometry (X : Type v) [MetricSpace X] : ULift.{u} X ≃ᵢ X where
  toEquiv := Equiv.ulift
  isometry_toFun := Isometry.of_dist_eq (fun _ _ => rfl)

lemma ulift_proper [ProperSpace X] : ProperSpace (ULift.{u} X) :=
  (uliftIsometry X).symm.isometry.antilipschitzWith.properSpace
    (uliftIsometry X).symm.continuous (uliftIsometry X).symm.surjective

end HyperbolicObstruction
end
end

section

end

end OAI
