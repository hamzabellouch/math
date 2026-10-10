import Mathlib
import OAI.Geometry.SplitTangent.HolomorphicTangentMapAt
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.RationalCoverLift

namespace OAI

/-! Positive Cover Lift. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent
variable {X Y : ComplexManifold.{u}} {p : Y.Carrier → X.Carrier}

 
def coverTangentLift
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    (y : Y.Carrier) : Tangent X (p y) →L[ℂ] Tangent Y y :=
  ((hp y).mfderivToContinuousLinearEquiv (by simp)).symm.toContinuousLinearMap

lemma coverTangentLift_leftInverse
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    (y : Y.Carrier) (v : Tangent Y y) :
    coverTangentLift hp y (mfderiv (ModelWithCorners Y) (ModelWithCorners X) p y v)=v :=
  ((hp y).mfderivToContinuousLinearEquiv (by simp)).symm_apply_apply v

lemma coverTangentLift_eq_localInverse
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    (y z : Y.Carrier) (hz : z∈(hp y).localInverse.target) (v : Tangent X (p z)) :
    coverTangentLift hp z v=
      mfderiv (ModelWithCorners X) (ModelWithCorners Y) (hp y).localInverse (p z) v := by
  let h := hp y
  have hps : p z∈h.localInverse.source := by
    rw [h.choose_spec.2 hz]
    exact h.choose.map_source hz
  have hdi := (h.localInverse_contMDiffOn.contMDiffAt
    (h.localInverse.open_source.mem_nhds hps)).mdifferentiableAt (by simp)
  have he : h.localInverse ∘ p =ᶠ[𝓝 z] id :=
    Filter.eventuallyEq_of_mem (h.localInverse.open_target.mem_nhds hz)
      h.localInverse_eqOn_left
  have hd := mfderiv_comp z hdi ((hp z).mdifferentiableAt (by simp))
  rw [he.mfderiv_eq,mfderiv_id] at hd
  let C := (hp z).mfderivToContinuousLinearEquiv (by simp)
  have hh := DFunLike.congr_fun hd (C.symm v)
  change C.symm v=mfderiv (ModelWithCorners X) (ModelWithCorners Y)
    h.localInverse (p z) (C (C.symm v)) at hh
  change C.symm v=mfderiv (ModelWithCorners X) (ModelWithCorners Y)
    h.localInverse (p z) v
  simpa only [C.apply_symm_apply] using hh

lemma coverTangentLift_holomorphic
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    {g : ℂ → Y.Carrier} {σ : ∀t,Tangent X (p (g t))}
    (hg : Continuous g)
    (hσ : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun t => (⟨p (g t),σ t⟩ : TangentBundle (ModelWithCorners X) X.Carrier))) :
    ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners Y).prod 𝓘(ℂ,Model Y)) ω
      (fun t => (⟨g t,coverTangentLift hp (g t) (σ t)⟩ :
        TangentBundle (ModelWithCorners Y) Y.Carrier)) := by
  intro t
  have hh := (holomorphicAt_tangentMap
    (hp (g t)).localInverse_contMDiffAt (σ t)).comp t (hσ t)
  apply hh.congr_of_eventuallyEq
  filter_upwards [hg.continuousAt.preimage_mem_nhds
    ((hp (g t)).localInverse.open_target.mem_nhds
      (hp (g t)).localInverse_mem_target)] with w hw
  exact Bundle.TotalSpace.ext ((hp (g t)).localInverse_left_inv hw).symm
    (heq_of_eq (coverTangentLift_eq_localInverse hp (g t) (g w) hw (σ w)))

namespace RationalCurve
variable {g : RationalCurve X} {k : RationalCurve Y}
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    (hf : ∀z,p (k.finite z)=g.finite z) (hi : ∀z,p (k.infinity z)=g.infinity z)

def coverSection (σ : CurveTangentSection g) : CurveTangentSection k where
  finite z := coverTangentLift hp (k.finite z) (σ.finite z)
  infinity z := coverTangentLift hp (k.infinity z) (σ.infinity z)
  finite_holomorphic := coverTangentLift_holomorphic hp k.finite_holomorphic.continuous
    (by
      have he : (fun t => (⟨p (k.finite t),σ.finite t⟩ :
          TangentBundle (ModelWithCorners X) X.Carrier))=
          (fun t => (⟨g.finite t,σ.finite t⟩ :
          TangentBundle (ModelWithCorners X) X.Carrier)) := by
        funext t
        exact Bundle.TotalSpace.ext (hf t) (heq_of_eq rfl)
      rw [he]
      exact σ.finite_holomorphic)
  infinity_holomorphic := coverTangentLift_holomorphic hp k.infinity_holomorphic.continuous
    (by
      have he : (fun t => (⟨p (k.infinity t),σ.infinity t⟩ :
          TangentBundle (ModelWithCorners X) X.Carrier))=
          (fun t => (⟨g.infinity t,σ.infinity t⟩ :
          TangentBundle (ModelWithCorners X) X.Carrier)) := by
        funext t
        exact Bundle.TotalSpace.ext (hi t) (heq_of_eq rfl)
      rw [he]
      exact σ.infinity_holomorphic)
  overlap z hz := by rw [k.overlap z hz,σ.overlap z hz]

include hp hf hi in
 
theorem pointedGenerated_cover_lift (hg : PointedGenerated g (fun _ => ⊤)) :
    PointedGenerated k (fun _ => ⊤) := by
  intro v hv
  let D := mfderiv (ModelWithCorners Y) (ModelWithCorners X) p (k.finite 1)
  obtain ⟨σ,_,_,h0,h1⟩ := hg (D v) Submodule.mem_top
  refine ⟨coverSection hp hf hi σ,fun _ => Submodule.mem_top,
    fun _ => Submodule.mem_top,?_,?_⟩
  · change coverTangentLift hp (k.finite 0) (σ.finite 0)=0
    erw [h0,map_zero]
  · change coverTangentLift hp (k.finite 1) (σ.finite 1)=v
    rw [h1]
    exact coverTangentLift_leftInverse hp (k.finite 1) v

 

theorem exists_positive_cover_lift
    (g : RationalCurve X) (hg : PointedGenerated g (fun _ => ⊤))
    (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    (y : Y.Carrier) (hy : p y=g.finite 0) :
    ∃k : RationalCurve Y,k.finite 0=y ∧ PointedGenerated k (fun _ => ⊤) ∧
      (∀z,p (k.finite z)=g.finite z) ∧ (∀z,p (k.infinity z)=g.infinity z) := by
  obtain ⟨k,hk,hf,hi⟩ := g.exists_cover_lift hcover hp y hy
  exact ⟨k,hk,pointedGenerated_cover_lift hp hf hi hg,hf,hi⟩

 

theorem exists_positive_cover_lift_at
    (g : RationalCurve X) (hg : PointedGenerated g (fun _ => ⊤))
    (hcover : IsCoveringMap p)
    (hp : IsLocalDiffeomorph (ModelWithCorners Y) (ModelWithCorners X) ω p)
    (a : ℂ) (y : Y.Carrier) (hy : p y=g.finite a) :
    ∃k : RationalCurve Y,k.finite a=y ∧ PointedGenerated k (fun _ => ⊤) ∧
      (∀z,p (k.finite z)=g.finite z) ∧ (∀z,p (k.infinity z)=g.infinity z) := by
  obtain ⟨k,hk,hf,hi⟩ := g.exists_cover_lift_at hcover hp a y hy
  exact ⟨k,hk,pointedGenerated_cover_lift hp hf hi hg,hf,hi⟩

end RationalCurve
end SplitTangent

end

end OAI
