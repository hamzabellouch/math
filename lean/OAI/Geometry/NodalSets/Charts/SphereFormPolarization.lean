import OAI.Geometry.NodalSets.Spectral.SphereWeakResolvent

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section

lemma symmetric_additive_polarization {V : Type*} [Add V] (B : V → V → ℝ)
    (hs : ∀ u v, B u v=B v u) (ha : ∀ u v w, B (u+v) w=B u w+B v w)
    (u v : V) : (B (u+v) (u+v)-B u u-B v v)/2=B u v := by
  rw [ha u v (u+v),hs u (u+v),hs v (u+v),ha u v u,ha u v v,hs v u]
  ring

lemma sphereDirichletForm_polarization (d : SphereEnergyData) (u v : sphereSmoothFunctions) :
    (sphereDirichletForm d.tensor (u+v) (u+v)-sphereDirichletForm d.tensor u u-
      sphereDirichletForm d.tensor v v)/2=sphereDirichletForm d.tensor u v :=
  symmetric_additive_polarization (fun u v : sphereSmoothFunctions ↦ sphereDirichletForm d.tensor u v)
    (fun u v ↦ sphereDirichletForm_symm d.tensor d.symm u v)
    (fun u v w ↦ sphereDirichletForm_add_left d.tensor d.smooth d.symm d.pos
      u v w u.property v.property w.property) u v

lemma sphereWeightedPairing_polarization (d : SphereEnergyData) (u v : sphereSmoothFunctions) :
    (sphereWeightedPairing d.density (u+v) (u+v)-sphereWeightedPairing d.density u u-
      sphereWeightedPairing d.density v v)/2=sphereWeightedPairing d.density u v :=
  symmetric_additive_polarization (fun u v : sphereSmoothFunctions ↦ sphereWeightedPairing d.density u v)
    (fun u v ↦ sphereWeightedPairing_symm d.density u v)
    (fun u v w ↦ sphereWeightedPairing_add_left d.density u v w d.continuous
      u.property.continuous v.property.continuous w.property.continuous) u v

lemma sphereCompletedDirichlet_polarization (d : SphereEnergyData) (u v : SphereEnergyHilbert d) :
    (sphereCompletedDirichlet d (u+v) (u+v)-sphereCompletedDirichlet d u u-
      sphereCompletedDirichlet d v v)/2=sphereCompletedDirichlet d u v := by
  apply symmetric_additive_polarization
  · intro u v
    simp only [sphereCompletedDirichlet,real_inner_comm u v,
      real_inner_comm (sphereEnergyL2Map d u) (sphereEnergyL2Map d v)]
  · intro u v w
    simp only [sphereCompletedDirichlet,map_add,inner_add_left]
    ring

end
end Yau.Target

end OAI
