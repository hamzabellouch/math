import OAI.Analysis.CircleDomains.Selection.TupleReference
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace OAI

/-! Projection onto any distinct selection of finite circle coordinates
preserves normalized Haar measure. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem torus_projection_measurePreserving {I J : Type*} [Fintype I] [Fintype J]
    (e : J → I) (he : Injective e) :
    MeasurePreserving (fun θ : I → UnitAddCircle => θ ∘ e) volume volume := by
  let f : (I → UnitAddCircle) →+ (J → UnitAddCircle) :=
    { toFun := fun θ => θ ∘ e
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hsurj : Surjective f := by
    intro θ
    refine ⟨Function.extend e θ (fun _ => 0), ?_⟩
    funext j
    exact he.extend_apply θ (fun _ => 0) j
  apply AddMonoidHom.measurePreserving (f := f)
    (by exact continuous_pi fun j => continuous_apply (e j)) hsurj
  change (Measure.pi (fun _ : I => (volume : Measure UnitAddCircle))) univ =
    (Measure.pi (fun _ : J => (volume : Measure UnitAddCircle))) univ
  simp [Measure.pi_univ, AddCircle.measure_univ]

end CircleDomainRigidity

end

end OAI
