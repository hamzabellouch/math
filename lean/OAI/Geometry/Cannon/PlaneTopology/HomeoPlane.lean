import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Plane

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonRegularDisk
open Metric

universe u v
variable {X : Type u} [TopologicalSpace X]
lemma IsRegularDisk.homeo_plane {U : Set X} (hU : IsRegularDisk U) : Nonempty (U ≃ₜ Plane) := by
  obtain ⟨e,he,q,r,hr,rfl⟩ := hU
  let b : Plane ≃ₜ ball q r := Homeomorph.unitBall.trans
    (OpenPartialHomeomorph.unitBallBall q r hr).toHomeomorphSourceTarget
  exact ⟨(b.trans (he.isEmbedding.homeomorphImage (ball q r))).symm⟩

lemma IsRegularDisk.tietzeExtension {U : Set X} (hU : IsRegularDisk U) :
    TietzeExtension.{v} U := by
  let : TietzeExtension.{v} Plane := TietzeExtension.of_homeo (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ))
  obtain ⟨e⟩ := hU.homeo_plane
  exact TietzeExtension.of_homeo e

theorem IsRegularDisk.extend {Y : Type v} [TopologicalSpace Y] [NormalSpace Y]
    {U : Set X} (hU : IsRegularDisk U) {S : Set Y} (hS : IsClosed S)
    (f : C(S,X)) (hf : ∀ y, f y∈U) :
    ∃ F : C(Y,X), (∀ y, F y∈U) ∧ F.restrict S=f := by
  let : TietzeExtension.{v} U := hU.tietzeExtension
  exact f.exists_forall_mem_restrict_eq hS hf

end CannonRegularDisk

end
end
end
end
end
end

end OAI
