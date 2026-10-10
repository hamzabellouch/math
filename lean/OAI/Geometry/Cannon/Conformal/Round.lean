import Mathlib
import OAI.Geometry.Cannon.Conformal.Sphere

namespace OAI

section
section
section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

abbrev Round := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def north : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
lemma north_norm : ‖north‖=1 := by simp [north]
lemma north_ne_zero : north ≠ 0 := by intro h; simpa [h] using north_norm

def planeHyperplane : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ north)ᗮ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))=2+1) := ⟨by simp⟩
  exact Complex.isometryOfOrthonormal
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 north_ne_zero)

def roundChart : Sphere ≃ₜ Round :=
  planeHyperplane.toHomeomorph.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere north_norm)

@[simp] lemma roundChart_coe (z : ℂ) :
    roundChart (z:Sphere)=stereoInvFun north_norm (planeHyperplane z) := rfl

instance sphereMetric : MetricSpace Sphere :=
  roundChart.isEmbedding.comapMetricSpace roundChart

lemma sphere_dist (p q : Sphere) : dist p q=dist (roundChart p) (roundChart q) := rfl
lemma roundChart_isometry : Isometry roundChart := Isometry.of_dist_eq (fun _ _ => rfl)

end CannonMobius

end
end
end
end

end OAI
