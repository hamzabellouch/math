import OAI.Analysis.CircleDomains.Topology.SpherePlaneContinuity
import OAI.Analysis.CircleDomains.Rigidity.LipschitzTracePairs
import OAI.Analysis.CircleDomains.Sobolev.ScalarFlatteningEnergy

namespace OAI

/-! Exact trace-pair transfer between the finite plane and a sphere
complement avoiding infinity. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem sphere_trace_pair_null_of_plane {G : Set Sphere}
    (hinf : OnePoint.infty ∈ G) (a b : Sphere → ℝ)
    (h : volume ((fun z : ℂ => (a (z : Sphere),b (z : Sphere))) ''
      {z : ℂ | (z : Sphere) ∉ G}) = 0) :
    volume ((fun z => (a z,b z)) '' Gᶜ) = 0 := by
  apply measure_mono_null (t := (fun z : ℂ => (a (z : Sphere),b (z : Sphere))) ''
    {z : ℂ | (z : Sphere) ∉ G}) ?_ h
  rintro _ ⟨z, hz, rfl⟩
  cases z using OnePoint.rec with
  | infty => exact (hz hinf).elim
  | coe z => exact ⟨z,hz,rfl⟩

 theorem plane_trace_pair_null_of_sphere {G : Set Sphere} (a b : Sphere → ℝ)
    (h : volume ((fun z => (a z,b z)) '' Gᶜ) = 0) :
    volume ((fun z : ℂ => (a (z : Sphere),b (z : Sphere))) ''
      {z : ℂ | (z : Sphere) ∉ G}) = 0 :=
  measure_mono_null (by rintro _ ⟨z,hz,rfl⟩; exact ⟨(z : Sphere),hz,rfl⟩) h

 theorem sphereFromPlaneFunction_flatten (O : Set ℝ) (u : EuclideanPlane → ℝ) (p : Sphere) :
    sphereFromPlaneFunction (flattenValues O ∘ u) p = flattenValues O (sphereFromPlaneFunction u p) := by
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction, flattenValues_zero]
  | coe z => simp only [sphereFromPlaneFunction_coe, Function.comp_apply]

end CircleDomainRigidity

end

end OAI
