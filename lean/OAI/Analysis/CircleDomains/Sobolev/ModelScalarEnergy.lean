import OAI.Analysis.CircleDomains.Sobolev.HolomorphicScalarEnergy
import OAI.Analysis.CircleDomains.Rigidity.ModelPointTrace

namespace OAI

/-! The actual source horizontal section is smooth off the dust and has
finite differential energy on each bounded source region. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem horizontalSection_plane_smooth (M : CompactScalarModel G u) (hG : IsOpen G) :
    ContDiffOn ℝ ∞ (fun z : ℂ => M.horizontalSection (z : Sphere)) {z : ℂ | (z : Sphere) ∈ G} := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hf : DifferentiableOn ℂ M.function D := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt
  have hc : ContDiffOn ℝ ∞ M.function D := (hf.contDiffOn hD).restrict_scalars ℝ
  apply (Complex.reCLM.contDiff.comp_contDiffOn hc).congr
  intro z hz
  simpa only [Function.comp_apply, Complex.reCLM_apply, extendAtInfinity_coe, finiteCoord_coe] using
    M.horizontalSection_on_domain hz

 theorem source_coordinate_memLp (M : CompactScalarModel G u) (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    MemLp (fderiv ℝ (fun z => (M.function z).re)) 2
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) ∧
    MemLp (fderiv ℝ (fun z => (M.function z).im)) 2
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) := by
  have hD : IsOpen {z : ℂ | (z : Sphere) ∈ G} := hG.preimage OnePoint.continuous_coe
  exact holomorphic_coordinate_memLp hD (hD.inter isOpen_ball).measurableSet inter_subset_left
    (fun z hz => (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt)
    (M.derivative_energy_on_source_ball hG hinf R)

 theorem horizontalSection_plane_memLp (M : CompactScalarModel G u) (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    MemLp (fderiv ℝ (fun z : ℂ => M.horizontalSection (z : Sphere))) 2
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) := by
  have hD : IsOpen {z : ℂ | (z : Sphere) ∈ G} := hG.preimage OnePoint.continuous_coe
  apply (M.source_coordinate_memLp hG hinf R).1.ae_eq
  filter_upwards [ae_restrict_mem (hD.inter isOpen_ball).measurableSet] with z hz
  have he : (fun w : ℂ => M.horizontalSection (w : Sphere)) =ᶠ[𝓝 z]
      (fun w => (M.function w).re) := by
    filter_upwards [hD.mem_nhds hz.1] with w hw
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using M.horizontalSection_on_domain hw
  exact he.fderiv_eq.symm

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
