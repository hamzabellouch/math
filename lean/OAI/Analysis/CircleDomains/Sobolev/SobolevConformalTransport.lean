import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneEnergyTransport
import OAI.Analysis.CircleDomains.Sobolev.SmoothEnergyLimit
import OAI.Analysis.CircleDomains.Sobolev.MollificationEnergy
import OAI.Analysis.CircleDomains.Sobolev.UniformLocalMollification

namespace OAI

/-! Continuous compactly supported Sobolev functions can be transported
by the actual smooth conformal inverse. The local target witness has at
most the source energy; no smoothness of the original test is assumed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem planarMollification_tendsto_of_continuous
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (x : EuclideanPlane) :
    Tendsto (fun n => planarMollification u n x) atTop (𝓝 (u x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := planarMollification_uniform_on_compact hu.aestronglyMeasurable
    (K := {x}) isCompact_singleton isOpen_univ (subset_univ _) hu.continuousOn hε
  filter_upwards [he] with n hn
  simpa only [Real.dist_eq] using hn x (mem_singleton x)

 theorem sobolev_conformal_transport
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hf : IsConformalOn f U) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (H : DeGiorgi.MemW1pWitness 2 u univ)
    (hv : EqOn v (planeInverseTransport fi u) (physicalPlaneDomain V))
    (hL : MemLp v 2 (volume.restrict (physicalPlaneDomain V))) :
    ∃ K : DeGiorgi.MemW1pWitness 2 v (physicalPlaneDomain V),
      (∫ x in physicalPlaneDomain V, K.weakGrad x 0 ^ 2 + K.weakGrad x 1 ^ 2) ≤
      ∫ x in physicalPlaneDomain U, H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2 := by
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using H.memLp
  let a (n : ℕ) := planarMollification u n
  let b (n : ℕ) := planeInverseTransport fi (a n)
  have ha (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (a n) :=
    planarMollification_smooth (huL.locallyIntegrable (by norm_num)) n
  have htransport (n : ℕ) := smooth_plane_energy_transport heq hU hV hinf hfix hf
    (ha n).contDiffOn (fun i => (planarMollification_partial_memLp H hs n i).restrict _)
  obtain ⟨C, hC⟩ := hu.bounded_above_of_compact_support hs
  have hunit (x : EuclideanPlane) : u x ∈ Icc (-C) C :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using hC x)
  have hb (n : ℕ) (x : EuclideanPlane) (_hx : x ∈ physicalPlaneDomain V) : ‖b n x‖ ≤ C := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (planarMollification_mem_Icc hu.aestronglyMeasurable hunit n _)
  have hp (x : EuclideanPlane) (hx : x ∈ physicalPlaneDomain V) :
      Tendsto (fun n => b n x) atTop (𝓝 (v x)) := by
    rw [hv hx]
    exact planarMollification_tendsto_of_continuous hu _
  apply smooth_energy_limit (isOpen_physicalPlaneDomain hV) hL b
    (fun n => (htransport n).1) (fun n => (htransport n).2.1) hb hp
  have he := planarMollification_energy_tendsto H hs (physicalPlaneDomain U)
  convert he using 1
  funext n
  exact (htransport n).2.2

end CircleDomainRigidity

end

end OAI
