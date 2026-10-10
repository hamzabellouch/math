import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatConcentration
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatEvolutionSmooth
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatPeriodicity
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Order.LeftRight

namespace OAI

/-! Joint continuity of the prescribed heat evolution at the initial boundary. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped Topology ContDiff

theorem torusHeatEvolution_initial_joint_limit {g : Plane → ℝ}
    (hg : ContDiff ℝ 1 g) (hp : PlanePeriodic g) (x : Plane) :
    Tendsto (fun p : ℝ × Plane => torusHeatEvolution g p.1 p.2)
      ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝 (g x)) := by
  have h := torusHeatEvolution_tendsto_uniformly hg hp
  have hu : TendstoUniformly
      (fun p : ℝ × Plane => torusHeatEvolution g p.1) g ((𝓝[>] 0) ×ˢ 𝓝 x) := by
    intro u hu
    exact tendsto_fst.eventually (h u hu)
  exact hu.tendsto_comp hg.continuous.continuousAt tendsto_snd

theorem torusHeatEvolution_continuous_initial {g : Plane → ℝ}
    (hg : ContDiff ℝ 1 g) (hp : PlanePeriodic g) (x : Plane) :
    ContinuousWithinAt (fun p : ℝ × Plane => torusHeatEvolution g p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ) (0, x) := by
  change Tendsto (fun p : ℝ × Plane => torusHeatEvolution g p.1 p.2)
    (𝓝[Ici (0 : ℝ) ×ˢ univ] (0, x)) (𝓝 (torusHeatEvolution g 0 x))
  rw [torusHeatEvolution_initial, nhdsWithin_prod_eq, nhdsWithin_univ,
    ← nhdsGT_sup_nhdsWithin_singleton, sup_prod, tendsto_sup]
  refine ⟨torusHeatEvolution_initial_joint_limit hg hp x, ?_⟩
  rw [nhdsWithin_singleton, pure_prod, tendsto_map'_iff]
  simpa only [ContinuousAt, Function.comp_def, torusHeatEvolution_initial] using hg.continuous.continuousAt

theorem torusHeatEvolution_continuousOn {g : Plane → ℝ}
    (hg : ContDiff ℝ 1 g) (hp : PlanePeriodic g) :
    ContinuousOn (fun p : ℝ × Plane => torusHeatEvolution g p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ) := by
  rintro ⟨t, x⟩ ht
  by_cases hzero : t = 0
  · subst t
    exact torusHeatEvolution_continuous_initial hg hp x
  · have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hzero)
    have hmem : (t,x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hpos, mem_univ x⟩
    exact ((torusHeatEvolution_smooth_positive g hg.continuous).continuousOn.continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)).continuousWithinAt

end ForcedComputation.VelocityDetector

end

end OAI
