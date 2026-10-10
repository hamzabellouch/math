import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpace

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

theorem compatible_closed (n : ℕ) : IsClosed (compatible n : Set
    (C₀(Coord n, ℝ) × Lp ℝ 1 (volume : Measure (Coord n)))) := by
  apply IsSeqClosed.isClosed
  intro F f hF hlim
  have hc : Tendsto (fun j => (F j).1) atTop (𝓝 f.1) := (continuous_fst.tendsto f).comp hlim
  have hl : Tendsto (fun j => (F j).2) atTop (𝓝 f.2) := (continuous_snd.tendsto f).comp hlim
  obtain ⟨k, hk, hkae⟩ := (tendstoInMeasure_of_tendsto_Lp hl).exists_seq_tendsto_ae
  have heq : ∀ᵐ X ∂(volume : Measure (Coord n)), ∀ j, (F j).2 X = (F j).1 X :=
    ae_all_iff.mpr hF
  change (fun X => f.2 X) =ᵐ[volume] (fun X => f.1 X)
  filter_upwards [hkae, heq] with X hx heqX
  have hx' : Tendsto (fun j => (F (k j)).1 X) atTop (𝓝 (f.1 X)) :=
    ((ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.mp hc).tendsto_at X).comp hk.tendsto_atTop
  have hh : Tendsto (fun j => (F (k j)).2 X) atTop (𝓝 (f.1 X)) := by
    simpa only [heqX] using hx'
  exact tendsto_nhds_unique hx hh

instance (n : ℕ) : CompleteSpace (compatible n) :=
  (compatible_closed n).isComplete.completeSpace_coe

end VelocityDetection.TailSpace
end

end OAI
