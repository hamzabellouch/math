import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.WeakVolterra

namespace OAI

noncomputable section
namespace VelocityDetection.WeakVolterra
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} (hT : 0 ≤ T) (K : ℝ → ℝ → E →L[ℝ] E) (β : ℝ → ℝ)
variable (hK : ContinuousOn (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (Ioi (0 : ℝ) ×ˢ univ))
variable (hβ : IntegrableOn β (Ioc (0 : ℝ) T))
variable (hβ0 : ∀ s ∈ Ioc (0 : ℝ) T, 0 ≤ β s)
variable (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ∀ r : ℝ, ∀ v : E, ‖K s r v‖ ≤ β s * ‖v‖)

include hK hβ hβ0 hbound

theorem integrable_causal (q : Curve T E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntegrableOn (fun s => K s (t - s) (extend hT q (t - s))) (Ioc (0 : ℝ) t) := by
  have hh := (integrableOn_indicator_iff measurableSet_Iic).mp
    (integrable_raw hT K β hK hβ hβ0 hbound q t)
  simpa only [Iic_inter_Ioc_of_le ht.2] using hh

end VelocityDetection.WeakVolterra
end

end OAI
