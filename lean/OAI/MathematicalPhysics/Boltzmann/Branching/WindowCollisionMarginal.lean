import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrableGainTail
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteRatesWindowUI

namespace OAI

/-! # Weak collision marginals and uniform integrability on a fixed elastic window -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

def windowCollisionMarginal (R : ℝ) (r : (X × (Velocity × Velocity)) × Sphere → ℝ)
    (p : X × Velocity) : ℝ :=
  ∫ q, (collisionWindow R).indicator r (collisionGrouping.symm (p,q))
    ∂((volume : Measure Velocity).prod sphereArea)

theorem windowCollisionMarginal_measurable (R : ℝ)
    {r : (X × (Velocity × Velocity)) × Sphere → ℝ} (hr : Measurable r) :
    Measurable (windowCollisionMarginal R r) :=
  ((hr.indicator (collisionWindow_measurable R)).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

theorem weak_windowCollisionMarginal {R : ℝ}
    {r : ℕ → (X × (Velocity × Velocity)) × Sphere → ℝ}
    {s : (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hr : ∀ n, Measurable (r n))
    (hu : UniformIntegrable r 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)))
    (hw : Published.WeakL1Converges
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)) r s) :
    Published.WeakL1Converges (μ.prod volume)
      (fun n => windowCollisionMarginal R (r n)) (windowCollisionMarginal R s) := by
  have hs := collisionWindow_measurable (X := X) R
  have he := hw.zeroExtension hs
  have hui := uniformIntegrable_indicator_of_restrict hs hu
  have hg := weak_grouped_rate (fun n => (hr n).indicator hs) (hw.1.indicator hs) he
  have hi n := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    (memLp_one_iff_integrable.mp (hui.memLp n))
  unfold windowCollisionMarginal
  simpa only [one_mul] using hg.marginal hi (k := fun _ => 1) measurable_const 1
    (fun _ => by norm_num)

theorem windowCollisionMarginal_uniformIntegrable {R : ℝ} (hR : 0 ≤ R)
    {r : ℕ → (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hr : ∀ n, Measurable (r n))
    (hu : UniformIntegrable r 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R))) :
    UniformIntegrable (fun n => windowCollisionMarginal R (r n)) 1 (μ.prod volume) := by
  let V : Set (Velocity × Sphere) := Metric.closedBall (0:Velocity) R ×ˢ univ
  have hV : MeasurableSet V := Metric.isClosed_closedBall.measurableSet.prod MeasurableSet.univ
  let : IsFiniteMeasure (((volume : Measure Velocity).prod sphereArea).restrict V) := by
    have he : (((volume : Measure Velocity).prod sphereArea).restrict V) = fiberMeasure R := by
      dsimp only [V,fiberMeasure]
      rw [← Measure.prod_restrict,Measure.restrict_univ]
    rw [he]
    infer_instance
  have hs := collisionWindow_measurable (X := X) R
  have hui := uniformIntegrable_indicator_of_restrict hs hu
  have hgi := Published.uniformIntegrable_comp_equiv collisionGrouping.symm
    (collisionGrouping_measurePreserving μ).symm (fun n => (collisionWindow R).indicator (r n)) hui
  apply uniformIntegrable_integral_of_support hV
    (fun n => ((hr n).indicator hs).comp collisionGrouping.symm.measurable) hgi
  intro n p q hq
  apply indicator_of_notMem
  intro hz
  have hv : q.1 ∈ Metric.closedBall (0:Velocity) R := by
    have hb := (collisionWindow_bounds hR hz).2
    change ‖q.1‖ ≤ R at hb
    simpa only [Metric.mem_closedBall,dist_zero_right] using hb
  exact hq ⟨hv,mem_univ _⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
