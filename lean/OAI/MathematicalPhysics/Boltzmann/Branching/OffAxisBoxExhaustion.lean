import OAI.MathematicalPhysics.Boltzmann.Branching.SeparationBoxContainment
import OAI.MathematicalPhysics.Boltzmann.Collision.SheetIntervals
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction

namespace OAI

section

/-! # Choosing a bounded representative of a collision kernel on the null axis -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

theorem measurableSet_offAxis :
    MeasurableSet {z : X × Velocity | transverse z.2 ≠ 0} := by
  exact ((measurableSet_singleton 0).preimage
    (measurable_transverse.comp measurable_snd)).compl

def offAxis (K : Kernel (X × Velocity) Velocity) : Kernel (X × Velocity) Velocity := by
  classical
  exact Kernel.piecewise measurableSet_offAxis K 0

instance offAxis_sFinite (K : Kernel (X × Velocity) Velocity) [IsSFiniteKernel K] :
    IsSFiniteKernel (offAxis K) := by
  classical
  unfold offAxis
  infer_instance

theorem offAxis_apply (K : Kernel (X × Velocity) Velocity) (z : X × Velocity)
    (hz : transverse z.2 ≠ 0) : offAxis K z = K z := by
  classical
  simp [offAxis,Kernel.piecewise_apply,hz]

theorem offAxis_axis (K : Kernel (X × Velocity) Velocity) (z : X × Velocity)
    (hz : transverse z.2 = 0) : offAxis K z = 0 := by
  classical
  simp [offAxis,Kernel.piecewise_apply,hz]

theorem offAxis_ae (K : Kernel (X × Velocity) Velocity) (x : X) :
    (fun v => offAxis K (x,v)) =ᵐ[volume] fun v => K (x,v) := by
  filter_upwards [SheetApplication.ae_transverse_ne_zero] with v hv
  exact offAxis_apply K (x,v) hv

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Null-axis changes leave the positive collision action unchanged -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

theorem action_offAxis_ae (μ : Measure X) [SFinite μ]
    (K : Kernel (X × Velocity) Velocity) (f : X × Velocity → ℝ≥0∞) :
    action (offAxis K) f =ᵐ[μ.prod volume] action K f := by
  have hv : ∀ᵐ z : X × Velocity ∂μ.prod volume, VelocityWeight.transverse z.2 ≠ 0 :=
    quasiMeasurePreserving_snd.ae SheetApplication.ae_transverse_ne_zero
  filter_upwards [hv] with z hz
  unfold action
  rw [offAxis_apply K z hz]

theorem action_offAxis_normalized_congr_ae (hcarleman : Published.GPV2009CarlemanInput)
    (μ : Measure X) [SFinite μ] (c : Kernel X Velocity) [IsSFiniteKernel c]
    {r : X × Velocity → ℝ≥0∞} (hr : Measurable r)
    (hc : ∀ x, c x = volume.withDensity (fun v => r (x,v))) (q : ℝ)
    {f g : X × Velocity → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[μ.prod volume] g) :
    action (offAxis (inputKernel c q)) f =ᵐ[μ.prod volume]
      action (offAxis (inputKernel c q)) g :=
  (action_offAxis_ae μ _ f).trans
    ((action_normalized_congr_ae hcarleman μ c hr hc q hf hg hfg).trans
      (action_offAxis_ae μ _ g).symm)

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Off-axis bounded boxes exhaust a kinetic time slab up to a null set -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem ae_zero_time_slab_of_boxes {A : ℝ} {g : Published.KineticPhase → ℝ}
    (hz : ∀ R ≥ 0, ∀ ε > 0, g =ᵐ[volume.restrict (awayKineticBox A R ε)] 0) :
    ∀ᵐ z ∂(volume : Measure Published.KineticPhase), z.1.1 ∈ Icc 0 A → g z = 0 := by
  have hbox (j : ℕ) : ∀ᵐ z ∂(volume : Measure Published.KineticPhase),
      z ∈ awayKineticBox A (j+1) (1/((j:ℝ)+1)) → g z = 0 :=
    (ae_restrict_iff' (measurableSet_awayKineticBox _ _ _)).mp (hz (j+1) (by positivity) _ (by positivity))
  have hv : ∀ᵐ z ∂(volume : Measure Published.KineticPhase), transverse z.2 ≠ 0 :=
    Measure.quasiMeasurePreserving_snd.ae SheetApplication.ae_transverse_ne_zero
  filter_upwards [ae_all_iff.mpr hbox,hv] with z hz hv ht
  let R := max ‖z.1.2‖ ‖z.2‖
  obtain ⟨j,_,hj,hε⟩ := exists_separationBox_parameters
    (show 0 ≤ R from (norm_nonneg _).trans (le_max_left _ _)) (norm_pos_iff.mpr hv)
  apply hz j
  refine ⟨⟨⟨ht,?_⟩,?_⟩,hε⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right] using (le_max_left _ _).trans hj
  · simpa only [Metric.mem_closedBall,dist_zero_right] using (le_max_right _ _).trans hj

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
