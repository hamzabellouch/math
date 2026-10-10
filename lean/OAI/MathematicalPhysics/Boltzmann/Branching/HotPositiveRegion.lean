import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationCompactness
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicProductTest
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanBackwardMap
import OAI.MathematicalPhysics.Boltzmann.Branching.SmoothTestFamily
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # A compact kinetic cutoff confines its velocity average to a compact base -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem average_eq_zero_outside_projection (χ : Published.KineticPhase → ℝ)
    (ψ : Velocity → ℝ) (f : Published.KineticPhase → ℝ) (z : Published.SpaceTime)
    (hz : z ∉ Prod.fst '' tsupport χ) :
    (∫ v, ψ v*(χ (z,v)*f (z,v))) = 0 := by
  apply integral_eq_zero_of_ae
  exact ae_of_all _ (fun v => by
    have hv : (z,v) ∉ tsupport χ := fun h => hz (mem_image_of_mem Prod.fst h)
    change ψ v*(χ (z,v)*f (z,v)) = 0
    rw [image_eq_zero_of_notMem_tsupport hv,zero_mul,mul_zero])

theorem average_difference_norm_restrict
    {χ : Published.KineticPhase → ℝ} (hc : HasCompactSupport χ)
    (ψ : Velocity → ℝ) (f g : Published.KineticPhase → ℝ) :
    eLpNorm (fun z => (∫ v, ψ v*(χ (z,v)*f (z,v)))-
      (∫ v, ψ v*(χ (z,v)*g (z,v)))) 1 volume =
    eLpNorm (fun z => (∫ v, ψ v*(χ (z,v)*f (z,v)))-
      (∫ v, ψ v*(χ (z,v)*g (z,v)))) 1
      (volume.restrict (Prod.fst '' tsupport χ)) := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict (hc.image continuous_fst).measurableSet]
  congr 1
  ext z
  by_cases hz : z ∈ Prod.fst '' tsupport χ
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz,average_eq_zero_outside_projection χ ψ f z hz,
      average_eq_zero_outside_projection χ ψ g z hz,sub_self]

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Cylinder densities and source measures in characteristic coordinates -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotCharacteristicEquiv : CharacteristicPhase ≃ᵐ
    JetCopyDatum.AttainedCapSequence.HotKineticPhase := characteristicEquiv.trans hotChart

theorem hotCharacteristic_measurePreserving :
    MeasurePreserving hotCharacteristicEquiv volume volume :=
  hotChart_global_measurePreserving.comp (characteristic_measurePreserving volume)

def cylinderPullback (a A R : ℝ)
    (f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ) : CharacteristicPhase → ℝ :=
  (JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R).indicator f ∘ hotCharacteristicEquiv

theorem cylinderPullback_integrable {a A R : ℝ}
    {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ}
    (hf : Integrable f ((JetCopyDatum.AttainedCapSequence.coldCylinderVolume a A R).prod volume)) :
    Integrable (cylinderPullback a A R f) volume := by
  rw [JetCopyDatum.AttainedCapSequence.coldCylinderVolume_eq] at hf
  exact hotCharacteristic_measurePreserving.integrable_comp_of_integrable
    ((integrable_indicator_iff
      (JetCopyDatum.AttainedCapSequence.coldCylinderSet_measurable a A R)).mpr hf)

theorem cylinderPullback_integral (a A R : ℝ)
    (f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ)
    (ψ : CharacteristicPhase → ℝ) :
    (∫ u, ψ u*cylinderPullback a A R f u) =
      ∫ z, ψ (hotCharacteristicEquiv.symm z)*f z
        ∂(JetCopyDatum.AttainedCapSequence.coldCylinderVolume a A R).prod volume := by
  rw [JetCopyDatum.AttainedCapSequence.coldCylinderVolume_eq,
    ← integral_indicator (JetCopyDatum.AttainedCapSequence.coldCylinderSet_measurable a A R),
    ← hotCharacteristic_measurePreserving.integral_comp']
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by
    simp only [Function.comp_def,cylinderPullback]
    by_cases hu : hotCharacteristicEquiv u ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R
    · simp only [indicator_of_mem hu,MeasurableEquiv.symm_apply_apply]
    · simp only [indicator_of_notMem hu,mul_zero])

def sourcePullback (μ : Measure JetCopyDatum.AttainedCapSequence.HotKineticPhase) :
    Measure CharacteristicPhase := μ.map hotCharacteristicEquiv.symm

instance sourcePullback_finite (μ : Measure JetCopyDatum.AttainedCapSequence.HotKineticPhase)
    [IsFiniteMeasure μ] : IsFiniteMeasure (sourcePullback μ) := by
  unfold sourcePullback
  infer_instance

theorem sourcePullback_integral (μ : Measure JetCopyDatum.AttainedCapSequence.HotKineticPhase)
    {ψ : CharacteristicPhase → ℝ} (hψ : Measurable ψ) :
    (∫ u, ψ u ∂sourcePullback μ) = ∫ z, ψ (hotCharacteristicEquiv.symm z) ∂μ := by
  exact integral_map hotCharacteristicEquiv.symm.measurable.aemeasurable hψ.aestronglyMeasurable

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Published weak compactness on the required two-velocity windows

N. Dunford and B. J. Pettis, *Linear operations on summable functions*,
Trans. AMS 47 (1940), Theorem 3.2.1, p. 376,
DOI 10.1090/S0002-9947-1940-0002020-4.

This is the same sequential weak compactness consequence as `HotWindowInput`,
specialized to the two-velocity measure needed for the hot pair product.
Uniform integrability includes the common L¹ bound. Uniform tightness controls
the velocity tails. No product factorization or nonlinear identification is
part of this published input.
-/

noncomputable section

namespace BoltzmannNonuniqueness.Published

def DunfordPettis1940HotPairWindows : Prop :=
  ∀ A R : ℝ, 0 ≤ A → 0 ≤ R →
    L1WeakCompactnessInput (JetCopyDatum.AttainedCapSequence.hotPairWindowVolume A R)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The positive-time region below the limiting hot horizon -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotRegion (U : ℝ≥0∞) : Set Published.SpaceTime :=
  {z | 0 < z.1 ∧ ENNReal.ofReal z.1 < U}

theorem hotRegion_open (U : ℝ≥0∞) : IsOpen (hotRegion U) :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt (ENNReal.continuous_ofReal.comp continuous_fst) continuous_const)

theorem hotRegion_nonempty {U : ℝ≥0∞} (hU : 1 ≤ U) : (hotRegion U).Nonempty := by
  refine ⟨(1/2,0),by norm_num,?_⟩
  exact lt_of_lt_of_le (by norm_num : ENNReal.ofReal (1/2:ℝ) < 1) hU

theorem hotBaseSet_closed (A R : ℝ) : IsClosed (hotBaseSet A R) :=
  isClosed_Icc.prod (Metric.isClosed_closedBall.preimage spaceEquiv_continuous)

theorem hotRegion_ae {U : ℝ≥0∞} {A : ℝ} (hA : ENNReal.ofReal A < U) (R : ℝ) :
    ∀ᵐ z ∂hotBaseVolume A R, z ∈ hotRegion U := by
  unfold hotBaseVolume
  apply (Measure.ae_prod_iff_ae_ae (hotRegion_open U).measurableSet).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with t ht hn
  exact ae_of_all _ (fun _ => ⟨lt_of_le_of_ne ht.1 hn.symm,
    (ENNReal.ofReal_le_ofReal ht.2).trans_lt hA⟩)

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
