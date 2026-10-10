import OAI.Analysis.IrrationalRotation.Product.ProductTailTrimming
import OAI.Analysis.IrrationalRotation.Analysis.DominatedL2Density
import OAI.Analysis.IrrationalRotation.Analysis.TrimmingWeakLimits

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel

local instance productSamplingTrimmingOpensMeasurableSpace :
    OpensMeasurableSpace EndpointPair := inferInstance

theorem weaklyConverges_iff_tendsto (η : ℕ → FiniteMeasure EndpointPair)
    (ν : FiniteMeasure EndpointPair) :
    WeaklyConverges (fun l => (η l : Measure EndpointPair)) (ν : Measure EndpointPair) ↔
      Tendsto η atTop (𝓝 ν) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  constructor
  · intro h φ
    exact h φ.toContinuousMap
  · intro h φ
    exact h (BoundedContinuousFunction.mkOfCompact φ)

theorem WeaklyConverges.tendsto_mass {η : ℕ → Measure EndpointPair}
    {ν : Measure EndpointPair} (hweak : WeaklyConverges η ν)
    (hη : ∀ l, IsFiniteMeasure (η l)) (hν : IsFiniteMeasure ν) :
    Tendsto (fun l => η l univ) atTop (𝓝 (ν univ)) := by
  let μn : ℕ → FiniteMeasure EndpointPair := fun l => ⟨η l, hη l⟩
  let μ : FiniteMeasure EndpointPair := ⟨ν, hν⟩
  have hμ := (weaklyConverges_iff_tendsto μn μ).mp hweak
  have hm : Tendsto (fun index => ((μn index).mass : ℝ≥0∞)) atTop
      (𝓝 (μ.mass : ℝ≥0∞)) := ENNReal.tendsto_coe.mpr hμ.mass
  rw [FiniteMeasure.ennreal_mass (μ := μ)] at hm
  exact hm.congr (fun index => FiniteMeasure.ennreal_mass (μ := μn index))

theorem WeaklyConverges.restrict_of_discarded_tendsto_zero
    {η : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hweak : WeaklyConverges η ν)
    (hη : ∀ l, IsFiniteMeasure (η l)) (hν : IsFiniteMeasure ν)
    (A : ℕ → Set EndpointPair) (hA : ∀ l, MeasurableSet (A l))
    (hlost : Tendsto (fun l => η l (A l)ᶜ) atTop (𝓝 0)) :
    WeaklyConverges (fun l => (η l).restrict (A l)) ν := by
  let μn : ℕ → FiniteMeasure EndpointPair := fun l => ⟨η l, hη l⟩
  let μ : FiniteMeasure EndpointPair := ⟨ν, hν⟩
  have hμ : Tendsto μn atTop (𝓝 μ) :=
    (weaklyConverges_iff_tendsto μn μ).mp hweak
  have hlost' : Tendsto (fun l => μn l (A l)ᶜ) atTop (𝓝 0) := by
    change Tendsto (fun l => (η l (A l)ᶜ).toNNReal) atTop (𝓝 0)
    have h := (ENNReal.tendsto_toNNReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlost
    exact h
  have htrim := Invariant233.TrimmingWeakLimits.tendsto_restrict_of_compl_mass_tendsto_zero
    hμ A hA hlost'
  exact (weaklyConverges_iff_tendsto (fun l => (μn l).restrict (A l)) μ).mpr htrim

namespace TailTrimming

theorem orderedOrbitSampling_of_untrimmed (θ : ℕ → ℝ) (I : Finset ℕ)
    (N : ℕ → Finset ℕ) (w : ℕ → ℕ → Base → ℝ≥0∞)
    (hN : ∀ l, ∀ n ∈ N l, 0 < n)
    (hL2 : HasUniformL2Marginals (fun l => orbitAverageMeasure θ (N l) (w l)))
    (hweak : WeaklyConverges (fun l => orbitAverageMeasure θ (N l) (w l))
      (triangularLaw I))
    (hlost : Tendsto (fun l => orbitAverageMeasure θ (N l) (w l) orderedPairEventᶜ)
      atTop (𝓝 0)) :
    OrderedOrbitSampling θ I := by
  refine ⟨fun l => (orbitAverageMeasure θ (N l) (w l)).restrict orderedPairEvent,
    ?_, ?_, hL2.restrict (fun _ => orderedPairEvent), ?_⟩
  · intro l
    let := hL2.isFiniteMeasure l
    infer_instance
  · intro l
    exact trimmed_orbitAverage_supported θ (N l) (hN l) (w l)
  · have hν : IsFiniteMeasure (triangularLaw I) := by
      unfold triangularLaw
      infer_instance
    exact hweak.restrict_of_discarded_tendsto_zero hL2.isFiniteMeasure hν
      (fun _ => orderedPairEvent) (fun _ => measurableSet_orderedPairEvent) hlost

theorem orderedOrbitSampling_of_prefix_samples (θ : ℕ → ℝ) (I : Finset ℕ)
    (hθ : ∀ i, 0 ≤ θ i) (D N : ℕ → Finset ℕ) (M : ℕ → ℕ)
    (w : ∀ l, ℕ → (D l → Circle) → ℝ≥0∞)
    (hw : ∀ l, ∀ n ∈ N l, Measurable (w l n))
    (hN : ∀ l, ∀ n ∈ N l, 0 < n)
    (hM : ∀ l, ∀ n ∈ N l, n ≤ M l)
    (hprefix : ∀ l, ∀ n ∈ N l,
      ∀ᵐ x ∂baseMeasure.withDensity (fun x : Base => w l n (fun i : D l => x i)),
        ∀ i ∈ D l, circleRepresentative (x i) ≤
          circleRepresentative (rotationIterate θ (n : ℤ) x i))
    (hL2 : HasUniformL2Marginals
      (fun l => orbitAverageMeasure θ (N l) (fun n x => w l n (fun i : D l => x i))))
    (hweak : WeaklyConverges
      (fun l => orbitAverageMeasure θ (N l) (fun n x => w l n (fun i : D l => x i)))
      (triangularLaw I))
    (htail : Tendsto (fun l => ENNReal.ofReal (M l : ℝ) *
      ∑' i : {i : ℕ // i ∉ D l}, ENNReal.ofReal (θ i)) atTop (𝓝 0)) :
    OrderedOrbitSampling θ I := by
  let η : ℕ → Measure EndpointPair :=
    fun l => orbitAverageMeasure θ (N l) (fun n x => w l n (fun i : D l => x i))
  have hν : IsFiniteMeasure (triangularLaw I) := by
    unfold triangularLaw
    infer_instance
  have hm : Tendsto (fun l => η l univ) atTop (𝓝 (triangularLaw I univ)) :=
    hweak.tendsto_mass hL2.isFiniteMeasure hν
  have hνtop : triangularLaw I univ ≠ ∞ := by
    let := hν
    exact measure_ne_top _ _
  have hbound := ENNReal.Tendsto.mul hm (Or.inr (by simp : (0 : ℝ≥0∞) ≠ ∞))
    htail (Or.inr hνtop)
  have hzero : Tendsto (fun l => η l univ * (ENNReal.ofReal (M l : ℝ) *
      ∑' i : {i : ℕ // i ∉ D l}, ENNReal.ofReal (θ i))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hbound
  apply orderedOrbitSampling_of_untrimmed θ I N
    (fun l n x => w l n (fun i : D l => x i)) hN hL2 hweak
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
  · intro l
    exact bot_le
  · intro l
    exact orbitAverageMeasure_unordered_le (D l) (N l) θ hθ (M l) (hM l)
      (w l) (hw l) (hprefix l)

end TailTrimming
end Invariant233.ProductModel

end

end OAI
