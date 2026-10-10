import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowLineDifferentiability
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! # Measurable, locally bounded derivatives along horizontal flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped NNReal

def flowDeriv {G V W : Type*} [Group G] [SMul ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : G → W) (Exp : V → G) (v : V) (g : G) : W :=
  deriv (fun t : ℝ => f (g * Exp (t • v))) 0

variable {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [SecondCountableTopology G] in
theorem stronglyMeasurable_flowDeriv
    (f : G → W) (hf : Continuous f) (Exp : V → G) (hExp : Continuous Exp) (v : V) :
    StronglyMeasurable (flowDeriv f Exp v) := by
  have hc : Continuous (fun z : G × ℝ => f (z.1 * Exp (z.2 • v))) := by fun_prop
  exact (stronglyMeasurable_deriv_with_param
    (f := fun g t => f (g * Exp (t • v))) hc).comp_measurable
    (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [FiniteDimensional ℝ W] in
theorem norm_flowDeriv_le
    (f : G → W) (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (v : V) (Ω : Set G) (hΩ : IsOpen Ω) (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ Ω}) {g : G} (hg : g ∈ Ω) :
    ‖flowDeriv f Exp v g‖ ≤ C := by
  apply norm_deriv_le_of_lipschitzOn _ (hlip g)
  apply (hΩ.preimage (by fun_prop)).mem_nhds
  simpa [hzero] using hg

theorem ae_hasDerivAt_flowDeriv
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f : G → W) (hf : Continuous f) (Ω : Set G) (hΩ : IsOpen Ω)
    (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ Ω}) :
    ∀ᵐ g ∂μ, g ∈ Ω → HasDerivAt (fun t : ℝ => f (g * Exp (t • v)))
      (flowDeriv f Exp v g) 0 := by
  filter_upwards [ae_flowLine_differentiableAt_zero μ Exp hExp hadd v f hf Ω hΩ C hlip]
    with g hg hmem
  exact (hg hmem).hasDerivAt

omit [SecondCountableTopology G] in
theorem locallyIntegrableOn_flowDeriv [LocallyCompactSpace G] [T2Space G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : G → W) (hf : Continuous f) (Exp : V → G) (hExp : Continuous Exp)
    (hzero : Exp 0 = 1) (v : V) (Ω : Set G) (hΩ : IsOpen Ω) (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ Ω}) : LocallyIntegrableOn (flowDeriv f Exp v) Ω μ := by
  apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
  intro K hKΩ hK
  apply IntegrableOn.of_bound hK.measure_lt_top
    (stronglyMeasurable_flowDeriv f hf Exp hExp v).aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with g hg
  exact norm_flowDeriv_le f Exp hExp hzero v Ω hΩ C hlip (hKΩ hg)

end PolycyclicRecognition

end

end OAI
