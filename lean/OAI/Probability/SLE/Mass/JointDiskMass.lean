import OAI.Probability.SLE.Mass.DiskChartMass
import OAI.Probability.SLE.Mass.RadonRandomTesting
import OAI.Probability.SLE.Stochastic.ProgressiveParameterTime
import OAI.Probability.SLE.Geometry.CanonicalRawTerminal

namespace OAI

/-! Measurable disk mass for a varying angle and raw path.
The defining integral agrees with the already constructed compact disk scalar. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge

/-- A formula for the derivative weight which is measurable at every real
angle and agrees with the disk chart derivative on the natural angle interval. -/
def diskDerivativeWeight (κ θ : ℝ) (z : upperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (‖(Complex.exp (θ*Complex.I)-Complex.exp (-θ*Complex.I))/
    ((z:ℂ)-Complex.exp (-θ*Complex.I))^2‖^dimension κ)

def diskMassValue (κ θ : ℝ) (μ : Measure upperHalfPlane) : ℝ≥0∞ :=
  ∫⁻ z, (if Target.diskMap θ z ∈ Target.diskK then diskDerivativeWeight κ θ z else 0) ∂μ

lemma diskMassValue_measurable
    {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) (θ : Ω → ℝ) (hθ : Measurable θ)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω)) :
    Measurable (fun ω => diskMassValue κ (θ ω) (μ ω)) := by
  unfold diskMassValue
  apply halfPlane_random_test_measurable μ hμ hfin
    (fun q => if Target.diskMap (θ q.1) q.2 ∈ Target.diskK then
      diskDerivativeWeight κ (θ q.1) q.2 else 0)
  have hm : Measurable (fun q : Ω × upperHalfPlane => Target.diskMap (θ q.1) q.2) := by
    unfold Target.diskMap
    fun_prop
  have hw : Measurable (fun q : Ω × upperHalfPlane => diskDerivativeWeight κ (θ q.1) q.2) := by
    unfold diskDerivativeWeight
    fun_prop
  exact hw.ite ((isClosed_closedBall.measurableSet).preimage hm) measurable_const

lemma diskMassValue_eq (κ θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (μ : Measure upperHalfPlane) :
    diskMassValue κ θ μ = ∫⁻ z in Target.diskSourceHalfPlane θ,
      (Target.diskMassWeight κ θ hθ z : ℝ≥0∞) ∂μ := by
  rw [diskMassValue,← lintegral_indicator (Target.diskSourceHalfPlane_compact hθ).measurableSet]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ Target.diskSourceHalfPlane θ
  · rw [indicator_of_mem hz,ite_eq_left ((Target.mem_diskSourceHalfPlane_iff hθ z).mp hz),
      Target.diskMassWeight_ennreal,diskDerivativeWeight,(Target.diskMap_hasDerivAt hθ z.property).deriv]
  · rw [indicator_of_notMem hz,ite_eq_right (fun h => hz ((Target.mem_diskSourceHalfPlane_iff hθ z).mpr h))]

lemma diskMassValue_toReal_eq (κ θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (μ : Measure upperHalfPlane) :
    (diskMassValue κ θ μ).toReal = Multipoint.compactWeightedMass
      (Target.diskMassWeight κ θ hθ) (Target.diskSourceHalfPlane θ) μ := by
  rw [diskMassValue_eq κ θ hθ μ,Multipoint.compactWeightedMass_eq_lintegral]

namespace Multipoint

local instance : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma RawCanonicalMass.disk_at_parameter_measurable
    {Ξ : Type*} [MeasurableSpace Ξ] (R : RawCanonicalMass) (κ : ℝ)
    (θ : Ξ → ℝ) (hθ : Measurable θ) (g : Ξ → C(ℝ≥0,ℝ)) (hg : Measurable g)
    (T : Ξ → ℝ≥0∞) (hT : Measurable T) :
    Measurable (fun x => diskMassValue κ (θ x)
      (extendedCanonicalMass R.process R.terminal (T x) (g x))) := by
  apply diskMassValue_measurable κ θ hθ
  · exact ((_root_.OAI.MeasureTheory.IsProgressive.parameter_time_measurable R.progressive g hg _ hT.ennreal_toNNReal).ite
      (measurableSet_lt hT measurable_const) (R.terminal_measurable.comp hg))
  · intro x
    exact (extendedCanonicalMass_radon R.process R.terminal R.radon R.terminal_radon (T x) (g x)).2

end Multipoint
end SLEExactGauge

end

end OAI
