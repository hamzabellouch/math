import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLE.Geometry.CompactTubeProbability
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! The finite-window planar Brownian support input.

Millet--Sanz-Sole (1994), A simple proof of the support theorem for
diffusion processes, Seminaire de Probabilites XXVIII, Theorem 3.5,
p. 47: specialize to dimension two, identity diffusion and zero drift.
Only positivity of uniform tubes about based continuous paths on [0,1]
is retained. The product of two real Wiener laws is the planar law.
The Hölder support statement implies this weaker uniform-topology
consequence, using density of polygonal Cameron--Martin paths.
https://www.numdam.org/article/SPS_1994__28__36_0.pdf
-/

noncomputable section
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction

namespace SLEExactGauge
open Target

local instance wienerDriverSecondCountable : SecondCountableTopology Driver :=
  ContinuousMapZero.isEmbedding_toContinuousMap.secondCountableTopology

local instance wienerUnitMeasurableSpace : MeasurableSpace (unitInterval →ᵇ ℂ) := borel _
local instance wienerUnitBorelSpace : BorelSpace (unitInterval →ᵇ ℂ) := ⟨rfl⟩

def planarUnitPath (b : Driver × Driver) : unitInterval →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => (b.1 ⟨(t : ℝ), t.property.1⟩ : ℂ) +
      (b.2 ⟨(t : ℝ), t.property.1⟩ : ℂ) * Complex.I, by fun_prop⟩

theorem continuous_planarUnitPath : Continuous planarUnitPath := by
  have hc : Continuous (fun b : Driver × Driver =>
      (⟨fun t : unitInterval => (b.1 ⟨(t : ℝ), t.property.1⟩ : ℂ) +
        (b.2 ⟨(t : ℝ), t.property.1⟩ : ℂ) * Complex.I, by fun_prop⟩ : C(unitInterval, ℂ))) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (Driver × Driver) × unitInterval =>
      (z.1.1 ⟨(z.2 : ℝ), z.2.property.1⟩ : ℂ) +
        (z.1.2 ⟨(z.2 : ℝ), z.2.property.1⟩ : ℂ) * Complex.I)
    fun_prop
  exact (ContinuousMap.isometryEquivBoundedOfCompact unitInterval ℂ).continuous.comp hc

/-- A precise published input about ordinary planar Brownian motion,
without any ribbon geometry or uniform-in-route probability conclusion. -/
def PublishedPlanarWienerUnitSupport : Prop :=
  ∀ W : WienerLaw, IsWiener W → ∀ f : unitInterval →ᵇ ℂ, f 0 = 0 →
    ∀ r : ℝ, 0 < r → 0 < (W.prod W) (planarUnitPath ⁻¹' ball f r)

/-- The uniform probability needed for the bounded-speed physical route
family is derived from the pointwise published support statement. -/
theorem uniform_planarWiener_tube_probability
    (hpublished : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W) (C : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ f : unitInterval →ᵇ ℂ,
      LipschitzWith C f → f 0 = 0 → q ≤ (W.prod W)
        {b | ∀ t : unitInterval, dist (planarUnitPath b t) (f t) < ε} := by
  have hm := continuous_planarUnitPath.measurable
  have hs : ∀ f : unitInterval →ᵇ ℂ, f 0 = 0 → ∀ r : ℝ, 0 < r →
      0 < Measure.map planarUnitPath (W.prod W) (ball f r) := by
    intro f hf r hr
    rw [Measure.map_apply hm isOpen_ball.measurableSet]
    exact hpublished W hW f hf r hr
  obtain ⟨q, hq, hbound⟩ := CompactRouteTubes.uniform_tube_probability_of_based_support
    (Measure.map planarUnitPath (W.prod W)) C hε hs
  refine ⟨q, hq, ?_⟩
  intro f hf hf0
  have he : {g : unitInterval →ᵇ ℂ | ∀ t, dist (g t) (f t) < ε} = ball f ε := by
    ext g
    exact (BoundedContinuousFunction.dist_lt_iff_of_compact hε).symm
  have hb := hbound f hf hf0
  rw [he, Measure.map_apply hm isOpen_ball.measurableSet] at hb
  exact hb.trans (measure_mono (by
    intro b hb t
    exact (BoundedContinuousFunction.dist_coe_le_dist t).trans_lt hb))

end SLEExactGauge

end

end OAI
