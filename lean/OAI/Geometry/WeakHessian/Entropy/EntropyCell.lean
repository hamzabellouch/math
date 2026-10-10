import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.GeodesicPlanSupportedBall
import OAI.Geometry.WeakHessian.Entropy.FiniteEntropy
import OAI.Geometry.WeakHessian.Transport.OptimalPlansShort
import OAI.Geometry.WeakHessian.Transport.RerouteFiniteSubplanShort
import OAI.Geometry.WeakHessian.LocalBounds.CompressionRate

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma integrable_plan_energy_of_length {π : Measure (Curve X)} [IsFiniteMeasure π] {D : ℝ}
    (hD : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ D) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π := by
  apply (integrable_const (D^2)).mono' plan_energy_measurable.aestronglyMeasurable
  filter_upwards [hD] with γ hγ
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ dist_nonneg hγ 2

lemma optimal_planEnergy_eq {μ₀ μ₁ : Measure X} {π η : Measure (Curve X)}
    (hπ : IsOptimalCoupling (endpointCoupling π) μ₀ μ₁)
    (hη : IsOptimalCoupling (endpointCoupling η) μ₀ μ₁)
    (hIπ : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π)
    (hIη : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) η) :
    planEnergy π = planEnergy η := by
  apply (ENNReal.ofReal_eq_ofReal_iff (planEnergy_nonneg π) (planEnergy_nonneg η)).mp
  rw [← planCost_eq_ofReal_energy hIπ,← planCost_eq_ofReal_energy hIη]
  exact le_antisymm (hπ.2 _ hη.1) (hη.2 _ hπ.1)

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma dominated_mono_constant {μ m : Measure X} {A B : ℝ≥0∞}
    (h : μ ≤ A • m) (hAB : A ≤ B) : μ ≤ B • m := by
  intro S
  exact (h S).trans (mul_le_mul' hAB le_rfl)

structure EntropyCell (m : Measure X) (K N : ℝ) where
  leftLaw : ProbabilityMeasure X
  rightLaw : ProbabilityMeasure X
  center : X
  radius : ℝ≥0
  length : ℝ≥0
  cap : ℝ≥0∞
  cap_pos : cap ≠ 0
  cap_finite : cap ≠ ∞
  left_supported : (leftLaw:Measure X) (Metric.closedBall center radius)ᶜ = 0
  right_supported : (rightLaw:Measure X) (Metric.closedBall center radius)ᶜ = 0
  left_dominated : (leftLaw:Measure X) ≤ cap • m
  right_dominated : (rightLaw:Measure X) ≤ cap • m
  left_entropy : FiniteEntropy m (leftLaw:Measure X)
  right_entropy : FiniteEntropy m (rightLaw:Measure X)
  short : OptimalPlansShort (leftLaw:Measure X) (rightLaw:Measure X) length

structure CellPlan {m : Measure X} {K N : ℝ} (c : EntropyCell m K N) where
  law : ProbabilityMeasure (Curve X)
  geodesic : ∀ᵐ γ ∂(law:Measure (Curve X)), IsGeodesic γ
  optimal : IsOptimalCoupling (endpointCoupling (law:Measure (Curve X))) c.leftLaw c.rightLaw

structure CDEnvironment (m : Measure X) (K N : ℝ) : Prop where
  dimension : 1 < N
  cd : CurvatureDimension m K N
  finite_bounded : FiniteOnBoundedSets m

variable {m : Measure X} {K N : ℝ}

namespace EntropyCell

def nextCap (c : EntropyCell m K N) : ℝ≥0∞ :=
  c.cap*ENNReal.ofReal (Real.exp (compressionRate K N*c.length))

def uniformCap (c : EntropyCell m K N) : ℝ≥0∞ :=
  c.cap*ENNReal.ofReal (Real.exp (2*compressionRate K N*c.length))

omit [BorelSpace X] [SecondCountableTopology X] in
lemma nextCap_pos (c : EntropyCell m K N) : c.nextCap ≠ 0 :=
  mul_ne_zero c.cap_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
omit [BorelSpace X] [SecondCountableTopology X] in
lemma nextCap_finite (c : EntropyCell m K N) : c.nextCap ≠ ∞ :=
  ENNReal.mul_ne_top c.cap_finite ENNReal.ofReal_ne_top
omit [BorelSpace X] [SecondCountableTopology X] in
lemma uniformCap_pos (c : EntropyCell m K N) : c.uniformCap ≠ 0 :=
  mul_ne_zero c.cap_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
omit [BorelSpace X] [SecondCountableTopology X] in
lemma uniformCap_finite (c : EntropyCell m K N) : c.uniformCap ≠ ∞ :=
  ENNReal.mul_ne_top c.cap_finite ENNReal.ofReal_ne_top
omit [BorelSpace X] [SecondCountableTopology X] in
lemma cap_le_nextCap (env : CDEnvironment m K N) (c : EntropyCell m K N) : c.cap ≤ c.nextCap := by
  have H : (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (compressionRate K N*c.length)) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (mul_nonneg (compressionRate_nonneg env.dimension) c.length.property))
  simpa only [nextCap, mul_one] using mul_le_mul' (le_refl c.cap) H
omit [BorelSpace X] [SecondCountableTopology X] in
lemma cap_le_uniformCap (env : CDEnvironment m K N) (c : EntropyCell m K N) : c.cap ≤ c.uniformCap := by
  have H : (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (2*compressionRate K N*c.length)) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (mul_nonneg (mul_nonneg (by norm_num) (compressionRate_nonneg (K:=K) env.dimension)) c.length.property))
  simpa only [uniformCap, mul_one] using mul_le_mul' (le_refl c.cap) H

end EntropyCell

namespace CellPlan
omit [BorelSpace X] [SecondCountableTopology X] in
lemma integrable_energy {c : EntropyCell m K N} (p : CellPlan c) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) (p.law:Measure (Curve X)) :=
  integrable_plan_energy_of_length (c.short _ inferInstance p.geodesic p.optimal)
lemma energy_eq {c : EntropyCell m K N} (p q : CellPlan c) :
    planEnergy (p.law:Measure (Curve X)) = planEnergy (q.law:Measure (Curve X)) :=
  optimal_planEnergy_eq p.optimal q.optimal p.integrable_energy q.integrable_energy
end CellPlan

structure CellMidpoint {m : Measure X} {K N : ℝ} (c : EntropyCell m K N) extends CellPlan c where
  dominated : interpolation (law:Measure (Curve X)) timeHalf ≤ c.nextCap • m
  finite_entropy : FiniteEntropy m (interpolation (law:Measure (Curve X)) timeHalf)
  entropy_bound : entropyReal m (interpolation (law:Measure (Curve X)) timeHalf) ≤
    (entropyReal m (c.leftLaw:Measure X)+entropyReal m (c.rightLaw:Measure X))/2 -
      K/8*planEnergy (law:Measure (Curve X))

variable [ProperSpace X] [SigmaFinite m]

lemma CDEnvironment.midpoint_nonempty (env : CDEnvironment m K N) (c : EntropyCell m K N) :
    Nonempty (CellMidpoint c) := by
  obtain ⟨π,hg,ho,hd,hE,he⟩ := env.cd.exists_entropy_bounded_midpoint_short env.dimension env.finite_bounded
    c.leftLaw c.rightLaw c.center c.radius c.left_supported c.right_supported c.length c.short
    c.cap_pos c.cap_finite c.left_dominated c.right_dominated c.left_entropy c.right_entropy
  rw [midpoint_cap_eq env.dimension] at hd
  have hd' : interpolation (π:Measure (Curve X)) timeHalf ≤ c.nextCap • m :=
    hd.trans (smul_le_smul_left c.nextCap Measure.restrict_le_self)
  exact ⟨⟨⟨π,hg,ho⟩,hd',hE,he⟩⟩

noncomputable def CDEnvironment.midpoint (env : CDEnvironment m K N) (c : EntropyCell m K N) :
    CellMidpoint c := Classical.choice (env.midpoint_nonempty c)

omit [SigmaFinite m]

namespace CellMidpoint
variable {c : EntropyCell m K N}
def middle (p : CellMidpoint c) : ProbabilityMeasure X :=
  p.law.map (fun γ => γ timeHalf)

omit [ProperSpace X] [SecondCountableTopology X] in
lemma middle_supported (p : CellMidpoint c) :
    (p.middle:Measure X) (Metric.closedBall c.center (3*(c.radius:ℝ)))ᶜ = 0 :=
  geodesic_plan_supported_ball (p.law:Measure (Curve X)) p.geodesic c.center c.radius
    (by rw [p.optimal.1.interpolation_endpoints.1]; exact c.left_supported)
    (by rw [p.optimal.1.interpolation_endpoints.2]; exact c.right_supported) timeHalf

lemma short_halves (p : CellMidpoint c) :
    OptimalPlansShort (c.leftLaw:Measure X) (p.middle:Measure X) ((c.length:ℝ)/2) ∧
    OptimalPlansShort (p.middle:Measure X) (c.rightLaw:Measure X) ((c.length:ℝ)/2) :=
  c.short.halves (p.law:Measure (Curve X)) p.geodesic p.optimal p.toCellPlan.integrable_energy

def leftCell (p : CellMidpoint c) (env : CDEnvironment m K N) : EntropyCell m K N where
  leftLaw := c.leftLaw
  rightLaw := p.middle
  center := c.center
  radius := 3*c.radius
  length := c.length/2
  cap := c.nextCap
  cap_pos := c.nextCap_pos
  cap_finite := c.nextCap_finite
  left_supported := measure_mono_null (compl_subset_compl.mpr (Metric.closedBall_subset_closedBall (by
    change (c.radius:ℝ) ≤ (3:ℝ)*(c.radius:ℝ); linarith [c.radius.property]))) c.left_supported
  right_supported := by simpa only [NNReal.coe_mul,NNReal.coe_ofNat] using p.middle_supported
  left_dominated := dominated_mono_constant c.left_dominated (c.cap_le_nextCap env)
  right_dominated := p.dominated
  left_entropy := c.left_entropy
  right_entropy := p.finite_entropy
  short := by simpa only [NNReal.coe_div,NNReal.coe_ofNat] using p.short_halves.1

def rightCell (p : CellMidpoint c) (env : CDEnvironment m K N) : EntropyCell m K N where
  leftLaw := p.middle
  rightLaw := c.rightLaw
  center := c.center
  radius := 3*c.radius
  length := c.length/2
  cap := c.nextCap
  cap_pos := c.nextCap_pos
  cap_finite := c.nextCap_finite
  left_supported := by simpa only [NNReal.coe_mul,NNReal.coe_ofNat] using p.middle_supported
  right_supported := measure_mono_null (compl_subset_compl.mpr (Metric.closedBall_subset_closedBall (by
    change (c.radius:ℝ) ≤ (3:ℝ)*(c.radius:ℝ); linarith [c.radius.property]))) c.right_supported
  left_dominated := p.dominated
  right_dominated := dominated_mono_constant c.right_dominated (c.cap_le_nextCap env)
  left_entropy := p.finite_entropy
  right_entropy := c.right_entropy
  short := by simpa only [NNReal.coe_div,NNReal.coe_ofNat] using p.short_halves.2

lemma left_uniformCap (p : CellMidpoint c) (env : CDEnvironment m K N) :
    (p.leftCell env).uniformCap = c.uniformCap := by
  change (c.cap*ENNReal.ofReal (Real.exp (compressionRate K N*c.length)))*
    ENNReal.ofReal (Real.exp (2*compressionRate K N*((c.length:ℝ)/2))) = _
  rw [mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  congr 1
  ring

lemma right_uniformCap (p : CellMidpoint c) (env : CDEnvironment m K N) :
    (p.rightCell env).uniformCap = c.uniformCap := p.left_uniformCap env

end CellMidpoint
end WeakHessian
end
end InlinedFile0

end OAI
