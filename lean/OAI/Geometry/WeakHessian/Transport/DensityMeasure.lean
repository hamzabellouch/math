import Mathlib
import OAI.Geometry.WeakHessian.Transport.BoundedHopfLpPairing
import OAI.Geometry.WeakHessian.Transport.ProbabilityTightMarginals

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

namespace WeakHessianTransport
variable {X : Type*} [MeasurableSpace X] (m : Measure X)

def densityMeasure (ρ : Lp ℝ 2 m) : Measure X := m.withDensity (fun x => ENNReal.ofReal (ρ x))

lemma integral_densityMeasure (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x) (f : X → ℝ) :
    ∫ x, f x ∂densityMeasure m ρ = ∫ x, ρ x*f x ∂m := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (Lp.aestronglyMeasurable ρ).aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

lemma densityMeasure_le {ρ : Lp ℝ 2 m} {B : ℝ} (hρ : ∀ᵐ x ∂m, ρ x ≤ B) :
    densityMeasure m ρ ≤ ENNReal.ofReal B • m := by
  rw [densityMeasure, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [hρ] with x hx
  exact ENNReal.ofReal_le_ofReal hx

lemma densityMeasure_ac (ρ : Lp ℝ 2 m) : densityMeasure m ρ ≪ m :=
  withDensity_absolutelyContinuous _ _

variable [IsFiniteMeasure m]
lemma densityMeasure_probability (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x)
    (hmass : ∫ x, ρ x ∂m = 1) : IsProbabilityMeasure (densityMeasure m ρ) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (Lp.memLp ρ)) hρ,
    hmass, ENNReal.ofReal_one]

def densityProbability (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x)
    (hmass : ∫ x, ρ x ∂m = 1) : ProbabilityMeasure X :=
  ⟨densityMeasure m ρ, densityMeasure_probability m ρ hρ hmass⟩

variable [TopologicalSpace X] [BorelSpace X] [CompactSpace X]
lemma integral_densityMeasure_continuousMap (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x) (f : C(X,ℝ)) :
    ∫ x, f x ∂densityMeasure m ρ = ⟪ContinuousMap.toLp 2 m ℝ f,ρ⟫_ℝ := by
  rw [integral_densityMeasure m ρ hρ, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) m f] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]

lemma continuous_densityProbability {T : Type*} [TopologicalSpace T]
    {ρ : T → Lp ℝ 2 m} (hcont : Continuous ρ)
    (hρ : ∀ t, ∀ᵐ x ∂m, 0 ≤ ρ t x) (hmass : ∀ t, ∫ x, ρ t x ∂m = 1) :
    Continuous (fun t => densityProbability m (ρ t) (hρ t) (hmass t)) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral]
  intro f
  have heq : (fun t => ∫ x, f x ∂(densityProbability m (ρ t) (hρ t) (hmass t) : Measure X)) =
      (fun t => ⟪ContinuousMap.toLp 2 m ℝ f,ρ t⟫_ℝ) := by
    funext t
    exact integral_densityMeasure_continuousMap m (ρ t) (hρ t) f
  rw [heq]
  exact continuous_const.inner hcont
end WeakHessianTransport

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  (m : Measure X) [IsFiniteMeasure m]
lemma integral_densityMeasure_boundedContinuous (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x)
    (f : X →ᵇ ℝ) :
    ∫ x,f x ∂densityMeasure m ρ = ⟪BoundedContinuousFunction.toLp 2 m ℝ f,ρ⟫_ℝ := by
  rw [integral_densityMeasure m ρ hρ,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 m ℝ f] with x hx
  simp only [hx,RCLike.inner_apply,conj_trivial]

lemma continuous_boundedDensityProbability {T : Type*} [TopologicalSpace T]
    {ρ : T → Lp ℝ 2 m} (hcont : Continuous ρ)
    (hρ : ∀ t, ∀ᵐ x ∂m, 0 ≤ ρ t x) (hmass : ∀ t,∫ x,ρ t x ∂m = 1) :
    Continuous (fun t => densityProbability m (ρ t) (hρ t) (hmass t)) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have heq : (fun t => ∫ x,f x ∂(densityProbability m (ρ t) (hρ t) (hmass t) : Measure X)) =
      (fun t => ⟪BoundedContinuousFunction.toLp 2 m ℝ f,ρ t⟫_ℝ) := by
    funext t
    exact integral_densityMeasure_boundedContinuous m (ρ t) (hρ t) f
  rw [heq]
  exact continuous_const.inner hcont
end WeakHessianTransport

namespace WeakHessianTransport
open WeakHessian WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma proper_density_coupling_bound (h : QuadraticCheegerEnergy m)
    {ρ u A : ℝ → Lp ℝ 2 m} {α c C : ℝ}
    (hα : 0 < α) (hρ : ContinuousOn ρ (Icc 0 1))
    (hpos : ∀ t ∈ Icc 0 1, ∀ᵐ x ∂m, 0 ≤ ρ t x)
    (hmass : ∀ t ∈ Icc 0 1, ∫ x, ρ t x ∂m = 1)
    (hlower : ∀ t ∈ Ico 0 1, ∀ᵐ x ∂m, α ≤ ρ t x)
    (hgen : ∀ t ∈ Ico 0 1, (cheeger_closedQuadraticEnergy h).IsFormGenerator (u t) (A t))
    (hener : ∀ t ∈ Ico 0 1, (cheegerEnergy m (u t : X → ℝ)).toReal ≤ C)
    (hderiv : ∀ t ∈ Ico 0 1, HasDerivWithinAt ρ (c • A t) (Ici t) t) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (ρ 1) ∧
      q.map Prod.snd = densityMeasure m (ρ 0) ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal (2*c^2/α*C) := by
  let hp0 := densityMeasure_probability m (ρ 0) (hpos 0 (by norm_num)) (hmass 0 (by norm_num))
  let hp1 := densityMeasure_probability m (ρ 1) (hpos 1 (by norm_num)) (hmass 1 (by norm_num))
  apply exists_proper_coupling_cost_of_hopf_bound _ _ (2*c^2/α*C)
  intro f hf
  obtain ⟨L,hf⟩ := hf
  let f' : X →ᵇ ℝ := f
  have H := boundedHopfLp_transport_pairing_le m h (f := f') hf (by norm_num : (0:ℝ) ≤ 1)
    hα hρ hlower hgen hener hderiv
  have hq : (fun x => hopfLax f 1 x) = (boundedHopfMap f' 1 : X → ℝ) := by
    funext x
    exact (boundedHopfMap_apply_pos f' (by norm_num) x).symm
  rw [hq, integral_densityMeasure_boundedContinuous m _ (hpos 1 (by norm_num))]
  change _ - (∫ x, f' x ∂densityMeasure m (ρ 0)) ≤ _
  rw [integral_densityMeasure_boundedContinuous m _ (hpos 0 (by norm_num))]
  change ⟪boundedHopfLp m f' 1,ρ 1⟫_ℝ - ⟪BoundedContinuousFunction.toLp 2 m ℝ f',ρ 0⟫_ℝ ≤ _
  calc
    _ ≤ 1*c^2/α*C := H
    _ = _ := by ring

end WeakHessianTransport

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

end
end InlinedFile0

end OAI
