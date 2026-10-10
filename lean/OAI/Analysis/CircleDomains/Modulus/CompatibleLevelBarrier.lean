import OAI.Analysis.CircleDomains.Sobolev.CoordinateGradientSize
import OAI.Analysis.CircleDomains.Sobolev.PriorSmoothedCompatibility

namespace OAI

/-! The real barrier in the endpoint problem, with its actual physical
representative, countable enlarged flags, and finite-torus compatibility. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

structure CompatibleLevelBarrier (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (previous : PriorLevelFamily d.physicalDomain π) (flags EStar : Set Sphere)
    (regions : ℕ → Set Sphere) (f : d.quotientDomain → Sphere) (W₁ : Set Sphere) where
  coordinate : PhysicalRealCoordinate d π
  level : ℕ
  penalty : Set Sphere
  penalty_open : IsOpen penalty
  penalty_inside : closure penalty ⊆ d.quotientDomain
  penalty_disjoint : Disjoint d.anchor (closure penalty)
  penalty_avoids : ∀x : d.quotientDomain, x.val ∈ closure penalty → f x ∉ W₁
  zero : ∀x ∈ EStar, coordinate.quotient x = 0
  one : ∀x ∈ closure (regions level) ∩ d.quotientDomain, coordinate.quotient x = 1
  exclusions : Set Sphere
  exclusions_countable : exclusions.Countable
  prior_flags : flags ⊆ exclusions
  weight : Sphere → ℝ≥0∞
  weight_finite : (∑'s, weight s ^ 2) < ∞
  weight_support : support weight ⊆ exclusions
  band_bound : ∀s ∈ d.dust, ENNReal.ofReal
    (limsup coordinate.quotient (𝓝[d.quotientDomain] s) -
      liminf coordinate.quotient (𝓝[d.quotientDomain] s)) ≤ weight s
  compatible : ∀n labels, (volume.prod (Measure.pi (fun _ : Fin (n + 1) =>
    (volume : Measure UnitAddCircle))))
    (freeComponentFailure (d.dust \ exclusions)
      (circleBandGraph d.quotientDomain coordinate.quotient)
      (fun i => previous.graph i) labels) = 0

namespace CompatibleLevelBarrier

variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : PriorLevelFamily d.physicalDomain π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere} {W₁ : Set Sphere}

def controlledSize (B : CompatibleLevelBarrier d π previous flags EStar regions f W₁) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (∫x in FiniteTransfer.realChartDomain d.physicalDomain \
    (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' B.penalty,
      FiniteTransfer.gradientEnergy B.coordinate.physical
        (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x)) +
    countingSquareNorm B.weight

theorem finite_compatibility
    (B : CompatibleLevelBarrier d π previous flags EStar regions f W₁)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (d.dust \ B.exclusions)
        (circleBandGraph d.quotientDomain B.coordinate.quotient)
        (fun i => previous.graph i) labels) = 0 := by
  cases n with
  | zero => simp only [freeComponentFailure_empty_labels, measure_empty]
  | succ n => exact B.compatible n labels

theorem controlledSize_le_of_partial_bounds
    (B : CompatibleLevelBarrier d π previous flags EStar regions f W₁)
    {A : ℝ≥0∞} (hA : A ≠ ∞)
    (hbound : ∀i : Fin 2, eLpNorm (fun x => (fderiv ℝ B.coordinate.physical x)
      (if i = 0 then (1, 0) else (0, 1))) 2
      (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain \
        (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' B.penalty)) ≤ A) :
    B.controlledSize ≤ 2 * A + countingSquareNorm B.weight := by
  refine add_le_add ?_ le_rfl
  have hb := physical_coordinate_gradient_size_le d π B.coordinate
    (fun _ hx => hx.1) hA hbound
  have h := ENNReal.ofReal_le_ofReal hb
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hA] using h

end CompatibleLevelBarrier
end CircleDomainRigidity

end

end OAI
