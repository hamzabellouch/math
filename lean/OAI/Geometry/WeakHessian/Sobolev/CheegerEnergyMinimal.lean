import Mathlib
import OAI.Geometry.WeakHessian.Calculus.NormSqLintegralEnorm
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyWeakBounded

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
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace

noncomputable section

namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [IsProbabilityMeasure m]

lemma CurvatureDimension.cheegerEnergy_eq_minimal {K N : ℝ}
    (hcd : CurvatureDimension m K N) (h : QuadraticCheegerEnergy m)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) :
    cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2) := by
  have hle := hcd.cheegerEnergy_le_weak h hD.1
  have hch : cheegerEnergy m (f : X → ℝ) < ∞ := lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  obtain ⟨E,hE,henergy⟩ := exists_minimalGradient_energy_le_cheeger
    (fun B _ => measure_lt_top m B) (Lp.memLp f) hch
  have heq : E = D := Lp.ext (hE.ae_eq hD)
  rw [heq] at henergy
  exact le_antisymm hle henergy

lemma CurvatureDimension.sobolev_iff_cheeger_lt_top {K N : ℝ}
    (hcd : CurvatureDimension m K N) (h : QuadraticCheegerEnergy m)
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Sobolev m f ↔ cheegerEnergy m f < ∞ := by
  constructor
  · intro hs
    have hD := (weakGradient_isMinimal hs.2.1.2).1
    have hw := hD.congr_ae hf.coeFn_toLp.symm hs.2.2.coeFn_toLp.symm
    have he := hcd.cheegerEnergy_le_weak h hw
    rw [cheegerEnergy_congr_ae hf.coeFn_toLp] at he
    exact lt_of_le_of_lt he ENNReal.ofReal_lt_top
  · intro hch
    obtain ⟨D,hD,_⟩ := exists_minimalGradient_energy_le_cheeger
      (fun B _ => measure_lt_top m B) hf hch
    exact ⟨hf, ⟨fun _ _ _ => hf.restrict _, ⟨D,hD⟩⟩,
      (Lp.memLp D).ae_eq (weakGradient_ae_eq_of_isMinimal hD).symm⟩

lemma CurvatureDimension.cheegerEnergy_eq_weakGradient {K N : ℝ}
    (hcd : CurvatureDimension m K N) (h : QuadraticCheegerEnergy m)
    {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy m f = ENNReal.ofReal (‖hf.2.2.toLp (weakGradient m f)‖^2/2) := by
  let D := hf.2.2.toLp (weakGradient m f)
  have hD : IsMinimalLocalWeakUpperGradient m (hf.1.toLp f) D := by
    have hm := weakGradient_isMinimal hf.2.1.2
    refine ⟨hm.1.congr_ae hf.1.coeFn_toLp.symm hf.2.2.coeFn_toLp.symm, ?_⟩
    intro E hE
    filter_upwards [hm.2 E (hE.congr_ae hf.1.coeFn_toLp Filter.EventuallyEq.rfl),
      hf.2.2.coeFn_toLp] with x hx hd
    exact hd.trans_le hx
  have he := hcd.cheegerEnergy_eq_minimal h hD
  rwa [cheegerEnergy_congr_ae hf.1.coeFn_toLp] at he

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

end
end
end
end InlinedFile0

end OAI
