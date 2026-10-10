import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyWeak

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma CurvatureDimension.global_cheegerEnergy_eq_minimal {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) :
    cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2) := by
  have hle := hcd.global_cheegerEnergy_le_weak hfinite o hD.1
  have hch : cheegerEnergy m (f : X → ℝ) < ∞ := lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  obtain ⟨E,hE,henergy⟩ := exists_minimalGradient_energy_le_cheeger
    hfinite (Lp.memLp f) hch
  have heq : E = D := Lp.ext (hE.ae_eq hD)
  rw [heq] at henergy
  exact le_antisymm hle henergy

lemma CurvatureDimension.global_sobolev_iff_cheeger_lt_top {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Sobolev m f ↔ cheegerEnergy m f < ∞ := by
  constructor
  · intro hs
    have hD := (weakGradient_isMinimal hs.2.1.2).1
    have hw := hD.congr_ae hf.coeFn_toLp.symm hs.2.2.coeFn_toLp.symm
    have he := hcd.global_cheegerEnergy_le_weak hfinite o hw
    rw [cheegerEnergy_congr_ae hf.coeFn_toLp] at he
    exact lt_of_le_of_lt he ENNReal.ofReal_lt_top
  · intro hch
    obtain ⟨D,hD,_⟩ := exists_minimalGradient_energy_le_cheeger
      hfinite hf hch
    exact ⟨hf, ⟨fun _ _ _ => hf.restrict _, ⟨D,hD⟩⟩,
      (Lp.memLp D).ae_eq (weakGradient_ae_eq_of_isMinimal hD).symm⟩

lemma CurvatureDimension.global_cheegerEnergy_eq_weakGradient {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
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
  have he := hcd.global_cheegerEnergy_eq_minimal hfinite o hD
  rwa [cheegerEnergy_congr_ae hf.1.coeFn_toLp] at he

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
