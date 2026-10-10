import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyComparable
import OAI.Geometry.WeakHessian.Measure.AeIntegralPositiveLipschitz

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
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

lemma sobolev_of_cheegerEnergy_lt_top (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : cheegerEnergy m f < ∞) : Sobolev m f := by
  have hfm : MemLp f 2 m := by
    by_contra hn
    simp only [cheegerEnergy, ite_eq_right hn, lt_self_iff_false] at hf
  obtain ⟨D,hD,_⟩ := exists_minimalGradient_energy_le_cheeger hfinite hfm hf
  refine ⟨hfm,⟨fun _ _ _ => hfm.restrict _, D,hD⟩,?_⟩
  exact (Lp.memLp D).ae_eq (hD.ae_eq (weakGradient_isMinimal ⟨D,hD⟩))

lemma integral_parallelogram_of_cheeger (hfinite : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) :
    (∫ x, (weakGradient m (fun y => f y+g y) x)^2 ∂m) +
      (∫ x, (weakGradient m (fun y => f y-g y) x)^2 ∂m) =
    2*(∫ x, (weakGradient m f x)^2 ∂m) + 2*(∫ x, (weakGradient m g x)^2 ∂m) := by
  have H := h f g (by rw [hID f hf]; exact ENNReal.ofReal_lt_top)
    (by rw [hID g hg]; exact ENNReal.ofReal_lt_top)
  rw [hID _ (hf.add hfinite hg),hID _ (hf.sub hfinite hg),hID f hf,hID g hg] at H
  have Hr := congrArg ENNReal.toReal H
  have hp : 0 ≤ (∫ x, (weakGradient m (fun y => f y+g y) x)^2 ∂m)/2 := by positivity
  have hm : 0 ≤ (∫ x, (weakGradient m (fun y => f y-g y) x)^2 ∂m)/2 := by positivity
  have hf0 : 0 ≤ (∫ x, (weakGradient m f x)^2 ∂m)/2 := by positivity
  have hg0 : 0 ≤ (∫ x, (weakGradient m g x)^2 ∂m)/2 := by positivity
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hm,
    ENNReal.toReal_ofReal hf0, ENNReal.toReal_ofReal hg0] at Hr
  linarith

lemma cheegerEnergy_integral_of_comparable (hfinite : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy ν f = ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂ν)/2) := by
  let f' := hf.1.toLp f
  let D' := hf.2.2.toLp (weakGradient m f)
  have hD : IsMinimalLocalWeakUpperGradient m (f' : X → ℝ) (D' : X → ℝ) :=
    (weakGradient_isMinimal hf.2.1.2).congr_ae hf.1.coeFn_toLp.symm hf.2.2.coeFn_toLp.symm
  have he : cheegerEnergy m (f' : X → ℝ) = ENNReal.ofReal (‖D'‖^2/2) := by
    rw [cheegerEnergy_congr_ae hf.1.coeFn_toLp,hID f hf,norm_toLp_sq_eq_integral]
  have H := cheegerEnergy_eq_of_comparable hfinite hm hν hD he
  have ha : (f' : X → ℝ) =ᵐ[ν] f := (Measure.absolutelyContinuous_of_le_smul hν).ae_eq hf.1.coeFn_toLp
  rw [cheegerEnergy_congr_ae ha] at H
  rw [H]
  congr 2
  let Dν := Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D'
  have heq : Dν = (hf.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).toLp (weakGradient m f) :=
    changeLp_toLp ENNReal.coe_ne_top hν hf.2.2
  change ‖Dν‖^2 = _
  rw [heq,norm_toLp_sq_eq_integral]

lemma quadraticCheegerEnergy_of_comparable [ProperSpace X]
    (hfinite : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m) :
    QuadraticCheegerEnergy ν := by
  intro f g hf hg
  have hfiniteν := hfinite.of_measure_le_smul ENNReal.coe_ne_top hν
  have hfm : Sobolev m f := (sobolev_iff_of_comparable hν hm f).mp
    (sobolev_of_cheegerEnergy_lt_top hfiniteν hf)
  have hgm : Sobolev m g := (sobolev_iff_of_comparable hν hm g).mp
    (sobolev_of_cheegerEnergy_lt_top hfiniteν hg)
  have hp := hfm.add hfinite hgm
  have hn := hfm.sub hfinite hgm
  have hpar := weakGradient_pointwise_parallelogram hfinite
    (fun _ _ hf hg => integral_parallelogram_of_cheeger hfinite h hID hf hg) hfm hgm
  have hparν := (Measure.absolutelyContinuous_of_le_smul hν).ae_le hpar
  have hpf := (hp.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).integrable_sq
  have hnf := (hn.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).integrable_sq
  have hff := (hfm.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).integrable_sq
  have hgf := (hgm.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).integrable_sq
  have hi : (∫ x, (weakGradient m (fun y => f y+g y) x)^2 ∂ν) +
      (∫ x, (weakGradient m (fun y => f y-g y) x)^2 ∂ν) =
    2*(∫ x, (weakGradient m f x)^2 ∂ν) + 2*(∫ x, (weakGradient m g x)^2 ∂ν) := by
    rw [← integral_add hpf hnf, ← integral_const_mul 2, ← integral_const_mul 2,
      ← integral_add (hff.const_mul 2) (hgf.const_mul 2)]
    exact integral_congr_ae hparν
  rw [cheegerEnergy_integral_of_comparable hfinite hID hm hν hp,
    cheegerEnergy_integral_of_comparable hfinite hID hm hν hn,
    cheegerEnergy_integral_of_comparable hfinite hID hm hν hfm,
    cheegerEnergy_integral_of_comparable hfinite hID hm hν hgm]
  have hp0 : 0 ≤ (∫ x, (weakGradient m (fun y => f y+g y) x)^2 ∂ν)/2 := by positivity
  have hn0 : 0 ≤ (∫ x, (weakGradient m (fun y => f y-g y) x)^2 ∂ν)/2 := by positivity
  have hf0 : 0 ≤ (∫ x, (weakGradient m f x)^2 ∂ν)/2 := by positivity
  have hg0 : 0 ≤ (∫ x, (weakGradient m g x)^2 ∂ν)/2 := by positivity
  rw [← ENNReal.ofReal_add hp0 hn0, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
