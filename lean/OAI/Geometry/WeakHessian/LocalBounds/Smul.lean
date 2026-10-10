import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.LocalSobolevLipschitz
import OAI.Geometry.WeakHessian.Entropy.LocalGradientParallelogram
import OAI.Geometry.WeakHessian.Measure.IntegralExponentialMeasure

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
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FiniteOnBoundedSets.of_le_smul (hfinite : FiniteOnBoundedSets m) {C : ℝ≥0}
    (hν : ν ≤ (C:ℝ≥0∞) • m) : FiniteOnBoundedSets ν := by
  intro s hs
  have H : (C:ℝ≥0∞)*m s < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (hfinite s hs)
  exact lt_of_le_of_lt (hν s) (by simpa only [Measure.smul_apply,smul_eq_mul] using H)

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocalGradientParallelogram.change_measure (hpar : LocalGradientParallelogram m)
    {C D : ℝ≥0} (hm : m ≤ (C:ℝ≥0∞) • ν) (hν : ν ≤ (D:ℝ≥0∞) • m) :
    LocalGradientParallelogram ν := by
  intro f g hf hg
  have hfm := (localSobolev_iff_of_comparable hm hν f).mpr hf
  have hgm := (localSobolev_iff_of_comparable hm hν g).mpr hg
  apply (Measure.absolutelyContinuous_of_le_smul hν).ae_le
  filter_upwards [hpar f g hfm hgm,weakGradient_eq_of_comparable hm hν f,
    weakGradient_eq_of_comparable hm hν g,
    weakGradient_eq_of_comparable hm hν (fun x => f x+g x),
    weakGradient_eq_of_comparable hm hν (fun x => f x-g x)] with x hp hf hg hplus hminus
  rwa [hf,hg,hplus,hminus] at hp

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma exponentialMeasure_neg {V : X → ℝ} (hV : AEMeasurable V m) :
    exponentialMeasure (exponentialMeasure m V) (fun x => -V x) = m := by
  change (m.withDensity (fun x => ENNReal.ofReal (Real.exp (V x)))).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-V x))) = m
  have h1 : AEMeasurable (fun x => ENNReal.ofReal (Real.exp (V x))) m :=
    (Real.measurable_exp.comp_aemeasurable hV).ennreal_ofReal
  have h2 : AEMeasurable (fun x => ENNReal.ofReal (Real.exp (-V x))) m :=
    (Real.measurable_exp.comp_aemeasurable hV.neg).ennreal_ofReal
  rw [← withDensity_mul₀ h1 h2]
  convert withDensity_one (μ := m) using 1
  congr 1
  funext x
  simp only [Pi.mul_apply,← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add,add_neg_cancel,Real.exp_zero,ENNReal.ofReal_one,Pi.one_apply]

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma IsLaplacian.congr_ae {f g L M : X → ℝ}
    (hf : IsLaplacian m f L) (hfg : f =ᵐ[m] g) (hLM : L =ᵐ[m] M) :
    IsLaplacian m g M := by
  refine ⟨(sobolev_congr_ae hfg).mp hf.1, hf.2.1.ae_eq hLM, ?_⟩
  intro v hv
  rw [← integral_congr_ae (gamma_congr_ae hfg (Filter.EventuallyEq.rfl)), hf.2.2 v hv]
  congr 1
  apply integral_congr_ae
  filter_upwards [hLM] with x hx
  rw [hx]

lemma IsLaplacian.of_exponentialMeasure (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A V : X → ℝ}
    {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ} (hB : ∀ x, |V x| ≤ B)
    (hA : IsLaplacian (exponentialMeasure m V) u A) :
    IsLaplacian m u (fun x => A x-gamma m V u x) := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  have hnfinite := hfinite.of_le_smul (C := (Real.exp B).toNNReal) hν
  have hnpar := hpar.change_measure (C := (Real.exp B).toNNReal)
    (D := (Real.exp B).toNNReal) hm hν
  have hnB : ∀ x, |(-V x)| ≤ B := fun x => by simpa only [abs_neg] using hB x
  have H := hA.reweight hnfinite hnpar hV.neg hnB
  dsimp only [Pi.neg_def] at H
  rw [exponentialMeasure_neg hV.continuous.aemeasurable] at H
  apply H.congr_ae EventuallyEq.rfl
  have hu : Sobolev m u := (sobolev_exponentialMeasure_iff hB u).mpr hA.1
  filter_upwards [gamma_exponentialMeasure (m := m) hB (fun x => -V x) u,
    gamma_neg_left hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.2.1] with x hc hn
  rw [← hc,hn,sub_eq_add_neg]

lemma inLaplacianDomain_exponentialMeasure_iff (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {V : X → ℝ}
    {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ} (hB : ∀ x, |V x| ≤ B)
    (u : X → ℝ) :
    (∃ A, IsLaplacian (exponentialMeasure m V) u A) ↔ ∃ A, IsLaplacian m u A := by
  constructor
  · rintro ⟨A,hA⟩
    exact ⟨_,hA.of_exponentialMeasure hfinite hpar hV hB⟩
  · rintro ⟨A,hA⟩
    exact ⟨_,hA.reweight hfinite hpar hV hB⟩
end WeakHessian

end
end InlinedFile0

end OAI
