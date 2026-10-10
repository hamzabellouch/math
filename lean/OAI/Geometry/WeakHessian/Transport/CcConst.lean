import Mathlib

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
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

namespace WeakHessianTransport
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y]

def ccConst (X : Type*) [TopologicalSpace X] [CompactSpace X] (r : ℝ) : C_c(X,ℝ) :=
  ⟨ContinuousMap.const X r, HasCompactSupport.of_compactSpace _⟩

@[simp] lemma ccConst_apply (r : ℝ) (x : X) : ccConst X r x = r := rfl

def marginalSum : (C_c(X,ℝ) × C_c(Y,ℝ)) →ₗ[ℝ] C_c(X×Y,ℝ) where
  toFun fg := ⟨⟨fun p => fg.1 p.1+fg.2 p.2, by fun_prop⟩,
    HasCompactSupport.of_compactSpace _⟩
  map_add' a b := by
    ext p
    change (a.1 p.1+b.1 p.1)+(a.2 p.2+b.2 p.2) = (a.1 p.1+a.2 p.2)+(b.1 p.1+b.2 p.2)
    ring
  map_smul' r a := by
    ext p
    change r*a.1 p.1+r*a.2 p.2 = r*(a.1 p.1+a.2 p.2)
    ring

@[simp] lemma marginalSum_apply (fg : C_c(X,ℝ) × C_c(Y,ℝ)) (p : X×Y) :
    marginalSum fg p = fg.1 p.1 + fg.2 p.2 := rfl

lemma exists_marginal_majorant (h : C_c(X×Y,ℝ)) :
    ∃ fg : C_c(X,ℝ) × C_c(Y,ℝ), h ≤ marginalSum fg := by
  refine ⟨(ccConst X ‖h.toContinuousMap‖,0), ?_⟩
  intro p
  change h.toContinuousMap p ≤ ‖h.toContinuousMap‖ + 0
  simpa only [add_zero] using h.toContinuousMap.apply_le_norm p

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

def marginalIntegral (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (C_c(X,ℝ) × C_c(Y,ℝ)) →ₗ[ℝ] ℝ :=
  (integralPositiveLinearMap μ).toLinearMap.comp (LinearMap.fst ℝ _ _) +
    (integralPositiveLinearMap ν).toLinearMap.comp (LinearMap.snd ℝ _ _)

@[simp] lemma marginalIntegral_apply (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (fg : C_c(X,ℝ) × C_c(Y,ℝ)) :
    marginalIntegral μ ν fg = (∫ x, fg.1 x ∂μ) + ∫ y, fg.2 y ∂ν := rfl

lemma integral_marginalSum (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (fg : C_c(X,ℝ) × C_c(Y,ℝ)) :
    ∫ p, marginalSum fg p ∂μ.prod ν = marginalIntegral μ ν fg := by
  rw [integral_prod _ (marginalSum fg).integrable]
  simp only [marginalSum_apply, marginalIntegral_apply]
  have H (x : X) : (∫ y, (fg.1 x + fg.2 y) ∂ν) = fg.1 x + ∫ y, fg.2 y ∂ν := by
    rw [integral_add (integrable_const _) fg.2.integrable]
    simp
  simp_rw [H]
  rw [integral_add fg.1.integrable (integrable_const _)]
  simp

lemma exists_measure_of_positive_functional
    (g : C_c(X,ℝ) →ₗ[ℝ] ℝ) (hg : Monotone g) :
    ∃ q : Measure X, IsFiniteMeasure q ∧
      ∀ f : C_c(X,ℝ), (∫ x, f x ∂q) = g f := by
  let Λ : C_c(X,ℝ) →ₚ[ℝ] ℝ := { g with monotone' := hg }
  exact ⟨RealRMK.rieszMeasure Λ, inferInstance, RealRMK.integral_rieszMeasure Λ⟩

omit [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y] [BorelSpace X] [BorelSpace Y] in
lemma probability_of_first_marginal {μ : Measure X} [IsProbabilityMeasure μ]
    {q : Measure (X×Y)} (hfst : q.map Prod.fst = μ) : IsProbabilityMeasure q := by
  constructor
  have H := congrArg (fun η : Measure X => η univ) hfst
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
    measure_univ] using H

lemma integral_marginalSum_of_marginals (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : Measure (X×Y)}
    (hfst : q.map Prod.fst = μ) (hsnd : q.map Prod.snd = ν)
    (fg : C_c(X,ℝ) × C_c(Y,ℝ)) :
    (∫ p, marginalSum fg p ∂q) = marginalIntegral μ ν fg := by
  let _ := probability_of_first_marginal hfst
  have h0 : Integrable (fun p : X×Y => fg.1 p.1) q :=
    (fg.1.continuous.comp continuous_fst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h1 : Integrable (fun p : X×Y => fg.2 p.2) q :=
    (fg.2.continuous.comp continuous_snd).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ p, fg.1 p.1+fg.2 p.2 ∂q) = _
  rw [integral_add h0 h1]
  rw [← integral_map (μ := q) (f := fg.1) measurable_fst.aemeasurable (map_continuous fg.1).aestronglyMeasurable,
    ← integral_map (μ := q) (f := fg.2) measurable_snd.aemeasurable (map_continuous fg.2).aestronglyMeasurable,
    hfst, hsnd]
  rfl

lemma marginals_of_integral_identity (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : Measure (X×Y)}
    [IsFiniteMeasure q]
    (hq : ∀ fg : C_c(X,ℝ) × C_c(Y,ℝ),
      (∫ p, marginalSum fg p ∂q) = marginalIntegral μ ν fg) :
    q.map Prod.fst = μ ∧ q.map Prod.snd = ν := by
  constructor
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable]
    simpa only [marginalSum_apply, marginalIntegral_apply,
      CompactlySupportedContinuousMap.zero_apply, add_zero, integral_zero] using hq (f,0)
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_snd.aemeasurable (map_continuous f).aestronglyMeasurable]
    simpa only [marginalSum_apply, marginalIntegral_apply,
      CompactlySupportedContinuousMap.zero_apply, zero_add, integral_zero] using hq (0,f)

end WeakHessianTransport

end
end InlinedFile0

end OAI
