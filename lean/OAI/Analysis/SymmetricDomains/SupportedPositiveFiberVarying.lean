import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetRoot

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set MeasureTheory Filter
open scoped Topology

theorem haar_image_null_of_equiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (e : E ≃L[ℝ] F) {A : E → F} {S : Set E}
    (hA : DifferentiableOn ℝ A S) (hS : μ S = 0) : ν (A '' S) = 0 := by
  have hz := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
    (e.symm.differentiable.comp_differentiableOn hA) hS
  apply (Measure.absolutelyContinuous_isAddHaarMeasure ν (μ.map e))
  change (Measure.map e.toHomeomorph μ) (A '' S) = 0
  rw [e.toHomeomorph.measurableEmbedding.map_apply]
  suffices he : e.toHomeomorph ⁻¹' (A '' S) = (e.symm ∘ A) '' S by rwa [he]
  ext y
  simp only [mem_preimage,mem_image,Function.comp_apply]
  constructor
  · rintro ⟨x,hx,hxy⟩
    exact ⟨x,hx,by rw [hxy]; exact e.symm_apply_apply y⟩
  · rintro ⟨x,hx,hxy⟩
    exact ⟨x,hx,by rw [← hxy]; exact (e.apply_symm_apply _).symm⟩

theorem supported_positive_fiber_varying
    {I P : Type*} [Countable I]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [MeasurableSpace P] [BorelSpace P]
    (ρ : Measure P) [ρ.IsAddHaarMeasure]
    (E F : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)]
    [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
    (μ : ∀ i, Measure (E i)) (ν : ∀ i, Measure (F i))
    [∀ i, (μ i).IsAddHaarMeasure] [∀ i, (ν i).IsAddHaarMeasure]
    (e : ∀ i, (E i × F i) ≃L[ℝ] P)
    (S : ∀ i, Set (E i × F i)) (hS : ∀ i, MeasurableSet (S i))
    (A : ∀ i, E i × F i → P) (hA : ∀ i, DifferentiableOn ℝ (A i) (S i))
    (bad : ∀ i, Set (E i)) (hbad : ∀ i, μ i (bad i) = 0)
    (T : Set P) (hT : ρ T ≠ 0) (hcover : T ⊆ ⋃ i, A i '' S i) :
    ∃ i x, x ∉ bad i ∧ ν i (Prod.mk x ⁻¹' S i) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hzero (i : I) : (μ i |>.prod (ν i)) (S i) = 0 := by
    apply Measure.measure_prod_null_of_ae_null (hS i)
    filter_upwards [show ∀ᵐ x ∂μ i, x ∉ bad i from by
      rw [ae_iff]
      simpa only [not_not,Set.ofPred_mem_eq] using hbad i] with x hx
    exact hn i x hx
  have himage (i : I) : ρ (A i '' S i) = 0 :=
    haar_image_null_of_equiv ((μ i).prod (ν i)) ρ (e i) (hA i) (hzero i)
  exact hT (measure_mono_null hcover (measure_iUnion_null himage))

end Release061

end

end OAI
