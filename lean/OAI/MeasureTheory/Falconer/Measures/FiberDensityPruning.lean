import OAI.MeasureTheory.Falconer.Incidence.IncidenceMoment
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Density pruning uses the original fibers in every retained cell -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]

noncomputable def fiberDensityBad (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (θ : ℝ≥0∞) : Set (P × X) :=
  G ∩ ⋃ i ∈ I, {p | μ (Q i ∩ Prod.mk p ⁻¹' G) < θ*μ (Q i)} ×ˢ Q i

theorem fiberDensityBad_measurable (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ι → Set X)
    (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (θ : ℝ≥0∞) :
    MeasurableSet (fiberDensityBad μ G Q I θ) := by
  apply hG.inter
  apply Finset.measurableSet_biUnion I
  intro i hi
  have hS : MeasurableSet ((univ ×ˢ Q i) ∩ G) := (MeasurableSet.univ.prod (hQ i hi)).inter hG
  have hm : Measurable (fun p => μ (Q i ∩ Prod.mk p ⁻¹' G)) := by
    convert measurable_measure_prodMk_left (ν := μ) hS using 1
    ext p
    congr 1
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]
  exact (measurableSet_lt hm measurable_const).prod (hQ i hi)

omit [MeasurableSpace P] in
theorem fiberDensityBad_fiber_mass (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (θ : ℝ≥0∞) (p : P) :
    μ (Prod.mk p ⁻¹' fiberDensityBad μ G Q I θ) ≤ θ*μ univ := by
  classical
  let D := I.filter (fun i => μ (Q i ∩ Prod.mk p ⁻¹' G) < θ*μ (Q i))
  have hs : Prod.mk p ⁻¹' fiberDensityBad μ G Q I θ =
      ⋃ i ∈ D, Q i ∩ Prod.mk p ⁻¹' G := by
    ext x
    simp only [fiberDensityBad,mem_preimage,mem_inter_iff,mem_iUnion,mem_prod,
      mem_ofPred_eq,D,Finset.mem_filter]
    aesop
  have hsum : ∑ i ∈ I, μ (Q i) ≤ μ univ := by
    rw [← measure_biUnion_finset hdisj hQ]
    exact measure_mono (subset_univ _)
  rw [hs]
  calc
    _ ≤ ∑ i ∈ D, μ (Q i ∩ Prod.mk p ⁻¹' G) := measure_biUnion_finset_le D _
    _ ≤ ∑ i ∈ D, θ*μ (Q i) := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2.le)
    _ ≤ ∑ i ∈ I, θ*μ (Q i) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = θ*(∑ i ∈ I, μ (Q i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ θ*μ univ := mul_le_mul' le_rfl hsum

theorem fiberDensityBad_product_mass (ν : Measure P) (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ι → Set X)
    (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (θ : ℝ≥0∞) :
    (ν.prod μ) (fiberDensityBad μ G Q I θ) ≤ (θ*μ univ)*ν univ := by
  rw [Measure.prod_apply (fiberDensityBad_measurable μ G hG Q I hQ θ)]
  calc
    _ ≤ ∫⁻ _p, θ*μ univ ∂ν := lintegral_mono (fiberDensityBad_fiber_mass μ G Q I hQ hdisj θ)
    _ = _ := by rw [lintegral_const,mul_comm]

omit [MeasurableSpace P] in
theorem fiberDensity_retained (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (θ : ℝ≥0∞) {p : P} {x : X}
    (hx : (p,x) ∈ G \ fiberDensityBad μ G Q I θ)
    {i : ι} (hi : i ∈ I) (hxi : x ∈ Q i) :
    θ*μ (Q i) ≤ μ (Q i ∩ Prod.mk p ⁻¹' G) := by
  by_contra! hlt
  apply hx.2
  refine ⟨hx.1,mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,?_⟩⟩⟩
  exact ⟨hlt,hxi⟩

end Falconer

end OAI
