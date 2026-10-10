import OAI.MeasureTheory.Falconer.Measures.PartitionMaskedMeasure
import OAI.MeasureTheory.Falconer.Shells.FilteredEndpointDistance

namespace OAI

/-! # Exact distance law for class-dependent endpoint masks -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

noncomputable def endpointPairMask (B C : Space d → Space d → ℝ)
    (z : Space d × Space d) : ℝ :=
  B z.1 (NormedSpace.normalize (z.1-z.2)) * C z.2 (NormedSpace.normalize (z.1-z.2))

theorem endpointPairMask_measurable (B C : Space d → Space d → ℝ)
    (hB : Measurable (Function.uncurry B)) (hC : Measurable (Function.uncurry C)) :
    Measurable (endpointPairMask B C) := by
  have hn : Measurable (fun z : Space d × Space d => NormedSpace.normalize (z.1-z.2)) := by
    unfold NormedSpace.normalize
    fun_prop
  exact (hB.comp (measurable_fst.prodMk hn)).mul (hC.comp (measurable_snd.prodMk hn))

noncomputable def partitionEndpointDistance (μ ν : Measure (Space d))
    (Γ : Set (Space d × Space d)) (F : Finset ι) (S T : ι → Set (Space d))
    (B C : ι → Space d → Space d → ℝ) : Measure ℝ :=
  (((μ.prod ν).restrict Γ).withDensity (fun z => ENNReal.ofReal
    ((dist z.1 z.2)^(-(((d:ℝ)-1)/2)) *
      finitePartitionMask F (fun i => S i ×ˢ T i) (fun i => endpointPairMask (B i) (C i)) z))).map
        (fun z => dist z.1 z.2)

theorem partitionEndpointDistance_eq_sum (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Γ : Set (Space d × Space d)) (_hΓ : MeasurableSet Γ)
    (F : Finset ι) (S T : ι → Set (Space d))
    (B C : ι → Space d → Space d → ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hT : ∀ i ∈ F, MeasurableSet (T i))
    (hB : ∀ i ∈ F, Measurable (Function.uncurry (B i)))
    (hC : ∀ i ∈ F, Measurable (Function.uncurry (C i)))
    (hB0 : ∀ i ∈ F, ∀ x w, 0 ≤ B i x w) (hC0 : ∀ i ∈ F, ∀ x w, 0 ≤ C i x w) :
    partitionEndpointDistance μ ν Γ F S T B C =
      ∑ i ∈ F, filteredEndpointDistance (μ.restrict (S i)) (ν.restrict (T i)) Γ (B i) (C i) := by
  unfold partitionEndpointDistance
  rw [finitePartitionMask_weighted_map _ F _ _ _ _
    (fun i hi => (hS i hi).prod (hT i hi))
    ((measurable_fst.dist measurable_snd).pow_const _)
    (fun i hi => endpointPairMask_measurable _ _ (hB i hi) (hC i hi))
    (by fun_prop) (fun _ => Real.rpow_nonneg dist_nonneg _)
    (fun i hi z => mul_nonneg (hB0 i hi _ _) (hC0 i hi _ _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.restrict_comm ((hS i hi).prod (hT i hi)),← Measure.prod_restrict]
  simp only [filteredEndpointDistance,endpointDistanceWeight,div_one,endpointPairMask,mul_assoc]

theorem partitionEndpointDistance_product_sum {κ : Type*} [Fintype κ]
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A D : κ → Set (Space d))
    (hm : ∀ j, MeasurableSet (A j) ∧ MeasurableSet (D j))
    (hd : Pairwise fun j k => Disjoint (A j ×ˢ D j) (A k ×ˢ D k))
    (F : Finset ι) (S T : ι → Set (Space d))
    (B C : ι → Space d → Space d → ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hT : ∀ i ∈ F, MeasurableSet (T i))
    (hB : ∀ i ∈ F, Measurable (Function.uncurry (B i)))
    (hC : ∀ i ∈ F, Measurable (Function.uncurry (C i)))
    (hB0 : ∀ i ∈ F, ∀ x w, 0 ≤ B i x w) (hC0 : ∀ i ∈ F, ∀ x w, 0 ≤ C i x w) :
    partitionEndpointDistance μ ν (⋃ j, A j ×ˢ D j) F S T B C =
      ∑ i ∈ F, ∑ j, endpointWeightedDistance (μ.restrict (A j ∩ S i))
        (ν.restrict (D j ∩ T i)) 1 1 1 (B i) (C i) := by
  rw [partitionEndpointDistance_eq_sum μ ν _
    (MeasurableSet.iUnion (fun j => (hm j).1.prod (hm j).2)) F S T B C hS hT hB hC hB0 hC0]
  apply Finset.sum_congr rfl
  intro i _
  rw [filteredEndpointDistance_product_sum _ _ A D hm hd]
  simp only [Measure.restrict_restrict (hm _).1,Measure.restrict_restrict (hm _).2]

end Falconer

end OAI
