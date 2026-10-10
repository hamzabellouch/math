import OAI.MeasureTheory.Falconer.Estimates.OriginalPairFilter
import OAI.MeasureTheory.Falconer.Measures.ProductCellPartition
import OAI.MeasureTheory.Falconer.Measures.BorelProductPartition

namespace OAI

/-! # Product partitions retain disjointness after the original-law pullback -/
namespace Falconer
open Set MeasureTheory
variable {d k N : ℕ} {ω : ℝ}

theorem continuous_image_support {μ : Measure (Space d)}
    (P : Space d →L[ℝ] Space k) {x : Space d} (hx : x ∈ μ.support) :
    P x ∈ (μ.map P).support := by
  have hclosed : IsClosed (P ⁻¹' (μ.map P).support) :=
    Measure.isClosed_support.preimage P.continuous
  apply Measure.support_subset_of_isClosed hclosed _ hx
  change μ (P ⁻¹' ((μ.map P).support)ᶜ) = 0
  rw [← Measure.map_apply P.continuous.measurable Measure.isClosed_support.measurableSet.compl]
  exact Measure.measure_compl_support

theorem lifted_dyadic_product_partition (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) (Q : DyadicCube k)
    (Γ : ℕ → Set (Space k × Space k)) (hω : 0 ≤ ω)
    (T : Finset (List (Fin k → Bool) × List (Fin k → Bool)))
    (hT : T ⊆ (cubePaths k ⌊ω*(N:ℝ)⌋₊).product (cubePaths k ⌊ω*(N:ℝ)⌋₊))
    (hΓ : Γ N = (⋃ pq ∈ T, (Q.descendant pq.1).carrier ×ˢ
      (Q.descendant pq.2).carrier) ∩ supportPair (μ.map P) (ν.map P)) :
    (T.card : ℝ) ≤ (2:ℝ)^(2*(k:ℝ)*ω*(N:ℝ)) ∧
    (∀ pq ∈ T,
      MeasurableSet ((μ : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.1).carrier) ∧
      MeasurableSet ((ν : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.2).carrier)) ∧
    (∀ pq ∈ T, ∀ ab ∈ T, pq ≠ ab →
      Disjoint
        (((μ : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.1).carrier) ×ˢ
         ((ν : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.2).carrier))
        (((μ : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant ab.1).carrier) ×ˢ
         ((ν : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant ab.2).carrier))) ∧
    liftedPairFilter μ ν P Γ N = ⋃ pq ∈ T,
      ((μ : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.1).carrier) ×ˢ
      ((ν : Measure (Space d)).support ∩ P ⁻¹' (Q.descendant pq.2).carrier) := by
  refine ⟨dyadic_product_card_bound hω T hT,?_,?_,?_⟩
  · intro pq _
    exact ⟨Measure.isClosed_support.measurableSet.inter
      ((Q.descendant pq.1).measurable.preimage P.continuous.measurable),
      Measure.isClosed_support.measurableSet.inter
      ((Q.descendant pq.2).measurable.preimage P.continuous.measurable)⟩
  · intro pq hpq ab hab hne
    apply Set.disjoint_left.mpr
    rintro ⟨x,y⟩ ⟨hx,hy⟩ ⟨hx',hy'⟩
    have hp : (P x,P y) ∈ (Q.descendant pq.1).carrier ×ˢ
        (Q.descendant pq.2).carrier := ⟨hx.2,hy.2⟩
    have ha : (P x,P y) ∈ (Q.descendant ab.1).carrier ×ˢ
        (Q.descendant ab.2).carrier := ⟨hx'.2,hy'.2⟩
    exact Set.disjoint_left.mp (Q.product_cells_disjoint (hT hpq) (hT hab) hne)
      hp ha
  · ext z
    simp only [liftedPairFilter,hΓ,supportPair,mem_inter_iff,mem_preimage,
      mem_iUnion,mem_prod]
    constructor
    · rintro ⟨⟨hx,hy⟩,⟨pq,hpq,hpx,hpy⟩,_⟩
      exact ⟨pq,hpq,⟨hx,hpx⟩,hy,hpy⟩
    · rintro ⟨pq,hpq,⟨hx,hpx⟩,hy,hpy⟩
      exact ⟨⟨hx,hy⟩,⟨pq,hpq,hpx,hpy⟩,continuous_image_support P hx,continuous_image_support P hy⟩


theorem lifted_pair_has_borel_product_partition (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) (Q : DyadicCube k)
    (Γ : ℕ → Set (Space k × Space k)) (hω : 0 ≤ ω)
    (T : Finset (List (Fin k → Bool) × List (Fin k → Bool)))
    (hT : T ⊆ (cubePaths k ⌊ω*(N:ℝ)⌋₊).product (cubePaths k ⌊ω*(N:ℝ)⌋₊))
    (hΓ : Γ N = (⋃ pq ∈ T, (Q.descendant pq.1).carrier ×ˢ
      (Q.descendant pq.2).carrier) ∩ supportPair (μ.map P) (ν.map P)) :
    HasBorelProductPartition (liftedPairFilter μ ν P Γ N)
      ((2:ℝ)^(2*(k:ℝ)*ω*(N:ℝ))) := by
  obtain ⟨hcard,hm,hd,heq⟩ := lifted_dyadic_product_partition μ ν P Q Γ hω T hT hΓ
  rw [heq]
  exact (borel_product_partition_of_finset T _ _ hm hd).mono_bound hcard

end Falconer

end OAI
