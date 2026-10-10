import OAI.MeasureTheory.Falconer.Estimates.EvenPreparation
import OAI.MeasureTheory.Falconer.Measures.BorelProductPartition

namespace OAI

/-! # Original starting pairs with the complete finite-filter interface

The pair and its Frostman gap are fixed before the coarse loss is chosen.
All cap bounds and partitions concern the original marginal laws.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

structure PreparedOriginalPair {d : ℕ} (E : Set (Space d)) (ε : ℝ) where
  auxiliaryDimension : ℕ
  exponent : ℝ
  exponent_gt : (d:ℝ)/2 < exponent
  base : ProbabilityMeasure (Space d)
  pair : ProjectedStartingPair base auxiliaryDimension exponent ε
  left_subset : (pair.left : Measure (Space d)).support ⊆ E
  right_subset : (pair.right : Measure (Space d)).support ⊆ E
  filters : ∀ ω : ℝ, 0 < ω → ω ≤ 1 →
    ∃ Γ : ℕ → Set (Space d × Space d),
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < ((pair.left : Measure (Space d)).prod (pair.right : Measure (Space d))) (⋂ N, Γ N) ∧
      (∀ N, Γ N ⊆ pair.relation) ∧
      (∀ N, HasBorelProductPartition (Γ N) ((2:ℝ)^(2*(d:ℝ)*ω*(N:ℝ)))) ∧
      CapAvailable pair.left pair.right Γ ((d:ℝ)/2)

theorem even_prepared_original_pair
    (hF : PublishedFrostmanAboveHalf) (hR : PublishedRadialMoment)
    {h : ℕ} (hh : 1 ≤ h) (E : Set (Space (2*h))) (hE : IsCompact E)
    (hDim : ((2*h:ℕ):ℝ≥0∞)/2 < dimH E) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (PreparedOriginalPair E ε) := by
  obtain ⟨ζ,δ,hδ,_,p,hleft,hright,hcap⟩ :=
    even_starting_pairs_of_published hF hR hh E hE hDim hε
  have hhalf : ((2*h:ℕ):ℝ)/2 = (h:ℝ) := by push_cast; ring
  refine ⟨{
    auxiliaryDimension := h+1
    exponent := (h:ℝ)+δ
    exponent_gt := by rw [hhalf]; linarith
    base := ζ
    pair := p
    left_subset := hleft
    right_subset := hright
    filters := ?_ }⟩
  intro ω hω _
  refine ⟨fun _ => p.relation,fun _ => p.relation_measurable,
    fun _ _ _ => subset_rfl,?_,fun _ => subset_rfl,?_,?_⟩
  · rw [iInter_const,p.relation_mass]
    norm_num
  · intro N
    have hbound : (1:ℝ) ≤ (2:ℝ)^(2*((2*h:ℕ):ℝ)*ω*(N:ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    exact (borel_product_partition_single Measure.isClosed_support.measurableSet
      Measure.isClosed_support.measurableSet).mono_bound hbound
  · simpa only [hhalf] using hcap

end Falconer

end OAI
