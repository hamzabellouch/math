import OAI.MeasureTheory.Falconer.Measures.BorelProductPartition
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Exact original-law splitting over the finite coarse product filter

No approximation of the spatial indicators is needed. Each filter piece
is a product of Borel sets, so its integral uses the two restricted original
marginals. The number of summands is the already proved partition bound.
-/
namespace Falconer
open Set MeasureTheory
open scoped BigOperators
variable {d : ℕ}

theorem finite_product_restriction {ι : Type*} [Fintype ι]
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A B : ι → Set (Space d))
    (hm : ∀ i, MeasurableSet (A i) ∧ MeasurableSet (B i))
    (hd : Pairwise fun i j => Disjoint (A i ×ˢ B i) (A j ×ˢ B j)) :
    (μ.prod ν).restrict (⋃ i, A i ×ˢ B i) =
      ∑ i, (μ.restrict (A i)).prod (ν.restrict (B i)) := by
  rw [Measure.restrict_iUnion hd (fun i => (hm i).1.prod (hm i).2),
    Measure.sum_fintype]
  simp only [Measure.prod_restrict]

theorem HasBorelProductPartition.measurableSet {S : Set (Space d × Space d)} {K : ℝ}
    (h : HasBorelProductPartition S K) : MeasurableSet S := by
  obtain ⟨n,_,A,B,hm,_,rfl⟩ := h
  exact MeasurableSet.iUnion (fun i => (hm i).1.prod (hm i).2)

theorem HasBorelProductPartition.integral_split {S : Set (Space d × Space d)} {K : ℝ}
    (h : HasBorelProductPartition S K)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ n : ℕ, (n : ℝ) ≤ K ∧ ∃ A B : Fin n → Set (Space d),
      (∀ i, MeasurableSet (A i) ∧ MeasurableSet (B i)) ∧
      (∀ F : Space d × Space d → ℂ, Integrable F ((μ.prod ν).restrict S) →
        (∫ z in S, F z ∂μ.prod ν) =
          ∑ i, ∫ x in A i, ∫ y in B i, F (x,y) ∂ν ∂μ) := by
  obtain ⟨n,hn,A,B,hm,hd,rfl⟩ := h
  refine ⟨n,hn,A,B,hm,?_⟩
  intro F hF
  have hFi (i : Fin n) : Integrable F ((μ.restrict (A i)).prod (ν.restrict (B i))) := by
    rw [Measure.prod_restrict]
    exact hF.mono_measure (Measure.restrict_mono (subset_iUnion (fun i => A i ×ˢ B i) i) le_rfl)
  rw [finite_product_restriction μ ν A B hm hd,
    integral_finsetSum_measure (fun i _ => hFi i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_prod F (hFi i)

end Falconer

end OAI
