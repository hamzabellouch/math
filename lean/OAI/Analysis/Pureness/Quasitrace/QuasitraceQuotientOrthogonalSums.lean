import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientOrthogonal

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientValue_orthogonal_sum {ι : Type*} (s : Finset ι) (a : ι → T.CauchyQuotient hadd)
    (hn : ∀ i ∈ s, 0 ≤ a i) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → a i*a j=0) :
    T.quotientValue hadd hsqrt (∑ i ∈ s, a i) = ∑ i ∈ s, T.quotientValue hadd hsqrt (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,T.quotientValue_zero]
  | @insert i s hi ih =>
    have hns : ∀ j ∈ s, 0 ≤ a j := fun j hj => hn j (Finset.mem_insert_of_mem hj)
    have hos : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → a j*a k=0 := fun j hj k hk hjk =>
      ho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    have hab : a i*(∑ j ∈ s, a j)=0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact ho i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro h; exact hi (h ▸ hj))
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    rw [T.quotientValue_orthogonal_add hadd hsqrt
      ⟨a i,hn i (Finset.mem_insert_self _ _)⟩ ⟨∑ j ∈ s, a j,Finset.sum_nonneg hns⟩ hab]
    rw [ih hns hos]
end CuntzPureness.PositiveQuasitrace

end

end OAI
