import OAI.NumberTheory.TwoPoint.Walks.WordRelations

namespace OAI

/-! Reindexing finite monomial relations preserves their events and supports. -/

namespace TwoPointCorrelations

open Finset

variable {ι τ σ : Type*} [DecidableEq ι] [Fintype τ] [Fintype σ]

omit [DecidableEq ι] in
lemma primeRelationEval_reindex (e : τ ≃ σ) (m : τ → PrimeMonomial ι)
    (n : σ → PrimeMonomial ι) (hm : ∀ i, n (e i) = m i) (x : ι → ℤ) :
    primeRelationEval n x = primeRelationEval m x := by
  unfold primeRelationEval
  rw [← e.sum_comp (fun i => (n i).eval x)]
  exact sum_congr rfl (fun i _ => by rw [hm])

lemma primeRelationCoefficient_reindex (e : τ ≃ σ) (m : τ → PrimeMonomial ι)
    (n : σ → PrimeMonomial ι) (hm : ∀ i, n (e i) = m i) (y : ι) (x : ι → ℤ) :
    primeRelationCoefficient n y x = primeRelationCoefficient m y x := by
  unfold primeRelationCoefficient
  rw [← e.sum_comp (fun i => (n i).coefficientAt y x)]
  exact sum_congr rfl (fun i _ => by rw [hm])

lemma primeRelationSupport_reindex (e : τ ≃ σ) (m : τ → PrimeMonomial ι)
    (n : σ → PrimeMonomial ι) (hm : ∀ i, n (e i) = m i) :
    primeRelationSupport n = primeRelationSupport m := by
  ext y
  simp only [primeRelationSupport, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨j, by simpa only [hm] using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e i, by simpa only [hm] using hi⟩

lemma primeRelationEvent_reindex (e : τ ≃ σ) (m : τ → PrimeMonomial ι)
    (n : σ → PrimeMonomial ι) (hm : ∀ i, n (e i) = m i)
    (selected control : ι) (x : ι → ℤ) :
    primeRelationEvent n selected control x ↔ primeRelationEvent m selected control x := by
  unfold primeRelationEvent
  rw [primeRelationEval_reindex e m n hm, primeRelationCoefficient_reindex e m n hm]

end TwoPointCorrelations

end OAI
