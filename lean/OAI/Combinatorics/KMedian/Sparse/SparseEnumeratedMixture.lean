import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseEnumeratedBatch
import OAI.Combinatorics.KMedian.Sparse.SparseEnumeratedCount

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem balanced_map (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (ω : Fin n → Bool) :
    (PhysicalBatchLaw.balanced (Z.map enum.symm.toEmbedding)
      (fun a => (C (enum a)).map enum.symm.toEmbedding) ω).map enum.toEmbedding=
      PhysicalBatchLaw.balanced Z C (fun e => ω (enum.symm e)) := by
  ext e
  simp only [mem_map_equiv,PhysicalBatchLaw.balanced,mem_inter,FiniteLaw.selected,
    mem_filter,mem_univ,true_and,Equiv.symm_symm,Equiv.apply_symm_apply]
  constructor
  · rintro ⟨⟨he,hc⟩,hz⟩
    refine ⟨⟨he,?_⟩,hz⟩
    intro j hj
    exact hc (enum.symm j) (by simpa only [Equiv.apply_symm_apply] using hj)
  · rintro ⟨⟨he,hc⟩,hz⟩
    refine ⟨⟨he,?_⟩,hz⟩
    intro j hj
    simpa only [Equiv.symm_apply_apply] using hc (enum j) hj

theorem unbalanced_map (enum : Fin n ≃ E) (Z : Finset E) (ω : Fin n → Bool) :
    (PhysicalBatchLaw.unbalanced (Z.map enum.symm.toEmbedding) ω).map enum.toEmbedding=
      PhysicalBatchLaw.unbalanced Z (fun e => ω (enum.symm e)) := by
  ext e
  simp only [mem_map_equiv,PhysicalBatchLaw.unbalanced,mem_filter,mem_univ,true_and,
    Equiv.symm_symm,Equiv.apply_symm_apply]

theorem prob_eq (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (R : Finset E → Prop) [DecidablePred R] :
    (law enum Z C p q hp hq).real.prob R=
      (1/2)*(SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hp)).real.prob
        (fun ω => R (PhysicalBatchLaw.balanced Z C ω))+
      (1/2)*(SparseEnumeratedBernoulli.law enum q hq).real.prob
        (fun ω => R (PhysicalBatchLaw.unbalanced Z ω)) := by
  rw [law,SparseIntegerLaw.prob_map,SparsePhysicalBatch.prob_eq,
    SparseEnumeratedBernoulli.law,SparseIntegerLaw.prob_map,
    SparseEnumeratedBernoulli.law,SparseIntegerLaw.prob_map]
  simp only [balanced_map,unbalanced_map]

end MetricKMedian.SparseEnumeratedBatch
end
end

end OAI
