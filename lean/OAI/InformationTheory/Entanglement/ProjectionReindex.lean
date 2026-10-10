import OAI.InformationTheory.Entanglement.ProjectionData

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace ProjectionCriterion
open ChannelCompletion
variable {Q K D I D' I' : Type} [Fintype Q] [Fintype K] [Fintype D] [Fintype I]
  [Fintype D'] [Fintype I'] [DecidableEq Q] [DecidableEq K] [DecidableEq D]
  [DecidableEq I] [DecidableEq D'] [DecidableEq I']
omit [DecidableEq D] [DecidableEq D'] in
lemma trace_reindex (e : D' ≃ D) (A : Mat D) :
    Matrix.trace (A.submatrix e e)=Matrix.trace A :=
  e.sum_comp (fun i => A i i)
namespace Data
variable (d : Data Q K D I) (eD : D' ≃ D) (eI : I' ≃ I)
def reindexP (i : I') : Mat D' := (d.P (eI i)).submatrix eD eD
omit [Fintype I'] [DecidableEq K] [DecidableEq I] [DecidableEq D'] [DecidableEq I'] in
lemma reindexP_overlap (i j : I') :
    Matrix.trace (d.reindexP eD eI i*d.reindexP eD eI j)=
      Matrix.trace (d.P (eI i)*d.P (eI j)) := by
  rw [reindexP,reindexP,Matrix.submatrix_mul_equiv,trace_reindex]
omit [Fintype D'] [DecidableEq K] [DecidableEq I] [DecidableEq I'] in
lemma reindexP_complete (q : Q) :
    ∑ i : I' with d.question (eI i)=q, d.reindexP eD eI i=1 := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ i : I, if d.question i=q then (d.P i).submatrix eD eD else 0 :=
      eI.sum_comp _
    _ = (∑ i : I with d.question i=q, d.P i).submatrix eD eD := by
      ext a b
      simp only [Matrix.sum_apply,Matrix.submatrix_apply,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs <;> rfl
    _ = 1 := by rw [d.complete,Matrix.submatrix_one_equiv]
omit [Fintype I'] [DecidableEq K] [DecidableEq D'] [DecidableEq I'] in
lemma reindexP_clique (J : Finset I')
    (hJ : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → 0 < (Matrix.trace (d.reindexP eD eI i*d.reindexP eD eI j)).re) :
    (J.card : ℝ) ≤ d.κ := by
  have hh := d.clique (J.image eI) (by
    intro i hi j hj hij
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hj
    rw [← d.reindexP_overlap eD eI]
    exact hJ a ha b hb (fun he => hij (he ▸ rfl)))
  simpa only [Finset.card_image_of_injective _ eI.injective] using hh

def reindex : Data Q K D' I' where
  question i := d.question (eI i)
  u := d.u
  unit := d.unit
  P := d.reindexP eD eI
  hermitian i := (d.hermitian (eI i)).submatrix eD
  idempotent i := by rw [reindexP,Matrix.submatrix_mul_equiv,d.idempotent]
  orthogonal i j hq hij := by
    rw [reindexP,reindexP,Matrix.submatrix_mul_equiv,
      d.orthogonal (eI i) (eI j) hq (eI.injective.ne hij)]
    rfl
  complete := d.reindexP_complete eD eI
  commute i j h := by
    rw [reindexP,reindexP,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,d.commute _ _ h]
  κ := d.κ
  gap := d.gap
  clique := d.reindexP_clique eD eI
end Data
end ProjectionCriterion

end

end OAI
