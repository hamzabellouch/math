import OAI.InformationTheory.Entanglement.ProjectionData

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace FiniteConstruction
open ChannelCompletion
variable {S V A : Type} [Fintype S] [Fintype V] [Fintype A]
  [DecidableEq S] [DecidableEq V]

def multiTensor (M : S → Mat V) : Mat (S → V) := fun i j => ∏ s, M s (i s) (j s)
omit [DecidableEq V] in
lemma multiTensor_mul (M N : S → Mat V) :
    multiTensor M*multiTensor N=multiTensor (fun s => M s*N s) := by
  ext i j
  simp only [Matrix.mul_apply,multiTensor,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun s : S => fun k : V => M s (i s) k*N s k (j s))).symm
omit [Fintype V] [DecidableEq S] in
lemma multiTensor_one : multiTensor (fun _ : S => (1 : Mat V))=1 := by
  ext i j
  simp only [multiTensor,Matrix.one_apply]
  rw [Fintype.prod_boole]
  simp only [funext_iff]
omit [Fintype V] [DecidableEq S] [DecidableEq V] in
lemma multiTensor_zero_of (M : S → Mat V) (s : S) (hs : M s=0) : multiTensor M=0 := by
  ext i j
  change (∏ t, M t (i t) (j t))=0
  exact Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs]; rfl)
omit [Fintype V] [DecidableEq S] [DecidableEq V] in
lemma multiTensor_adjoint (M : S → Mat V) :
    (multiTensor M)ᴴ=multiTensor (fun s => (M s)ᴴ) := by
  ext i j
  simp [multiTensor,Matrix.conjTranspose_apply]
omit [Fintype V] [DecidableEq S] [DecidableEq V] in
lemma multiTensor_hermitian (M : S → Mat V) (hM : ∀ s, (M s).IsHermitian) :
    (multiTensor M).IsHermitian := by
  rw [Matrix.IsHermitian,multiTensor_adjoint]
  simp_rw [(hM _).eq]
omit [DecidableEq V] in
lemma multiTensor_idempotent (M : S → Mat V) (hM : ∀ s, M s*M s=M s) :
    multiTensor M*multiTensor M=multiTensor M := by
  rw [multiTensor_mul]
  simp_rw [hM]
omit [DecidableEq V] in
lemma multiTensor_commute (M N : S → Mat V) (h : ∀ s, M s*N s=N s*M s) :
    multiTensor M*multiTensor N=multiTensor N*multiTensor M := by
  rw [multiTensor_mul,multiTensor_mul]
  simp_rw [h]
omit [DecidableEq V] in
lemma multiTensor_trace (M : S → Mat V) :
    Matrix.trace (multiTensor M)=∏ s, Matrix.trace (M s) := by
  change (∑ i : S → V, ∏ s, M s (i s) (i s))=∏ s, ∑ i, M s i i
  exact (Fintype.prod_sum (fun s : S => fun i : V => M s i i)).symm
omit [Fintype V] [DecidableEq V] in
lemma multiTensor_sum (M : S → A → Mat V) :
    (∑ a : S → A, multiTensor (fun s => M s (a s)))=
      multiTensor (fun s => ∑ a, M s a) := by
  ext i j
  simp only [Matrix.sum_apply,multiTensor]
  exact (Fintype.prod_sum (fun s : S => fun a : A => M s a (i s) (j s))).symm
omit [Fintype V] in
lemma multiTensor_complete (M : S → A → Mat V) (hM : ∀ s, ∑ a, M s a=1) :
    (∑ a : S → A, multiTensor (fun s => M s (a s)))=1 := by
  rw [multiTensor_sum]
  simp only [hM,multiTensor_one]
omit [Fintype A] [DecidableEq V] in
lemma multiTensor_orthogonal (M : S → A → Mat V)
    (hM : ∀ s a b, a ≠ b → M s a*M s b=0)
    (a b : S → A) (hab : a ≠ b) :
    multiTensor (fun s => M s (a s))*multiTensor (fun s => M s (b s))=0 := by
  rw [multiTensor_mul]
  obtain ⟨s,hs⟩ := Function.ne_iff.mp hab
  exact multiTensor_zero_of _ s (hM s _ _ hs)
omit [DecidableEq V] in
lemma multiTensor_trace_mul (M N : S → Mat V) :
    Matrix.trace (multiTensor M*multiTensor N)=∏ s, Matrix.trace (M s*N s) := by
  rw [multiTensor_mul,multiTensor_trace]
end FiniteConstruction

end

end OAI
