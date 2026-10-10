import OAI.InformationTheory.QuantumCircuit.Computational

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

/-- The zero-ancilla computational subspace, without any condition on final garbage. -/
def ancillaValid {N : ℕ} (n : ℕ) (z : Word N) : Prop := ∀ i, n ≤ i.val → z i=0

instance {N : ℕ} (n : ℕ) (z : Word N) : Decidable (ancillaValid n z) := by
  unfold ancillaValid
  infer_instance

def restrictWord {n N : ℕ} (hnN : n ≤ N) (z : Word N) : Word n :=
  fun i => z ⟨i.val,lt_of_lt_of_le i.isLt hnN⟩

lemma restrict_inputWord {n N : ℕ} (hnN : n ≤ N) (x : Word n) :
    restrictWord hnN (inputWord x)=x := by
  funext i
  simp [restrictWord,inputWord,i.isLt]

lemma inputWord_injective {n N : ℕ} (hnN : n ≤ N) :
    Function.Injective (@inputWord n N) :=
  Function.LeftInverse.injective (restrict_inputWord hnN)

lemma inputWord_valid {n N : ℕ} (x : Word n) : ancillaValid n (@inputWord n N x) := by
  intro i hi
  simp [inputWord,not_lt.mpr hi]

lemma input_restrictWord {n N : ℕ} (hnN : n ≤ N) (z : Word N) (hz : ancillaValid n z) :
    inputWord (restrictWord hnN z)=z := by
  funext i
  by_cases hi : i.val<n
  · simp [inputWord,hi,restrictWord]
  · simp [inputWord,hi,hz i (not_lt.mp hi)]

lemma sum_ancillaValid {n N : ℕ} (hnN : n ≤ N) {α : Type*} [AddCommMonoid α]
    (f : Word N → α) :
    (∑ z : Word N, if ancillaValid n z then f z else 0) = ∑ x : Word n, f (inputWord x) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun x _ => inputWord x)
  · intro x _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact inputWord_valid x
  · intro x _ y _ hxy
    exact inputWord_injective hnN hxy
  · intro z hz
    refine ⟨restrictWord hnN z,Finset.mem_univ _,?_⟩
    exact input_restrictWord hnN z (Finset.mem_filter.mp hz).2
  · intro x _
    rfl

def ancillaProjection (n N : ℕ) : Operator N :=
  tensorMatrix fun i => if i.val<n then 1 else rankOne (basisVector 0)

lemma ancillaProjection_diagonal (n N : ℕ) :
    ancillaProjection n N = Matrix.diagonal (fun z => if ancillaValid n z then 1 else 0) := by
  classical
  have hloc : (fun i : Fin N => if i.val<n then (1 : QubitOperator) else rankOne (basisVector 0)) =
      fun i => Matrix.diagonal (fun b => if n ≤ i.val → b=0 then (1:ℂ) else 0) := by
    funext i
    by_cases hi : i.val<n
    · simp [hi,not_le.mpr hi,Matrix.diagonal_one]
    · simp [hi,not_lt.mp hi,rankOne_basis_diagonal]
  rw [ancillaProjection,hloc,tensorMatrix_diagonal]
  congr 1
  funext z
  by_cases hz : ancillaValid n z
  · rw [ite_eq_left hz]
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_left (hz i)
  · rw [ite_eq_right hz]
    obtain ⟨i,hi⟩ := not_forall.mp hz
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma inputHadamard_ancilla_flip (n N : ℕ) :
    localMatrix (inputHadamard n N)*(inputFlip n N*ancillaProjection n N)*
      localMatrix (inputHadamard n N) = inputPhase n N*ancillaProjection n N := by
  unfold localMatrix inputFlip inputPhase ancillaProjection
  simp only [tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i.val<n
  · simpa only [inputHadamard,ite_eq_left hi,hadamardGate,mul_one] using bitH_X_H
  · simp [inputHadamard,hi]

lemma bitX_entry (a b : Bit) : bitX a b = if a=1-b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [bitX]

lemma inputFlip_entry (n N : ℕ) (x y : Word N) :
    inputFlip n N x y = if x=flipWord (inputSet n N) y then 1 else 0 := by
  classical
  have hloc (i : Fin N) : (if i.val<n then bitX else (1:QubitOperator)) (x i) (y i) =
      if x i=flipWord (inputSet n N) y i then 1 else 0 := by
    by_cases hi : i.val<n
    · simp [hi,bitX_entry,flipWord,inputSet]
    · simp [hi,Matrix.one_apply,flipWord,inputSet]
  simp only [inputFlip,tensorMatrix,hloc]
  rw [Fintype.prod_boole]
  simp only [← funext_iff]

lemma ancillaValid_flip {n N : ℕ} (z : Word N) :
    ancillaValid n (flipWord (inputSet n N) z) ↔ ancillaValid n z := by
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  simp [flipWord,inputSet,not_lt.mpr hi]

lemma inputFlip_mul_ancilla_entry {n N : ℕ} (B : Operator N) (z : Word N) :
    (inputFlip n N*ancillaProjection n N*B) z z =
      if ancillaValid n z then B (flipWord (inputSet n N) z) z else 0 := by
  classical
  rw [ancillaProjection_diagonal]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,inputFlip_entry]
  have hf (y : Word N) : z=flipWord (inputSet n N) y ↔ y=flipWord (inputSet n N) z := by
    constructor
    · intro h; rw [h,flipWord_involutive]
    · intro h; rw [h,flipWord_involutive]
  simp only [hf,ite_mul,zero_mul]
  simp [ancillaValid_flip]

lemma trace_flip_ancilla {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    Matrix.trace (inputFlip n N*ancillaProjection n N*B) =
      ∑ x : Word n, B (flipWord (inputSet n N) (inputWord x)) (inputWord x) := by
  simp only [Matrix.trace,Matrix.diag_apply,inputFlip_mul_ancilla_entry]
  exact sum_ancillaValid hnN _

end QAC

end

end OAI
