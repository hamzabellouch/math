import OAI.InformationTheory.QuantumCircuit.Ancilla

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma bitSign_add (a b : Bit) : bitSign (a+b)=bitSign a*bitSign b := by
  fin_cases a <;> fin_cases b <;> norm_num [bitSign,Fin.add_def,Fin.ext_iff]

lemma bitSign_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Bit) :
    bitSign (∑ i ∈ s, f i)=∏ i ∈ s, bitSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bitSign]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Finset.prod_insert hi,bitSign_add,ih]

lemma bitSign_parity {n : ℕ} (x : Word n) : bitSign (parity x)=∏ i, bitSign (x i) :=
  bitSign_finset_sum _ _

lemma sum_bitSign_parity {n : ℕ} (hn : 0<n) : (∑ x : Word n, bitSign (parity x))=0 := by
  simp only [bitSign_parity]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bit) => bitSign b)]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0,hn⟩ : Fin n)) (by norm_num [Fin.sum_univ_two,bitSign])

def inputSign {N : ℕ} (n : ℕ) (z : Word N) : ℝ :=
  ∏ i : Fin N, if i.val<n then bitSign (z i) else 1

lemma inputPhase_diagonal (n N : ℕ) :
    inputPhase n N = Matrix.diagonal (fun z => (inputSign n z:ℂ)) := by
  have hloc : (fun i : Fin N => if i.val<n then bitZ else (1:QubitOperator)) =
      fun i => Matrix.diagonal (fun b => ((if i.val<n then bitSign b else 1:ℝ):ℂ)) := by
    funext i
    split_ifs <;> simp [bitZ,Matrix.diagonal_one]
  rw [inputPhase,hloc,tensorMatrix_diagonal]
  congr 1
  funext z
  simp only [inputSign,Complex.ofReal_prod]

lemma inputSign_inputWord {n N : ℕ} (hnN : n ≤ N) (x : Word n) :
    inputSign n (@inputWord n N x)=bitSign (parity x) := by
  classical
  rw [inputSign,bitSign_parity,← Finset.prod_filter]
  symm
  apply Finset.prod_bij (fun i _ => Fin.castLE hnN i)
  · intro i _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_castLE]
    exact i.isLt
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun k : Fin N => k.val) hij)
  · intro i hi
    refine ⟨⟨i.val,(Finset.mem_filter.mp hi).2⟩,Finset.mem_univ _,?_⟩
    rfl
  · intro i _
    simp [inputWord,i.isLt]

lemma trace_phase_ancilla {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    Matrix.trace (inputPhase n N*ancillaProjection n N*B) =
      ∑ x : Word n, (bitSign (parity x):ℂ)*B (inputWord x) (inputWord x) := by
  classical
  rw [inputPhase_diagonal,ancillaProjection_diagonal,Matrix.diagonal_mul_diagonal]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.diagonal_mul]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  rw [sum_ancillaValid hnN]
  simp only [inputSign_inputWord hnN]

/-- Character orthogonality as a finite-dimensional cyclic trace identity. -/
lemma parity_trace_identity {n N : ℕ} (hnN : n ≤ N) (B : Operator N) :
    (∑ x : Word n, (localMatrix (inputHadamard n N)*B*localMatrix (inputHadamard n N))
      (flipWord (inputSet n N) (inputWord x)) (inputWord x)) =
    ∑ x : Word n, (bitSign (parity x):ℂ)*B (inputWord x) (inputWord x) := by
  rw [← trace_flip_ancilla hnN]
  let H := localMatrix (inputHadamard n N)
  let T := inputFlip n N*ancillaProjection n N
  change Matrix.trace (T*(H*B*H)) = _
  calc
    Matrix.trace (T*(H*B*H)) = Matrix.trace ((T*(H*B))*H) :=
      congrArg Matrix.trace (mul_assoc T (H*B) H).symm
    _ = Matrix.trace (H*T*(H*B)) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace ((H*T*H)*B) := by rw [mul_assoc (H*T) H B]
    _ = Matrix.trace (inputPhase n N*ancillaProjection n N*B) := by
      rw [show H*T*H=inputPhase n N*ancillaProjection n N from inputHadamard_ancilla_flip n N]
    _ = _ := trace_phase_ancilla hnN B

end QAC

end

end OAI
