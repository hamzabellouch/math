import OAI.InformationTheory.QuantumCircuit.Trajectory

namespace OAI

/-! Local support and degree bounds for quantum operators. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial

namespace QAC

def TensorSupported {N : ℕ} (J : Finset (Fin N)) (A : Operator N) : Prop :=
  ∃ a : Fin N → QubitOperator, A = tensorMatrix a ∧ ∀ i ∉ J, a i = 1

def degreeSpace (N : ℕ) (r : ℝ) : Submodule ℂ (Operator N) :=
  Submodule.span ℂ {A | ∃ J : Finset (Fin N), (J.card : ℝ) ≤ r ∧ TensorSupported J A}

def HasDegreeLE {N : ℕ} (A : Operator N) (r : ℝ) : Prop := A ∈ degreeSpace N r

lemma HasDegreeLE.mono {N : ℕ} {A : Operator N} {r s : ℝ}
    (h : HasDegreeLE A r) (hrs : r ≤ s) : HasDegreeLE A s := by
  apply Submodule.span_mono ?_ h
  rintro A ⟨J, hJ, ha⟩
  exact ⟨J, hJ.trans hrs, ha⟩

lemma tensor_hasDegreeLE {N : ℕ} (J : Finset (Fin N)) (A : Operator N)
    (hA : TensorSupported J A) {r : ℝ} (hr : (J.card : ℝ) ≤ r) : HasDegreeLE A r :=
  Submodule.subset_span ⟨J, hr, hA⟩

lemma degree_zero {N : ℕ} (r : ℝ) : HasDegreeLE (0 : Operator N) r :=
  (degreeSpace N r).zero_mem

lemma degree_one {N : ℕ} {r : ℝ} (hr : 0 ≤ r) : HasDegreeLE (1 : Operator N) r := by
  apply tensor_hasDegreeLE ∅ _ _ (by simpa using hr)
  exact ⟨fun _ => 1, tensorMatrix_one.symm, by simp⟩

lemma HasDegreeLE.add {N : ℕ} {A B : Operator N} {r : ℝ}
    (hA : HasDegreeLE A r) (hB : HasDegreeLE B r) : HasDegreeLE (A + B) r :=
  (degreeSpace N r).add_mem hA hB

lemma HasDegreeLE.smul {N : ℕ} {A : Operator N} {r : ℝ}
    (hA : HasDegreeLE A r) (c : ℂ) : HasDegreeLE (c • A) r :=
  (degreeSpace N r).smul_mem c hA

lemma degree_sum {N : ℕ} {ι : Type*} (s : Finset ι) (A : ι → Operator N) {r : ℝ}
    (hA : ∀ i ∈ s, HasDegreeLE (A i) r) : HasDegreeLE (∑ i ∈ s, A i) r :=
  (degreeSpace N r).sum_mem hA

lemma degree_list_sum {N : ℕ} (l : List (Operator N)) {r : ℝ}
    (hl : ∀ A ∈ l, HasDegreeLE A r) : HasDegreeLE l.sum r := by
  induction l with
  | nil => exact degree_zero r
  | cons A l ih =>
    exact (hl A (List.mem_cons_self ..)).add
      (ih (fun B hB => hl B (List.mem_cons_of_mem A hB)))

lemma TensorSupported.mul {N : ℕ} {J K : Finset (Fin N)} {A B : Operator N}
    (hA : TensorSupported J A) (hB : TensorSupported K B) : TensorSupported (J ∪ K) (A * B) := by
  rcases hA with ⟨a, rfl, ha⟩
  rcases hB with ⟨b, rfl, hb⟩
  refine ⟨fun i => a i * b i, tensorMatrix_mul a b, ?_⟩
  intro i hi
  have hiJ : i ∉ J := fun h => hi (Finset.mem_union_left K h)
  have hiK : i ∉ K := fun h => hi (Finset.mem_union_right J h)
  simp only [ha i hiJ, hb i hiK, one_mul]

lemma HasDegreeLE.mul {N : ℕ} {A B : Operator N} {r s : ℝ}
    (hA : HasDegreeLE A r) (hB : HasDegreeLE B s) : HasDegreeLE (A * B) (r + s) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    rcases hA with ⟨J, hJ, ha⟩
    induction hB using Submodule.span_induction with
    | mem B hB =>
      rcases hB with ⟨K, hK, hb⟩
      apply tensor_hasDegreeLE (J ∪ K) _ (ha.mul hb)
      have hcard : ((J ∪ K).card : ℝ) ≤ J.card + K.card := by
        exact_mod_cast Finset.card_union_le J K
      exact hcard.trans (add_le_add hJ hK)
    | zero => simpa only [mul_zero] using degree_zero (N := N) (r + s)
    | add B C _ _ hb hc => simpa only [mul_add] using hb.add hc
    | smul c B _ hb => simpa only [mul_smul_comm] using hb.smul c
  | zero => simpa only [zero_mul] using degree_zero (N := N) (r + s)
  | add A C _ _ ha hc => simpa only [add_mul] using ha.add hc
  | smul c A _ ha => simpa only [smul_mul_assoc] using ha.smul c

lemma HasDegreeLE.pow {N : ℕ} {A : Operator N} {r : ℝ}
    (hA : HasDegreeLE A r) (k : ℕ) : HasDegreeLE (A ^ k) ((k : ℝ) * r) := by
  induction k with
  | zero => simpa using degree_one (N := N) (le_refl (0 : ℝ))
  | succ k ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hA

lemma Count.zero_degree {N : ℕ} (A : Count N) :
    HasDegreeLE A.zero (A.support.card : ℝ) := by
  apply tensor_hasDegreeLE A.support _ _ le_rfl
  exact ⟨_, rfl, by intro i hi; simp [hi]⟩

lemma Count.operator_degree {N : ℕ} (A : Count N) : HasDegreeLE A.operator 1 := by
  apply degree_sum
  intro i _
  apply tensor_hasDegreeLE {i} _ _ (by simp)
  exact ⟨_, rfl, by intro j hj; simp only [Finset.mem_singleton] at hj; simp [hj]⟩

lemma Count.polynomial_degree {N : ℕ} (A : Count N) (p : ℝ[X]) :
    HasDegreeLE (A.polynomial p) (p.natDegree : ℝ) := by
  rw [A.polynomial_eq_sum]
  apply degree_sum
  intro k hk
  have hk' : (k : ℝ) ≤ p.natDegree := by exact_mod_cast le_natDegree_of_ne_zero (mem_support_iff.mp hk)
  change HasDegreeLE ((p.coeff k : ℂ) • A.operator ^ k) (p.natDegree : ℝ)
  exact ((A.operator_degree.pow k).mono (by simpa using hk')).smul _

lemma TensorSupported.local_conjugate {N : ℕ} {J : Finset (Fin N)}
    {A : Operator N} (hA : TensorSupported J A) (L : LocalLayer N) :
    TensorSupported J (conjugate (localMatrix L) A) := by
  rcases hA with ⟨a, rfl, ha⟩
  refine ⟨fun i => (L i : QubitOperator) * a i * star (L i : QubitOperator), ?_, ?_⟩
  · simp only [conjugate, localMatrix, tensorMatrix_star, tensorMatrix_mul]
  · intro i hi
    change (L i : QubitOperator) * a i * star (L i : QubitOperator) = 1
    rw [ha i hi, mul_one, Unitary.mul_star_self_of_mem (L i).property]

lemma HasDegreeLE.local_conjugate {N : ℕ} {A : Operator N} {r : ℝ}
    (hA : HasDegreeLE A r) (L : LocalLayer N) :
    HasDegreeLE (conjugate (localMatrix L) A) r := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    rcases hA with ⟨J, hJ, ha⟩
    exact tensor_hasDegreeLE J _ (ha.local_conjugate L) hJ
  | zero => simpa [conjugate] using degree_zero (N := N) r
  | add A B _ _ ha hb => simpa [conjugate, mul_add, add_mul] using ha.add hb
  | smul c A _ ha => simpa [conjugate, mul_smul_comm, smul_mul_assoc] using ha.smul c

end QAC

end

end OAI
