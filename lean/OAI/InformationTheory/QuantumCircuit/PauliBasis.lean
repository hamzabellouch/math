import OAI.InformationTheory.QuantumCircuit.ProductSpectralResolution
import OAI.InformationTheory.QuantumCircuit.Computational

namespace OAI

/-! The tensor-product Pauli basis. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

def pauli (s : Fin 4) : QubitOperator :=
  if s = 0 then 1 else if s = 1 then !![0,1;1,0]
  else if s = 2 then !![1,0;0,-1] else !![0,1;-1,0]

@[simp] lemma pauli_zero : pauli 0 = 1 := by simp [pauli]

lemma pauli_unitary (s : Fin 4) : pauli s ∈ unitary QubitOperator := by
  rw [Unitary.mem_iff]
  fin_cases s <;> constructor <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    norm_num [pauli, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply]

lemma pauli_trace_star {s : Fin 4} (hs : s ≠ 0) : Matrix.trace (star (pauli s)) = 0 := by
  fin_cases s <;> simp_all [pauli, Matrix.trace, Matrix.star_apply, Fin.sum_univ_two]

lemma pauli_complete (x y u v : Bit) :
    (∑ s : Fin 4, pauli s x y * star (pauli s u v)) =
      if x = u ∧ y = v then (2 : ℂ) else 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases v <;>
    norm_num [pauli, Fin.sum_univ_succ, Matrix.one_apply]

def pauliTensor {N : ℕ} (w : Fin N → Fin 4) : Operator N :=
  tensorMatrix (fun i => pauli (w i))

def pauliSupport {N : ℕ} (w : Fin N → Fin 4) : Finset (Fin N) :=
  Finset.univ.filter (fun i => w i ≠ 0)

lemma pauliTensor_unitary {N : ℕ} (w : Fin N → Fin 4) :
    pauliTensor w ∈ unitary (Operator N) := tensorMatrix_unitary _ (fun i => pauli_unitary (w i))

lemma pauliTensor_complete {N : ℕ} (x y u v : Word N) :
    (∑ w : Fin N → Fin 4, pauliTensor w x y * star (pauliTensor w u v)) =
      if x = u ∧ y = v then (2 : ℂ)^N else 0 := by
  classical
  simp only [pauliTensor, tensorMatrix, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i s => pauli s (x i) (y i) * star (pauli s (u i) (v i)))]
  simp_rw [pauli_complete]
  by_cases h : x = u ∧ y = v
  · rcases h with ⟨rfl, rfl⟩
    simp
  · rw [ite_eq_right h]
    have hh : ∃ i, ¬ (x i = u i ∧ y i = v i) := by
      by_contra hn
      push Not at hn
      exact h ⟨funext (fun i => (hn i).1), funext (fun i => (hn i).2)⟩
    obtain ⟨i, hi⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

def pauliCoefficient {N : ℕ} (E : Operator N) (w : Fin N → Fin 4) : ℂ :=
  ((2 : ℂ)^N)⁻¹ * Matrix.trace (star (pauliTensor w) * E)

lemma sum_three_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

lemma matrix_delta_sum {N : ℕ} (E : Operator N) (x y : Word N) (z : ℂ) :
    (∑ u : Word N, ∑ v : Word N, E u v * (if x = u ∧ y = v then z else 0)) =
      E x y * z := by
  classical
  simp [ite_and, mul_ite]

lemma pauli_expansion {N : ℕ} (E : Operator N) :
    (∑ w : Fin N → Fin 4, pauliCoefficient E w • pauliTensor w) = E := by
  classical
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change (∑ w : Fin N → Fin 4, pauliCoefficient E w * pauliTensor w x y) = E x y
  calc
    _ = ((2 : ℂ)^N)⁻¹ * ∑ w : Fin N → Fin 4, ∑ u : Word N, ∑ v : Word N,
        E u v * (pauliTensor w x y * star (pauliTensor w u v)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      simp only [pauliCoefficient, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.star_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = ((2 : ℂ)^N)⁻¹ * ∑ u : Word N, ∑ v : Word N,
        E u v * ∑ w : Fin N → Fin 4, pauliTensor w x y * star (pauliTensor w u v) := by
      rw [sum_three_rotate]
      simp only [Finset.mul_sum]
    _ = E x y := by
      simp_rw [pauliTensor_complete]
      rw [matrix_delta_sum]
      have htwo : (2 : ℂ)^N ≠ 0 := pow_ne_zero N (by norm_num)
      calc
        _ = E x y * (((2 : ℂ)^N)⁻¹ * (2 : ℂ)^N) := by ring
        _ = _ := by rw [inv_mul_cancel₀ htwo, mul_one]

lemma pauliCoefficient_add {N : ℕ} (E F : Operator N) (w : Fin N → Fin 4) :
    pauliCoefficient (E + F) w = pauliCoefficient E w + pauliCoefficient F w := by
  simp [pauliCoefficient, mul_add, Matrix.trace_add]

lemma pauliCoefficient_smul {N : ℕ} (c : ℂ) (E : Operator N) (w : Fin N → Fin 4) :
    pauliCoefficient (c • E) w = c * pauliCoefficient E w := by
  simp [pauliCoefficient, Matrix.trace_smul, smul_eq_mul, mul_left_comm]

lemma tensorMatrix_trace {N : ℕ} (a : Fin N → QubitOperator) :
    Matrix.trace (tensorMatrix a) = ∏ i, Matrix.trace (a i) := by
  classical
  exact (Fintype.prod_sum (fun i b => a i b b)).symm

lemma pauliCoefficient_supported_zero {N : ℕ} (J : Finset (Fin N))
    (E : Operator N) (hE : TensorSupported J E) (w : Fin N → Fin 4)
    (hw : ¬ pauliSupport w ⊆ J) : pauliCoefficient E w = 0 := by
  classical
  rcases hE with ⟨a, rfl, ha⟩
  obtain ⟨i, hi, hiJ⟩ := Finset.not_subset.mp hw
  have hwi : w i ≠ 0 := (Finset.mem_filter.mp hi).2
  unfold pauliCoefficient pauliTensor
  rw [tensorMatrix_star, tensorMatrix_mul, tensorMatrix_trace]
  have hz : Matrix.trace (star (pauli (w i)) * a i) = 0 := by
    rw [ha i hiJ, mul_one, pauli_trace_star hwi]
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]

lemma pauliCoefficient_degree_zero {N ell : ℕ} (E : Operator N)
    (hE : HasDegreeLE E ell) (w : Fin N → Fin 4) (hw : ell < (pauliSupport w).card) :
    pauliCoefficient E w = 0 := by
  induction hE using Submodule.span_induction with
  | mem E hE =>
    obtain ⟨J, hJ, hJE⟩ := hE
    apply pauliCoefficient_supported_zero J E hJE w
    intro hs
    have hh := Finset.card_le_card hs
    have hj : J.card ≤ ell := by exact_mod_cast hJ
    omega
  | zero => simp [pauliCoefficient]
  | add E F _ _ hE hF => rw [pauliCoefficient_add, hE, hF, add_zero]
  | smul c E _ hE => rw [pauliCoefficient_smul, hE, mul_zero]

lemma pauliCoefficient_norm {N : ℕ} (E : Operator N) (w : Fin N → Fin 4) :
    ‖pauliCoefficient E w‖ ≤ ‖E‖ := by
  have ht : ‖Matrix.trace (star (pauliTensor w) * E)‖ ≤ (2 : ℝ)^N * ‖E‖ := by
    calc
      _ ≤ ∑ x : Word N, ‖(star (pauliTensor w) * E) x x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : Word N, ‖star (pauliTensor w) * E‖ :=
        Finset.sum_le_sum (fun x _ => matrix_entry_norm_le _ x x)
      _ = (2 : ℝ)^N * ‖E‖ := by
        simp [CStarRing.norm_mem_unitary_mul E
          (Unitary.star_mem (pauliTensor_unitary w))]
  unfold pauliCoefficient
  rw [norm_mul, norm_inv, norm_pow]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ ((2 : ℝ)^N)⁻¹ * ((2 : ℝ)^N * ‖E‖) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end QAC

end

end OAI
