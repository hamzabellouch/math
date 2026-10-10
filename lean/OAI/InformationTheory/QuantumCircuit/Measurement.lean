import OAI.InformationTheory.QuantumCircuit.ParityTrace

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

/-- The measured zero-outcome projector is a product projection on one qubit. -/
def outputZeroCount {N : ℕ} (out : Fin N) : Count N where
  support := {out}
  vector _ := basisVector 0
  normalized _ _ := basisVector_normalized 0

lemma outputZeroCount_diagonal {N : ℕ} (out : Fin N) :
    (outputZeroCount out).zero = Matrix.diagonal (fun z => if z out=0 then 1 else 0) := by
  classical
  have hloc : (fun i : Fin N => if i=out then rankOne (basisVector 0) else (1:QubitOperator)) =
      fun i => Matrix.diagonal (fun b => if i=out → b=0 then (1:ℂ) else 0) := by
    funext i
    by_cases hi : i=out
    · simp [hi,rankOne_basis_diagonal]
    · simp [hi,Matrix.diagonal_one]
  simp only [Count.zero,outputZeroCount,Finset.mem_singleton]
  rw [hloc,tensorMatrix_diagonal]
  congr 1
  funext z
  rw [Fintype.prod_boole]
  simp

/-- Born probability for an arbitrary fixed input basis state. -/
def outputProbability {N : ℕ} (W : Operator N) (out : Fin N) (b : Bit) (z : Word N) : ℝ :=
  ∑ y, if y out=b then Complex.normSq (W y z) else 0

lemma born_zero_diagonal {N : ℕ} (W : Operator N) (out : Fin N) (z : Word N) :
    (star W*(outputZeroCount out).zero*W) z z = (outputProbability W out 0 z:ℂ) := by
  classical
  rw [outputZeroCount_diagonal,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.star_apply,outputProbability,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y out=0
  · simp only [ite_eq_left hy,mul_one,Complex.star_def,← Complex.normSq_eq_conj_mul_self]
  · simp [hy]

lemma total_born_probability {N : ℕ} (W : Operator N) (hW : W ∈ unitary (Operator N))
    (z : Word N) : (∑ y, Complex.normSq (W y z))=1 := by
  apply Complex.ofReal_injective
  have h := congrArg (fun A : Operator N => A z z) (Unitary.star_mul_self_of_mem hW)
  simpa only [Matrix.mul_apply,Matrix.star_apply,Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self,← Complex.ofReal_sum,Matrix.one_apply_eq,Complex.ofReal_one] using h

lemma outputProbability_complement {N : ℕ} (W : Operator N) (hW : W ∈ unitary (Operator N))
    (out : Fin N) (z : Word N) :
    outputProbability W out 0 z+outputProbability W out 1 z=1 := by
  rw [outputProbability,outputProbability,← Finset.sum_add_distrib,← total_born_probability W hW z]
  apply Finset.sum_congr rfl
  intro y _
  generalize y out=b
  fin_cases b <;> simp

lemma success_character_lower {n N : ℕ} (W : Operator N) (hW : W ∈ unitary (Operator N))
    (out : Fin N) (x : Word n) {ε : ℝ} (hsuccess : 1/2+ε ≤ successProbability W out x) :
    ε+bitSign (parity x)/2 ≤
      ((bitSign (parity x):ℂ)*(star W*(outputZeroCount out).zero*W) (inputWord x) (inputWord x)).re := by
  rw [born_zero_diagonal,← Complex.ofReal_mul,Complex.ofReal_re]
  have htotal := outputProbability_complement W hW out (inputWord x)
  change 1/2+ε ≤ outputProbability W out (parity x) (inputWord x) at hsuccess
  generalize hp : parity x=b at hsuccess ⊢
  fin_cases b
  · norm_num [bitSign] at *
    linarith only [hsuccess]
  · norm_num [bitSign] at *
    linarith only [hsuccess,htotal]

/-- The finite Fourier step, with all final garbage summed out by the Born rule. -/
lemma parity_advantage_from_entries {n N : ℕ} (hn : 0<n) (hnN : n ≤ N)
    (W : Operator N) (hW : W ∈ unitary (Operator N)) (out : Fin N) {ε δ : ℝ}
    (hsuccess : ∀ x : Word n, 1/2+ε ≤ successProbability W out x)
    (hentry : ∀ x : Word n,
      ‖(localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
        localMatrix (inputHadamard n N)) (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤ δ) :
    ε ≤ δ := by
  let B := star W*(outputZeroCount out).zero*W
  let H := localMatrix (inputHadamard n N)
  have hlow := Finset.sum_le_sum (fun (x : Word n) (_ : x∈Finset.univ) =>
    success_character_lower W hW out x (hsuccess x))
  have hzero := sum_bitSign_parity hn
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Finset.sum_div,hzero,zero_div,add_zero] at hlow
  have hupp := Finset.sum_le_sum (fun (x : Word n) (_ : x∈Finset.univ) =>
    (Complex.re_le_norm ((H*B*H) (flipWord (inputSet n N) (inputWord x)) (inputWord x))).trans (hentry x))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hupp
  have heq := congrArg Complex.re (parity_trace_identity hnN B)
  have hsumre (f : Word n → ℂ) : (∑ x, f x).re = ∑ x, (f x).re :=
    map_sum Complex.reAddGroupHom f Finset.univ
  rw [hsumre,hsumre] at heq
  change (∑ x : Word n, ((H*B*H) (flipWord (inputSet n N) (inputWord x)) (inputWord x)).re) =
    ∑ x : Word n, ((bitSign (parity x):ℂ)*B (inputWord x) (inputWord x)).re at heq
  rw [heq] at hupp
  have hc : 0 < (Fintype.card (Word n):ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact (mul_le_mul_iff_right₀ hc).mp (hlow.trans hupp)

end QAC

end

end OAI
