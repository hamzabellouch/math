import OAI.InformationTheory.QuantumCircuit.ProductProjection

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma coe_sum_normSq (v : Bit → ℂ) :
    ((∑ b, Complex.normSq (v b) : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp only [Complex.ofReal_sum, dotProduct, Pi.star_apply, Complex.star_def,
    mul_comm ((starRingEnd ℂ) _), Complex.mul_conj]

lemma normalized_mulVec {U : QubitOperator} (hU : U ∈ unitary QubitOperator)
    {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    ∑ b, Complex.normSq ((U *ᵥ v) b) = 1 := by
  apply Complex.ofReal_injective
  rw [coe_sum_normSq, Matrix.star_mulVec, dotProduct_mulVec, Matrix.vecMul_vecMul]
  change Matrix.vecMul (star v) (star U * U) ⬝ᵥ v = _
  rw [Unitary.star_mul_self_of_mem hU, Matrix.vecMul_one]
  simpa only [dotProduct, Pi.star_apply, Complex.ofReal_one] using normalized_complex hv

lemma rankOne_mulVec (U : QubitOperator) (v : Bit → ℂ) :
    rankOne (U *ᵥ v) = U * rankOne v * star U := by
  change Matrix.vecMulVec (U *ᵥ v) (star (U *ᵥ v)) =
    U * Matrix.vecMulVec v (star v) * star U
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  rfl

/-- The canonical orthogonal unit vector in a qubit. -/
def orthogonalVector (v : Bit → ℂ) : Bit → ℂ := ![-star (v 1), star (v 0)]

lemma orthogonalVector_normalized {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    ∑ b, Complex.normSq (orthogonalVector v b) = 1 := by
  simpa [orthogonalVector, Fin.sum_univ_two, Complex.star_def, add_comm] using hv

lemma rankOne_orthogonalVector {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    rankOne (orthogonalVector v) = 1 - rankOne v := by
  have h := normalized_complex hv
  simp only [Fin.sum_univ_two, Complex.star_def] at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rankOne, orthogonalVector]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

/-- Conjugation by a local layer preserves the exact count support. -/
def Count.rotate {N : ℕ} (M : Count N) (L : LocalLayer N) : Count N where
  support := M.support
  vector i := (L i : QubitOperator) *ᵥ M.vector i
  normalized i hi := normalized_mulVec (L i).property (M.normalized i hi)

lemma Count.rotate_zero {N : ℕ} (M : Count N) (L : LocalLayer N) :
    (M.rotate L).zero = localMatrix L * M.zero * star (localMatrix L) := by
  classical
  dsimp only [Count.zero, Count.rotate, localMatrix]
  rw [tensorMatrix_star, tensorMatrix_mul, tensorMatrix_mul]
  congr 1
  funext i
  by_cases hi : i ∈ M.support
  · simp only [ite_eq_left hi]
    exact rankOne_mulVec _ _
  · simp only [ite_eq_right hi, mul_one, Unitary.mul_star_self_of_mem (L i).property]

/-- Flipping any subset of the reference axes is still a count, not an added gate. -/
def Count.flip {N : ℕ} (M : Count N) (F : Finset (Fin N)) : Count N where
  support := M.support
  vector i := if i ∈ F then orthogonalVector (M.vector i) else M.vector i
  normalized i hi := by
    split_ifs
    · exact orthogonalVector_normalized (M.normalized i hi)
    · exact M.normalized i hi

lemma Count.flip_zero {N : ℕ} (M : Count N) (F : Finset (Fin N)) :
    (M.flip F).zero = M.pattern F := by
  classical
  dsimp only [Count.zero, Count.flip, Count.pattern]
  congr 1
  funext i
  split_ifs with hi hF
  · exact rankOne_orthogonalVector (M.normalized i hi)
  · rfl
  · rfl

lemma localMatrix_unitary {N : ℕ} (L : LocalLayer N) : localMatrix L ∈ unitary (Operator N) :=
  tensorMatrix_unitary _ (fun i => (L i).property)

lemma localMatrix_mul {N : ℕ} (L K : LocalLayer N) :
    localMatrix L * localMatrix K = localMatrix (fun i => L i * K i) := by
  exact tensorMatrix_mul _ _

lemma localMatrix_star {N : ℕ} (L : LocalLayer N) :
    star (localMatrix L) = localMatrix (fun i => star (L i)) := by
  exact tensorMatrix_star _

lemma reflection_unitary {N : ℕ} (M : Count N) :
    (1 : Operator N) - (2 : ℂ) • M.zero ∈ unitary (Operator N) := by
  have h := M.zero_projection.two_mul_sub_one_mem_unitary
  have hneg : -(2 * M.zero - 1) ∈ unitary (Operator N) := by
    simpa only [Unitary.mem_iff, star_neg, neg_mul_neg] using h
  simpa only [two_smul, two_mul, neg_sub] using hneg

lemma reflectionMatrix_unitary {N : ℕ} (R : ReflectionLayer N) :
    reflectionMatrix R ∈ unitary (Operator N) := by
  apply (unitary (Operator N)).list_prod_mem
  intro U hU
  obtain ⟨M, _, rfl⟩ := List.mem_map.mp hU
  exact reflection_unitary M

lemma IsCircuit.mem_unitary {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) :
    U ∈ unitary (Operator N) := by
  induction d generalizing U with
  | zero => obtain ⟨L, rfl⟩ := hU; exact localMatrix_unitary L
  | succ d ih =>
    obtain ⟨V, R, L, hV, rfl⟩ := hU
    exact (unitary (Operator N)).mul_mem
      ((unitary (Operator N)).mul_mem (ih hV) (reflectionMatrix_unitary R)) (localMatrix_unitary L)


lemma IsCircuit.mul_local {N d : ℕ} {U : Operator N} (hU : IsCircuit d U)
    (L : LocalLayer N) : IsCircuit d (U * localMatrix L) := by
  cases d with
  | zero =>
    obtain ⟨K, rfl⟩ := hU
    exact ⟨fun i => K i * L i, localMatrix_mul K L⟩
  | succ d =>
    obtain ⟨V, R, K, hV, rfl⟩ := hU
    exact ⟨V, R, (fun i => K i * L i), hV, by rw [mul_assoc, localMatrix_mul]⟩

lemma IsCircuit.mul {N d e : ℕ} {U V : Operator N}
    (hU : IsCircuit d U) (hV : IsCircuit e V) : IsCircuit (d + e) (U * V) := by
  induction e generalizing V with
  | zero =>
    obtain ⟨L, rfl⟩ := hV
    exact hU.mul_local L
  | succ e ih =>
    obtain ⟨W, R, L, hW, rfl⟩ := hV
    exact ⟨U * W, R, L, ih hW, by simp only [mul_assoc]⟩

lemma star_list_prod_reverse {A B : Type*} [Ring B] [StarRing B]
    (f : A → B) (hf : ∀ a, star (f a) = f a) (l : List A) :
    star (l.map f).prod = (l.reverse.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.reverse_cons, List.map_append, List.prod_append, star_mul, hf, ih]

def ReflectionLayer.reverse {N : ℕ} (R : ReflectionLayer N) : ReflectionLayer N where
  gates := R.gates.reverse
  disjoint := (R.disjoint.imp (fun h => h.symm)).reverse

lemma reflectionMatrix_star {N : ℕ} (R : ReflectionLayer N) :
    star (reflectionMatrix R) = reflectionMatrix R.reverse := by
  apply star_list_prod_reverse
  intro M
  simp only [star_sub, star_one, star_smul, star_ofNat, M.zero_projection.isSelfAdjoint.star_eq]

lemma IsCircuit.star_mem {N d : ℕ} {U : Operator N} (hU : IsCircuit d U) :
    IsCircuit d (star U) := by
  induction d generalizing U with
  | zero =>
    obtain ⟨L, rfl⟩ := hU
    exact ⟨fun i => star (L i), localMatrix_star L⟩
  | succ d ih =>
    obtain ⟨V, R, L, hV, rfl⟩ := hU
    have hL : IsCircuit 0 (star (localMatrix L)) := ⟨_, localMatrix_star L⟩
    have hLR : IsCircuit 1 (star (localMatrix L) * reflectionMatrix R.reverse) := by
      refine ⟨_, R.reverse, (fun _ => 1), hL, ?_⟩
      simp [localMatrix]
    have h := hLR.mul (ih hV)
    simpa only [star_mul, reflectionMatrix_star, Nat.add_comm 1, mul_assoc] using h

end QAC

end

end OAI
