import OAI.Analysis.Laughlin.Spin.LadderMatrix

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def vectorNormSq (v : I → ℝ) : ℝ := ∑ i, (v i)^2

omit [DecidableEq I] in
theorem matrix_transpose_pairing (L : Matrix I I ℝ) (v w : I → ℝ) :
    (∑ i, (L *ᵥ v) i*w i) = ∑ i, v i*((Lᵀ) *ᵥ w) i := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem descendant_weight (H L : Matrix I I ℝ) (v : I → ℝ) (μ : ℝ)
    (hHL : H*L=L*H-(2 : ℝ) • L) (hv : H *ᵥ v=μ • v) (n : ℕ) :
    H *ᵥ (L^n *ᵥ v) = (μ-2*(n : ℝ)) • (L^n *ᵥ v) := by
  have hs (n : ℕ) : L^(n+1) *ᵥ v = L *ᵥ (L^n *ᵥ v) := by
    rw [Matrix.mulVec_mulVec,pow_succ']
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [hs,Matrix.mulVec_mulVec,hHL,Matrix.sub_mulVec,Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul]
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Nat.cast_add,Nat.cast_one]
    ring

theorem descendant_raising (R H L : Matrix I I ℝ) (v : I → ℝ) (μ : ℝ)
    (hRL : R*L=L*R+H) (hHL : H*L=L*H-(2 : ℝ) • L)
    (hv : H *ᵥ v=μ • v) (hr : R *ᵥ v=0) (n : ℕ) :
    R *ᵥ (L^(n+1) *ᵥ v) = (((n : ℝ)+1)*(μ-n)) • (L^n *ᵥ v) := by
  have hs (n : ℕ) : L^(n+1) *ᵥ v = L *ᵥ (L^n *ᵥ v) := by
    rw [Matrix.mulVec_mulVec,pow_succ']
  induction n with
  | zero =>
    simp only [pow_one,pow_zero,Matrix.one_mulVec,Nat.cast_zero,zero_add,sub_zero,one_mul]
    rw [Matrix.mulVec_mulVec,hRL,Matrix.add_mulVec,← Matrix.mulVec_mulVec,hr,
      Matrix.mulVec_zero,zero_add,hv]
  | succ n ih =>
    rw [hs (n+1),Matrix.mulVec_mulVec,hRL,Matrix.add_mulVec,← Matrix.mulVec_mulVec,
      ih,Matrix.mulVec_smul,descendant_weight H L v μ hHL hv (n+1),hs n]
    funext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Nat.cast_add,Nat.cast_one]
    ring

theorem descendant_norm_step (R H L : Matrix I I ℝ) (v : I → ℝ) (μ : ℝ)
    (hRL : R*L=L*R+H) (hHL : H*L=L*H-(2 : ℝ) • L) (ht : Lᵀ=R)
    (hv : H *ᵥ v=μ • v) (hr : R *ᵥ v=0) (n : ℕ) :
    vectorNormSq (L^(n+1) *ᵥ v) = (((n : ℝ)+1)*(μ-n))*vectorNormSq (L^n *ᵥ v) := by
  have hs : L^(n+1) *ᵥ v = L *ᵥ (L^n *ᵥ v) := by
    rw [Matrix.mulVec_mulVec,pow_succ']
  unfold vectorNormSq
  simp only [pow_two]
  conv_lhs => arg 2; ext i; arg 1; rw [hs]
  rw [matrix_transpose_pairing,ht,descendant_raising R H L v μ hRL hHL hv hr n]
  simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem descendant_norm_pos (R H L : Matrix I I ℝ) (v : I → ℝ) (μ n : ℕ)
    (hRL : R*L=L*R+H) (hHL : H*L=L*H-(2 : ℝ) • L) (ht : Lᵀ=R)
    (hv : H *ᵥ v=(μ : ℝ) • v) (hr : R *ᵥ v=0)
    (hnorm : 0 < vectorNormSq v) (hn : n ≤ μ) : 0 < vectorNormSq (L^n *ᵥ v) := by
  induction n with
  | zero => simpa using hnorm
  | succ n ih =>
    rw [descendant_norm_step R H L v μ hRL hHL ht hv hr n]
    have hp : (n : ℝ) < μ := by exact_mod_cast (show n < μ by omega)
    have hi := ih (by omega)
    positivity

end Laughlin.Spin

end OAI
