import OAI.Analysis.Laughlin.Spin.Sl2DescendantNorm

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem descendants_orthogonal (R H L : Matrix I I ℝ) (v w : I → ℝ) (ν : ℝ)
    (hRL : R*L=L*R+H) (hHL : H*L=L*H-(2 : ℝ) • L) (ht : Lᵀ=R)
    (hw : H *ᵥ w=ν • w) (hvR : R *ᵥ v=0) (hwR : R *ᵥ w=0)
    (n m : ℕ) (h : (∑ i, v i*w i)=0 ∨ n ≠ m) :
    (∑ i, (L^n *ᵥ v) i*(L^m *ᵥ w) i) = 0 := by
  have hs (k : ℕ) (u : I → ℝ) : L^(k+1) *ᵥ u = L *ᵥ (L^k *ᵥ u) := by
    rw [Matrix.mulVec_mulVec,pow_succ']
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa using h.resolve_right (by simp)
    | succ m =>
      simp only [pow_zero,Matrix.one_mulVec]
      calc
        _ = ∑ i, (L *ᵥ (L^m *ᵥ w)) i*v i := by
          rw [hs m w]
          apply Finset.sum_congr rfl; intro i hi; ring
        _ = ∑ i, (L^m *ᵥ w) i*(R *ᵥ v) i := by rw [matrix_transpose_pairing,ht]
        _ = 0 := by rw [hvR]; simp
  | succ n ih =>
    cases m with
    | zero =>
      simp only [pow_zero,Matrix.one_mulVec]
      rw [hs n v,matrix_transpose_pairing,ht,hwR]
      simp
    | succ m =>
      rw [hs n v,matrix_transpose_pairing,ht,descendant_raising R H L w ν hRL hHL hw hwR m]
      have hp : (∑ i, v i*w i)=0 ∨ n ≠ m := by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      calc
        _ = (((m : ℝ)+1)*(ν-m))*(∑ i, (L^n *ᵥ v) i*(L^m *ᵥ w) i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i hi
          simp only [Pi.smul_apply,smul_eq_mul]; ring
        _ = 0 := by rw [ih m hp,mul_zero]

end Laughlin.Spin

end OAI
