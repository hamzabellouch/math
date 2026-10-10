import OAI.Combinatorics.PolynomialVacuum.Algebra.BitRigidityTarget
import OAI.Combinatorics.PolynomialVacuum.Algebra.TripleBitRigidity

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem Pzero_mulVec_eq_zero (v : Pair → ℂ) (h : ∑ ab : Pair, cup ab*v ab=0) :
    Pzero.mulVec v=0 := by
  ext ab
  simp only [Matrix.mulVec,dotProduct,Pzero,div_eq_mul_inv]
  have he : (∑ cd : Pair, -cup ab*cup cd*nZero⁻¹*v cd)=
      (-cup ab*nZero⁻¹)*(∑ cd : Pair, cup cd*v cd) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cd _; ring
  rw [he,h,mul_zero]
  rfl

theorem bitSwap_inverse : (Pone-zeta⁻¹ • Ptwo)*bitSwap=1-Pzero := by
  have hz : zeta≠0 := pow_ne_zero _ (pow_ne_zero _ q_ne_zero)
  unfold bitSwap
  rw [sub_mul,mul_sub,mul_sub,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,Pone_idempotent,Pone_Ptwo,
    Ptwo_Pone,Ptwo_idempotent,smul_zero,smul_zero,sub_zero,inv_mul_cancel₀ hz,one_smul]
  rw [Ptwo]
  abel

theorem bitSwap_kernel (v : Pair → ℂ) (hcup : ∑ ab : Pair, cup ab*v ab=0)
    (h : bitSwap.mulVec v=0) : v=0 := by
  have hp := Pzero_mulVec_eq_zero v hcup
  have hm := congrArg (Matrix.mulVec (Pone-zeta⁻¹ • Ptwo)) h
  rw [Matrix.mulVec_mulVec,bitSwap_inverse,Matrix.sub_mulVec,Matrix.one_mulVec,hp] at hm
  simpa using hm

 

theorem bit_tensor_rigidity (W : BitTensorFamily) (hW : BitTensorEquations W) : W=0 := by
  rcases hW with ⟨hs,hfirst,hlast,hcup1,hcup2,hmove⟩
  have hequal1 (i k : Bool) : ∀ a b c, W i i k a b c=0 := by
    apply triple_bit_first_equal i k (W i i k) (hs i i k) (hfirst i k)
    · intro h a; subst k; exact hlast i i a
    · exact hcup2 i i k
  have hequal2 (i k : Bool) : ∀ a b c, W i k k a b c=0 := by
    apply triple_bit_last_equal k i (W i k k) (hs i k k) (hlast i k)
    · intro h c; subst i; exact hfirst k k c
    · exact hcup1 i k k
  have halternating1 (a b c : Spin) : W false true false a b c=0 := by
    have h := congrFun (hmove false a) (b,c)
    simp only [hequal1] at h
    change bitSwap.mulVec 0 (b,c)=W false true false a b c at h
    simpa using h.symm
  have halternating2 (a b c : Spin) : W true false true a b c=0 := by
    have h := hmove true a
    have hz : (fun bc : Pair => W true true false a bc.1 bc.2)=0 := by
      funext bc; exact hequal1 true false _ _ _
    rw [hz] at h
    exact congrFun (bitSwap_kernel _ (hcup2 true false true a) h) (b,c)
  funext i j k a b c
  change W i j k a b c=0
  cases i <;> cases j <;> cases k
  · exact hequal1 _ _ _ _ _
  · exact hequal1 _ _ _ _ _
  · exact halternating1 _ _ _
  · exact hequal2 _ _ _ _ _
  · exact hequal2 _ _ _ _ _
  · exact halternating2 _ _ _
  · exact hequal1 _ _ _ _ _
  · exact hequal1 _ _ _ _ _

end PolynomialVacuumAlgebra

end OAI
