import OAI.Combinatorics.PolynomialVacuum.Algebra.BilinearChannels
import OAI.Combinatorics.PolynomialVacuum.Algebra.BitRigidity

namespace OAI

namespace PolynomialVacuumAlgebra
open Matrix

def VectorBilinearExchange (a b c d : Pair → ℂ) : Prop :=
  ∀ x y, (exchangeNumerator x y).mulVec (a+x • b+y • c+(x*y) • d)=
    eigenOne x y • (a+y • b+x • c+(x*y) • d)

theorem projector_exchange_zero (x y : ℂ) : Pzero*exchangeNumerator x y=eigenZero x y • Pzero := by
  simp only [exchangeNumerator,mul_add,Matrix.mul_smul,Pzero_idempotent,Pzero_Pone,Pzero_Ptwo,smul_zero,add_zero,eigenZero]
theorem projector_exchange_one (x y : ℂ) : Pone*exchangeNumerator x y=eigenOne x y • Pone := by
  simp only [exchangeNumerator,mul_add,Matrix.mul_smul,Pone_Pzero,Pone_idempotent,Pone_Ptwo,smul_zero,zero_add,add_zero,eigenOne]
theorem projector_exchange_two (x y : ℂ) : Ptwo*exchangeNumerator x y=eigenTwo x y • Ptwo := by
  simp only [exchangeNumerator,mul_add,Matrix.mul_smul,Ptwo_Pzero,Ptwo_Pone,Ptwo_idempotent,smul_zero,zero_add,eigenTwo]

theorem scalarBilinear_projector (a b c d : Pair → ℂ) (h : VectorBilinearExchange a b c d)
    (P : Matrix Pair Pair ℂ) (e : ℂ → ℂ → ℂ) (he : ∀ x y, P*exchangeNumerator x y=e x y • P) (ab : Pair) :
    ScalarBilinearExchange e (P.mulVec a ab) (P.mulVec b ab) (P.mulVec c ab) (P.mulVec d ab) := by
  intro x y
  have hh := congrArg (Matrix.mulVec P) (h x y)
  rw [Matrix.mulVec_mulVec,he] at hh
  simpa only [Matrix.smul_mulVec,Matrix.mulVec_add,Matrix.mulVec_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,mul_left_comm,mul_assoc]
    using congrFun hh ab

theorem vectorBilinear_zero (a b c d : Pair → ℂ) (h : VectorBilinearExchange a b c d) :
    Pzero.mulVec a=0 ∧ Pzero.mulVec b=0 ∧ Pzero.mulVec c=0 ∧ Pzero.mulVec d=0 := by
  have hh := scalarBilinear_projector a b c d h Pzero eigenZero projector_exchange_zero
  refine ⟨?_,?_,?_,?_⟩ <;> funext ab
  · exact bilinearZero_a _ _ _ _ (hh ab)
  · exact bilinearZero_b _ _ _ _ (hh ab)
  · exact bilinearZero_c _ _ _ _ (hh ab)
  · exact bilinearZero_d _ _ _ _ (hh ab)

theorem vectorBilinear_two (a b c d : Pair → ℂ) (h : VectorBilinearExchange a b c d) :
    Ptwo.mulVec a=0 ∧ Ptwo.mulVec d=0 ∧ Ptwo.mulVec b= -(t^2) • Ptwo.mulVec c := by
  have hh := scalarBilinear_projector a b c d h Ptwo eigenTwo projector_exchange_two
  refine ⟨?_,?_,?_⟩ <;> funext ab
  · exact bilinearTwo_a _ _ _ _ (hh ab)
  · exact bilinearTwo_d _ _ _ _ (hh ab)
  · exact bilinearTwo_bc _ _ _ _ (hh ab)

theorem vectorBilinear_one (a b c d : Pair → ℂ) (h : VectorBilinearExchange a b c d) :
    Pone.mulVec b=Pone.mulVec c := by
  funext ab
  exact bilinearOne_bc _ _ _ _ (scalarBilinear_projector a b c d h Pone eigenOne projector_exchange_one ab)

theorem Pzero_vanishing_cup (v : Pair → ℂ) (h : Pzero.mulVec v=0) : ∑ ab : Pair, cup ab*v ab=0 := by
  have hh := congrFun h (Spin.zero,Spin.zero)
  simp only [Matrix.mulVec,dotProduct,Pzero,Pi.zero_apply,div_eq_mul_inv] at hh
  have hc : cup (Spin.zero,Spin.zero)=1 := by simp [cup,charge]
  rw [hc] at hh
  have he : (∑ ab : Pair, -(1:ℂ)*cup ab*nZero⁻¹*v ab)=
      -nZero⁻¹*(∑ ab : Pair, cup ab*v ab) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ab _; ring
  rw [he] at hh
  exact (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr (inv_ne_zero nZero_ne_zero))

theorem projector_one_of_other_zero (v : Pair → ℂ) (h0 : Pzero.mulVec v=0) (h2 : Ptwo.mulVec v=0) :
    Pone.mulVec v=v := by
  have h := congrArg (fun P : Matrix Pair Pair ℂ => P.mulVec v) projectors_sum
  rw [Matrix.add_mulVec,Matrix.add_mulVec,Matrix.one_mulVec,h0,h2,zero_add,add_zero] at h
  exact h

theorem vectorBilinear_equal_bits (a b c d : Pair → ℂ) (h : VectorBilinearExchange a b c d) :
    Pone.mulVec a=a ∧ Pone.mulVec d=d := by
  have h0 := vectorBilinear_zero a b c d h
  have h2 := vectorBilinear_two a b c d h
  exact ⟨projector_one_of_other_zero a h0.1 h2.1,projector_one_of_other_zero d h0.2.2.2 h2.2.1⟩

theorem vectorBilinear_bitSwap (a b c d : Pair → ℂ) (h : VectorBilinearExchange a b c d) : bitSwap.mulVec c=b := by
  have h0 := (vectorBilinear_zero a b c d h).2.1
  have h1 := vectorBilinear_one a b c d h
  have h2 := (vectorBilinear_two a b c d h).2.2
  have hh := congrArg (fun P : Matrix Pair Pair ℂ => P.mulVec b) projectors_sum
  rw [Matrix.add_mulVec,Matrix.add_mulVec,Matrix.one_mulVec,h0,zero_add,h1,h2] at hh
  unfold bitSwap
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,zeta,sub_eq_add_neg]
  simpa only [neg_smul] using hh

end PolynomialVacuumAlgebra

end OAI
