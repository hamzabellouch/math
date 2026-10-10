import Mathlib
import OAI.Analysis.Commutator.TracialConjugation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixExpectation

open Matrix TracialGNS

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

def expectation : A →ₗ[ℂ] A :=
  (Fintype.card I:ℂ)⁻¹ • ∑ i,∑ j,
    (LinearMap.mulLeft ℂ (φ (single i j 1))).comp (LinearMap.mulRight ℂ (φ (single j i 1)))

lemma expectation_apply (a : A) : expectation φ a=
    (Fintype.card I:ℂ)⁻¹ • ∑ i,∑ j,φ (single i j 1)*a*φ (single j i 1) := by
  simp only [expectation,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,LinearMap.mulRight_apply,mul_assoc]

lemma star_expectation (a : A) : star (expectation φ a)=expectation φ (star a) := by
  rw [expectation_apply,expectation_apply]
  simp only [star_smul,star_sum,star_mul,←map_star,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_single,star_one,star_inv₀,star_natCast,mul_assoc]

lemma selfAdjoint {a : A} (ha : IsSelfAdjoint a) : IsSelfAdjoint (expectation φ a) := by
  change star (expectation φ a)=expectation φ a
  rw [star_expectation,ha.star_eq]

lemma single_left (a : A) (k l : I) :
    φ (single k l 1)*expectation φ a=
      (Fintype.card I:ℂ)⁻¹ • ∑ j,φ (single k j 1)*a*φ (single j l 1) := by
  rw [expectation_apply,mul_smul_comm,Finset.mul_sum]
  simp only [Finset.mul_sum,←mul_assoc,←map_mul]
  rw [Finset.sum_eq_single l]
  · simp only [single_mul_single_same,one_mul]
  · intro i hi hil
    apply Finset.sum_eq_zero
    intro j hj
    rw [single_mul_single_of_ne 1 k l i hil.symm 1,map_zero,zero_mul,zero_mul]
  · simp

lemma single_right (a : A) (k l : I) :
    expectation φ a*φ (single k l 1)=
      (Fintype.card I:ℂ)⁻¹ • ∑ j,φ (single k j 1)*a*φ (single j l 1) := by
  rw [expectation_apply,smul_mul_assoc,Finset.sum_mul]
  simp only [Finset.sum_mul,mul_assoc,←map_mul]
  rw [Finset.sum_eq_single k]
  · simp only [single_mul_single_same,one_mul]
  · intro i hi hik
    apply Finset.sum_eq_zero
    intro j hj
    rw [single_mul_single_of_ne 1 j i k hik 1,map_zero,mul_zero,mul_zero]
  · simp

lemma commutes (a : A) (x : Matrix I I ℂ) : φ x*expectation φ a=expectation φ a*φ x := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single x]
  conv_rhs => rw [Matrix.matrix_eq_sum_single x]
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hs : single k l (x k l)=(x k l) • single k l (1:ℂ) := by simp
  rw [hs,map_smul,smul_mul_assoc,mul_smul_comm,single_left,single_right]

lemma matrixSandwich (x : Matrix I I ℂ) (i j : I) :
    single i j 1*x*single j i 1=x j j • single i i 1 := by
  ext k l
  by_cases hik : i=k
  · subst k
    by_cases hil : i=l
    · subst l; simp [Matrix.mul_apply,Matrix.single,smul_eq_mul]
    · simp [Matrix.mul_apply,Matrix.single,smul_eq_mul,hil]
  · simp [Matrix.mul_apply,Matrix.single,smul_eq_mul,hik]

lemma matrixSum (x : Matrix I I ℂ) :
    (∑ i,∑ j,single i j 1*x*single j i 1)=x.trace • (1:Matrix I I ℂ) := by
  simp only [matrixSandwich,←Finset.sum_smul]
  simp only [Matrix.trace,Matrix.diag,←Finset.smul_sum,Matrix.sum_single_one]

lemma on_matrix (x : Matrix I I ℂ) :
    expectation φ (φ x)=((Fintype.card I:ℂ)⁻¹*x.trace) • (1:A) := by
  rw [expectation_apply]
  simp only [←map_mul,←map_sum]
  rw [matrixSum,map_smul,map_one,smul_smul]

variable [Nonempty I]

omit [DecidableEq I] in
lemma card_ne : (Fintype.card I:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero

lemma fixes (a : A) (ha : ∀ x : Matrix I I ℂ,φ x*a=a*φ x) : expectation φ a=a := by
  rw [expectation_apply]
  have he (i j : I) : φ (single i j 1)*a*φ (single j i 1)=a*φ (single i i 1) := by
    rw [ha,mul_assoc,←map_mul,single_mul_single_same,one_mul]
  have hsum : (∑ i,a*φ (single i i 1))=a := by
    rw [←Finset.mul_sum,←map_sum,Matrix.sum_single_one,map_one,mul_one]
  simp only [he,Finset.sum_const,Finset.card_univ]
  rw [←Finset.smul_sum,hsum,←Nat.cast_smul_eq_nsmul ℂ,smul_smul,
    inv_mul_cancel₀ (card_ne (I:=I)),one_smul]

lemma idempotent (a : A) : expectation φ (expectation φ a)=expectation φ a :=
  fixes φ _ (commutes φ a)

variable [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

omit [Nonempty I] in
include hτ in
lemma inner_symm (a b : A) :
    inner ℂ (algebraVector τ (expectation φ a)) (algebraVector τ b)=
      inner ℂ (algebraVector τ a) (algebraVector τ (expectation φ b)) := by
  rw [inner_algebraVector,inner_algebraVector,expectation_apply,expectation_apply]
  simp only [star_smul,star_sum,star_mul,←map_star,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_single,star_one,smul_mul_assoc,mul_smul_comm,
    Finset.sum_mul,Finset.mul_sum,map_smul,map_sum]
  congr 1
  · simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [mul_assoc] using
      hτ (φ (single j i 1)) (star a*φ (single i j 1)*b)

include hτ in
lemma norm_vector_le (a : A) : ‖algebraVector τ (expectation φ a)‖≤‖algebraVector τ a‖ := by
  have hi := inner_symm φ τ hτ a (expectation φ a)
  rw [idempotent] at hi
  have hr := congrArg (RCLike.re : ℂ → ℝ) hi
  rw [←norm_sq_eq_re_inner (𝕜:=ℂ)] at hr
  have hb := re_inner_le_norm (𝕜:=ℂ) (algebraVector τ a) (algebraVector τ (expectation φ a))
  have h0 := norm_nonneg (algebraVector τ (expectation φ a))
  nlinarith [norm_nonneg (algebraVector τ a)]

include hτ in
lemma trace_preserving (a : A) : τ (expectation φ a)=τ a := by
  have he := fixes φ (1:A) (fun x => by rw [mul_one,one_mul])
  have hi := inner_symm φ τ hτ 1 a
  rw [he] at hi
  simpa only [inner_algebraVector,star_one,one_mul] using hi.symm

include hτ in
lemma on_matrix_trace (hone : τ 1=1) (x : Matrix I I ℂ) :
    expectation φ (φ x)=τ (φ x) • (1:A) := by
  have ht := trace_preserving φ τ hτ (φ x)
  rw [on_matrix,map_smul,hone,smul_eq_mul,mul_one] at ht
  rw [on_matrix,ht]

end Kadison.MatrixExpectation

end

end
end

end OAI
