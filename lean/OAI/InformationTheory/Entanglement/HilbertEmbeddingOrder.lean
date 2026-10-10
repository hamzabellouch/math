import OAI.InformationTheory.Entanglement.HilbertEmbedding

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder
open ContinuousLinearMap Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {n e : Type} [Fintype n] [Fintype e]
lemma hilbertEmbed_adjoint (v : n → H) (A : Mat n) :
    star (hilbertEmbed v A)=hilbertEmbed v Aᴴ := by
  simp only [hilbertEmbed,star_sum,star_smul,ContinuousLinearMap.star_eq_adjoint,
    InnerProductSpace.adjoint_rankOne,Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
lemma hilbertEmbed_psd (v : n → H) {A : Mat n} (hA : A.PosSemidef) :
    0≤hilbertEmbed v A := by
  apply nonneg_iff_isPositive.mpr
  refine ⟨?_,?_⟩
  · apply isSelfAdjoint_iff_isSymmetric.mp
    change star (hilbertEmbed v A)=hilbertEmbed v A
    rw [hilbertEmbed_adjoint,hA.isHermitian.eq]
  · intro x
    have h := hA.dotProduct_mulVec_nonneg (fun i => inner ℂ (v i) x)
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_re_symm]
    change 0≤(inner ℂ x (hilbertEmbed v A x)).re
    have he : inner ℂ x (hilbertEmbed v A x)=
        (star fun i => inner ℂ (v i) x) ⬝ᵥ A *ᵥ (fun i => inner ℂ (v i) x) := by
      simp only [hilbertEmbed_apply,inner_sum,inner_smul_right,dotProduct,Matrix.mulVec,
        Pi.star_apply,Finset.mul_sum]
      simp only [← inner_conj_symm x,mul_assoc,mul_comm,RCLike.star_def]
    rw [he]
    exact (Complex.nonneg_iff.mp h).1
lemma hilbertEmbed_psd_finite (b : HilbertBasis ι ℂ H) (v : n → H)
    {A : Mat n} (hA : A.PosSemidef) : HasFinitePositiveTrace b (hilbertEmbed v A) :=
  ⟨hilbertEmbed_psd v hA,(hilbertEmbed_diagonal_hasSum b v A).summable⟩

omit [CompleteSpace H] in
lemma hilbertEmbed_congruence (v : e → H) (B : Matrix e n ℂ) (A : Mat n) :
    hilbertEmbed (fun j => ∑ i, B i j • v i) A=hilbertEmbed v (B*A*Bᴴ) := by
  ext x
  simp only [hilbertEmbed_apply,sum_inner,inner_smul_left,Finset.mul_sum,
    Finset.sum_mul,Finset.smul_sum,Finset.sum_smul,smul_smul,Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext k; arg 2; ext j; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  simp only [mul_assoc,mul_left_comm,mul_comm,RCLike.star_def]

end SecretKey

end

end OAI
