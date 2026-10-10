import OAI.InformationTheory.Entanglement.HilbertRecovery
import OAI.InformationTheory.Entanglement.FiniteRecovery

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder
open ContinuousLinearMap Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} {n : Type} [Fintype n] [DecidableEq n]

def hilbertEmbed (v : n → H) (A : Mat n) : H →L[ℂ] H :=
  ∑ i, ∑ j, A i j • InnerProductSpace.rankOne ℂ (v i) (v j)
omit [DecidableEq n] in
lemma hilbertEmbed_apply (v : n → H) (A : Mat n) (x : H) :
    hilbertEmbed v A x=∑ i, ∑ j, (A i j*inner ℂ (v j) x) • v i := by
  simp only [hilbertEmbed,_root_.sum_apply,_root_.smul_apply,
    InnerProductSpace.rankOne_apply,smul_smul]
lemma hilbertCompress_embed (v : n → H) (hv : Orthonormal ℂ v) (A : Mat n) :
    hilbertCompress v (hilbertEmbed v A)=A := by
  ext i j
  change inner ℂ (v i) (hilbertEmbed v A (v j))=A i j
  rw [hilbertEmbed_apply]
  simp only [inner_sum,inner_smul_right,orthonormal_iff_ite.mp hv]
  simp [mul_ite]
omit [DecidableEq n] in
lemma hilbertEmbed_diagonal_hasSum (b : HilbertBasis ι ℂ H) (v : n → H) (A : Mat n) :
    HasSum (fun k => (inner ℂ (b k) (hilbertEmbed v A (b k))).re)
      (∑ i, ∑ j, (A i j*inner ℂ (v j) (v i)).re) := by
  have h (i j : n) : HasSum (fun k => (A i j*(inner ℂ (v j) (b k)*inner ℂ (b k) (v i))).re)
      (A i j*inner ℂ (v j) (v i)).re := by
    simpa only [Complex.reCLM_apply] using
      ((b.hasSum_inner_mul_inner (v j) (v i)).mul_left (A i j)).mapL Complex.reCLM
  have hs := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun j _ => h i j))
  convert hs using 1
  ext k
  simp only [hilbertEmbed_apply,inner_sum,inner_smul_right,Complex.re_sum,mul_assoc]
lemma hilbertEmbed_trace (b : HilbertBasis ι ℂ H) (v : n → H) (hv : Orthonormal ℂ v)
    (A : Mat n) : hilbertTrace b (hilbertEmbed v A)=(Matrix.trace A).re := by
  rw [hilbertTrace,(hilbertEmbed_diagonal_hasSum b v A).tsum_eq]
  simp only [orthonormal_iff_ite.mp hv]
  simp [Matrix.trace,Matrix.diag,Complex.re_sum,apply_ite]

theorem hilbertErase_embed (b : HilbertBasis ι ℂ H) (v : n → H) (hv : Orthonormal ℂ v)
    (i₀ : n) (A : Mat n) : hilbertErase b v i₀ (hilbertEmbed v A)=A := by
  rw [hilbertErase,hilbertCompress_embed v hv,hilbertEmbed_trace b v hv]
  simp

end SecretKey

end

end OAI
