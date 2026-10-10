import OAI.Algebra.OddKaplansky.AdmissibleCount

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.WeightedProjection
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {X : Type portUniverse2} {I : Type portUniverse3} [Field K] [Fintype X] [sectionInstance23 : Fintype I] [DecidableEq X] [sectionInstance24 : DecidableEq I]
def gram (B : Matrix X I K) (τ : X → K) := B.transpose * Matrix.diagonal τ * B
def projection (B : Matrix X I K) (τ : X → K) := B * (gram B τ)⁻¹ * B.transpose * Matrix.diagonal τ

lemma fixes (B : Matrix X I K) (τ : X → K) (h : (gram B τ).det ≠ 0) : projection B τ * B = B := by
  have hi := Matrix.nonsing_inv_mul (gram B τ) (isUnit_iff_ne_zero.mpr h)
  simpa only [projection,gram,Matrix.mul_assoc,Matrix.mul_one] using congrArg (fun A => B * A) hi

lemma idempotent (B : Matrix X I K) (τ : X → K) (h : (gram B τ).det ≠ 0) :
    projection B τ * projection B τ = projection B τ := by
  calc
    _ = (projection B τ * B) * (gram B τ)⁻¹ * B.transpose * Matrix.diagonal τ := by simp only [projection, Matrix.mul_assoc]
    _ = _ := by rw [fixes B τ h]; rfl

lemma rank (B : Matrix X I K) (τ : X → K) (h : (gram B τ).det ≠ 0) : (projection B τ).rank = B.rank := by
  apply le_antisymm
  · unfold projection
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _))
  · calc
      B.rank = (projection B τ * B).rank := congrArg Matrix.rank (fixes B τ h).symm
      _ ≤ _ := Matrix.rank_mul_le_left _ _

lemma annihilate_left (B : Matrix X I K) (τ : X → K) (A : Matrix X X K) (h : A * B = 0) :
    A * projection B τ = 0 := by
  simp only [projection,← Matrix.mul_assoc,h,Matrix.zero_mul]

lemma annihilate_right (B : Matrix X I K) (τ : X → K) (A : Matrix X X K)
    (h : B.transpose * Matrix.diagonal τ * A = 0) : projection B τ * A = 0 := by
  calc
    _ = (B * (gram B τ)⁻¹) * (B.transpose * Matrix.diagonal τ * A) := by simp only [Matrix.mul_assoc,projection]
    _ = 0 := by rw [h,Matrix.mul_zero]

lemma conjugate_sub_pow (D D' A : Matrix X X K) (hD : D * D' = 1) (hD' : D' * D = 1) (ell : ℕ) :
    (D*A*D' - 1)^ell = D*(A-1)^ell*D' := by
  induction ell with
  | zero => simpa using hD.symm
  | succ n ih =>
    rw [pow_succ,ih,pow_succ]
    have hs : D*A*D'-1 = D*(A-1)*D' := by simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_one,hD]
    rw [hs]
    calc
      _ = D * (A-1)^n * (D'*D) * (A-1) * D' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hD',Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma conjugate_annihilate
    {K : Type contextUniverse1}
    {X : Type contextUniverse2}
    {I : Type contextUniverse3}
    [Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} X]
    [Fintype.{contextUniverse3} I]
    [DecidableEq.{contextUniverse2 + 1} X]
    [DecidableEq.{contextUniverse3 + 1} I] (B : Matrix X I K) (D D' A : Matrix X X K)
    (hD : D * D' = 1) (hD' : D' * D = 1) (ell : ℕ) (hB : B.transpose * (A-1)^ell = 0) :
    B.transpose * D' * (D*A*D'-1)^ell = 0 := by
  rw [conjugate_sub_pow D D' A hD hD']
  calc
    _ = B.transpose * (D'*D) * (A-1)^ell * D' := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hD',Matrix.mul_one,hB,Matrix.zero_mul]
end
end OddKaplansky.WeightedProjection

end

end OAI
