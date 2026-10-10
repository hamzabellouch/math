import OAI.InformationTheory.Entanglement.ProjectionData

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace ProjectionCriterion
variable {Q K : Type} [Fintype Q] [Fintype K]

lemma symmetric_trace_square (M : Matrix K K ℝ) (hM : Mᵀ=M) :
    Matrix.trace (M*M) = ∑ a, ∑ b, (M a b)^2 := by
  change (∑ a, ∑ b, M a b*M b a) = _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : M b a=M a b := congrArg (fun N : Matrix K K ℝ => N a b) hM
  rw [he,pow_two]

lemma trace_square_lower [DecidableEq K] (M : Matrix K K ℝ) (hM : Mᵀ=M) :
    (Matrix.trace M)^2 ≤ (Fintype.card K : ℝ)*Matrix.trace (M*M) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : K => (1 : ℝ)) (fun a => M a a)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hc
  change (Matrix.trace M)^2 ≤ (Fintype.card K : ℝ)*(∑ a, (M a a)^2) at hc
  have hs : (∑ a, (M a a)^2) ≤ ∑ a, ∑ b, (M a b)^2 := by
    apply Finset.sum_le_sum
    intro a _
    exact Finset.single_le_sum (fun b _ => sq_nonneg (M a b)) (Finset.mem_univ a)
  rw [symmetric_trace_square M hM]
  exact hc.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))

theorem correlation_lower [DecidableEq K] [Nonempty K] (u : Q → K → ℝ)
    (hu : ∀ q, ∑ a, u q a*u q a=1) :
    (Fintype.card Q : ℝ)^2/(Fintype.card K : ℝ) ≤
       ∑ q, ∑ r, (correlation u q r)^2 := by
  let U : Matrix Q K ℝ := u
  let M := Uᵀ*U
  let G := U*Uᵀ
  have hm : Mᵀ=M := by simp [M,Matrix.transpose_mul]
  have hg : Gᵀ=G := by simp [G,Matrix.transpose_mul]
  have ht : Matrix.trace M=(Fintype.card Q : ℝ) := by
    rw [show M=Uᵀ*U from rfl,Matrix.trace_mul_comm]
    change (∑ q, ∑ a, u q a*u q a) = _
    simp only [hu,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have hsq : Matrix.trace (M*M)=Matrix.trace (G*G) := by
    dsimp only [M,G]
    calc
      Matrix.trace (Uᵀ*U*(Uᵀ*U)) = Matrix.trace (Uᵀ*(U*Uᵀ)*U) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (U*Uᵀ*(U*Uᵀ)) := Matrix.trace_mul_cycle _ _ _
  have hc := trace_square_lower M hm
  rw [ht,hsq,symmetric_trace_square G hg] at hc
  have hGq (q r : Q) : G q r = correlation u q r := rfl
  simp_rw [hGq] at hc
  have hK : 0 < (Fintype.card K : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hK).mpr
  simpa only [mul_comm] using hc
end ProjectionCriterion

end

end OAI
