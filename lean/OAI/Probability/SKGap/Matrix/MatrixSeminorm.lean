import Mathlib
import OAI.Probability.SKGap.Matrix.MatrixEntryCLM

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
def offDiagonalVector (M : Matrix ι ι ℝ) : PiLp 4 (fun _ : ι×ι=>ℝ) :=
  WithLp.toLp 4 (fun p=>if p.1=p.2 then 0 else M p.1 p.2)
def diagonalSeminorm (M : Matrix ι ι ℝ) : ℝ := ‖diagonalVector M‖
def offDiagonalSeminorm (M : Matrix ι ι ℝ) : ℝ := ‖offDiagonalVector M‖

omit [DecidableEq ι] in
lemma diagonalSeminorm_sq (M : Matrix ι ι ℝ) : diagonalSeminorm M^2=∑ i,(M i i)^2 := by
  simp only [diagonalSeminorm,EuclideanSpace.norm_sq_eq,diagonalVector,Real.norm_eq_abs,sq_abs]

lemma offDiagonalSeminorm_fourth (M : Matrix ι ι ℝ) :
    offDiagonalSeminorm M^4=∑ p : ι×ι,if p.1=p.2 then 0 else (M p.1 p.2)^4 := by
  rw [offDiagonalSeminorm,PiLp.norm_eq_of_nat (p:=4) 4 (by norm_num)]
  rw [←Real.rpow_natCast,←Real.rpow_mul (Finset.sum_nonneg (fun _ _=>pow_nonneg (norm_nonneg _) _))]
  norm_num only [Nat.cast_ofNat,one_div,mul_inv_cancel₀ (by norm_num : (4:ℝ)≠0),Real.rpow_one]
  apply Finset.sum_congr rfl
  intro p _
  simp only [offDiagonalVector,WithLp.ofLp_toLp]
  split_ifs
  · simp
  · rw [Real.norm_eq_abs]
    calc
      |M p.1 p.2|^4=(|M p.1 p.2|^2)^2 := by ring
      _ = ((M p.1 p.2)^2)^2 := by rw [sq_abs]
      _ = (M p.1 p.2)^4 := by ring

lemma diagonalSeminorm_le (M : Matrix ι ι ℝ) : diagonalSeminorm M≤‖M‖ := by
  apply le_of_pow_le_pow_left₀ (by decide : 2≠0) (norm_nonneg _)
  rw [diagonalSeminorm_sq,frobenius_sq]
  exact Finset.sum_le_sum (fun i _=>Finset.single_le_sum (fun k _=>sq_nonneg (M i k)) (Finset.mem_univ i))

lemma offDiagonalSeminorm_le (M : Matrix ι ι ℝ) : offDiagonalSeminorm M≤‖M‖ := by
  let a : ι×ι→ℝ := fun p=>if p.1=p.2 then 0 else (M p.1 p.2)^2
  have ha : ∀ p,0≤a p := by intro p;dsimp [a];split_ifs <;> positivity
  have hs : (∑ p,a p)≤‖M‖^2 := by
    rw [frobenius_sq]
    rw [show (∑ i,∑ k,(M i k)^2) = ∑ p : ι×ι,(M p.1 p.2)^2 from (Fintype.sum_prod_type fun p : ι×ι=>(M p.1 p.2)^2).symm]
    apply Finset.sum_le_sum
    intro p _
    dsimp [a]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  apply le_of_pow_le_pow_left₀ (by decide : 4≠0) (norm_nonneg _)
  rw [offDiagonalSeminorm_fourth]
  calc
    _ = ∑ p,a p^2 := by
      apply Finset.sum_congr rfl
      intro p _
      dsimp [a]
      split_ifs <;> ring
    _ ≤ (∑ p,a p)^2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun p _=>ha p)
    _ ≤ (‖M‖^2)^2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun p _=>ha p)) hs 2
    _ = ‖M‖^4 := by ring

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma diagonalVector_sub (M N : Matrix ι ι ℝ) : diagonalVector (M-N)=diagonalVector M-diagonalVector N := by rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma diagonalVector_add (M N : Matrix ι ι ℝ) : diagonalVector (M+N)=diagonalVector M+diagonalVector N := by rfl
omit [Fintype ι] in
@[simp] lemma offDiagonalVector_sub (M N : Matrix ι ι ℝ) : offDiagonalVector (M-N)=offDiagonalVector M-offDiagonalVector N := by
  ext p
  simp only [offDiagonalVector,WithLp.ofLp_toLp,PiLp.sub_apply]
  split_ifs <;> simp
omit [Fintype ι] in
@[simp] lemma offDiagonalVector_add (M N : Matrix ι ι ℝ) : offDiagonalVector (M+N)=offDiagonalVector M+offDiagonalVector N := by
  ext p
  simp only [offDiagonalVector,WithLp.ofLp_toLp,PiLp.add_apply]
  split_ifs <;> simp

lemma diagonalSeminorm_lipschitz : LipschitzWith 1 (diagonalSeminorm (ι:=ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,diagonalSeminorm,←diagonalVector_sub] using!
    (abs_norm_sub_norm_le (diagonalVector M) (diagonalVector N)).trans (diagonalSeminorm_le (M-N))
lemma offDiagonalSeminorm_lipschitz : LipschitzWith 1 (offDiagonalSeminorm (ι:=ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  have hh : ‖offDiagonalVector M-offDiagonalVector N‖≤‖M-N‖ := by
    simpa only [←offDiagonalVector_sub,offDiagonalSeminorm] using! offDiagonalSeminorm_le (M-N)
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,offDiagonalSeminorm] using!
    (abs_norm_sub_norm_le (offDiagonalVector M) (offDiagonalVector N)).trans hh
omit [DecidableEq ι] in
lemma diagonalSeminorm_add (M N : Matrix ι ι ℝ) :
    diagonalSeminorm (M+N)≤diagonalSeminorm M+diagonalSeminorm N := by
  simpa only [diagonalSeminorm,diagonalVector_add] using norm_add_le (diagonalVector M) (diagonalVector N)
lemma offDiagonalSeminorm_add (M N : Matrix ι ι ℝ) :
    offDiagonalSeminorm (M+N)≤offDiagonalSeminorm M+offDiagonalSeminorm N := by
  simpa only [offDiagonalSeminorm,offDiagonalVector_add] using norm_add_le (offDiagonalVector M) (offDiagonalVector N)
end SKGap
end
end

end OAI
