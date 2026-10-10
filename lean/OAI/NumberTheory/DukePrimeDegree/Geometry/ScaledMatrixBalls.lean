import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationRadius

namespace OAI

/-! # Uniform scaled matrix-ball operations for adjacent observation cells -/

noncomputable section
open Matrix Set
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrixBall_mul_scaled {n : ℕ} {C D δ : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {g h : G n} (hg : g ∈ matrixBall n (C*δ)) (hh : h ∈ matrixBall n (D*δ)) :
    g*h ∈ matrixBall n
      ((((n:ℝ)*C)*((n:ℝ)*D)+(n:ℝ)*C+(n:ℝ)*D+1)*δ) := by
  let A : ℝ := n*C
  let B : ℝ := n*D
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) hC
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hD
  have hgN : ‖g.val-1‖ ≤ A*δ := by
    simpa only [A,mul_assoc] using matrix_operator_norm_le_card_mul (g.val-1)
      (mul_nonneg hC hδ.le) (fun i j => (hg i j).le)
  have hhN : ‖h.val-1‖ ≤ B*δ := by
    simpa only [B,mul_assoc] using matrix_operator_norm_le_card_mul (h.val-1)
      (mul_nonneg hD hδ.le) (fun i j => (hh i j).le)
  have he : (g*h).val-1=(g.val-1)*(h.val-1)+(g.val-1)+(h.val-1) := by
    change g.val*h.val-1= _
    noncomm_ring
  have hd : δ^2 ≤ δ := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hd (mul_nonneg hA hB)
  have hb : ‖(g*h).val-1‖ ≤ (A*B+A+B)*δ := by
    calc
      _ ≤ ‖(g.val-1)*(h.val-1)‖+‖g.val-1‖+‖h.val-1‖ := by
        rw [he]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (A*δ)*(B*δ)+A*δ+B*δ := by
        exact add_le_add (add_le_add
          ((norm_mul_le _ _).trans (mul_le_mul hgN hhN (norm_nonneg _) (mul_nonneg hA hδ.le)))
          hgN) hhN
      _ ≤ _ := by nlinarith
  intro i j
  change |((g*h).val-1) i j| < (A*B+A+B+1)*δ
  exact ((matrix_entry_abs_le_operator_norm _ i j).trans hb).trans_lt (by nlinarith)

lemma matrixBall_right_translate_scaled {n : ℕ} (hn : 0 < n)
    (a : G n) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    {g : G n} (hg : g ∈ matrixBall n (C*δ)) :
    a⁻¹*g*a ∈ matrixBall n ((2*(n:ℝ)*Real.exp (2*matrixLogLength a)*C)*δ) := by
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  let R : ℝ := (2*(n:ℝ)*Real.exp (2*matrixLogLength a)*C)*δ
  have hR : 0 < R := by dsimp [R]; positivity
  have hm : MulAut.conj a⁻¹ g ∈ matrixBall n R := by
    apply conjugation_matrixBall_exp_bound hn a⁻¹ hR
    refine ⟨g,?_,rfl⟩
    rw [matrixLogLength_inv]
    have he : R/(2*(n:ℝ)*Real.exp (2*matrixLogLength a))=C*δ := by
      dsimp [R]
      field_simp [hnp.ne',Real.exp_ne_zero]
    rwa [he]
  simpa only [MulAut.conj_apply,inv_inv] using hm

end DukePrimeDegree

end

end OAI
