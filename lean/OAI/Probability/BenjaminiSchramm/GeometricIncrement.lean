import OAI.Probability.BenjaminiSchramm.UpwardFractionalSlabProfile

namespace OAI

noncomputable section
open scoped ENNReal BigOperators
namespace Percolation.BenjaminiSchramm

lemma geometric_increment_factored (F : ℕ → ℝ≥0∞) (B K W : ℝ≥0∞) (s : ℝ)
    (h0 : F 0 ≤ B*W)
    (hstep : ∀ n, F (n+1) ≤ F n+K*W*ENNReal.ofReal (Real.exp (-s*n))) :
    ∀ n, F n ≤ (B+K*(∑' i : ℕ, ENNReal.ofReal (Real.exp (-s*i))))*W := by
  have hb : ∀ n, F n ≤ (B+K*∑ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (-s*i)))*W := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      calc
        _ ≤ F n+K*W*ENNReal.ofReal (Real.exp (-s*n)) := hstep n
        _ ≤ (B+K*∑ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (-s*i)))*W+
            K*W*ENNReal.ofReal (Real.exp (-s*n)) := add_le_add ih le_rfl
        _ = _ := by
          rw [Finset.sum_range_succ]
          simp only [mul_add,add_mul]
          ac_rfl
  intro n
  exact (hb n).trans (mul_le_mul' (add_le_add le_rfl
    (mul_le_mul' le_rfl (ENNReal.sum_le_tsum _))) le_rfl)

lemma geometric_increment_uniform (F : ℕ → ℝ≥0∞) (B K : ℝ≥0∞) (s : ℝ)
    (hs : 0 < s) (h0 : F 0 ≤ B)
    (hstep : ∀ n, F (n+1) ≤ F n+K*ENNReal.ofReal (Real.exp (-s*n))) :
    ∃ C : ℝ≥0∞, (B < ⊤ → K < ⊤ → C < ⊤) ∧ ∀ n, F n ≤ C := by
  let S : ℝ≥0∞ := ∑' n : ℕ, ENNReal.ofReal (Real.exp (-s*n))
  have hS : S < ⊤ := by
    apply Summable.tsum_ofReal_lt_top
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hs)
  have hfinite : ∀ n, F n ≤ B+K*∑ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (-s*i)) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      apply (hstep n).trans
      rw [Finset.sum_range_succ,mul_add,←add_assoc]
      exact add_le_add ih le_rfl
  refine ⟨B+K*S,fun hB hK => ENNReal.add_lt_top.mpr ⟨hB,ENNReal.mul_lt_top hK hS⟩,
    fun n => (hfinite n).trans (add_le_add le_rfl (mul_le_mul' le_rfl ?_))⟩
  exact ENNReal.sum_le_tsum _

end Percolation.BenjaminiSchramm

end

end OAI
