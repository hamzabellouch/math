import OAI.Analysis.Laughlin.Spin.GenericNormalizedLadder
import OAI.Analysis.Laughlin.Spin.Support

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericUnitDescendant_raising_succ (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n < genericCoupledWeight A B z) :
    totalRaise A B *ᵥ genericUnitDescendant A B z hA hB (n+1) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) •
        genericUnitDescendant A B z hA hB n := by
  have hr : totalRaise A B *ᵥ genericDescendant A B z hA hB (n+1) =
      (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) • genericDescendant A B z hA hB n := by
    exact descendant_raising (totalRaise A B) (totalWeight A B) (totalRaise A B)ᵀ
      (genericHighest A B z hA hB) (genericCoupledWeight A B z)
      (total_raise_lower_commutator A B) (total_weight_lower_commutator A B)
      (genericHighest_weight A B z hA hB) (genericHighest_raising_zero A B z hA hB) n
  have hc : 0 < ((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n) := by
    have hn' : (n : ℝ) < genericCoupledWeight A B z := by exact_mod_cast hn
    positivity
  have hden : Real.sqrt (vectorNormSq (genericDescendant A B z hA hB (n+1))) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        Real.sqrt (vectorNormSq (genericDescendant A B z hA hB n)) := by
    rw [genericDescendant_norm_step,Real.sqrt_mul (le_of_lt hc)]
  have hx : (Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)))⁻¹ *
      (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) =
        Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) := by
    apply mul_left_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hc))
    rw [mul_inv_cancel_left₀ (ne_of_gt (Real.sqrt_pos.mpr hc))]
    exact (Real.mul_self_sqrt (le_of_lt hc)).symm
  unfold genericUnitDescendant
  rw [Matrix.mulVec_smul,hr,smul_smul,smul_smul,hden,mul_inv_rev]
  rw [mul_assoc,hx,mul_comm]

theorem genericDescendant_past_lowest (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    genericDescendant A B z hA hB (genericCoupledWeight A B z+1)=0 := by
  have h := genericDescendant_norm_step A B z (genericCoupledWeight A B z) hA hB
  simp only [sub_self,mul_zero,zero_mul] at h
  funext i
  have hi : (genericDescendant A B z hA hB (genericCoupledWeight A B z+1) i)^2 ≤
      vectorNormSq (genericDescendant A B z hA hB (genericCoupledWeight A B z+1)) :=
    Finset.single_le_sum (fun k hk => sq_nonneg _) (Finset.mem_univ i)
  rw [h] at hi
  change genericDescendant A B z hA hB (genericCoupledWeight A B z+1) i=0
  nlinarith [sq_nonneg (genericDescendant A B z hA hB (genericCoupledWeight A B z+1) i)]

theorem genericUnitDescendant_lowest (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    (totalRaise A B)ᵀ *ᵥ genericUnitDescendant A B z hA hB (genericCoupledWeight A B z)=0 := by
  unfold genericUnitDescendant
  rw [Matrix.mulVec_smul,← genericDescendant_succ,genericDescendant_past_lowest,smul_zero]

end Laughlin.Spin

end OAI
