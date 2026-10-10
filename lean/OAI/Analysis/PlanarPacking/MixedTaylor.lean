import OAI.Analysis.PlanarPacking.RationalEnvelopes

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
noncomputable def transformTaylor (ell n : ℕ) : ℝ :=
  (23:ℝ)/10*transformRational ell n+(17:ℝ)/1000*atomicRational ell n
lemma fullMoment_transformed_bound (a : Bool) (ell n : ℕ) :
    |fullMoment a true n ell|≤transformTaylor ell n/(ell.factorial:ℝ) := by
  rw [fullMoment_transformed,abs_div,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ)≤(ell.factorial:ℝ))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hk:=sharp_moment_bound (tableData a) ell (Nat.cast_nonneg n)
  have hm:=table_coeff_mass a
  have hc:=table_constant_bound a
  have htn:=transformEnvelope_nonneg ell (Nat.cast_nonneg n)
  have han:=atomicEnvelope_nonneg ell (n:ℝ)
  have hk1:=mul_le_mul (show |(tableData a).c₀|+|(tableData a).d₀|+‖(tableData a).x‖≤(23:ℝ)/10 by linarith)
    (transformEnvelope_le_rat ell n) htn (by norm_num : (0:ℝ)≤23/10)
  have hk2:=mul_le_mul hc (atomicEnvelope_le_rat ell n) han (by norm_num : (0:ℝ)≤17/1000)
  unfold transformTaylor
  exact hk.trans (add_le_add hk1 hk2)
lemma fullMoment_transformed_cap (a : Bool) (ell n : ℕ) {B : ℝ}
    (hB : transformTaylor ell n/(ell.factorial:ℝ)≤B) :
    |fullMoment a true n ell|≤B := (fullMoment_transformed_bound a ell n).trans hB
end SharpPlanar

end OAI
