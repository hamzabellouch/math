import OAI.Analysis.Pureness.Quasitrace.QuasitraceComplexNormContinuity

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma cauchyValue_sub_norm_le (u v : T.cauchySequenceAlgebra hadd) :
    ‖T.cauchyValue hadd hsqrt u-T.cauchyValue hadd hsqrt v‖ ≤ (2*T ⟨1,zero_le_one⟩)*‖u-v‖ := by
  apply le_of_tendsto ((T.cauchyValue_tendsto hadd hsqrt u).sub (T.cauchyValue_tendsto hadd hsqrt v)).norm
  apply Eventually.of_forall
  intro k
  exact (T.complexValue_sub_norm_le (u.1 k) (v.1 k)).trans
    (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero (u.1-v.1) k)
      (mul_nonneg (by norm_num) (T.nonneg _)))

lemma quotientValue_sub_norm_le (x y : T.CauchyQuotient hadd) :
    ‖T.quotientValue hadd hsqrt x-T.quotientValue hadd hsqrt y‖ ≤
      (2*T ⟨1,zero_le_one⟩)*‖x-y‖ := by
  let K := 2*T ⟨1,zero_le_one⟩
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (T.nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < ε/(K+1) := div_pos hε (by linarith)
  have hKδ : K*(ε/(K+1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < K+1 by linarith)).mpr
    nlinarith
  obtain ⟨w,hw,hwn⟩ := T.cauchyQuotient_norm_lt_rep hadd (x-y) hδ
  obtain ⟨v,hv⟩ := T.cauchyQuotientMap_surjective hadd y
  have hsum : T.cauchyQuotientMap hadd (w+v) = x := by rw [map_add,hw,hv,sub_add_cancel]
  have he := T.cauchyValue_sub_norm_le hadd hsqrt (w+v) v
  rw [← T.quotientValue_map hadd hsqrt (w+v),← T.quotientValue_map hadd hsqrt v,
    hsum,hv,add_sub_cancel_right] at he
  have hbound := mul_le_mul_of_nonneg_left hwn.le hK
  change ‖T.quotientValue hadd hsqrt x-T.quotientValue hadd hsqrt y‖ ≤ K*‖x-y‖+ε
  change ‖T.quotientValue hadd hsqrt x-T.quotientValue hadd hsqrt y‖ ≤ K*‖w‖ at he
  nlinarith

lemma quotientValue_norm_lipschitz :
    LipschitzWith ⟨2*T ⟨1,zero_le_one⟩,mul_nonneg (by norm_num) (T.nonneg _)⟩ (T.quotientValue hadd hsqrt) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  exact T.quotientValue_sub_norm_le hadd hsqrt x y

lemma quotientValue_norm_continuous : Continuous (T.quotientValue hadd hsqrt) :=
  (T.quotientValue_norm_lipschitz hadd hsqrt).continuous
end CuntzPureness.PositiveQuasitrace

end

end OAI
