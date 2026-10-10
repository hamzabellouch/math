import OAI.Analysis.KadisonKastler.ScalingAdjointEstimate

namespace OAI

/-! # Uniform adjoint commutator control away from scaling ratio zero -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem StateScales.coisometry_adjoint_commutator_bound
    (d : ModularConjugationData M Ω) {r c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hcr : c ≤ r)
    (v : Algebra M) (hv : v*star v=1) (hs : StateScales M Ω r v.val)
    (a b : Algebra M) (hb : Commute b (star v)) :
    c*‖(a*star v-star v*a).val Ω‖ ≤ (1+c)*‖(a-b).val Ω‖ := by
  have hfirst := hs.coisometry_adjoint_vector_bound d (hc.trans_le hcr) v hv (a-b)
  have hcsq : c*‖(a-b).val ((star v).val Ω)‖^2 ≤ ‖(a-b).val Ω‖^2 :=
    (mul_le_mul_of_nonneg_right hcr (sq_nonneg _)).trans hfirst
  have hscaled : c*‖(a-b).val ((star v).val Ω)‖ ≤ ‖(a-b).val Ω‖ := by
    have hsquare : (c*‖(a-b).val ((star v).val Ω)‖)^2 ≤ ‖(a-b).val Ω‖^2 := by
      calc
        _ = c*(c*‖(a-b).val ((star v).val Ω)‖^2) := by ring
        _ ≤ c*‖(a-b).val Ω‖^2 := mul_le_mul_of_nonneg_left hcsq hc.le
        _ ≤ _ := mul_le_of_le_one_left (sq_nonneg _) hc1
    nlinarith [norm_nonneg ((a-b).val Ω),
      mul_nonneg hc.le (norm_nonneg ((a-b).val ((star v).val Ω)))]
  have hvnorm : ‖(star v).val‖ ≤ 1 := by
    change ‖star v‖ ≤ 1
    rw [norm_star]
    exact coisometry_norm_le v hv
  have hsecond : ‖(star v).val ((a-b).val Ω)‖ ≤ ‖(a-b).val Ω‖ :=
    ((star v).val.le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hvnorm)
  have he : a*star v-star v*a=(a-b)*star v-star v*(a-b) := by
    rw [sub_mul,mul_sub,hb.eq]
    abel
  rw [he]
  change c*‖(a-b).val ((star v).val Ω)-(star v).val ((a-b).val Ω)‖ ≤ _
  calc
    _ ≤ c*(‖(a-b).val ((star v).val Ω)‖+‖(star v).val ((a-b).val Ω)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hc.le
    _ ≤ (1+c)*‖(a-b).val Ω‖ := by
      have hh := mul_le_mul_of_nonneg_left hsecond hc.le
      nlinarith

end

end KadisonKastler

end OAI
