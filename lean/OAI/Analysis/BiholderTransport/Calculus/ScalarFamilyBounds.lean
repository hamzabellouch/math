import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.ExactScalarBounds

namespace OAI


noncomputable section
open Set Filter
open scoped ContDiff Topology NNReal

namespace WeakMTWTransport

lemma modifiedScalar_lipschitz {B:ℝ → ℝ} (hB:ContDiff ℝ ∞ B)
    {C D b:ℝ} (hC:0 ≤ C) (hD:0 < D) (hb:0 ≤ b) (hbd:b/D*C ≤ 1/2)
    (hder:∀s,|deriv B s|≤C) (a:ℝ) :
    LipschitzWith 2 (fun s=>modifiedScalar a D B (b,s)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact fun s=>(scalar_family_derivable (modifiedScalar_contDiff hB a D) (b,s)).differentiableAt
  · intro s
    apply (NNReal.coe_le_coe).mp
    rw [coe_nnnorm,Real.norm_eq_abs]
    obtain ⟨hl,hu⟩:=modifiedScalar_slope_bounds hB hC hD hb hbd hder a s
    rw [abs_of_nonneg (by linarith only [hl])]
    norm_num only [NNReal.coe_ofNat]
    linarith only [hu]

lemma exact_center_deriv_abs (s:ℝ) : |deriv centerTemplate s| ≤ centerGamma/2 := by
  rw [abs_of_neg (centerTemplate_deriv_neg s)]
  exact (centerTemplate_deriv_bound s).2

lemma exact_center_slope_small {a D b s eps:ℝ} (hD:0 < D) (hb:0 ≤ b)
    (hsmall:b/D*centerGamma/2 < eps) :
    |deriv (fun x=>modifiedScalar a D centerTemplate (b,x)) s-1| < eps := by
  rw [modifiedScalar_deriv centerTemplate_smooth,add_sub_cancel_left,abs_mul,
    abs_of_nonneg (div_nonneg hb hD.le)]
  have H:=mul_le_mul_of_nonneg_left (exact_center_deriv_abs ((s-a)/D)) (div_nonneg hb hD.le)
  exact H.trans_lt (by simpa only [mul_div_assoc] using hsmall)

end WeakMTWTransport

end

end OAI
