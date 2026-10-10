import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section

noncomputable section
open Set
namespace SKGap.SourceTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma segment_taylor (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) (x y : E) {L : ℝ}
    (hL : 0≤L)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F (F' (x+t • (y-x))) (x+t • (y-x)))
    (hLip : ∀t∈Icc (0:ℝ) 1,‖F' (x+t • (y-x))-F' x‖≤L*‖t • (y-x)‖) :
    |F y-F x-F' x (y-x)|≤L*‖y-x‖^2 := by
  let g : ℝ→ℝ:=fun t=>F (x+t • (y-x))-F x-t*(F' x (y-x))
  let g' : ℝ→ℝ:=fun t=>(F' (x+t • (y-x))-F' x) (y-x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t := by
    have H:=(((hF t ht).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (y-x)).const_add x)).sub_const (F x)).sub
      ((hasDerivAt_id t).mul_const (F' x (y-x)))
    convert! H using 1
    simp only [g',sub_apply,one_smul,one_mul]
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖g' t‖≤L*‖y-x‖^2 := by
    calc
      _ ≤ ‖F' (x+t • (y-x))-F' x‖*‖y-x‖ := (F' (x+t • (y-x))-F' x).le_opNorm _
      _ ≤ (L*‖t • (y-x)‖)*‖y-x‖ := mul_le_mul_of_nonneg_right (hLip t ⟨ht.1,ht.2.le⟩) (norm_nonneg _)
      _ ≤ (L*‖y-x‖)*‖y-x‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
      _ = _ := by ring
  have H:=norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht=>(hg t ht).hasDerivWithinAt) hb
  simpa only [g,one_smul,zero_smul,add_sub_cancel,add_zero,one_mul,zero_mul,sub_self,sub_zero,
    Real.norm_eq_abs] using H

lemma segment_lipschitz (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) (x y : E) {C : ℝ}
    (hC : 0≤C)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F (F' (x+t • (y-x))) (x+t • (y-x)))
    (hBound : ∀t∈Icc (0:ℝ) 1,‖F' (x+t • (y-x))‖≤C) :
    |F y-F x|≤C*‖y-x‖ := by
  let g : ℝ→ℝ:=fun t=>F (x+t • (y-x))
  let g' : ℝ→ℝ:=fun t=>F' (x+t • (y-x)) (y-x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t := by
    convert! (hF t ht).comp_hasDerivAt t (((hasDerivAt_id t).smul_const (y-x)).const_add x) using 1
    simp only [g',one_smul]
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖g' t‖≤C*‖y-x‖ :=
    ((F' (x+t • (y-x))).le_opNorm _).trans
      (mul_le_mul (hBound t ⟨ht.1,ht.2.le⟩) le_rfl (norm_nonneg _) hC)
  have H:=norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht=>(hg t ht).hasDerivWithinAt) hb
  simpa only [g,one_smul,zero_smul,add_sub_cancel,add_zero,Real.norm_eq_abs] using H

end SKGap.SourceTaylor

end
end

end OAI
