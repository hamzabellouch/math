import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace OAI

/-! # Differentiating a varying pairing from its frozen pairing

Only continuity of the second vector is needed once its pairing against
the fixed first vector has a scalar derivative.
-/

open Filter Asymptotics
open scoped Topology

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A scalar product rule that does not ask the second vector for a
vector-valued derivative. -/
theorem hasDerivAt_inner_of_frozen {W Q : ℝ → E} {t : ℝ} {W' : E} {a : ℝ}
    (hW : HasDerivAt W W' t) (hQ : ContinuousAt Q t)
    (hfixed : HasDerivAt (fun s => inner ℝ (W t) (Q s)) a t) :
    HasDerivAt (fun s => inner ℝ (W s) (Q s)) (inner ℝ W' (Q t)+a) t := by
  let e : ℝ → ℝ := fun s => inner ℝ (W s-W t) (Q s-Q t)
  have hsmall : (fun s => ‖Q s-Q t‖) =o[𝓝 t] (fun _ => (1:ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    simpa only [sub_self,norm_zero] using (hQ.tendsto.sub_const (Q t)).norm
  have hprod : (fun s => ‖W s-W t‖*‖Q s-Q t‖) =o[𝓝 t] (fun s => s-t) := by
    simpa only [mul_one] using hW.isBigO_sub.norm_left.mul_isLittleO hsmall
  have he : e =o[𝓝 t] (fun s => s-t) :=
    (IsBigO.of_norm_le (fun s => norm_inner_le_norm (W s-W t) (Q s-Q t))).trans_isLittleO hprod
  have hed : HasDerivAt e 0 t := by
    apply HasDerivAt.of_isLittleO
    simpa only [e,sub_self,inner_zero_left,smul_zero,sub_zero] using he
  have hfirst := hW.inner ℝ (hasDerivAt_const t (Q t))
  have hd : HasDerivAt
      (fun s => inner ℝ (W s) (Q t)+inner ℝ (W t) (Q s)-inner ℝ (W t) (Q t)+e s)
      (inner ℝ W' (Q t)+a) t := by
    simpa only [inner_zero_right,zero_add,add_zero] using!
      ((hfirst.add hfixed).sub_const (inner ℝ (W t) (Q t))).add hed
  convert hd using 1
  ext s
  simp only [e,inner_sub_left,inner_sub_right]
  ring

end RegularPointCoordinates

end OAI
