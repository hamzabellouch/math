import OAI.Geometry.RCD.Sobolev.InnerProductVariation

namespace OAI

/-! # A pairing derivative from both frozen scalar pairings

One Lipschitz-order increment and continuity of the other factor make
the mixed increment negligible. Neither factor needs a vector derivative.
-/

open Filter Asymptotics
open scoped Topology
namespace RegularPointCoordinates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_inner_of_two_frozen {W Q : ℝ → E} {t a b : ℝ}
    (hW : (fun s => W s-W t) =O[𝓝 t] (fun s => s-t))
    (hQ : ContinuousAt Q t)
    (hleft : HasDerivAt (fun s => inner ℝ (W s) (Q t)) a t)
    (hright : HasDerivAt (fun s => inner ℝ (W t) (Q s)) b t) :
    HasDerivAt (fun s => inner ℝ (W s) (Q s)) (a+b) t := by
  let e := fun s => inner ℝ (W s-W t) (Q s-Q t)
  have hsmall : (fun s => ‖Q s-Q t‖) =o[𝓝 t] (fun _ => (1:ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    simpa only [sub_self,norm_zero] using (hQ.tendsto.sub_const (Q t)).norm
  have hprod : (fun s => ‖W s-W t‖*‖Q s-Q t‖) =o[𝓝 t] (fun s => s-t) := by
    simpa only [mul_one] using hW.norm_left.mul_isLittleO hsmall
  have he : e =o[𝓝 t] (fun s => s-t) :=
    (IsBigO.of_norm_le (fun s => norm_inner_le_norm (W s-W t) (Q s-Q t))).trans_isLittleO hprod
  have hed : HasDerivAt e 0 t := by
    apply HasDerivAt.of_isLittleO
    simpa only [e,sub_self,inner_zero_left,smul_zero,sub_zero] using he
  have hd := ((hleft.add hright).sub_const (inner ℝ (W t) (Q t))).add hed
  simp only [add_zero] at hd
  convert hd using 1
  ext s
  simp only [Pi.add_apply,e,inner_sub_left,inner_sub_right]
  ring

end RegularPointCoordinates

end OAI
