import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.FlatHeat

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open scoped ContDiff

lemma heat_joint_contDiffAt {x : ℝ × V} (hx : x.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun v : ℝ × V => heat v.1 v.2) x := by
  have hp : ContDiffAt ℝ ∞ (fun v : ℝ × V => 4*Real.pi*v.1) x :=
    contDiffAt_const.mul contDiffAt_fst
  have hi : ContDiffAt ℝ ∞ (fun v : ℝ × V => (4*Real.pi*v.1)⁻¹^2) x :=
    (hp.inv (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx)).pow 2
  have hn : ContDiffAt ℝ ∞ (fun v : ℝ × V => -‖v.2‖^2) x :=
    (contDiffAt_snd.norm_sq (𝕜 := ℝ)).neg
  have he : ContDiffAt ℝ ∞ (fun v : ℝ × V => -‖v.2‖^2/(4*v.1)) x :=
    hn.div (contDiffAt_const.mul contDiffAt_fst) (mul_ne_zero (by norm_num) hx)
  exact hi.mul he.exp

end TamingCompatibility.GeometricHilbert.FlatHeat

end
end

end

end OAI
