import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.ScalarFamily

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma modifiedScalar_deriv {B:ℝ → ℝ} (hB:ContDiff ℝ ∞ B) (a D b s:ℝ) :
    deriv (fun x=>modifiedScalar a D B (b,x)) s=1+b/D*deriv B ((s-a)/D) := by
  have H:= (hasDerivAt_id s).add (((hB.differentiable (by simp) ((s-a)/D)).hasDerivAt.comp s
    (((hasDerivAt_id s).sub_const a).div_const D)).const_mul b)
  convert! H.deriv using 1
  ring

lemma modifiedScalar_second {B:ℝ → ℝ} (hB:ContDiff ℝ ∞ B) (a D b s:ℝ) :
    iteratedDeriv 2 (fun x=>modifiedScalar a D B (b,x)) s=b/D^2*iteratedDeriv 2 B ((s-a)/D) := by
  have hb:ContDiff ℝ ∞ (deriv B):=(contDiff_infty_iff_deriv.mp hB).2
  have H:= (hasDerivAt_const s (1:ℝ)).add (((hb.differentiable (by simp) ((s-a)/D)).hasDerivAt.comp s
    (((hasDerivAt_id s).sub_const a).div_const D)).const_mul (b/D))
  have heq:deriv (fun x=>modifiedScalar a D B (b,x))=(fun x=>1+b/D*deriv B ((x-a)/D)) :=
    funext (modifiedScalar_deriv hB a D b)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [heq]
  convert! H.deriv using 1
  ring

end WeakMTWTransport

end

end OAI
