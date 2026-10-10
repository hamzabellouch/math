import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile196
noncomputable section
namespace WeakHessian
open Set
open scoped Topology

lemma exponential_ode_comparison {E : ℝ → ℝ} {c T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn E (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T,DifferentiableAt ℝ E t)
    (hi : ∀ t ∈ Ioo 0 T,c*E t ≤ deriv E t) :
    E 0 ≤ Real.exp (-c*T)*E T := by
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (fun s => Real.exp (-c*s)*E s)
        (Real.exp (-c*t)*(deriv E t-c*E t)) t := by
    convert! (((hasDerivAt_id t).const_mul (-c)).exp).mul (hd t ht).hasDerivAt using 1
    simp only [id_eq]
    ring
  have hm : MonotoneOn (fun t => Real.exp (-c*t)*E t) (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      ((((continuous_const.mul continuous_id).rexp).continuousOn).mul hc)
    · intro t ht
      exact (hder t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      change 0 ≤ deriv (fun s => Real.exp (-c*s)*E s) t
      rw [(hder t ht').deriv]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hi t ht'))
  simpa only [mul_zero,Real.exp_zero,one_mul] using hm ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT
end WeakHessian

end
end InlinedFile196

end OAI
