import Mathlib
import OAI.Geometry.WeakHessian.Entropy.LogAddTwoSqrt
import OAI.Geometry.WeakHessian.LocalBounds.SqrtWeighted

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile55
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integral_reducedEntropy_weighted_bound (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {V : X → ℝ} (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m) (hw : Integrable (fun x => Real.exp (-V x)) m) :
    |∫ x,reducedEntropy (u x) ∂m| ≤ ‖u‖^2/2+‖hU.toLp _‖*‖hD.toLp _‖+(∫ x,Real.exp (-V x) ∂m) := by
  have hp := weighted_pairing hU hD
  have he := integrable_reducedEntropy (Lp.memLp u) hun hp.1 hw
  have hup : (∫ x,reducedEntropy (u x) ∂m) ≤ ‖u‖^2/2 := by
    have H := integral_mono_ae he ((Lp.memLp u).integrable_sq.div_const 2)
      (hun.mono fun x hx => reducedEntropy_upper hx)
    rw [integral_div] at H
    have heq : (∫ x,u x^2 ∂m) = ‖u‖^2 := by
      simpa only [L2.inner_def,RCLike.inner_apply,conj_trivial,pow_two] using real_inner_self_eq_norm_sq u
    rwa [heq] at H
  have hlo : -(∫ x,u x*V x ∂m)-(∫ x,Real.exp (-V x) ∂m) ≤ ∫ x,reducedEntropy (u x) ∂m := by
    have H := integral_mono_ae (hp.1.neg.sub hw) he (by
      filter_upwards [hun] with x hx
      have H := reducedEntropy_lower hx (Real.exp_pos (-V x))
      simpa only [Real.log_exp,mul_neg,Pi.sub_apply,Pi.neg_apply] using! H)
    change (∫ x,-(u x*V x)-Real.exp (-V x) ∂m) ≤ _ at H
    rw [integral_sub (by convert! hp.1.neg using 1) hw,integral_neg] at H
    exact H
  apply abs_le.mpr
  have hp' : (∫ x,u x*V x ∂m) ≤ ‖hU.toLp _‖*‖hD.toLp _‖ := (le_abs_self _).trans hp.2
  have hw0 : 0 ≤ ∫ x,Real.exp (-V x) ∂m := integral_nonneg fun x => (Real.exp_pos _).le
  constructor <;> nlinarith [sq_nonneg ‖u‖,norm_nonneg (hU.toLp _),norm_nonneg (hD.toLp _)]

lemma integral_reducedEntropy_tendsto_weighted {V : X → ℝ}
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    {us : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hlim : Tendsto us atTop (𝓝 u)) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hns : ∀ n,∀ᵐ x ∂m,0 ≤ us n x) (hi : Integrable u m) (his : ∀ n,Integrable (us n) m)
    (hm : ∀ n,(∫ x,us n x ∂m) = ∫ x,u x ∂m)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hUs : ∀ n,MemLp (fun x => us n x*Real.exp (V x)) 2 m)
    {C : ℝ} (hC : ‖hU.toLp _‖ ≤ C) (hCs : ∀ n,‖(hUs n).toLp _‖ ≤ C) :
    Tendsto (fun n => ∫ x,reducedEntropy (us n x) ∂m) atTop (𝓝 (∫ x,reducedEntropy (u x) ∂m)) := by
  have hroot := integrable_sqrt_weighted (Lp.aestronglyMeasurable u) hun hU hhalf hhalfi
  have hroots (n : ℕ) := integrable_sqrt_weighted (Lp.aestronglyMeasurable (us n)) (hns n) (hUs n) hhalf hhalfi
  apply tendsto_integral_reducedEntropy_of_sqrt_bound hlim hun hns hi his hm hroot.1 (fun n => (hroots n).1)
    (C := (C*‖hhalf.toLp _‖+(∫ x,Real.exp (-(V x/2)) ∂m))/2)
  · exact hroot.2.trans (by gcongr)
  · intro n
    exact (hroots n).2.trans (by gcongr; exact hCs n)
end WeakHessian

end
end InlinedFile55

end OAI
