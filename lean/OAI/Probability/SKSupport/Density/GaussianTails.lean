import Mathlib
import OAI.Probability.SKSupport.Density.FiniteForwardRatio
import OAI.Probability.SKSupport.Density.GaussianDecay

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma ExponentialBound.const (a : ℝ) : ExponentialBound (fun _ => a) :=
  ExponentialBound.of_bounded (A := Real.nnabs a) (fun _ => le_rfl)

lemma ExponentialBound.neg {f : ℝ → ℝ} (hf : ExponentialBound f) : ExponentialBound (fun x => -f x) := by
  obtain ⟨A,K,hA⟩ := hf
  exact ⟨A,K,fun x => by simpa only [abs_neg] using hA x⟩

lemma ExponentialBound.add {f g : ℝ → ℝ} (hf : ExponentialBound f) (hg : ExponentialBound g) :
    ExponentialBound (fun x => f x+g x) := by
  obtain ⟨A,K,hA⟩ := hf
  obtain ⟨B,J,hB⟩ := hg
  refine ⟨A+B,K+J,fun x => ?_⟩
  simp only [NNReal.coe_add]
  have hk : Real.exp ((K:ℝ)*|x|) ≤ Real.exp (((K:ℝ)+J)*|x|) := by gcongr;exact le_add_of_nonneg_right J.coe_nonneg
  have hj : Real.exp ((J:ℝ)*|x|) ≤ Real.exp (((K:ℝ)+J)*|x|) := by gcongr;exact le_add_of_nonneg_left K.coe_nonneg
  calc
    |f x+g x| ≤ |f x|+|g x| := abs_add_le _ _
    _ ≤ (A:ℝ)*Real.exp ((K:ℝ)*|x|)+(B:ℝ)*Real.exp ((J:ℝ)*|x|) := add_le_add (hA x) (hB x)
    _ ≤ ((A:ℝ)+B)*Real.exp (((K:ℝ)+J)*|x|) := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hk A.coe_nonneg) (mul_le_mul_of_nonneg_left hj B.coe_nonneg)

lemma ExponentialBound.sub {f g : ℝ → ℝ} (hf : ExponentialBound f) (hg : ExponentialBound g) :
    ExponentialBound (fun x => f x-g x) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma ExponentialBound.pow {f : ℝ → ℝ} (hf : ExponentialBound f) (n : ℕ) : ExponentialBound (fun x => (f x)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using ExponentialBound.const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma gaussian_expBound_tendsto_zero {g : ℝ → ℝ} (hg : ExponentialBound g)
    {d : ℝ} (hd : 0 < d) : Tendsto (fun x => Real.exp (-d*x^2)*g x) atTop (𝓝 0) := by
  obtain ⟨A,K,hA⟩ := hg
  have hpow : Tendsto (fun x : ℝ => x^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have he : Tendsto (fun x : ℝ => Real.exp (-(d/2)*x^2)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hpow.const_mul_atTop (half_pos hd))) using 1
    first | rfl | (funext x;dsimp only [Function.comp_apply];congr 1;ring)
  have hlim := he.const_mul ((A:ℝ)*Real.exp ((K:ℝ)^2/(2*d)))
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm _ hlim
  intro x
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-d*x^2)*|g x| ≤ Real.exp (-d*x^2)*((A:ℝ)*Real.exp ((K:ℝ)*|x|)) :=
      mul_le_mul_of_nonneg_left (hA x) (Real.exp_nonneg _)
    _ = (A:ℝ)*Real.exp (-d*x^2+(K:ℝ)*|x|) := by rw [Real.exp_add];ring
    _ ≤ (A:ℝ)*Real.exp (((K:ℝ)^2/(2*d)) + (-(d/2)*x^2)) := by
      apply mul_le_mul_of_nonneg_left _ A.coe_nonneg
      apply Real.exp_le_exp.mpr
      linarith [linear_abs_le_quadratic hd (K:ℝ) x]
    _ = _ := by rw [Real.exp_add];ring

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma BoundedSmooth.regular {r : ℝ → ℝ} (hr : BoundedSmooth r) : RegularDatum r := ⟨hr.smooth,hr.deriv⟩

lemma BoundedSmooth.exponentialBound {r : ℝ → ℝ} (hr : BoundedSmooth r) : ExponentialBound r := by
  obtain ⟨C,hC⟩ := hr.bound
  exact ExponentialBound.of_bounded hC

lemma certW_odd {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (ho : Function.Odd r) : Function.Odd (certW r) := by
  simpa only [certW,iteratedDeriv_succ,iteratedDeriv_zero] using
    even_deriv_odd ((contDiff_infty_iff_deriv.mp hr |>.2).differentiable (by simp))
      (odd_deriv_even (hr.differentiable (by simp)) ho)

lemma certV_even {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (ho : Function.Odd r) : Function.Even (certV r) :=
  odd_deriv_even (hr.differentiable (by simp)) ho

lemma certZ_even {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (ho : Function.Odd r) : Function.Even (certZ r) := by
  have hh := odd_deriv_even ((contDiff_iteratedDeriv_infty hr 2).differentiable (by simp)) (certW_odd hr ho)
  simpa only [certZ,certW,iteratedDeriv_succ] using hh

lemma odd_zero {r : ℝ → ℝ} (ho : Function.Odd r) : r 0=0 := by
  have hh := ho 0
  simp only [neg_zero] at hh
  linarith

lemma cert_flux_continuous {r s ρ : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hshape : BackwardShape r) (hso : Function.Odd s) (hρ : Continuous ρ) : Continuous (certFlux r s ρ) := by
  have hw := contDiff_iteratedDeriv_infty hr 2
  have hbw := quotientExtension_continuous (hw.differentiable (by simp)) (hr.differentiable (by simp)) hshape
  have hbs := quotientExtension_continuous (hs.differentiable (by simp)) (hr.differentiable (by simp)) hshape
  have hv : Continuous (certV r) := (contDiff_infty_iff_deriv.mp hr |>.2).continuous
  have hsd : Continuous (deriv s) := (contDiff_infty_iff_deriv.mp hs |>.2).continuous
  have he : certFlux r s ρ = fun x => r x*Certificate.F₂ (certR r x) (certK r s x) (certV r x)
      (-quotientExtension (certW r) r x) (deriv s x-quotientExtension s r x*certV r x)*ρ x := by
    funext x
    by_cases hx : x=0
    · subst x;simp only [certFlux,hshape.zero,zero_mul]
    · rw [quotientExtension_eq (odd_zero (certW_odd hr hshape.odd)) hshape.zero hx,
        quotientExtension_eq (odd_zero hso) hshape.zero hx]
      simp only [certFlux,certB,certJ,neg_div]
  rw [he]
  dsimp only [Certificate.F₂,Certificate.F₁,certR,certK]
  fun_prop

lemma certificate_growth {r s : ℝ → ℝ} (hr : BoundedSmooth r) (hs : RegularDatum s)
    (hshape : BackwardShape r) (hso : Function.Odd s) :
    ExponentialBound (fun x => Certificate.F₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)) ∧
    ExponentialBound (fun x => Certificate.WF₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)
      (certZ r x) (certL r s x)) := by
  obtain ⟨K,hK⟩ := hs.exists_lipschitz
  have hsE := exponentialBound_of_lipschitz hK
  have hrE := hr.exponentialBound
  have hR : ExponentialBound (certR r) := hrE.pow 2
  have hKv : ExponentialBound (certK r s) := hrE.mul hsE
  have hv : ExponentialBound (certV r) := hr.deriv.exponentialBound
  have hw : BoundedSmooth (certW r) := by simpa only [certW,iteratedDeriv_succ,iteratedDeriv_zero] using hr.deriv.deriv
  obtain ⟨J,hJ⟩ := hw.regular.exists_lipschitz
  have hbe := exponentialBound_quotient (hw.smooth.differentiable (by simp)) hJ
    (odd_zero (certW_odd hr.smooth hshape.odd)) (hr.smooth.differentiable (by simp)) hshape
  have hb : ExponentialBound (certB r) := by
    unfold certB
    simpa only [neg_div] using hbe.neg
  have hse := exponentialBound_quotient (hs.smooth.differentiable (by simp)) hK (odd_zero hso)
    (hr.smooth.differentiable (by simp)) hshape
  have hj : ExponentialBound (certJ r s) := hs.deriv_bounded.exponentialBound.sub (hse.mul hv)
  have hz : ExponentialBound (certZ r) := by
    simpa only [certZ,iteratedDeriv_succ,iteratedDeriv_zero] using hr.deriv.deriv.deriv.exponentialBound
  have hL : ExponentialBound (certL r s) := by
    unfold certL
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hrE.neg.mul hs.deriv_bounded.deriv.exponentialBound
  constructor
  · dsimp only [Certificate.F₂,Certificate.F₁]
    repeat' first | assumption | apply ExponentialBound.add | apply ExponentialBound.sub |
      apply ExponentialBound.mul | apply ExponentialBound.neg | apply ExponentialBound.pow | exact ExponentialBound.const _
  · dsimp only [Certificate.WF₂,Certificate.DF₂,Certificate.F₂R,Certificate.F₂K,Certificate.F₂v,
      Certificate.F₂b,Certificate.F₂j,Certificate.F₂,Certificate.F₁,Certificate.Q,Certificate.T]
    repeat' first | assumption | apply ExponentialBound.add | apply ExponentialBound.sub |
      apply ExponentialBound.mul | apply ExponentialBound.neg | apply ExponentialBound.pow | exact ExponentialBound.const _

end ZeroTemperatureSK.Heat

end
end

end OAI
