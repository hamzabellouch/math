import Mathlib
import OAI.Probability.SKValue.Gaussian.GaussianSquareVariance
import OAI.Probability.SKValue.Equations.ThirdOrderRemainderBound
import OAI.Probability.SKValue.Processes.Measurable

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace SKValue
structure BackwardTest (T:ℝ) (γ:ℝ → ℝ) (u V:ℝ → ℝ → ℝ) (K L:ℝ) : Prop where
  K_nonneg : 0≤K
  L_nonneg : 0≤L
  gamma_nonneg : ∀ t∈Icc (0:ℝ) T,0≤γ t
  gamma_mono : MonotoneOn γ (Icc (0:ℝ) T)
  drift_measurable : ∀ t∈Icc (0:ℝ) T,Measurable (u t)
  drift_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|u t x|≤1
  smooth : ∀ t∈Icc (0:ℝ) T,ContDiff ℝ 3 (V t)
  bound : ∀ t∈Icc (0:ℝ) T,∀ x,|V t x|≤K
  first_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|deriv (V t) x|≤K
  second_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|deriv (deriv (V t)) x|≤K
  third_bound : ∀ t∈Icc (0:ℝ) T,∀ x,|iteratedDeriv 3 (V t) x|≤K
  second_lipschitz : ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x y,
    |deriv (deriv (V s)) y-deriv (deriv (V t)) x|≤L*(|s-t|+|y-x|)
  product_lipschitz : ∀ t∈Icc (0:ℝ) T,∀ s∈Icc (0:ℝ) T,∀ x y,
    |u s y*deriv (V s) y-u t x*deriv (V t) x|≤L*(|s-t|+|y-x|)
  second_integrable : ∀ y,IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume 0 T
  product_integrable : ∀ y,IntervalIntegrable (fun s ↦ γ s*(u s y*deriv (V s) y)) volume 0 T
  pde : ∀ a∈Icc (0:ℝ) T,∀ b∈Icc (0:ℝ) T,∀ x,
    V b x-V a x=-(∫ s in a..b,(1/2:ℝ)*deriv (deriv (V s)) x+γ s*(u s x*deriv (V s) x))

lemma BackwardTest.product_bound {T K L:ℝ} {γ:ℝ → ℝ} {u V:ℝ → ℝ → ℝ}
    (h:BackwardTest T γ u V K L) {t:ℝ} (ht:t∈Icc (0:ℝ) T) (x:ℝ) :
    |u t x*deriv (V t) x|≤K := by
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul (h.drift_bound t ht x) (h.first_bound t ht x)
    (abs_nonneg _) (by norm_num : (0:ℝ)≤1)

lemma BackwardTest.euler_one_step {T K L t δ x z:ℝ} {γ:ℝ → ℝ} {u V:ℝ → ℝ → ℝ}
    (h:BackwardTest T γ u V K L) (ht:0≤t) (hδ:0≤δ) (hδ1:δ≤1) (htδ:t+δ≤T) :
    let d := Real.sqrt δ*z+δ*γ t*u t x
    |V (t+δ) (x+d)-V t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2:ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)|≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) z+
        δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*γ t*u t x
  have htT:t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have hT:0≤T := ht.trans htT
  have hsub:Icc t (t+δ)⊆Icc (0:ℝ) T := Icc_subset_Icc ht htδ
  have htm:t∈Icc (0:ℝ) T := ⟨ht,htT⟩
  have hem:t+δ∈Icc (0:ℝ) T := ⟨by linarith,htδ⟩
  have hTm:T∈Icc (0:ℝ) T := ⟨hT,le_rfl⟩
  have hbint (y:ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ) :=
    (h.second_integrable y).mono_set (by rw [uIcc_of_le (by linarith:t≤t+δ),uIcc_of_le hT];exact hsub)
  have hpint (y:ℝ) : IntervalIntegrable (fun s ↦ γ s*(u s y*deriv (V s) y)) volume t (t+δ) :=
    (h.product_integrable y).mono_set (by rw [uIcc_of_le (by linarith:t≤t+δ),uIcc_of_le hT];exact hsub)
  have hgen := gradient_generator_quadrature
    (b:=fun s y ↦ deriv (deriv (V s)) y) (p:=fun s y ↦ u s y*deriv (V s) y) (y:=x+d)
    hδ (h.gamma_nonneg T hTm) h.K_nonneg h.L_nonneg (h.gamma_mono.mono hsub)
    (h.gamma_nonneg t htm) (h.gamma_mono htm hTm htT)
    (fun s hs ↦ h.product_bound (hsub hs) _) (fun s hs ↦ h.second_lipschitz t htm s (hsub hs) x _)
    (fun s hs ↦ h.product_lipschitz t htm s (hsub hs) x _) (hbint _) (hpint _)
  have htime : |(V (t+δ) (x+d)-V t x+u t x)-(V t (x+d)-V t x+u t x)+
      δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*u t x*deriv (V t) x)|≤
        δ*(((1/2:ℝ)+γ T)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    have heq : (V (t+δ) (x+d)-V t x+u t x)-(V t (x+d)-V t x+u t x)+
        δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*u t x*deriv (V t) x)=
        (V (t+δ) (x+d)-V t (x+d))+
          δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*(u t x*deriv (V t) x)) := by ring
    rw [heq,h.pde t htm (t+δ) hem]
    rw [show -(∫ s in t..t+δ,(1/2:ℝ)*deriv (deriv (V s)) (x+d)+γ s*(u s (x+d)*deriv (V s) (x+d)))+
        δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*(u t x*deriv (V t) x))=
        -((∫ s in t..t+δ,(1/2:ℝ)*deriv (deriv (V s)) (x+d)+γ s*(u s (x+d)*deriv (V s) (x+d)))-
          δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*(u t x*deriv (V t) x))) by ring,abs_neg]
    simpa only [add_sub_cancel_left] using hgen
  have hspace : |(V t (x+d)-V t x+u t x)-u t x-deriv (V t) x*d-
      (1/2:ℝ)*deriv (deriv (V t)) x*d^2|≤K*|d|^3 := by
    simpa only [add_sub_cancel_right] using third_order_remainder_bound (h.smooth t htm) h.K_nonneg (h.third_bound t htm) x d
  have hh := euler_cubic_remainder hδ hδ1 (h.gamma_nonneg T hTm) h.K_nonneg
    (mul_nonneg (by linarith [h.gamma_nonneg T hTm] : 0≤1/2+γ T) h.L_nonneg)
    (by rw [abs_of_nonneg (h.gamma_nonneg t htm)];exact h.gamma_mono htm hTm htT)
    (h.drift_bound t htm x) (h.second_bound t htm x) hspace htime
  convert! hh using 1
  congr 1
  dsimp only [d,cubicEnvelope]
  ring
end SKValue

end

end OAI
