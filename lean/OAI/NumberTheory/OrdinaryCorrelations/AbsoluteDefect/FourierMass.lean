import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormPhase

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryAnalyticCutoff
open OrdinaryLocalAdditive Finset MeasureTheory
open scoped FourierTransform

noncomputable def fourierMass (phi : SchwartzMap ℝ ℂ) : ℝ := ∫t:ℝ, ‖(𝓕 phi : SchwartzMap ℝ ℂ) t‖
lemma fourierMass_nonneg (phi : SchwartzMap ℝ ℂ) : 0≤fourierMass phi :=
  integral_nonneg (fun _=>norm_nonneg _)

lemma inversion (phi : SchwartzMap ℝ ℂ) (x : ℝ) :
    phi x = ∫t:ℝ, ((𝓕 phi : SchwartzMap ℝ ℂ) t)*phase (t*x) := by
  have hi := congrArg (fun f : SchwartzMap ℝ ℂ=>f x)
    (FourierTransform.fourierInv_fourier_eq (F:=SchwartzMap ℝ ℂ) phi)
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq'] at hi
  simpa only [Real.inner_apply,smul_eq_mul,
    phase,mul_comm] using hi.symm

lemma integrable_kernel (phi : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun t:ℝ=>((𝓕 phi : SchwartzMap ℝ ℂ) t)*phase (t*x)) := by
  apply ((𝓕 phi : SchwartzMap ℝ ℂ)).integrable.norm.mono'
  · apply Continuous.aestronglyMeasurable
    exact ((𝓕 phi : SchwartzMap ℝ ℂ)).continuous.mul (by unfold phase;fun_prop)
  · filter_upwards [] with t
    simp only [norm_mul,norm_phase,mul_one,le_refl]

lemma linear_cutoff_bound {ι : Type*} (I : Finset ι) (w : ι→ℂ) (a : ι→ℝ)
    (phi : SchwartzMap ℝ ℂ) (mu R : ℝ)
    (hR : ∀t:ℝ, ‖∑i∈I,w i*phase (t*a i)‖≤R) :
    ‖∑i∈I,w i*phi ((a i-mu)/Real.sqrt mu)‖≤fourierMass phi*R := by
  have hi (i:ι) : Integrable (fun t:ℝ=>w i*(((𝓕 phi : SchwartzMap ℝ ℂ) t)*phase (t*((a i-mu)/Real.sqrt mu)))) :=
    (integrable_kernel phi _).const_mul _
  have he : (∑i∈I,w i*phi ((a i-mu)/Real.sqrt mu)) =
      ∫t:ℝ,∑i∈I,w i*(((𝓕 phi : SchwartzMap ℝ ℂ) t)*phase (t*((a i-mu)/Real.sqrt mu))) := by
    rw [integral_finsetSum I (fun i _=>hi i)]
    apply sum_congr rfl
    intro i _
    rw [MeasureTheory.integral_const_mul,← inversion]
  have hf (t:ℝ) : (∑i∈I,w i*(((𝓕 phi : SchwartzMap ℝ ℂ) t)*phase (t*((a i-mu)/Real.sqrt mu)))) =
      (((𝓕 phi : SchwartzMap ℝ ℂ) t)*phase (-t*mu/Real.sqrt mu))*(∑i∈I,w i*phase ((t/Real.sqrt mu)*a i)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    have hx : t*((a i-mu)/Real.sqrt mu)=(-t*mu/Real.sqrt mu)+(t/Real.sqrt mu)*a i := by ring
    rw [hx,phase_add]
    ring
  rw [he]
  calc
    _ ≤ ∫t:ℝ,‖∑i∈I,w i*(((𝓕 phi : SchwartzMap ℝ ℂ) t)*phase (t*((a i-mu)/Real.sqrt mu)))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫t:ℝ,‖(𝓕 phi : SchwartzMap ℝ ℂ) t‖*R := by
      apply integral_mono (integrable_finsetSum I (fun i _=>hi i)).norm
        (((𝓕 phi : SchwartzMap ℝ ℂ)).integrable.norm.mul_const R)
      intro t
      dsimp only
      rw [hf,norm_mul,norm_mul,norm_phase,mul_one]
      exact mul_le_mul_of_nonneg_left (hR _) (norm_nonneg _)
    _ = _ := by rw [MeasureTheory.integral_mul_const];rfl

lemma bilinear_cutoff_bound {ι : Type*} (I : Finset ι) (w : ι→ℂ) (a b : ι→ℝ)
    (phi : SchwartzMap ℝ ℂ) (mu R : ℝ)
    (hR : ∀s t:ℝ, ‖∑i∈I,w i*phase (s*a i)*phase (t*b i)‖≤R) :
    ‖∑i∈I,w i*phi ((a i-mu)/Real.sqrt mu)*phi ((b i-mu)/Real.sqrt mu)‖
      ≤fourierMass phi^2*R := by
  have ht (s:ℝ) := linear_cutoff_bound I (fun i=>w i*phase (s*a i)) b phi mu R (hR s)
  have ho := linear_cutoff_bound I (fun i=>w i*phi ((b i-mu)/Real.sqrt mu)) a phi mu
    (fourierMass phi*R) (fun s=>by simpa only [mul_assoc,mul_left_comm,mul_comm] using ht s)
  convert ho using 1
  · congr 1
    apply sum_congr rfl
    intro i _
    ring
  · ring
end OrdinaryAnalyticCutoff

end

end OAI
