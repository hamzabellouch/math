import Mathlib
import OAI.Probability.LogConcave.JetEstimates.NormalizedLaplace
import OAI.Probability.LogConcave.Sampling.PrimitiveField

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma integral_gibbs_add_const {d : ℕ} {H : Point d → ℝ} (hc : Continuous H)
    (hi : Integrable (fun z => Real.exp (-H z))) (c : ℝ) (f : Point d → ℝ) :
    (∫ z,f z ∂gibbs (fun z => H z+c))=∫ z,f z ∂gibbs H := by
  have he : (fun z => Real.exp (-(H z+c)))=fun z => Real.exp (-c)*Real.exp (-H z) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  have hi' : Integrable (fun z => Real.exp (-(H z+c))) := by rw [he]; exact hi.const_mul _
  rw [integral_gibbs (hc.add_const c) hi', integral_gibbs hc hi]
  simp_rw [congrFun he,mul_assoc]
  rw [integral_const_mul,integral_const_mul,mul_div_mul_left _ _ (Real.exp_pos _).ne']

lemma HasGaussianLowerTail.integrable_exp {d : ℕ} {H : Point d → ℝ}
    (ht : HasGaussianLowerTail H) (hc : Continuous H) :
    Integrable (fun z => Real.exp (-H z)) := by
  simpa only [inner_zero_left,zero_sub,smul_eq_mul,mul_one] using
    integrable_tilted H hc continuous_const ht (growth_const (1:ℝ)) 0

lemma HasGaussianLowerTail.comp_inverse_affine {d : ℕ} {H : Point d → ℝ}
    (ht : HasGaussianLowerTail H) (v : Point d) {s : ℝ} (hs : 0<s) :
    HasGaussianLowerTail (fun z => H (s⁻¹ • (z-v))) := by
  obtain ⟨m,hm,C,hb⟩ := ht
  refine ⟨m/(2*s^2),by positivity,C+(m/s^2)*‖v‖^2,fun z => ?_⟩
  have hh := hb (s⁻¹ • (z-v))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),mul_pow,inv_pow] at hh
  have hn := norm_add_le (z-v) v
  rw [sub_add_cancel] at hn
  have hk := pow_le_pow_left₀ (norm_nonneg z) hn 2
  have hsq : ‖z‖^2 ≤ 2*‖z-v‖^2+2*‖v‖^2 := by
    nlinarith [sq_nonneg (‖z-v‖-‖v‖)]
  have hd : m/(2*s^2)*2=m/s^2 := by field_simp
  have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ m / (2*s^2))
  simp only [mul_add,← mul_assoc,hd] at hmul
  have he : m*(s^2)⁻¹=m/s^2 := by ring
  rw [← mul_assoc,he] at hh
  linarith

lemma normalizedLaplace_gibbs {d : ℕ} {H : Point d → ℝ} (hc : Continuous H)
    (hi : Integrable (fun z => Real.exp (-H z))) (θ : Point d)
    (hit : Integrable (fun z => Real.exp (inner ℝ θ z-H z))) (f : Point d → ℝ) :
    Appell.normalizedLaplace (gibbs H) f θ =
      ∫ z,f z ∂gibbs (fun z => H z-inner ℝ θ z) := by
  have he : ∀ z,Real.exp (-H z)*Real.exp (inner ℝ θ z)=Real.exp (inner ℝ θ z-H z) := by
    intro z
    rw [← Real.exp_add]
    congr 1
    ring
  have hit' : Integrable (fun z => Real.exp (-(H z-inner ℝ θ z))) := by
    simpa only [neg_sub] using hit
  rw [Appell.normalizedLaplace,Appell.laplace,Appell.laplace]
  have hct : Continuous (fun z => H z-inner ℝ θ z) := by fun_prop
  rw [integral_gibbs hc hi,integral_gibbs hc hi,integral_gibbs hct hit']
  simp only [smul_eq_mul,mul_one,← mul_assoc,he,neg_sub]
  have hA : (∫ z,Real.exp (-H z))≠0 := (integral_exp_pos hi).ne'
  have hB : (∫ z,Real.exp (inner ℝ θ z-H z))≠0 := (integral_exp_pos hit).ne'
  field_simp

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma conditionalPotential_continuous {d : ℕ} {F : Point d → ℝ} (hc : Continuous F)
    (x : Point d) (r ρ : ℝ) (y : Point d) : Continuous (conditionalPotential F x r ρ y) := by
  unfold conditionalPotential
  fun_prop

lemma conditional_hasGaussianLowerTail {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    HasGaussianLowerTail (conditionalPotential F x r ρ y) := by
  obtain ⟨ha,ha1⟩ := probability_time hρ0 hρ1
  have hs := conditional_smallness hl ha ha1
  have ht := (hF.hasGaussianLowerTail (x+r • (ρ • y))
    (mul_nonneg hr (Real.sqrt_nonneg _)) (by linarith :
      (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2<1)).comp_inverse_affine
      (ρ • y) (Real.sqrt_pos.mpr ha)
  simpa only [conditionalPotential_pullback F x r ρ y _ ha] using ht

lemma conditionalPotential_shift {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y h z : Point d) :
    conditionalPotential F x r ρ (y+h) z =
    conditionalPotential F x r ρ y z-inner ℝ ((ρ/(1-ρ^2)) • h) z+
      (ρ^2/(2*(1-ρ^2)))*(‖y+h‖^2-‖y‖^2) := by
  simp only [conditionalPotential,norm_sub_sq_real,inner_smul_right,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs,inner_add_right,inner_smul_left,starRingEnd_apply,star_trivial]
  rw [real_inner_comm h z]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def conditionalMeanScalar {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (f : Point d → ℝ) (y : Point d) : ℝ := ∫ z,f z ∂gibbs (conditionalPotential F x r ρ y)

theorem conditionalMeanScalar_shift {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (f : Point d → ℝ) (y h : Point d) :
    conditionalMeanScalar F x r ρ f (y+h)=
      Appell.normalizedLaplace (gibbs (conditionalPotential F x r ρ y)) f
        ((ρ/(1-ρ^2)) • h) := by
  let H := conditionalPotential F x r ρ y
  let θ := (ρ/(1-ρ^2)) • h
  have hH : Continuous H := conditionalPotential_continuous hF.smooth.continuous x r ρ y
  have ht : HasGaussianLowerTail H := conditional_hasGaussianLowerTail hF x hr hl hρ0 hρ1 y
  have hi := ht.integrable_exp hH
  have hit : Integrable (fun z => Real.exp (inner ℝ θ z-H z)) := by
    simpa only [smul_eq_mul,mul_one] using
      integrable_tilted H hH continuous_const ht (growth_const (1:ℝ)) θ
  rw [normalizedLaplace_gibbs hH hi θ hit]
  unfold conditionalMeanScalar
  have hp : conditionalPotential F x r ρ (y+h) = fun z =>
      (H z-inner ℝ θ z)+(ρ^2/(2*(1-ρ^2)))*(‖y+h‖^2-‖y‖^2) := by
    funext z
    exact conditionalPotential_shift F x r ρ y h z
  rw [hp]
  apply integral_gibbs_add_const (hH.sub (continuous_const.inner continuous_id))
  simpa only [Pi.sub_apply,id_eq,neg_sub] using hit

theorem conditionalMeanScalar_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {f : Point d → ℝ} (hf : Continuous f) (hg : Appell.HasGrowth f) :
    ContDiff ℝ (⊤ : ℕ∞) (conditionalMeanScalar F x r ρ f) := by
  let μ := gibbs (conditionalPotential F x r ρ 0)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 (0 : Point d)
  have hμ := conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 (0 : Point d)
  have he : conditionalMeanScalar F x r ρ f = fun y =>
      Appell.normalizedLaplace μ f ((ρ/(1-ρ^2)) • y) := by
    funext y
    simpa only [zero_add] using conditionalMeanScalar_shift hF x hr hl hρ0 hρ1 f 0 y
  rw [he]
  exact (Appell.smooth_normalizedLaplace hμ hf hg).comp (by fun_prop)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
