import Mathlib
import OAI.Geometry.PrescribedPotential.RealJetEnergy

namespace OAI

/-! Jet Energy Coercivity. -/

section

 
noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma family_inner_lower (f g : κ → F) :
    -Real.sqrt (∑ j, ‖f j‖^2)*Real.sqrt (∑ j, ‖g j‖^2) ≤ ∑ j, inner ℝ (f j) (g j) := by
  let a : PiLp 2 (fun _ : κ => F) := WithLp.toLp 2 f
  let b : PiLp 2 (fun _ : κ => F) := WithLp.toLp 2 g
  have ha : Real.sqrt (∑ j, ‖f j‖^2) = ‖a‖ := by
    have he : ‖a‖^2 = ∑ j, ‖f j‖^2 := by rw [PiLp.norm_sq_eq_of_L2]
    rw [← he,Real.sqrt_sq (norm_nonneg _)]
  have hb : Real.sqrt (∑ j, ‖g j‖^2) = ‖b‖ := by
    have he : ‖b‖^2 = ∑ j, ‖g j‖^2 := by rw [PiLp.norm_sq_eq_of_L2]
    rw [← he,Real.sqrt_sq (norm_nonneg _)]
  rw [ha,hb]
  simpa only [neg_mul,PiLp.inner_apply,a,b,PiLp.toLp_apply] using
    (neg_le_neg (abs_real_inner_le_norm a b)).trans (neg_abs_le (inner ℝ a b))

lemma familyEnergy_laplace_lower {U : Set E} (hU : IsOpen U) {f : κ → E → F}
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) U) {x : E} (hx : x ∈ U) (v : ι → E) :
    2*familyDissipation v f x - 2*Real.sqrt (familyEnergy f x)*
      Real.sqrt (∑ j, ‖frameLaplace v (f j) x‖^2) ≤ frameLaplace v (familyEnergy f) x := by
  rw [familyEnergy_laplace hU hf hx]
  have hb := family_inner_lower (fun j => f j x) (fun j => frameLaplace v (f j) x)
  change -Real.sqrt (familyEnergy f x)*_ ≤ _ at hb
  linarith only [hb]
end HigherJet

namespace BernsteinEstimate
lemma energy_first_numeric {r d B C L : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hC : 0 ≤ C) (hrC : r ≤ C) (hB : B ≤ C*(1+d))
    (hL : 2*d^2-2*r*B ≤ L) :
    d^2-(2*C^2+C^4) ≤ L := by
  have h1 := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2*r)
  have h2 := mul_le_mul_of_nonneg_right hrC (by positivity : 0 ≤ 2*C*(1+d))
  nlinarith only [hL,h1,h2,sq_nonneg (d-C^2)]

lemma energy_cubic_numeric {r d B C L : ℝ} (hr : 0 ≤ r) (_hd : 0 ≤ d)
    (hC : 0 ≤ C) (hB : B ≤ C*(1+r^2+d))
    (hL : 2*d^2-2*r*B ≤ L) :
    d^2-(4*C+2*C^2)*(1+r^3) ≤ L := by
  have hrb : r ≤ 1+r^3 := by
    by_cases h : r ≤ 1
    · nlinarith [pow_nonneg hr 3]
    · have h' : 1 ≤ r := le_of_not_ge h
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h' 2
      nlinarith [mul_nonneg hr (by linarith : 0 ≤ r^2-1)]
  have hr2b : r^2 ≤ 1+r^3 := by
    by_cases h : r ≤ 1
    · nlinarith [pow_nonneg hr 3]
    · nlinarith [mul_nonneg (sq_nonneg r) (by linarith : 0 ≤ r-1)]
  have h1 := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2*r)
  have h2 := mul_le_mul_of_nonneg_left hrb (by positivity : 0 ≤ 2*C)
  have h3 := mul_le_mul_of_nonneg_left hr2b (sq_nonneg C)
  have h4 : 0 ≤ 2*C+C^2*(1+r^3) := by positivity
  nlinarith only [hL,h1,h2,h3,h4,sq_nonneg (d-C*r)]

lemma energy_linear_numeric {r d B C L : ℝ} (hr : 0 ≤ r) (_hd : 0 ≤ d)
    (hC : 0 ≤ C) (hB : B ≤ C*(1+r+d))
    (hL : 2*d^2-2*r*B ≤ L) :
    d^2-(4*C+C^2)*(1+r^2) ≤ L := by
  have h1 := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2*r)
  have h2 := mul_le_mul_of_nonneg_left (sq_nonneg (r-1)) hC
  have h3 : 0 ≤ 3*C+C^2+C*r^2 := by positivity
  nlinarith only [hL,h1,h2,h3,sq_nonneg (d-C*r)]
end BernsteinEstimate

end
end

end OAI
