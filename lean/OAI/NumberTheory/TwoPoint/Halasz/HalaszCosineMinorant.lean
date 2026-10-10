import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OAI

/-! A three-harmonic minorant for the prime-phase defect in corrected
MRT Lemma A.4(ii). Its mean is 81/256, enough to retain the needed 1/10
after restricting primes above exp((log X)^(27/40)). -/
namespace TwoPointCorrelations

open Finset

lemma halasz_sqrt_polynomial_minorant (a : ℝ) (ha : 0 ≤ a) :
    (1-a^2)/2+(1-a^2)^2/8+(1-a^2)^3/16 ≤ 1-a := by
  have h : 0 ≤ (a-1)^4*(a^2+4*a+5)/16 := by positivity
  nlinarith only [h]

lemma halasz_cosine_three_harmonics (x : ℝ) :
    (81/256:ℝ)-(175/512)*Real.cos (2*x)+(7/256)*Real.cos (4*x)-
      (1/512)*Real.cos (6*x) ≤ 1-|Real.cos x| := by
  have h := halasz_sqrt_polynomial_minorant |Real.cos x| (abs_nonneg _)
  have hsq : |Real.cos x|^2 = Real.cos x^2 := sq_abs _
  rw [hsq] at h
  have hfour : Real.cos (4*x) = 2*(2*Real.cos x^2-1)^2-1 := by
    rw [show 4*x=2*(2*x) by ring,Real.cos_two_mul,Real.cos_two_mul]
  have hsix : Real.cos (6*x) = 4*(2*Real.cos x^2-1)^3-3*(2*Real.cos x^2-1) := by
    rw [show 6*x=3*(2*x) by ring,Real.cos_three_mul,Real.cos_two_mul]
  rw [hfour,hsix,Real.cos_two_mul]
  convert h using 1; ring

/-- Three bounded prime-phase sums suffice; no Fourier approximation or
limit interchange is needed for this part of the repulsion argument. -/
theorem halasz_weighted_cosine_repulsion {ι : Type*} (P : Finset ι)
    (w θ : ι → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) (E : ℝ)
    (h₁ : |∑ p ∈ P, w p*Real.cos (θ p)| ≤ E)
    (h₂ : |∑ p ∈ P, w p*Real.cos (2*θ p)| ≤ E)
    (h₃ : |∑ p ∈ P, w p*Real.cos (3*θ p)| ≤ E) :
    (81/256:ℝ)*(∑ p ∈ P, w p)-(95/256)*E ≤
      ∑ p ∈ P, w p*(1-|Real.cos (θ p/2)|) := by
  have hpoint (p : ι) (hp : p ∈ P) :=
    mul_le_mul_of_nonneg_left (halasz_cosine_three_harmonics (θ p/2)) (hw p hp)
  have hsum := sum_le_sum hpoint
  have hphase (p : ι) :
      2*(θ p/2)=θ p ∧ 4*(θ p/2)=2*θ p ∧ 6*(θ p/2)=3*θ p := by
    constructor
    · ring
    constructor <;> ring
  simp only [(hphase _).1,(hphase _).2.1,(hphase _).2.2,
    mul_sub,mul_add,sum_sub_distrib,sum_add_distrib] at hsum
  have hm (c : ℝ) (f : ι → ℝ) :
      (∑ p ∈ P, w p*(c*f p)) = c*(∑ p ∈ P, w p*f p) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [hm,hm,hm,← sum_mul] at hsum
  have ha := (abs_le.mp h₁).2
  have hb := (abs_le.mp h₂).1
  have hc := (abs_le.mp h₃).2
  simp only [mul_sub,sum_sub_distrib]
  linarith only [hsum,ha,hb,hc]

end TwoPointCorrelations

end OAI
