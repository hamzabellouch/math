import OAI.NumberTheory.JointDickman.Amplification.FirstFormDiagonal
import OAI.NumberTheory.JointDickman.Amplification.ArithmeticProfilePreservation

namespace OAI

/-! # The linear diagonal majorant is the ordinary divisor-weight mean -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem firstFormMass_reindex {B : ℕ} (hB : 0 < B) (L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) (N : ℕ) :
    firstFormMass B L τ C u v φ N = (B : ℝ) *
      ((∑ n ∈ range N, φ n * arithmeticSubsetAmplification B L τ C (fun a c => u c * v a c) n) /
        (N : ℝ)) := by
  have he := arithmeticAmplification_reindex B L τ C (fun a c => u c * v a c)
    (fun n => (φ n : ℂ)) N
  have hf := amplification_first_form B L τ C u v (fun _ => 1) (fun n => (φ n : ℂ)) N
    (fun _ _ _ => rfl)
  simp only [star_one, one_mul] at hf
  have hz : (∑ n ∈ range N, (φ n : ℂ) *
      (arithmeticSubsetAmplification B L τ C (fun a c => u c * v a c) n : ℂ)) / (N : ℂ) =
      (1/(B : ℂ)) * firstDivisorForm B L τ C u v (fun _ => 1) (fun n => (φ n : ℂ)) N := by
    rw [he, mul_div_assoc, hf]
  have hr := congrArg Complex.re hz
  simp only [Complex.div_natCast_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Complex.one_re, Complex.one_im, zero_div, Complex.div_natCast_im] at hr
  change _ = (1/(B : ℝ)) * firstFormMass B L τ C u v φ N at hr
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  have hh := congrArg (fun x : ℝ => (B : ℝ)*x) hr
  have hc : (B : ℝ)*(1/(B : ℝ)*firstFormMass B L τ C u v φ N) =
      firstFormMass B L τ C u v φ N := by field_simp
  rw [hc] at hh
  exact hh.symm

theorem arithmeticMoment_first_sq_le_second (B L : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ) :
    (arithmeticAmplificationMoment B L τ C w 1)^2 ≤ arithmeticAmplificationMoment B L τ C w 2 := by
  have h := residueMean_mul_norm_sq
    (fun a => (residueAmplification B L τ C w a : ℂ)) (fun _ => 1)
  have hc : residueEnergy (fun _ : ZMod (auxiliarySquarePeriod B) => (1 : ℂ)) = 1 := by
    simp [residueEnergy, NeZero.ne (auxiliarySquarePeriod B)]
  have he : residueEnergy (fun a => (residueAmplification B L τ C w a : ℂ)) =
      arithmeticAmplificationMoment B L τ C w 2 := by
    unfold residueEnergy residueAmplification arithmeticAmplificationMoment
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [mul_one, hc, he, residueAmplification_mean, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] using h

theorem smooth_arithmetic_first_upper
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (L : ℕ) (τ C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B T) 1 ≤ K := by
  obtain ⟨K,hK,hb⟩ := smooth_arithmetic_second_bound hFord hM L τ C
  refine ⟨K+1,by linarith,?_⟩
  filter_upwards [hb] with B hB
  intro T hT hTs
  have hsq := arithmeticMoment_first_sq_le_second B L τ C (amplificationSmoothWeight B T)
  have h := hB T hT hTs
  nlinarith [sq_nonneg K]

end JointDickman

end OAI
