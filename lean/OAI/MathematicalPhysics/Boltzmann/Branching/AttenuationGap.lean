import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicInitialEntropyLimit
import OAI.MathematicalPhysics.Boltzmann.Jets.JetEnvelopeTimeIntegral

namespace OAI

section

/-! # Stability of the nonnegative loss integrating factor -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.AttenuationLipschitz

private theorem exp_neg_difference_ordered {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-a) - Real.exp (-b) ≤ b - a := by
  have he : Real.exp (a - b) ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr hab)
  have hne : 0 ≤ 1 - Real.exp (a - b) := sub_nonneg.mpr he
  have heq : Real.exp (-b) = Real.exp (-a) * Real.exp (a - b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (-a) * (1 - Real.exp (a - b)) := by rw [heq]; ring
    _ ≤ 1 - Real.exp (a - b) :=
      mul_le_of_le_one_left hne (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha))
    _ ≤ b - a := by linarith [Real.add_one_le_exp (a - b)]

theorem exp_neg_difference {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hab))),
      abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    exact exp_neg_difference_ordered ha hab
  · rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hba))),
      abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    exact exp_neg_difference_ordered hb hba

theorem attenuation_difference {ν μ : ℝ → JetPrototype.Phase → ℝ} {a t : ℝ}
    (hat : a ≤ t) (p : JetPrototype.Phase)
    (hν : ∀ r ∈ Icc a t, 0 ≤ ν r (JetBarrier.flight r p))
    (hμ : ∀ r ∈ Icc a t, 0 ≤ μ r (JetBarrier.flight r p))
    (hνi : IntervalIntegrable (fun r => ν r (JetBarrier.flight r p)) volume a t)
    (hμi : IntervalIntegrable (fun r => μ r (JetBarrier.flight r p)) volume a t) :
    |JetPicardComparison.attenuation ν a t p - JetPicardComparison.attenuation μ a t p| ≤
      ∫ r in a..t, |ν r (JetBarrier.flight r p) - μ r (JetBarrier.flight r p)| := by
  have hn := intervalIntegral.integral_nonneg (μ := volume) hat hν
  have hm := intervalIntegral.integral_nonneg (μ := volume) hat hμ
  apply (exp_neg_difference hn hm).trans
  rw [← intervalIntegral.integral_sub hνi hμi]
  exact intervalIntegral.abs_integral_le_integral_abs hat

theorem attenuation_difference_le {ν μ : ℝ → JetPrototype.Phase → ℝ} {a t D : ℝ}
    (hat : a ≤ t) (p : JetPrototype.Phase)
    (hν : ∀ r ∈ Icc a t, 0 ≤ ν r (JetBarrier.flight r p))
    (hμ : ∀ r ∈ Icc a t, 0 ≤ μ r (JetBarrier.flight r p))
    (hνi : IntervalIntegrable (fun r => ν r (JetBarrier.flight r p)) volume a t)
    (hμi : IntervalIntegrable (fun r => μ r (JetBarrier.flight r p)) volume a t)
    (hD : ∀ r ∈ Icc a t, |ν r (JetBarrier.flight r p) - μ r (JetBarrier.flight r p)| ≤ D) :
    |JetPicardComparison.attenuation ν a t p - JetPicardComparison.attenuation μ a t p| ≤
      D * (t - a) := by
  apply (attenuation_difference hat p hν hμ hνi hμi).trans
  calc
    _ ≤ ∫ _r in a..t, D := intervalIntegral.integral_mono_on hat (hνi.sub hμi).abs
      intervalIntegrable_const hD
    _ = D * (t - a) := by rw [intervalIntegral.integral_const]; ring

end BoltzmannNonuniqueness.AttenuationLipschitz

end

end

section

/-! # Quantitative removal of the symmetric collision attenuation -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem one_sub_attenuation_le {N S : ℝ} (hN : 0 < N) (hS : 0 ≤ S) :
    1-attenuation N S ≤ 2*S/N := by
  have hd : 0 < N+S := add_pos_of_pos_of_nonneg hN hS
  have he : 1-attenuation N S = (2*N*S+S^2)/(N+S)^2 := by
    unfold attenuation
    field_simp [ne_of_gt hd]
    ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hN).mpr
  nlinarith [mul_nonneg hS (sq_nonneg S),mul_nonneg hN.le (sq_nonneg S)]

theorem abs_one_sub_attenuation_le {N S : ℝ} (hN : 0 < N) (hS : 0 ≤ S) :
    |1-attenuation N S| ≤ 2*S/N := by
  rw [abs_of_nonneg (sub_nonneg.mpr (attenuation_le_one hN hS))]
  exact one_sub_attenuation_le hN hS

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem rateMultiplier_gap_le {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    |1-rateMultiplier N f z| ≤ 2/N*
      (f (z.1.1,z.1.2.1)+f (z.1.1,z.1.2.2)+
        f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)+
        f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)) := by
  have h := abs_one_sub_attenuation_le hN
    (rateSum_nonneg (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
      (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
      (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)))
  unfold rateMultiplier
  convert h using 1
  unfold rateSum
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
