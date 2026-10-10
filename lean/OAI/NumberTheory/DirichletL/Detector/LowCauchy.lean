import OAI.NumberTheory.DirichletL.Detector.LowSeparated
import OAI.NumberTheory.DirichletL.Moments.Cauchy

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def lowNumeratorWeight (C : CalibrationData) (Ω : ℝ→ℂ) (X Y : ℝ) (m : O) (v : ℝ) : ℂ :=
  Ω (elementNorm m/lowPhysicalScale C X Y)*C.residueMonoid m*
    ((elementNorm m/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))

lemma lowOuterCutoff_norm (a b x : ℝ) : ‖lowOuterCutoff a b x‖≤1 := by
  rw [lowOuterCutoff,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _),abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

lemma lowNumeratorWeight_norm (C : CalibrationData) (Ω : ℝ→ℂ)
    (hΩ : ∀x,‖Ω x‖≤1) (hΩ0 : Ω 0=0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (m : O) (v : ℝ) :
    ‖lowNumeratorWeight C Ω X Y m v‖≤1 := by
  by_cases hm : m=0
  · simp [lowNumeratorWeight,hm,elementNorm,hΩ0]
  have hmpos : 0<elementNorm m := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
  have he : -((v:ℂ)*Complex.I)=((-v:ℝ):ℂ)*Complex.I := by simp
  rw [lowNumeratorWeight,norm_mul,norm_mul,he,
    low_mellin_phase_norm _ (-v) (div_pos hmpos (lowPhysicalScale_pos C X Y hX hY)),mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΩ _)).trans (C.residueMonoid_norm_le_one m)

lemma lowNumeratorWeight_common_support (C : CalibrationData) (Ω : ℝ→ℂ)
    (hΩ : HasCompactSupport Ω) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset O,∀m∉R,∀v : ℝ,lowNumeratorWeight C Ω X Y m v=0 := by
  have hh := elementWindow_finite_support Ω hΩ _ (lowPhysicalScale_pos C X Y hX hY)
  refine ⟨hh.toFinset,?_⟩
  intro m hm v
  have hz : Ω (elementNorm m/lowPhysicalScale C X Y)=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hm
  simp [lowNumeratorWeight,hz]

theorem lowSeparatedIntegrand_cauchy (C : CalibrationData) (Ω : ℝ→ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ∀x,‖Ω x‖≤1) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset O,∀W0 W1 : ℝ→ℂ,∀B : RayRing→O→ℂ,∀v : ℝ,
      ‖lowSeparatedIntegrand C W0 W1 Ω X Y B v‖≤
        ‖mellin W0 ((v:ℂ)*Complex.I)‖*
          ∑σ : RayRing,Real.sqrt (∑m∈R,‖lowRayAmplitude C W1 Y σ m v‖^2)*
            Real.sqrt (∑m∈R,‖B σ m‖^2) := by
  obtain ⟨R,hR⟩ := lowNumeratorWeight_common_support C Ω hΩc X Y hX hY
  refine ⟨R,?_⟩
  intro W0 W1 B v
  have he : lowSeparatedIntegrand C W0 W1 Ω X Y B v=
      mellin W0 ((v:ℂ)*Complex.I)*
        ∑σ : RayRing,∑m∈R,lowNumeratorWeight C Ω X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m := by
    unfold lowSeparatedIntegrand
    change mellin W0 ((v:ℂ)*Complex.I)*
      (∑'m : O,lowNumeratorWeight C Ω X Y m v*∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m)=_
    rw [tsum_eq_sum (s:=R) (fun m hm=>by rw [hR m hm v,zero_mul])]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [he,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑σ : RayRing,‖∑m∈R,lowNumeratorWeight C Ω X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun σ _=>CenteredMomentCauchy.bounded_row_cauchy R
      (fun m=>lowNumeratorWeight C Ω X Y m v) (fun m=>lowRayAmplitude C W1 Y σ m v) (B σ)
      (fun m _=>lowNumeratorWeight_norm C Ω hΩ hΩ0 X Y hX hY m v))

end SevenEighths.ProbePhysical
end

end OAI
