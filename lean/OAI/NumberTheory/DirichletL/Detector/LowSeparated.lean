import OAI.NumberTheory.DirichletL.Detector.LowMellinFubini
import OAI.NumberTheory.DirichletL.Detector.LowRayAmplitude

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowSeparatedIntegrand (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (B : RayRing→O→ℂ) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I)*
    ∑'m : O,Ω (elementNorm m/lowPhysicalScale C X Y)*C.residueMonoid m*
      ((elementNorm m/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
        ∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m

lemma lowSeparatedIntegrand_eq (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) (v : ℝ) :
    (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B (physicalIdealRay r.1) r.2)=
      lowSeparatedIntegrand C W0 W1 Ω X Y B v := by
  have hs := lowRowMellinIntegrand_mul_summable C W0 W1 Ω hW1 hΩ X Y hX hY v
    (fun r=>B (physicalIdealRay r.1) r.2)
  rw [hs.tsum_prod,←hs.tsum_comm]
  unfold lowSeparatedIntegrand
  rw [←tsum_mul_left]
  apply tsum_congr
  intro m
  rw [←lowRayAmplitude_group C W1 hW1 Y hY m v (fun σ=>B σ m)]
  repeat rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  unfold lowRowMellinIntegrand
  ring

lemma lowSeparatedIntegrand_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    Integrable (lowSeparatedIntegrand C W0 W1 Ω X Y B) := by
  have hh := lowRowMellinIntegrand_sum_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1 hΩ hΩ0 X Y hX hY
    (fun r=>B (physicalIdealRay r.1) r.2)
  simpa only [lowSeparatedIntegrand_eq C W0 W1 Ω hW1 hΩ X Y hX hY B] using hh

theorem physicalRowWeight_low_separated (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*B (physicalIdealRay r.1) r.2)=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y B v := by
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩ := lowOuterCutoff_compact (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  rw [physicalRowWeight_tsum_low_mellin C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY]
  simp_rw [lowSeparatedIntegrand_eq C W0 W1 _ hW1c hΩ X Y hX hY B]

theorem markedPhysicalProbe_low_separated (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y
          (fun σ m=>correctedCompletedT C.excluded D (physicalRayRowMonoid η C σ m) gaussianCompletedProfile Z) v := by
  have hW0c : HasCompactSupport W0 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  rw [markedPhysicalProbe_eq_gaussian_rows η C D W0 W1 hW0c hW1c X Y Z hX hY hZ]
  simp_rw [physicalRowMonoid_eq_ray]
  exact physicalRowWeight_low_separated C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY
    (fun σ m=>correctedCompletedT C.excluded D (physicalRayRowMonoid η C σ m) gaussianCompletedProfile Z)

end SevenEighths.ProbePhysical
end

end OAI
