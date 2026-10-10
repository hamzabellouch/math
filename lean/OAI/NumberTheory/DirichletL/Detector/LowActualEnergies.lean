import OAI.NumberTheory.DirichletL.Detector.LowColumnBounds
import OAI.NumberTheory.DirichletL.Detector.LowCauchy

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

def lowNumeratorRows (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q) : Finset O :=
  (elementWindow_finite_support (lowOuterCutoff a b) (lowOuterCutoff_compact a b ha hb) Q hQ).toFinset

lemma lowNumeratorRows_mem (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q) (m : O) :
    m∈lowNumeratorRows a b ha hb Q hQ ↔ lowOuterCutoff a b (elementNorm m/Q)≠0 := by
  simp only [lowNumeratorRows,Set.Finite.mem_toFinset,Function.mem_support]

def lowGaussMajorant (a b : ℝ) (ha : 0<a) (hb : 0<b) : SchwartzMap ℝ ℂ :=
  (lowOuterCutoff_compact (a/2) (2*b) (by positivity) (by positivity)).toSchwartzMap
    (lowOuterCutoff_smooth (a/2) (2*b))

lemma lowGaussMajorant_nonneg (a b : ℝ) (ha : 0<a) (hb : 0<b) (x : ℝ) :
    0≤(lowGaussMajorant a b ha hb x).re := by
  change 0≤(lowOuterCutoff (a/2) (2*b) x).re
  simp only [lowOuterCutoff,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma lowGaussMajorant_on_rows (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (m : O) (hm : m∈lowNumeratorRows a b ha hb Q hQ) :
    lowGaussMajorant a b ha hb (‖ConcreteTraceCRT.eisEmbedding m‖^2/Q)=1 := by
  have hh := lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q hQ m).mp hm)
  change lowOuterCutoff (a/2) (2*b) (‖ConcreteTraceCRT.eisEmbedding m‖^2/Q)=1
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  exact lowOuterCutoff_one _ _ (by positivity) (by positivity) _ hh.1 hh.2

theorem lowRayAmplitude_actual_energy (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v Q : ℝ) (hQ : 0<Q) :
    (∑m∈lowNumeratorRows a b ha hb Q hQ,‖lowRayAmplitude C W1 Y σ m v‖^2)≤
      (gaussEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
        (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
        (lowGaussColumn C W1 Y σ v) (lowGaussMajorant a b ha hb) Q).re := by
  simp_rw [lowRayAmplitude_source_columns C W1 hW1 Y hY σ v]
  exact CenteredMomentReflectedChild.finite_reflected_energy_le_gaussEnergy _ _ _ _ _ Q hQ _
    (fun _=>lowGaussMajorant_nonneg a b ha hb _)
    (fun m hm=>by rw [lowGaussMajorant_on_rows a b ha hb Q hQ m hm];norm_num)

lemma lowSeparatedIntegrand_source_cauchy (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (B : RayRing→O→ℂ) (v : ℝ) :
    ‖lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v‖≤
      ‖mellin W0 ((v:ℂ)*Complex.I)‖*
        ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY),
          ‖lowRayAmplitude C W1 Y σ m v‖^2)*
          Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY),‖B σ m‖^2) := by
  let R := lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY)
  have hR (m : O) (hm : m∉R) : lowNumeratorWeight C (lowOuterCutoff a b) X Y m v=0 := by
    have hz : lowOuterCutoff a b (elementNorm m/lowPhysicalScale C X Y)=0 := by
      simpa only [R,lowNumeratorRows_mem,not_not] using hm
    simp [lowNumeratorWeight,hz]
  have he : lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v=
      mellin W0 ((v:ℂ)*Complex.I)*
        ∑σ : RayRing,∑m∈R,lowNumeratorWeight C (lowOuterCutoff a b) X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m := by
    unfold lowSeparatedIntegrand
    change mellin W0 ((v:ℂ)*Complex.I)*
      (∑'m : O,lowNumeratorWeight C (lowOuterCutoff a b) X Y m v*∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m)=_
    rw [tsum_eq_sum (s:=R) (fun m hm=>by rw [hR m hm,zero_mul])]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [he,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑σ : RayRing,‖∑m∈R,lowNumeratorWeight C (lowOuterCutoff a b) X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun σ _=>CenteredMomentCauchy.bounded_row_cauchy R
      (fun m=>lowNumeratorWeight C (lowOuterCutoff a b) X Y m v) (fun m=>lowRayAmplitude C W1 Y σ m v) (B σ)
      (fun m _=>lowNumeratorWeight_norm C _ (lowOuterCutoff_norm a b)
        (lowOuterCutoff_small a b ha 0 (by positivity)) X Y hX hY m v))

theorem lowSeparatedIntegrand_actual_energies (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) (v : ℝ) :
    ‖lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v‖≤
      ‖mellin W0 ((v:ℂ)*Complex.I)‖*
        ∑σ : RayRing,Real.sqrt ((gaussEnergy (lowGaussColumns W1 hW1 Y hY)
          (fun s=>primaryGenerator s.val) (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
          (lowGaussColumn C W1 Y σ v) (lowGaussMajorant a b ha hb) (lowPhysicalScale C X Y)).re)*
          Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY),‖B σ m‖^2) := by
  apply (lowSeparatedIntegrand_source_cauchy a b ha hb C W0 W1 X Y hX hY B v).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro σ hσ
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (lowRayAmplitude_actual_energy a b ha hb C W1 hW1 Y hY σ v
    (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY))) (Real.sqrt_nonneg _)

end SevenEighths.ProbePhysical
end

end OAI
