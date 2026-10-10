import OAI.NumberTheory.DirichletL.Detector.InitialMajorant
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def initialHighOnLines (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (σ υ ξ : ℝ) (i : FullHighIndex) (p : HeightSpace) : ℂ :=
  fullHighCoefficient S D η mask ((σ:ℂ)+p.1.1*Complex.I)
    ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) i

lemma initialHighOnLines_continuous (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (σ υ ξ : ℝ) (i : FullHighIndex) :
    Continuous (initialHighOnLines S D η mask σ υ ξ i) := by
  unfold initialHighOnLines
  have hc : Continuous (fun p : HeightSpace =>
      (((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),(ξ:ℂ)+p.1.2*Complex.I)) := by fun_prop
  have hh := (fullHighCoefficient_continuous S D η mask i).comp hc
  simpa only [Function.comp_def] using hh

lemma initialHighOnLines_norm_le (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1) (σ υ ξ : ℝ)
    (i : FullHighIndex) (p : HeightSpace) :
    ‖initialHighOnLines S D η mask σ υ ξ i p‖≤ initialHighMajorant σ υ ξ i := by
  exact fullHighCoefficient_norm_le S D η mask hm _ _ _ σ υ ξ (by simp) (by simp) (by simp) i

lemma initial_profile_integrable (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1) (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Integrable (onLines W0 W1 σ ξ υ) heightMeasure := by
  simpa only [one_mul] using profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ ξ υ hξ (fun _=>1) aestronglyMeasurable_const 1 0 (fun _=>by simp)

theorem initialHigh_integral_tsum (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    (∫p,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*
      onLines W0 W1 σ ξ υ p ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p,initialHighOnLines S D η mask σ υ ξ i p*
        onLines W0 W1 σ ξ υ p ∂heightMeasure := by
  have hξ0 : 0<ξ := by linarith
  have hp := initial_profile_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 σ ξ υ hξ0
  let F := fun i p=>initialHighOnLines S D η mask σ υ ξ i p*onLines W0 W1 σ ξ υ p
  have hb (i : FullHighIndex) (p : HeightSpace) :
      ‖F i p‖≤ initialHighMajorant σ υ ξ i*‖onLines W0 W1 σ ξ υ p‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (initialHighOnLines_norm_le S D η mask hm σ υ ξ i p) (norm_nonneg _)
  have hF (i : FullHighIndex) : Integrable (F i) heightMeasure := by
    apply (hp.norm.const_mul (initialHighMajorant σ υ ξ i)).mono'
    · exact ((initialHighOnLines_continuous S D η mask σ υ ξ i).mul
        (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ0)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb i)
  have hsum : Summable (fun i : FullHighIndex=>∫p,‖F i p‖ ∂heightMeasure) := by
    apply Summable.of_nonneg_of_le (fun i=>integral_nonneg (fun _=>norm_nonneg _))
      (fun i=>?_) ((initialHighMajorant_summable σ υ ξ hσ hυ hξ).mul_right
        (∫p,‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure))
    rw [←integral_const_mul]
    exact integral_mono (hF i).norm (hp.norm.const_mul _) (hb i)
  exact (integral_tsum_of_summable_integral_norm hF hsum).symm

theorem initialHigh_integral_tsum_test (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) :
    (∫p,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*T p ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p,initialHighOnLines S D η mask σ υ ξ i p*T p ∂heightMeasure := by
  let F := fun i p=>initialHighOnLines S D η mask σ υ ξ i p*T p
  have hb (i : FullHighIndex) (p : HeightSpace) :
      ‖F i p‖≤ initialHighMajorant σ υ ξ i*‖T p‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (initialHighOnLines_norm_le S D η mask hm σ υ ξ i p) (norm_nonneg _)
  have hF (i : FullHighIndex) : Integrable (F i) heightMeasure := by
    apply (hT.norm.const_mul (initialHighMajorant σ υ ξ i)).mono'
    · exact (initialHighOnLines_continuous S D η mask σ υ ξ i).aestronglyMeasurable.mul hT.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb i)
  have hsum : Summable (fun i : FullHighIndex=>∫p,‖F i p‖ ∂heightMeasure) := by
    apply Summable.of_nonneg_of_le (fun i=>integral_nonneg (fun _=>norm_nonneg _))
      (fun i=>?_) ((initialHighMajorant_summable σ υ ξ hσ hυ hξ).mul_right
        (∫p,‖T p‖ ∂heightMeasure))
    rw [←integral_const_mul]
    exact integral_mono (hF i).norm (hT.norm.const_mul _) (hb i)
  exact (integral_tsum_of_summable_integral_norm hF hsum).symm

end SevenEighths.ProbePhysical
end

end OAI
