import OAI.NumberTheory.DirichletL.Detector.GramBound
import OAI.NumberTheory.DirichletL.Detector.LowSlotPolynomial

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem lowSeparatedIntegrand_actual_gram (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M : ℝ) (ha : 0<a) (hab : a<b) (hM : 0≤M)
    (W1 : ℝ→ℂ) (hW1c : HasCompactSupport W1) (hW1 : Function.support W1⊆Set.Icc a b)
    (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (hb₀ : 0<b₀) :
    ∃J : ℕ,∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→
      ∃K : ℝ,0<K ∧ ∀(W0 : ℝ→ℂ)(X Y : ℝ)(hX : 0<X)(hY : 1≤Y)
        (B : RayRing→O→ℂ)(v : ℝ),1≤Y^2/lowPhysicalScale (calibrationForSet S hS) X Y→
      ‖lowSeparatedIntegrand (calibrationForSet S hS) W0 W1 (lowOuterCutoff a₀ b₀) X Y B v‖≤
        ‖mellin W0 ((v:ℂ)*Complex.I)‖*
        Real.sqrt (K*(1+|v|)^J*(lowPhysicalScale (calibrationForSet S hS) X Y/Y)*
          (1+(Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^(1/6:ℝ)+
            (Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^2/Y)*Y^δ)*
        ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀
          (lowPhysicalScale (calibrationForSet S hS) X Y)
          (lowPhysicalScale_pos _ X Y hX (lt_of_lt_of_le zero_lt_one hY)),‖B σ m‖^2) := by
  obtain ⟨J,hgram⟩ := ProbeGramCommon.actual_additive_gram_bound δ hδ hδ1 a b M ha hab hM
    W1 hW1c hW1 hW1s hWM
  refine ⟨J,?_⟩
  intro S hS hbad
  obtain ⟨K,hK,hgram⟩ := hgram S hS hbad (lowGaussMajorant a₀ b₀ ha₀ hb₀)
  refine ⟨K,hK,?_⟩
  intro W0 X Y hX hY B v hP
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let Q := lowPhysicalScale (calibrationForSet S hS) X Y
  have hQ : 0<Q := lowPhysicalScale_pos _ X Y hX hy
  let A := K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ
  have hbound (σ : RayRing) :
      (gaussEnergy (lowGaussColumns W1 hW1c Y hy) (fun I=>primaryGenerator I.val)
        (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W1 Y σ v) (lowGaussMajorant a₀ b₀ ha₀ hb₀) Q).re≤A :=
    (Complex.re_le_norm _).trans (hgram σ v Y Q hY hQ hP)
  apply (lowSeparatedIntegrand_actual_energies a₀ b₀ ha₀ hb₀ (calibrationForSet S hS)
    W0 W1 hW1c X Y hX hy B v).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _≤∑σ : RayRing,Real.sqrt A*Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀ Q hQ,‖B σ m‖^2) :=
      Finset.sum_le_sum (fun σ _=>mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hbound σ)) (Real.sqrt_nonneg _))
    _=_ := (Finset.mul_sum ..).symm

end SevenEighths.ProbePhysical
end

end OAI
