import OAI.NumberTheory.DirichletL.Detector.LowGramApplied

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_mellin_sqrt_weight_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (hWs : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃C : ℝ,0<C ∧ ∀v : ℝ,
      ‖mellin W ((v:ℂ)*Complex.I)‖*Real.sqrt ((1+|v|)^J)≤C/(1+v^2) := by
  obtain ⟨C,hC,hb⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W a b ha hW hWs 0 0 (J+2)
  refine ⟨C,hC,?_⟩
  intro v
  apply CubicReflectionKernel.weighted_two_to_cauchy (by positivity) v
  have hp : 1≤(1+|v|)^J := one_le_pow₀ (by linarith [abs_nonneg v])
  have hs : Real.sqrt ((1+|v|)^J)≤(1+|v|)^J := Real.sqrt_le_self_iff.mpr (Or.inr hp)
  have hb' := hb 0 (by simp) v
  simp only [Complex.ofReal_zero,zero_add] at hb'
  calc
    _≤(1+|v|)^2*(‖mellin W ((v:ℂ)*Complex.I)‖*(1+|v|)^J) := by gcongr
    _=(1+|v|)^(J+2)*‖mellin W ((v:ℂ)*Complex.I)‖ := by rw [pow_add];ring
    _≤C := hb'

theorem lowSeparatedIntegral_actual_gram (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M : ℝ) (ha : 0<a) (hab : a<b) (hM : 0≤M)
    (W1 : ℝ→ℂ) (hW1c : HasCompactSupport W1) (hW1 : Function.support W1⊆Set.Icc a b)
    (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (hb₀ : 0<b₀)
    (W0 : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW0s : ContDiff ℝ ∞ W0) :
    ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→
      ∃C : ℝ,0<C ∧ ∀(X Y : ℝ)(hX : 0<X)(hY : 1≤Y)(B : RayRing→O→ℂ),
        1≤Y^2/lowPhysicalScale (calibrationForSet S hS) X Y→
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff a₀ b₀) X Y B v‖≤
        C*Real.sqrt ((lowPhysicalScale (calibrationForSet S hS) X Y/Y)*
          (1+(Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^(1/6:ℝ)+
            (Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^2/Y)*Y^δ)*
        ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀
          (lowPhysicalScale (calibrationForSet S hS) X Y)
          (lowPhysicalScale_pos _ X Y hX (lt_of_lt_of_le zero_lt_one hY)),‖B σ m‖^2) := by
  obtain ⟨J,hgram⟩ := lowSeparatedIntegrand_actual_gram δ hδ hδ1 a b M ha hab hM W1 hW1c hW1 hW1s hWM a₀ b₀ ha₀ hb₀
  obtain ⟨CM,hCM,hm⟩ := low_mellin_sqrt_weight_bound W0 a0 b0 ha0 hW0 hW0s J
  intro S hS hbad
  obtain ⟨K,hK,hgram⟩ := hgram S hS hbad
  refine ⟨CM*Real.sqrt K*Real.pi,by positivity,?_⟩
  intro X Y hX hY B hP
  let Q := lowPhysicalScale (calibrationForSet S hS) X Y
  have hQ : 0<Q := lowPhysicalScale_pos _ X Y hX (lt_of_lt_of_le zero_lt_one hY)
  let A := (Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ
  have hA : 0≤A := by dsimp [A]; positivity
  let E := ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀ Q hQ,‖B σ m‖^2)
  have hE : 0≤E := Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _)
  have hh (v : ℝ) : ‖lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
      (lowOuterCutoff a₀ b₀) X Y B v‖≤(CM*Real.sqrt K*Real.sqrt A*E)*(1+v^2)⁻¹ := by
    have hg := hgram W0 X Y hX hY B v hP
    have he : K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ=
        (1+|v|)^J*(K*A) := by dsimp [A];ring
    rw [he,Real.sqrt_mul (by positivity),Real.sqrt_mul hK.le] at hg
    calc
      _≤(‖mellin W0 ((v:ℂ)*Complex.I)‖*Real.sqrt ((1+|v|)^J))*
          (Real.sqrt K*Real.sqrt A*E) := by convert hg using 1 ;ring
      _≤(CM/(1+v^2))*(Real.sqrt K*Real.sqrt A*E) :=
        mul_le_mul_of_nonneg_right (hm v) (by positivity)
      _=_ := by rw [div_eq_mul_inv];ring
  have hi := norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul
    (CM*Real.sqrt K*Real.sqrt A*E)) (Filter.Eventually.of_forall hh)
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hi
  convert hi using 1 ;ring

end SevenEighths.ProbePhysical
end

end OAI
