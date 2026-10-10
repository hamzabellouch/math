import OAI.Probability.ClassicalON.FamilyBound

namespace OAI

universe uE uI uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

omit [Fintype I] in
theorem norm_avg_coeff_two (S : SpinSystem 3 V E) (β v : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) (e : E)
    (F G : C((V → Spin 3), ℂ))
    (hF : S.averageLinear (normObservable F * normObservable F) ≤ v)
    (hG : S.averageLinear (normObservable G * normObservable G) ≤ v) :
    ‖S.averageComplexLinear (S.coefficientObservable M e * F * G)‖ ≤ β*v :=
  S.norm_averageComplex_mul_mul_le_of_moments _ F G β v hβ
    (S.coefficientObservable_norm_le β hb M hM e) hF hG

omit [Fintype I] in
theorem norm_avg_coeff_coeff_const (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M N : SpinOperator 3) (hM : ‖M‖ ≤ 1) (hN : ‖N‖ ≤ 1) (e l : E) (z : ℂ) :
    ‖S.averageComplexLinear (S.coefficientObservable M e * S.coefficientObservable N l *
      ContinuousMap.const _ z)‖ ≤ β^2*‖z‖ := by
  apply S.norm_averageComplex_le_const
  intro σ
  simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  rw [pow_two]
  exact mul_le_mul (S.coefficientObservable_norm_le β hb M hM e σ)
    (S.coefficientObservable_norm_le β hb N hN l σ) (norm_nonneg _) hβ

omit [Fintype I] in
theorem norm_avg_coeff_const_current (S : SpinSystem 3 V E) (β q : ℝ)
    (hβ : 0 ≤ β) (hq : 0 ≤ q)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) (e : E) (z : ℂ)
    (hz : ‖z‖ ≤ Real.sqrt q) (F : C((V → Spin 3), ℂ))
    (hF : S.averageLinear (normObservable F * normObservable F) ≤ β*q) :
    ‖S.averageComplexLinear (S.coefficientObservable M e * ContinuousMap.const _ z * F)‖ ≤
      β*Real.sqrt β*q := by
  have hcoeff (σ : V → Spin 3) :
      ‖(S.coefficientObservable M e * ContinuousMap.const (V → Spin 3) z) σ‖ ≤ β*‖z‖ := by
    simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (S.coefficientObservable_norm_le β hb M hM e σ)
      (norm_nonneg z)
  calc _ ≤ (β*‖z‖)*Real.sqrt (β*q) :=
        S.norm_averageComplex_mul_le_of_moment _ F (β*‖z‖) (β*q)
          (mul_nonneg hβ (norm_nonneg z)) hcoeff hF
       _ ≤ (β*Real.sqrt q)*Real.sqrt (β*q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hβ) (Real.sqrt_nonneg _)
       _ = β*Real.sqrt β*q := by
          rw [Real.sqrt_mul hβ]
          calc _ = β*Real.sqrt β*(Real.sqrt q*Real.sqrt q) := by ring
               _ = _ := by rw [Real.mul_self_sqrt hq]

omit [Fintype I] in
theorem norm_avg_coeff_const (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) (e : E) (z : ℂ) :
    ‖S.averageComplexLinear (S.coefficientObservable M e * ContinuousMap.const _ z)‖ ≤ β*‖z‖ := by
  apply S.norm_averageComplex_le_const
  intro σ
  simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (S.coefficientObservable_norm_le β hb M hM e σ) (norm_nonneg z)

end ClassicalON.SpinSystem

end

end OAI
