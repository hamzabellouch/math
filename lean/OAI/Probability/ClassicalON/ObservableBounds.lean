import OAI.Probability.ClassicalON.GradientComplex

namespace OAI

universe uE uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [NeZero n]

@[simp] theorem averageLinear_const (S : SpinSystem n V E) (c : ℝ) :
    S.averageLinear (ContinuousMap.const _ c) = c := S.average_const c

@[simp] theorem averageLinear_one (S : SpinSystem n V E) : S.averageLinear 1 = 1 :=
  S.average_const 1

@[simp] theorem normObservable_mul {Ω : Type uΩ} [TopologicalSpace Ω] (f g : C(Ω, ℂ)) :
    normObservable (f*g) = normObservable f * normObservable g := by
  ext x
  exact norm_mul (f x) (g x)

theorem norm_averageComplex_le_const (S : SpinSystem n V E)
    (f : C((V → Spin n), ℂ)) (c : ℝ) (h : ∀ σ, ‖f σ‖ ≤ c) :
    ‖S.averageComplexLinear f‖ ≤ c := by
  calc _ ≤ S.averageLinear (normObservable f) := S.norm_averageComplex_le f
       _ ≤ S.averageLinear (ContinuousMap.const _ c) := S.averageLinear_mono _ _ h
       _ = c := S.averageLinear_const c

theorem norm_averageComplex_mul_le (S : SpinSystem n V E)
    (f g : C((V → Spin n), ℂ)) :
    ‖S.averageComplexLinear (f*g)‖ ≤
      Real.sqrt (S.averageLinear (normObservable f * normObservable f)) *
      Real.sqrt (S.averageLinear (normObservable g * normObservable g)) := by
  calc _ ≤ S.averageLinear (normObservable (f*g)) := S.norm_averageComplex_le _
       _ = S.averageLinear (normObservable f * normObservable g) := by rw [normObservable_mul]
       _ ≤ _ := S.averageLinear_mul_le_sqrt _ _

theorem averageLinear_norm_le_sqrt (S : SpinSystem n V E)
    (f : C((V → Spin n), ℂ)) :
    S.averageLinear (normObservable f) ≤
      Real.sqrt (S.averageLinear (normObservable f * normObservable f)) := by
  simpa only [mul_one, one_mul, S.averageLinear_one, Real.sqrt_one] using
    S.averageLinear_mul_le_sqrt (normObservable f) 1

theorem norm_averageComplex_mul_mul_le (S : SpinSystem n V E)
    (a f g : C((V → Spin n), ℂ)) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ, ‖a σ‖ ≤ c) :
    ‖S.averageComplexLinear (a*f*g)‖ ≤ c *
      (Real.sqrt (S.averageLinear (normObservable f * normObservable f)) *
       Real.sqrt (S.averageLinear (normObservable g * normObservable g))) := by
  have hpt : ∀ σ, normObservable (a*f*g) σ ≤
      (c • (normObservable f * normObservable g)) σ := by
    intro σ
    change ‖a σ*f σ*g σ‖ ≤ c * (‖f σ‖*‖g σ‖)
    rw [norm_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (ha σ) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc _ ≤ S.averageLinear (normObservable (a*f*g)) := S.norm_averageComplex_le _
       _ ≤ S.averageLinear (c • (normObservable f * normObservable g)) :=
          S.averageLinear_mono _ _ hpt
       _ = c * S.averageLinear (normObservable f * normObservable g) := by
          rw [map_smul, smul_eq_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_left (S.averageLinear_mul_le_sqrt _ _) hc

theorem norm_averageComplex_mul_mul_le_of_moments (S : SpinSystem n V E)
    (a f g : C((V → Spin n), ℂ)) (c v : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ, ‖a σ‖ ≤ c)
    (hf : S.averageLinear (normObservable f * normObservable f) ≤ v)
    (hg : S.averageLinear (normObservable g * normObservable g) ≤ v) :
    ‖S.averageComplexLinear (a*f*g)‖ ≤ c*v := by
  have hv : 0 ≤ v := (S.averageLinear_mul_self_nonneg (normObservable f)).trans hf
  calc _ ≤ c * (Real.sqrt (S.averageLinear (normObservable f * normObservable f)) *
      Real.sqrt (S.averageLinear (normObservable g * normObservable g))) :=
      S.norm_averageComplex_mul_mul_le a f g c hc ha
       _ ≤ c * (Real.sqrt v * Real.sqrt v) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (Real.sqrt_le_sqrt hf) (Real.sqrt_le_sqrt hg)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc
       _ = c*v := by rw [Real.mul_self_sqrt hv]

theorem norm_averageComplex_mul_le_of_moment (S : SpinSystem n V E)
    (a f : C((V → Spin n), ℂ)) (c v : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ, ‖a σ‖ ≤ c)
    (hf : S.averageLinear (normObservable f * normObservable f) ≤ v) :
    ‖S.averageComplexLinear (a*f)‖ ≤ c*Real.sqrt v := by
  have h := S.norm_averageComplex_mul_mul_le a f 1 c hc ha
  simp only [mul_one] at h
  have h1 : normObservable (1 : C((V → Spin n), ℂ)) = 1 := by
    ext σ
    change ‖(1 : ℂ)‖ = (1 : ℝ)
    exact norm_one
  rw [h1, mul_one, S.averageLinear_one, Real.sqrt_one, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hf) hc)

end ClassicalON.SpinSystem

end

end OAI
