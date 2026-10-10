import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators Polynomial
namespace SphericalPerceptronFreeEnergy

lemma weighted_compact_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {a b : ℝ}
    (A : Ω → ℝ) (hA : Measurable A) (Z : Ω → Icc a b) (hZ : Measurable Z)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ x, |A x| ≤ C) (f : C(Icc a b,ℝ)) :
    Integrable (fun x => A x*f (Z x)) μ := by
  apply Integrable.of_bound (hA.mul (f.continuous.measurable.comp hZ)).aestronglyMeasurable (C*‖f‖)
  exact ae_of_all _ fun x => by
    change |A x*f (Z x)| ≤ C*‖f‖
    rw [abs_mul]
    exact mul_le_mul (hB x) (f.norm_coe_le_norm (Z x)) (abs_nonneg _) hC

lemma weighted_compact_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {a b : ℝ}
    (A : Ω → ℝ) (hA : Measurable A) (Z : Ω → Icc a b) (hZ : Measurable Z)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ x, |A x| ≤ C) (f g : C(Icc a b,ℝ)) :
    |(∫ x, A x*f (Z x) ∂μ)-(∫ x, A x*g (Z x) ∂μ)| ≤ C*‖f-g‖ := by
  rw [← integral_sub (weighted_compact_integrable μ A hA Z hZ C hC hB f)
    (weighted_compact_integrable μ A hA Z hZ C hC hB g)]
  have hb : ∀ x, ‖A x*f (Z x)-A x*g (Z x)‖ ≤ C*‖f-g‖ := fun x => by
    rw [←mul_sub,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hB x) ((f-g).norm_coe_le_norm (Z x)) (abs_nonneg _) hC
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ hb)

lemma bounded_weighted_moment_limit {Ω : ℕ → Type*} {Ω' : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    (μ : (n : ℕ) → Measure (Ω n)) (ν : Measure Ω')
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν] {a b : ℝ}
    (A : (n : ℕ) → Ω n → ℝ) (A' : Ω' → ℝ)
    (Z : (n : ℕ) → Ω n → Icc a b) (Z' : Ω' → Icc a b)
    (hA : ∀ n, Measurable (A n)) (hA' : Measurable A')
    (hZ : ∀ n, Measurable (Z n)) (hZ' : Measurable Z')
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ n x, |A n x| ≤ C) (hB' : ∀ x, |A' x| ≤ C)
    (hm : ∀ k : ℕ, Tendsto (fun n => ∫ x, A n x*(Z n x).val^k ∂μ n) atTop
      (𝓝 (∫ x, A' x*(Z' x).val^k ∂ν))) (f : C(Icc a b,ℝ)) :
    Tendsto (fun n => ∫ x, A n x*f (Z n x) ∂μ n) atTop
      (𝓝 (∫ x, A' x*f (Z' x) ∂ν)) := by
  have hpn (n : ℕ) (p : ℝ[X]) : Integrable (fun x => A n x*p.eval (Z n x).val) (μ n) :=
    weighted_compact_integrable (μ n) (A n) (hA n) (Z n) (hZ n) C hC (hB n) (p.toContinuousMapOn _)
  have hpl (p : ℝ[X]) : Integrable (fun x => A' x*p.eval (Z' x).val) ν :=
    weighted_compact_integrable ν A' hA' Z' hZ' C hC hB' (p.toContinuousMapOn _)
  have hp (p : ℝ[X]) : Tendsto (fun n => ∫ x, A n x*p.eval (Z n x).val ∂μ n) atTop
      (𝓝 (∫ x, A' x*p.eval (Z' x).val ∂ν)) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [Polynomial.eval_add,mul_add,integral_add (hpn _ p) (hpn _ q),
        integral_add (hpl p) (hpl q)] using hp.add hq
    | monomial k c =>
      simpa only [Polynomial.eval_monomial,mul_left_comm _ c,integral_const_mul]
        using (hm k).const_mul c
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε/(3*(C+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p,hpδ⟩ := exists_polynomial_near_continuousMap a b f δ hδ
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hp p) (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h₁ := weighted_compact_error (μ n) (A n) (hA n) (Z n) (hZ n) C hC (hB n)
    (p.toContinuousMapOn _) f
  have h₂ := weighted_compact_error ν A' hA' Z' hZ' C hC hB' (p.toContinuousMapOn _) f
  have hsmall : C*‖p.toContinuousMapOn (Icc a b)-f‖ < ε/3 := by
    calc
      _ ≤ C*δ := mul_le_mul_of_nonneg_left hpδ.le hC
      _ < ε/3 := by dsimp [δ]; rw [← mul_div_assoc]; apply (div_lt_iff₀ (by positivity)).mpr; nlinarith
  have h₃ := hN n hn
  rw [Real.dist_eq] at h₃ ⊢
  have ht := abs_sub_le (∫ x, A n x*f (Z n x) ∂μ n)
    (∫ x, A n x*p.eval (Z n x).val ∂μ n) (∫ x, A' x*f (Z' x) ∂ν)
  have ht' := abs_sub_le (∫ x, A n x*p.eval (Z n x).val ∂μ n)
    (∫ x, A' x*p.eval (Z' x).val ∂ν) (∫ x, A' x*f (Z' x) ∂ν)
  simp only [Polynomial.toContinuousMapOn_apply,Polynomial.toContinuousMap_apply] at h₁ h₂
  rw [abs_sub_comm] at h₁
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
