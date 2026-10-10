import Mathlib
import OAI.Probability.Perceptron.Cascade.ReweightedMomentLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Polynomial
namespace SphericalPerceptronFreeEnergy
lemma bounded_weighted_moment_comparison {Ω Ξ : ℕ→Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (μ : (n : ℕ)→Measure (Ω n)) (ν : (n : ℕ)→Measure (Ξ n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)] {a b : ℝ}
    (A : (n : ℕ)→Ω n→ℝ) (A' : (n : ℕ)→Ξ n→ℝ)
    (Z : (n : ℕ)→Ω n→Icc a b) (Z' : (n : ℕ)→Ξ n→Icc a b)
    (hA : ∀ n, Measurable (A n)) (hA' : ∀ n, Measurable (A' n))
    (hZ : ∀ n, Measurable (Z n)) (hZ' : ∀ n, Measurable (Z' n))
    (C : ℝ) (hC : 0≤C) (hb : ∀ n x, |A n x|≤C) (hb' : ∀ n x, |A' n x|≤C)
    (hm : ∀ k : ℕ, Tendsto (fun n => (∫ x, A n x*(Z n x).val^k ∂μ n)-
      ∫ x, A' n x*(Z' n x).val^k ∂ν n) atTop (𝓝 0)) (f : C(Icc a b,ℝ)) :
    Tendsto (fun n => (∫ x, A n x*f (Z n x) ∂μ n)-∫ x, A' n x*f (Z' n x) ∂ν n) atTop (𝓝 0) := by
  have hpi (n : ℕ) (p : ℝ[X]) : Integrable (fun x => A n x*p.eval (Z n x).val) (μ n) :=
    weighted_compact_integrable (μ n) (A n) (hA n) (Z n) (hZ n) C hC (hb n) (p.toContinuousMapOn _)
  have hpi' (n : ℕ) (p : ℝ[X]) : Integrable (fun x => A' n x*p.eval (Z' n x).val) (ν n) :=
    weighted_compact_integrable (ν n) (A' n) (hA' n) (Z' n) (hZ' n) C hC (hb' n) (p.toContinuousMapOn _)
  have hp (p : ℝ[X]) : Tendsto (fun n => (∫ x, A n x*p.eval (Z n x).val ∂μ n)-
      ∫ x, A' n x*p.eval (Z' n x).val ∂ν n) atTop (𝓝 0) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have he n : (∫ x, A n x*(p+q).eval (Z n x).val ∂μ n)-
          ∫ x, A' n x*(p+q).eval (Z' n x).val ∂ν n =
        ((∫ x, A n x*p.eval (Z n x).val ∂μ n)-∫ x, A' n x*p.eval (Z' n x).val ∂ν n)+
        ((∫ x, A n x*q.eval (Z n x).val ∂μ n)-∫ x, A' n x*q.eval (Z' n x).val ∂ν n) := by
        simp_rw [Polynomial.eval_add,mul_add]
        rw [integral_add (hpi n p) (hpi n q),integral_add (hpi' n p) (hpi' n q)]
        ring
      simp_rw [he]
      simpa only [add_zero] using hp.add hq
    | monomial k c =>
      simpa only [Polynomial.eval_monomial,mul_left_comm _ c,integral_const_mul,←mul_sub,mul_zero]
        using (hm k).const_mul c
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε/(3*(C+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨p,hpδ⟩ := exists_polynomial_near_continuousMap a b f δ hδ
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hp p) (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h₁ := weighted_compact_error (μ n) (A n) (hA n) (Z n) (hZ n) C hC (hb n) (p.toContinuousMapOn _) f
  have h₂ := weighted_compact_error (ν n) (A' n) (hA' n) (Z' n) (hZ' n) C hC (hb' n) (p.toContinuousMapOn _) f
  have hs : C*‖p.toContinuousMapOn (Icc a b)-f‖<ε/3 := by
    calc
      _ ≤ C*δ := mul_le_mul_of_nonneg_left hpδ.le hC
      _ < (C+1)*δ := mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε/3 := by dsimp [δ]; field_simp
  have ht := hN n hn
  simp only [Real.dist_eq,sub_zero] at ht ⊢
  simp only [Polynomial.toContinuousMapOn_apply,Polynomial.toContinuousMap_apply] at h₁ h₂
  have ha := abs_sub_le (∫ x, A n x*f (Z n x) ∂μ n)
    (∫ x, A n x*p.eval (Z n x).val ∂μ n) (∫ x, A' n x*f (Z' n x) ∂ν n)
  have hb₂ := abs_sub_le (∫ x, A n x*p.eval (Z n x).val ∂μ n)
    (∫ x, A' n x*p.eval (Z' n x).val ∂ν n) (∫ x, A' n x*f (Z' n x) ∂ν n)
  rw [abs_sub_comm] at h₁
  linarith
end SphericalPerceptronFreeEnergy
end

end OAI
