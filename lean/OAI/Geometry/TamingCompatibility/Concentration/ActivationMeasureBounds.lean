import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ManifoldScalarCalculus
import OAI.Geometry.TamingCompatibility.Concentration.ActivationScales
import OAI.Geometry.TamingCompatibility.Charts.SummableCutoff

namespace OAI

section

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff
variable {X : Type*} [MeasurableSpace X]

lemma activation_boundary_integral (μ : Measure X) [IsProbabilityMeasure μ]
    (f e g : X → ℝ) (ε δ C : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hf : ∀ x, 0 ≤ f x) (he : ∀ x, 0 ≤ e x) (hei : Integrable e μ)
    (heg : (∫ x, e x ∂μ) ≤ δ) (hg : Integrable g μ)
    (hbound : ∀ x, g x ≤ (ε/(δ+f x))*(C*(f x+e x))) :
    (∫ x, g x ∂μ) ≤ 2*C*ε := by
  calc
    _ ≤ ∫ x, C*(ε+(ε/δ)*e x) ∂μ := integral_mono hg
      (((integrable_const ε).add (hei.const_mul (ε/δ))).const_mul C) (fun x => by
        apply (hbound x).trans
        have hh := mul_le_mul_of_nonneg_left (weighted_nonneg_ratio_bound hε hδ (hf x) (he x)) hC
        nlinarith)
    _ = C*(ε+(ε/δ)*(∫ x, e x ∂μ)) := by
      rw [integral_const_mul,integral_add (integrable_const _) (hei.const_mul _),
        integral_const_mul,integral_const]
      simp
    _ ≤ C*(ε+(ε/δ)*δ) := mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left heg (show 0 ≤ ε/δ by positivity)) _) hC
    _ = _ := by field_simp; ring

lemma activation_error_integral (μ : Measure X)
    (f e g : X → ℝ) (ε δ C : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hf : ∀ x, 0 ≤ f x) (he : ∀ x, 0 ≤ e x) (hei : Integrable e μ)
    (heg : (∫ x, e x ∂μ) ≤ δ) (hg : Integrable g μ)
    (hbound : ∀ x, g x ≤ (ε/(δ+f x))*(C*e x)) :
    (∫ x, g x ∂μ) ≤ C*ε := by
  calc
    _ ≤ ∫ x, (ε/δ)*(C*e x) ∂μ := integral_mono hg
      ((hei.const_mul C).const_mul _) (fun x => (hbound x).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hε hδ (by linarith [hf x]))
          (mul_nonneg hC (he x))))
    _ = (ε/δ)*(C*(∫ x, e x ∂μ)) := by rw [integral_const_mul,integral_const_mul]
    _ ≤ (ε/δ)*(C*δ) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left heg hC) (by positivity)
    _ = _ := by field_simp

lemma exceptional_null_of_integrals (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n))
    (ν : Measure X) (hi : ∀ n, Integrable (c n) ν)
    (e : ℕ → ℝ) (hes : Summable e) (hb : ∀ n, (∫ x, c n x ∂ν) ≤ e n) :
    ν (exceptional c) = 0 := by
  apply exceptional_null c hc hm ν
  apply ne_top_of_le_ne_top (hes.tsum_ofReal_ne_top)
  apply ENNReal.tsum_le_tsum
  intro n
  rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (hc n))]
  exact ENNReal.ofReal_le_ofReal (hb n)
end TamingCompatibility.SummableCutoff

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]

lemma contMDiff_logActivation {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) {ε δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ x, 0 ≤ f x) :
    ContMDiff Model 𝓘(ℝ,ℝ) ∞ (fun x => SummableCutoff.logActivation ε δ (f x)) := by
  intro x
  have hx := hpos x
  apply contMDiffAt_const.mul
  exact (Real.contDiffAt_log.mpr (show 1+f x/δ ≠ 0 by positivity)).comp_contMDiffAt
    (f := fun y => 1+f y/δ) (contMDiffAt_const.add ((hf x).div_const δ))

lemma scalarDifferential_logActivation {f : X → ℝ}
    (hf : MDifferentiable Model 𝓘(ℝ,ℝ) f) {ε δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ x, 0 ≤ f x) :
    scalarDifferential (fun x => SummableCutoff.logActivation ε δ (f x)) =
      fun x => (ε/(δ+f x)) • scalarDifferential f x :=
  scalarDifferential_comp hf (g := SummableCutoff.logActivation ε δ)
    (g' := fun t => ε/(δ+t)) (fun x => SummableCutoff.hasDerivAt_logActivation hδ (hpos x))

lemma contMDiff_saturation {c : ℕ → X → ℝ}
    (hc : ∀ k, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (c k)) (n N : ℕ) :
    ContMDiff Model 𝓘(ℝ,ℝ) ∞ (SummableCutoff.saturation c n N) := by
  apply contMDiff_const.sub
  apply Real.contDiff_exp.comp_contMDiff
  exact (contMDiff_finsetSum (fun k _ => hc (k+n))).neg

lemma scalarDifferential_saturation {c : ℕ → X → ℝ}
    (hc : ∀ k, MDifferentiable Model 𝓘(ℝ,ℝ) (c k)) (n N : ℕ) :
    scalarDifferential (SummableCutoff.saturation c n N) =
      fun x => Real.exp (-(∑ k ∈ Finset.range N, c (k+n) x)) •
        (∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) x) := by
  let f : X → ℝ := ∑ k ∈ Finset.range N, c (k+n)
  have hf : MDifferentiable Model 𝓘(ℝ,ℝ) f := MDifferentiable.sum (fun k _ => hc (k+n))
  have h := scalarDifferential_comp hf (g := fun t : ℝ => 1-Real.exp (-t))
    (g' := fun t => Real.exp (-t)) (fun x => by
      convert! ((Real.hasDerivAt_exp (-f x)).comp (f x) (hasDerivAt_neg (f x))).const_sub 1 using 1; ring)
  rw [scalarDifferential_sum _ _ (fun k _ => hc (k+n))] at h
  convert! h using 1
  · congr 1
    funext x
    simp only [SummableCutoff.saturation,f,Function.comp_def,Finset.sum_apply]
  · funext x
    simp only [f,Finset.sum_apply]
end TamingCompatibility.ManifoldForms

end
end

end OAI
