import OAI.Probability.PosteriorReplicas.Model

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma withDensity_apply_le_moment (f : X → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∫⁻ x, f x ^ p ∂μ ≤ C) (S : Set X) (hS : MeasurableSet S) :
    μ.withDensity f S ≤ C^(1/p) * (μ S)^(1 - 1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) hpq
    hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have he : 1 / (Real.conjExponent p) = 1 - 1/p := by
    have hh := hpq.inv_add_inv_eq_one
    simpa only [one_div] using (eq_sub_of_add_eq' hh)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul, he] at h
  rw [withDensity_apply _ hS]
  exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow
    ((lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans hC) (by positivity)) le_rfl)
end HolderSet

end PosteriorRegression
end

end OAI
