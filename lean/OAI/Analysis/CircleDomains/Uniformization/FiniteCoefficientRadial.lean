import OAI.Analysis.CircleDomains.Sobolev.InversePowerAnnulusIntegral

namespace OAI

/-! Exact integration of a finite Laurent coefficient energy sum. -/
open Set Filter Function Metric Real MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def finiteCoefficientRadialDensity (d : ℕ → ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  2*Real.pi*r*(1+∑ n ∈ Finset.range N,
    ((n : ℝ)+1)^2*d n*(r⁻¹)^(2*(n+2)))

lemma finiteCoefficientRadialDensity_nonneg {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n)
    (N : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ finiteCoefficientRadialDensity d N r := by
  unfold finiteCoefficientRadialDensity
  apply mul_nonneg (by positivity)
  apply add_nonneg zero_le_one
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (mul_nonneg (sq_nonneg _) (hd n)) (by positivity))

lemma finiteCoefficientRadialDensity_integrable {a b : ℝ} (ha : 0 < a)
    (d : ℕ → ℝ) (N : ℕ) : IntegrableOn (finiteCoefficientRadialDensity d N) (Ioo a b) := by
  have hi : ContinuousOn (fun r : ℝ => r⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun r hr => ne_of_gt (ha.trans_le hr.1))
  have hc : ContinuousOn (finiteCoefficientRadialDensity d N) (Icc a b) := by
    unfold finiteCoefficientRadialDensity
    exact (continuousOn_const.mul continuousOn_id).mul (continuousOn_const.add
      (continuousOn_finsetSum _ (fun n _ => continuousOn_const.mul (hi.pow _))))
  exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

lemma finiteCoefficientRadialDensity_integral {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (d : ℕ → ℝ) (N : ℕ) :
    (∫ r in Ioo a b, finiteCoefficientRadialDensity d N r) =
      Real.pi*(b^2-a^2)+Real.pi*∑ n ∈ Finset.range N, ((n : ℝ)+1)*d n*
        ((a⁻¹)^(2*(n+1))-(b⁻¹)^(2*(n+1))) := by
  have hi : ContinuousOn (fun r : ℝ => r⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun r hr => ne_of_gt (ha.trans_le hr.1))
  have ht (n : ℕ) : IntegrableOn
      (fun r : ℝ => (2*Real.pi*((n : ℝ)+1)^2*d n)*(r*(r⁻¹)^(2*(n+2)))) (Ioo a b) :=
    ((continuousOn_const.mul (continuousOn_id.mul (hi.pow _))).integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hl : IntegrableOn (fun r : ℝ => 2*Real.pi*r) (Ioo a b) :=
    ((continuous_const.mul continuous_id).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have he : finiteCoefficientRadialDensity d N = fun r => 2*Real.pi*r+
      ∑ n ∈ Finset.range N, (2*Real.pi*((n : ℝ)+1)^2*d n)*(r*(r⁻¹)^(2*(n+2))) := by
    funext r
    unfold finiteCoefficientRadialDensity
    rw [mul_add, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he, integral_add hl (integrable_finsetSum _ (fun n _ => ht n)),
    integral_finsetSum _ (fun n _ => ht n)]
  have hlin : (∫ r in Ioo a b, 2*Real.pi*r) = Real.pi*(b^2-a^2) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le,
      intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hlin, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_const_mul, integral_radial_inverse_power ha hab n]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

end CircleDomainRigidity

end

end OAI
