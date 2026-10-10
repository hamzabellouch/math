import OAI.Analysis.LipschitzHilbert.Trees.SourceCentralHolder

namespace OAI

/-! The central Hölder estimate needs the mass cap only almost
 everywhere. In the application the measure is restricted to the
 constructed common good set. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem central_weight_integral_ae (μ : Measure X) [IsFiniteMeasure μ]
    (n : X → ℝ) (A : X → EuclideanSpace ℂ κ) (alpha p beta M B : ℝ)
    (hn : ∀ x, 0 < n x) (hnM : ∀ᵐ x ∂μ, n x ≤ M)
    (hnmeas : Measurable n) (hA : Measurable A) (hp : 1 < p) (hM : 0 ≤ M)
    (hgamma : 0 ≤ 1-alpha/p+beta)
    (henergy : Integrable (fun x => ‖(n x^(alpha/p-1)) • A x‖^p) μ)
    (hmoment : (∫ x, ‖(n x^(alpha/p-1)) • A x‖^p ∂μ)^(1/p) ≤ B) :
    Integrable (fun x => n x^beta*‖A x‖) μ ∧
      (∫ x, n x^beta*‖A x‖ ∂μ) ≤
        B*(μ.real Set.univ)^(1-1/p)*M^(1-alpha/p+beta) := by
  let F := fun x => (n x^(alpha/p-1)) • A x
  have hFmeas : Measurable F := (hnmeas.pow_const _).smul hA
  have hp0 : 0 < p := by linarith
  have hpzero : ENNReal.ofReal p ≠ 0 := by
    simpa only [ne_eq,ENNReal.ofReal_eq_zero,not_le] using hp0
  have hFp : MemLp F (ENNReal.ofReal p) μ :=
    (integrable_norm_rpow_iff hFmeas.aestronglyMeasurable hpzero (by simp)).mp
      (by simpa only [ENNReal.toReal_ofReal hp0.le] using henergy)
  have hFi : Integrable F μ := hFp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hpoint : ∀ᵐ x ∂μ, n x^beta*‖A x‖ ≤ M^(1-alpha/p+beta)*‖F x‖ := by
    filter_upwards [hnM] with x hx
    rw [central_weight_factorization (hn x)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (hn x).le hx hgamma) (norm_nonneg _)
  have hleft : Integrable (fun x => n x^beta*‖A x‖) μ :=
    (hFi.norm.const_mul (M^(1-alpha/p+beta))).mono'
      ((hnmeas.pow_const _).mul hA.norm).aestronglyMeasurable
      (by
        filter_upwards [hpoint] with x hx
        rwa [Real.norm_eq_abs,abs_of_nonneg
          (mul_nonneg (Real.rpow_nonneg (hn x).le _) (norm_nonneg _))])
  have hpq : p.HolderConjugate (p/(p-1)) := Real.HolderConjugate.conjExponent hp
  have hq : 1/(p/(p-1)) = 1-1/p := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x => norm_nonneg (F x))
    (Filter.Eventually.of_forall fun _ : X => (zero_le_one : (0:ℝ) ≤ 1))
    hFp.norm (memLp_const (1:ℝ))
  simp only [mul_one,Real.one_rpow,integral_const,smul_eq_mul] at hh
  rw [hq] at hh
  have hnorm : (∫ x, ‖F x‖ ∂μ) ≤ B*(μ.real Set.univ)^(1-1/p) := by
    apply hh.trans
    exact mul_le_mul_of_nonneg_right hmoment (Real.rpow_nonneg (by positivity) _)
  refine ⟨hleft,?_⟩
  calc
    _ ≤ ∫ x, M^(1-alpha/p+beta)*‖F x‖ ∂μ :=
      integral_mono_ae hleft (hFi.norm.const_mul _) hpoint
    _ = M^(1-alpha/p+beta)*(∫ x, ‖F x‖ ∂μ) := integral_const_mul _ _
    _ ≤ M^(1-alpha/p+beta)*(B*(μ.real Set.univ)^(1-1/p)) :=
      mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg hM _)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
