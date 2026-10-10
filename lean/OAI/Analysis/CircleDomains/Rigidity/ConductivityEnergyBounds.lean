import OAI.Analysis.CircleDomains.Rigidity.ConductivityGlobalEnergy

namespace OAI

/-! The two separate nonnegative terms in the conductivity identity:
small error from the vertical coordinate and vanishing energy on the
coefficient support. Local ordinary energy is then uniformly bounded. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace PlaneLocalWeakComplex

 theorem conductivity_energy_bounds {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) {F : Set EuclideanPlane}
    {n : ℕ} (hn : 2 ≤ n) {c d : ℝ} (hcd : c ≤ d)
    (heq : (∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) +
      ((n : ℝ)-1) * (∫ x in F, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) =
        2 * Real.pi * c) :
    (∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) ≤ 2 * Real.pi * d ∧
    (∫ x in F, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) ≤
      2 * Real.pi * d / ((n : ℝ)-1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ)-1 := by linarith
  have hH : 0 ≤ ∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2 :=
    integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hE : 0 ≤ ∫ x in F, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2 :=
    integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hbudget : 2 * Real.pi * c ≤ 2 * Real.pi * d :=
    mul_le_mul_of_nonneg_left hcd (by positivity)
  constructor
  · nlinarith [mul_nonneg hp.le hE]
  · apply (le_div_iff₀ hp).mpr
    nlinarith

 theorem imag_local_energy_le_error {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) (R : ℝ)
    (hH : Integrable (fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2)) :
    (∫ x in Metric.ball 0 R, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) ≤
      2 * (∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) +
      2 * (volume (Metric.ball (0 : EuclideanPlane) R)).toReal := by
  let μ := volume.restrict (Metric.ball (0 : EuclideanPlane) R)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hE : Integrable (fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) μ :=
    (D.imag_memLp R 0).integrable_sq.add (D.imag_memLp R 1).integrable_sq
  have hB : Integrable (fun x => 2 * ((D.imagGradient x 0)^2 +
      (D.imagGradient x 1-1)^2) + 2) μ := (hH.restrict.const_mul 2).add (integrable_const 2)
  have hle : (∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2 ∂μ) ≤
      ∫ x, 2 * ((D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) + 2 ∂μ := by
    apply integral_mono hE hB
    intro x
    nlinarith [sq_nonneg (D.imagGradient x 0), sq_nonneg (D.imagGradient x 1-2)]
  rw [integral_add (hH.restrict.const_mul 2) (integrable_const 2), integral_const_mul,
    integral_const] at hle
  have hmono : (∫ x in Metric.ball 0 R, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) ≤
      ∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2 :=
    setIntegral_le_integral hH (Eventually.of_forall (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
  simp only [μ, Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at hle
  nlinarith [hle, hmono]

end PlaneLocalWeakComplex
end CircleDomainRigidity

end

end OAI
