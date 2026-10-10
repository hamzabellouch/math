import OAI.Analysis.CircleDomains.Rigidity.ConductivityLocalEnergy
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! Passage from the exact finite-ball conductivity identity to its
whole-plane version. The two geometric inputs remain separately visible:
the Jacobian area defect tends to zero, and the vertical flux defect tends
to minus pi times the real Laurent coefficient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace PlaneLocalWeakComplex

 theorem imag_energy_integrableOn_compact {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) {F : Set EuclideanPlane} (hF : IsCompact F) :
    IntegrableOn (fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) F := by
  obtain ⟨R, hR⟩ := hF.isBounded.subset_ball 0
  have hh : IntegrableOn (fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2)
      (Metric.ball 0 R) := (D.imag_memLp R 0).integrable_sq.add (D.imag_memLp R 1).integrable_sq
  exact hh.mono_set hR

 theorem conductivity_global_energy {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) {F : Set EuclideanPlane} (hF : IsCompact F)
    (n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0)
    (harea : Tendsto (fun R : ℝ =>
      (∫ x in Metric.ball 0 R,
        D.realGradient x 0 * D.imagGradient x 1 - D.realGradient x 1 * D.imagGradient x 0) -
        (volume (Metric.ball (0 : EuclideanPlane) R)).toReal) atTop (𝓝 0))
    (hflux : Tendsto (fun R : ℝ =>
      (∫ x in Metric.ball 0 R, D.imagGradient x 1) -
        (volume (Metric.ball (0 : EuclideanPlane) R)).toReal) atTop (𝓝 (-Real.pi * c))) :
    Integrable (fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) ∧
    (∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) +
      ((n : ℝ)-1) * (∫ x in F, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) =
        2 * Real.pi * c := by
  classical
  let H : EuclideanPlane → ℝ := fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2
  let E : EuclideanPlane → ℝ := fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2
  let A : EuclideanPlane → ℝ := fun x => H x + ((n : ℝ)-1) * F.indicator E x
  have hEF : IntegrableOn E F := D.imag_energy_integrableOn_compact hF
  have hI : Integrable (F.indicator E) := (integrable_indicator_iff hF.measurableSet).mpr hEF
  have hH (R : ℝ) : IntegrableOn H (Metric.ball 0 R) := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanPlane) R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact (D.imag_memLp R 0).integrable_sq.add
      ((D.imag_memLp R 1).sub (memLp_const 1)).integrable_sq
  have hA (R : ℝ) : IntegrableOn A (Metric.ball 0 R) :=
    (hH R).add ((hI.restrict).const_mul _)
  have hAn : ∀ x, 0 ≤ A x := by
    intro x
    have hi : 0 ≤ F.indicator E x := indicator_nonneg (fun y _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) x
    have hc : 0 ≤ (n : ℝ)-1 := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg hc hi)
  have heq (R : ℝ) : (∫ x in Metric.ball 0 R, A x) =
      ((∫ x in Metric.ball 0 R,
        D.realGradient x 0 * D.imagGradient x 1 - D.realGradient x 1 * D.imagGradient x 0) -
        (volume (Metric.ball (0 : EuclideanPlane) R)).toReal) -
      2 * ((∫ x in Metric.ball 0 R, D.imagGradient x 1) -
        (volume (Metric.ball (0 : EuclideanPlane) R)).toReal) := by
    have hh := D.conductivity_local_energy_balance R hF.measurableSet n hsys
    change (∫ x in Metric.ball 0 R, H x) + ((n : ℝ)-1) * (∫ x in Metric.ball 0 R ∩ F, E x) = _ at hh
    change (∫ x in Metric.ball 0 R, H x + ((n : ℝ)-1) * F.indicator E x) = _
    rw [integral_add (hH R) ((hI.restrict).const_mul _), integral_const_mul,
      integral_indicator hF.measurableSet, Measure.restrict_restrict hF.measurableSet, inter_comm F]
    linarith [hh]
  have ht : Tendsto (fun R : ℝ => ∫ x in Metric.ball 0 R, A x) atTop
      (𝓝 (2 * Real.pi * c)) := by
    have hh := harea.sub (hflux.const_mul 2)
    simp only [zero_sub] at hh
    convert hh using 1
    · funext R
      exact heq R
    · congr 1
      ring
  have hcover : AECover volume atTop (fun R : ℝ => Metric.ball (0 : EuclideanPlane) R) :=
    aecover_ball tendsto_id
  have hAI : Integrable A := hcover.integrable_of_integral_tendsto_of_nonneg_ae
    (2 * Real.pi * c) hA (Eventually.of_forall hAn) ht
  have htotal : (∫ x, A x) = 2 * Real.pi * c := hcover.integral_eq_of_tendsto _ hAI ht
  have hHI : Integrable H := by
    have hh := hAI.sub (hI.const_mul ((n : ℝ)-1))
    convert hh using 1
    funext x
    change H x = (H x + ((n : ℝ)-1) * F.indicator E x) - ((n : ℝ)-1) * F.indicator E x
    ring
  refine ⟨hHI, ?_⟩
  change (∫ x, H x) + ((n : ℝ)-1) * (∫ x in F, E x) = _
  rw [show (∫ x in F, E x) = ∫ x, F.indicator E x from (integral_indicator hF.measurableSet).symm]
  rw [← integral_const_mul, ← integral_add hHI (hI.const_mul _)]
  exact htotal

end PlaneLocalWeakComplex
end CircleDomainRigidity

end

end OAI
