import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPenaltyLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPressureConstraint

namespace OAI

/-! Bounded radial pressure multiplication and its exact quadratic form on L². -/

open MeasureTheory
namespace DefocusingNLS
local notation "H(" R ")" => Lp ℂ 2 (radialPressureMeasure R)

private theorem pressureProduct_memLp (R : ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q (radialPressureMeasure R))
    (hqb : ∀ᵐ r ∂radialPressureMeasure R, ‖q r‖ ≤ 1) (u : H(R)) :
    MemLp (fun r => q r • u r) 2 (radialPressureMeasure R) := by
  apply (Lp.memLp u).of_le_mul (hq.smul (Lp.aestronglyMeasurable u))
  filter_upwards [hqb] with r hr
  change ‖q r • u r‖ ≤ (1 : ℝ)*‖u r‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)

noncomputable def spectralPressureProduct (R : ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q (radialPressureMeasure R))
    (hqb : ∀ᵐ r ∂radialPressureMeasure R, ‖q r‖ ≤ 1) (u : H(R)) : H(R) :=
  (pressureProduct_memLp R q hq hqb u).toLp (fun r => q r • u r)

theorem spectralPressureProduct_ae (R : ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q (radialPressureMeasure R))
    (hqb : ∀ᵐ r ∂radialPressureMeasure R, ‖q r‖ ≤ 1) (u : H(R)) :
    spectralPressureProduct R q hq hqb u =ᵐ[radialPressureMeasure R] (fun r => q r • u r) :=
  MemLp.coeFn_toLp _

theorem spectralPressureProduct_norm (R : ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q (radialPressureMeasure R))
    (hqb : ∀ᵐ r ∂radialPressureMeasure R, ‖q r‖ ≤ 1) (u : H(R)) :
    ‖spectralPressureProduct R q hq hqb u‖ ≤ ‖u‖ := by
  calc
    _ ≤ 1*‖u‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [spectralPressureProduct_ae R q hq hqb u,hqb] with r he hr
      rw [he,norm_smul]
      exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    _ = _ := one_mul _

noncomputable def spectralPressureOperator (R : ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q (radialPressureMeasure R))
    (hqb : ∀ᵐ r ∂radialPressureMeasure R, ‖q r‖ ≤ 1) : H(R) →L[ℝ] H(R) :=
  let A := spectralPressureProduct R q hq hqb
  let L : H(R) →ₗ[ℝ] H(R) :=
    { toFun := A
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [spectralPressureProduct_ae R q hq hqb (u+v),
          spectralPressureProduct_ae R q hq hqb u,spectralPressureProduct_ae R q hq hqb v,
          Lp.coeFn_add u v,Lp.coeFn_add (A u) (A v)] with r hsum hu hv hin hout
        change A (u+v) r=(A u+A v : H(R)) r
        rw [hsum,hout,hin,Pi.add_apply,Pi.add_apply,hu,hv,smul_add]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [spectralPressureProduct_ae R q hq hqb (c • u),
          spectralPressureProduct_ae R q hq hqb u,Lp.coeFn_smul c u,
          Lp.coeFn_smul c (A u)] with r hcu hu hin hout
        change A (c • u) r=(c • A u : H(R)) r
        rw [hcu,hout,hin,Pi.smul_apply,Pi.smul_apply,hu]
        exact smul_comm (q r) c (u r) }
  L.mkContinuous 1 (fun u => by
    change ‖spectralPressureProduct R q hq hqb u‖ ≤ 1*‖u‖
    simpa only [one_mul] using spectralPressureProduct_norm R q hq hqb u)

theorem spectralPressureOperator_norm (R : ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q (radialPressureMeasure R))
    (hqb : ∀ᵐ r ∂radialPressureMeasure R, ‖q r‖ ≤ 1) :
    ‖spectralPressureOperator R q hq hqb‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖spectralPressureProduct R q hq hqb u‖ ≤ 1*‖u‖
  simpa only [one_mul] using spectralPressureProduct_norm R q hq hqb u

theorem spectralPressureOperator_quadratic (R : ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q (radialPressureMeasure R))
    (hqb : ∀ᵐ r ∂radialPressureMeasure R, ‖q r‖ ≤ 1) (u : H(R)) :
    inner ℝ (spectralPressureOperator R q hq hqb u) u=
      ∫ r, q r*‖u r‖^2 ∂radialPressureMeasure R := by
  change (∫ r, inner ℝ (spectralPressureProduct R q hq hqb u r) (u r)
    ∂radialPressureMeasure R)=_
  apply integral_congr_ae
  filter_upwards [spectralPressureProduct_ae R q hq hqb u] with r hr
  rw [hr,real_inner_smul_left,real_inner_self_eq_norm_sq]

end DefocusingNLS

end OAI
