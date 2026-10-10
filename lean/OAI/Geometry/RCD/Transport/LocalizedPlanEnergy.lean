import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Local energy control along a bounded-compression plan

The squared endpoint difference only uses energy on the region containing
the paths. This localization is needed for the interior Poincare input.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem IsRelaxedSlope.testPlan_integrated_square_on
    (μ : Measure X) (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {Ω : Set X}
    (hstay : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ Ω)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) :
    (∫ γ : C(Time, X), (u (γ 1) - u (γ 0)) ^ 2 ∂π) ≤
      D ^ 2 * (C.toReal * ∫ x in Ω, G x ^ 2 ∂μ) := by
  have hiu (s : Time) : MemLp (fun γ : C(Time, X) => u (γ s)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval s) hC (hcomp s) u
  have hleft := ((hiu 1).sub (hiu 0)).integrable_sq
  have hprod : Integrable (fun z : ℝ × C(Time, X) => G (geodesicExtension z.2 z.1) ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod π) :=
    (testPlanMeasure_eval_memLp μ π hC hcomp G).integrable_sq
  have hb (r : ℝ) : (∫ γ : C(Time, X), G (geodesicExtension γ r) ^ 2 ∂π) ≤
      C.toReal * ∫ x in Ω, G x ^ 2 ∂μ := by
    let s := Set.projIcc 0 1 zero_le_one r
    have hm : AEMeasurable (fun γ : C(Time, X) => γ s) π :=
      (measurable_path_eval s).aemeasurable
    change (∫ γ : C(Time, X), G (γ s) ^ 2 ∂π) ≤ _
    have hsm : AEStronglyMeasurable (fun x => G x ^ 2) (π.map (fun γ => γ s)) :=
      ((Lp.stronglyMeasurable G).pow 2).aestronglyMeasurable
    rw [← integral_map hm hsm]
    have hc := (compression_iff_localized μ _ (hstay s) C).mp (hcomp s)
    have hh := integral_mono_measure hc (ae_of_all _ fun x => sq_nonneg (G x))
      ((Lp.memLp G).integrable_sq.integrableOn.smul_measure hC)
    simpa only [integral_smul_measure, smul_eq_mul] using hh
  have hbound : (∫ γ : C(Time, X), (∫ r in Icc (0 : ℝ) 1,
      G (geodesicExtension γ r) ^ 2) ∂π) ≤ C.toReal * ∫ x in Ω, G x ^ 2 ∂μ := by
    rw [← integral_prod_symm _ hprod, integral_prod _ hprod]
    calc
      _ ≤ ∫ _r in Icc (0 : ℝ) 1, C.toReal * ∫ x in Ω, G x ^ 2 ∂μ :=
        integral_mono hprod.integral_prod_left (integrable_const _) hb
      _ = _ := by simp
  have hae : ∀ᵐ γ ∂π, (u (γ 1) - u (γ 0)) ^ 2 ≤
      D ^ 2 * ∫ r in Icc (0 : ℝ) 1, G (geodesicExtension γ r) ^ 2 := by
    filter_upwards [hG.testPlan_ae_subinterval μ π hgeo hC hcomp hD 0 1 zero_le_one,
      hprod.prod_left_ae, hDb] with γ hγ hi hdb
    have hmt : MemLp (fun r => G (geodesicExtension γ r)) 2
        (volume.restrict (Icc (0 : ℝ) 1)) := by
      apply (memLp_two_iff_integrable_sq _).mpr hi
      exact ((Lp.stronglyMeasurable G).comp_measurable
        (γ.continuous.comp (LipschitzWith.projIcc zero_le_one).continuous).measurable).aestronglyMeasurable
    have hcs := integral_sq_le_mass_mul_sq _ hmt
    simp only [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one, ENNReal.toReal_one, one_mul] at hcs
    change |u (γ 1) - u (γ 0)| ≤ dist (γ 0) (γ 1) *
      (∫ r in (0 : ℝ)..1, G (geodesicExtension γ r)) at hγ
    have hsq := mul_self_le_mul_self (abs_nonneg _) hγ
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at hsq
    simp only [← sq, sq_abs, mul_pow] at hsq
    calc
      _ ≤ dist (γ 0) (γ 1) ^ 2 *
          (∫ r in Icc (0 : ℝ) 1, G (geodesicExtension γ r)) ^ 2 := hsq
      _ ≤ dist (γ 0) (γ 1) ^ 2 *
          (∫ r in Icc (0 : ℝ) 1, G (geodesicExtension γ r) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (sq_le_sq₀ dist_nonneg (dist_nonneg.trans hdb) |>.mpr hdb)
        (integral_nonneg fun _ => sq_nonneg _)
  calc
    _ ≤ ∫ γ : C(Time, X), D ^ 2 *
        (∫ r in Icc (0 : ℝ) 1, G (geodesicExtension γ r) ^ 2) ∂π :=
      integral_mono_ae hleft (hprod.integral_prod_right.const_mul _) hae
    _ = D ^ 2 * (∫ γ : C(Time, X),
        (∫ r in Icc (0 : ℝ) 1, G (geodesicExtension γ r) ^ 2) ∂π) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (sq_nonneg D)

end RegularPointCoordinates

end

end OAI
