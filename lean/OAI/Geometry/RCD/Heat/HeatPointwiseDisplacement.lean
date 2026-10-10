import OAI.Geometry.RCD.Heat.HeatBoundedLaplacian
import OAI.Geometry.RCD.Sobolev.PointwiseIntegralBound

namespace OAI

/-! # Pointwise heat displacement from a bounded weak Laplacian -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heat_bounded_laplacian_pointwise
    (g : SobolevSpace (hausdorff n X) hX.quadratic)
    (dg : Lp ℝ 2 (hausdorff n X)) (hg : IsWeakLaplacian (hausdorff n X) hX.quadratic g dg)
    {B : ℝ} (hB : 0 ≤ B) (hdg : ∀ᵐ x ∂hausdorff n X, |dg x| ≤ B)
    (w : X → ℝ) (hw : Continuous w)
    (hrep : SobolevSpace.toLp (hausdorff n X) hX.quadratic g =ᵐ[hausdorff n X] w)
    (C : ℝ≥0) (hC : ∀ x, |w x| ≤ C) (t : ℝ) (ht : 0 < t) (x : X) :
    |(∫ y, w y ∂hX.heatRadonMeasure hn p t ht x) - w x| ≤ t*B := by
  let μ := hausdorff n X
  let gL := SobolevSpace.toLp μ hX.quadratic g
  have hgb : ∀ᵐ y ∂μ, |gL y| ≤ C := by
    filter_upwards [hrep] with y hy
    rw [hy]
    exact hC y
  let u := hX.boundedHeat hn p gL ⟨C, hgb⟩ t ht
  let v (y : X) := u y - w y
  have hu : Continuous u := hX.boundedHeat_continuous hn p gL ⟨C, hgb⟩ t ht
  have hub (y : X) : |u y| ≤ C := hX.boundedHeat_abs_le hn p gL ⟨C, hgb⟩ t ht C hgb y
  have hvi (S : Set X) (_hS : MeasurableSet S) (hf : μ S < ∞) : IntegrableOn v S μ := by
    apply (integrableOn_const (μ := μ) (s := S) (C := (2*(C : ℝ))) hf.ne).mono'
      (hu.sub hw).aestronglyMeasurable.restrict
    exact Eventually.of_forall fun y => by
      change ‖u y-w y‖ ≤ 2*(C : ℝ)
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by linarith [hub y, hC y])
  have hset (S : Set X) (hS : MeasurableSet S) (hf : μ S < ∞) :
      |∫ y in S, v y ∂μ| ≤ (t*B) * μ.real S := by
    let F := indicatorConstLp 2 hS hf.ne (1 : ℝ)
    have hFe : F =ᵐ[μ] S.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
    have hF0 : 0 ≤ F := by
      apply (Lp.coeFn_nonneg _).mp
      filter_upwards [hFe] with y hy
      rw [hy]
      exact indicator_nonneg (fun _ _ => zero_le_one) y
    have hFi : Integrable F μ :=
      ((integrableOn_const (C := (1 : ℝ)) hf.ne).integrable_indicator hS).congr hFe.symm
    have hFm : (∫ y, F y ∂μ) = μ.real S := by
      rw [integral_congr_ae hFe, integral_indicator hS, integral_const]
      simp only [smul_eq_mul, mul_one, measureReal_restrict_apply MeasurableSet.univ, univ_inter]
    have he : (∫ y in S, v y ∂μ) = inner ℝ (heatAt μ hX.quadratic t F-F) gL := by
      calc
        _ = ∫ y, F y * v y ∂μ := (integral_indicatorConstLp_mul μ S hS hf.ne v).symm
        _ = inner ℝ F (heatAt μ hX.quadratic t gL-gL) := by
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub (heatAt μ hX.quadratic t gL) gL,
            hX.boundedHeat_represents hn p gL ⟨C, hgb⟩ t ht, hrep] with y hsub hheat hgL
          change heatAt μ hX.quadratic t gL y = u y at hheat
          change gL y = w y at hgL
          simp only [Real.inner_apply, hsub, Pi.sub_apply]
          change F y * (u y-w y) = F y * (heatAt μ hX.quadratic t gL y-gL y)
          rw [hheat, hgL]
        _ = _ := by rw [inner_sub_right, inner_sub_left, heatAt_inner]
    rw [he]
    have hh := hX.heat_bounded_laplacian_pairing hn p g dg hg hB hdg F hF0 hFi ht.le
    change |inner ℝ (heatAt μ hX.quadratic t F-F) gL| ≤ t*B*(∫ y, F y ∂μ) at hh
    rw [hFm] at hh
    exact hh
  let := hX.openPos K n
  have hb := continuous_abs_le_of_setIntegral_bound μ (hu.sub hw) hvi hset x
  have heq : (∫ y, w y ∂hX.heatRadonMeasure hn p t ht x) = u x := by
    change (∫ y, w y ∂hX.heatRadonMeasure hn p t ht x) =
      hX.boundedHeat hn p gL ⟨C, hgb⟩ t ht x
    rw [← hX.heatRadonMeasure_integral_bounded hn p t ht x gL C hgb]
    exact integral_congr_ae ((hX.heatRadonMeasure_absolutelyContinuous hn p t ht x).ae_le hrep.symm)
  change |u x-w x| ≤ t*B at hb
  rw [heq]
  exact hb

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
