import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.MulBounded
import OAI.Geometry.WeakHessian.LocalBounds.GammaAddConstLeft
import OAI.Geometry.WeakHessian.Measure.RadialCutoffLp

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma abs_gamma_lipschitz_le (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u φ : X → ℝ}
    (hu : LocalSobolev m u) {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    ∀ᵐ x ∂m, |gamma m u φ x| ≤ (L:ℝ)*weakGradient m u x := by
  filter_upwards [abs_gamma_le hfinite hpar hu (localSobolev_of_lipschitz hfinite hφ),
    weakGradient_le_lipschitz hfinite hφ,weakGradient_nonneg (m := m) u] with x h1 h2 h3
  exact h1.trans (by nlinarith)

lemma integrable_gamma_lipschitz (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u φ : X → ℝ}
    (hu : LocalSobolev m u) (hD : Integrable (weakGradient m u) m)
    {L : ℝ≥0} (hφ : LipschitzWith L φ) : Integrable (gamma m u φ) m := by
  apply (hD.const_mul (L:ℝ)).mono'
    (gamma_aestronglyMeasurable hfinite hu (localSobolev_of_lipschitz hfinite hφ))
  exact abs_gamma_lipschitz_le hfinite hpar hu hφ

lemma IsLaplacian.bounded_lipschitz_pairing (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {u A φ : X → ℝ}
    (hu : IsLaplacian m u A) (hA : Integrable A m)
    (hD : Integrable (weakGradient m u) m) {L : ℝ≥0} (hφ : LipschitzWith L φ)
    {B : ℝ} (hB : ∀ x, |φ x| ≤ B) :
    (∫ x, A x*φ x ∂m) = -(∫ x,gamma m u φ x ∂m) := by
  let : Nonempty X := ⟨o⟩
  have hφs := localSobolev_of_lipschitz hfinite hφ
  have hγ := integrable_gamma_lipschitz hfinite hpar hu.1.2.1 hD hφ
  have hAφ : Integrable (fun x => A x*φ x) m :=
    hA.mul_bdd hφ.continuous.aestronglyMeasurable (ae_of_all _ hB)
  have hχs (n : ℕ) := localSobolev_of_lipschitz hfinite (radialCutoff_lipschitz o n)
  have hχB (n : ℕ) : ∀ᵐ x ∂m, |weakGradient m (radialCutoff o n) x| ≤ ((n:ℝ)+1)⁻¹ := by
    filter_upwards [weakGradient_nonneg (m := m) (radialCutoff o n),
      weakGradient_le_lipschitz hfinite (radialCutoff_lipschitz o n)] with x h0 h1
    rw [abs_of_nonneg h0]
    exact h1
  have he (n : ℕ) : (∫ x,A x*φ x*radialCutoff o n x ∂m) =
      -(∫ x,gamma m u φ x*radialCutoff o n x ∂m) -
      (∫ x,φ x*gamma m u (radialCutoff o n) x ∂m) := by
    have H := hu.2.2 (fun x => φ x*radialCutoff o n x)
      (hφs.mul_lipschitz_compactSupport hfinite (radialCutoff_lipschitz o n) (radialCutoff_compact o n))
    have hp := gamma_mul_left hfinite hpar hφs (hχs n) hu.1.2.1
      (ae_of_all _ fun x => by rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x) (hχB n)
    have Hg : gamma m u (fun x => φ x*radialCutoff o n x) =ᵐ[m]
        (fun x => φ x*gamma m u (radialCutoff o n) x+radialCutoff o n x*gamma m u φ x) := by
      filter_upwards [hp,gamma_comm (m := m) u (fun x => φ x*radialCutoff o n x),
        gamma_comm (m := m) (radialCutoff o n) u,gamma_comm (m := m) φ u] with x h1 h2 h3 h4
      rw [h2,h1,h3,h4]
    have hg1 : Integrable (fun x => φ x*gamma m u (radialCutoff o n) x) m :=
      (integrable_gamma_lipschitz hfinite hpar hu.1.2.1 hD (radialCutoff_lipschitz o n)).bdd_mul
        hφ.continuous.aestronglyMeasurable (ae_of_all _ hB)
    have hg2 : Integrable (fun x => radialCutoff o n x*gamma m u φ x) m :=
      hγ.bdd_mul (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x)
    rw [integral_congr_ae Hg,integral_add hg1 hg2] at H
    simp_rw [mul_assoc, mul_comm (radialCutoff o n _)] at H ⊢
    linarith
  have hcross (n : ℕ) : ‖∫ x,φ x*gamma m u (radialCutoff o n) x ∂m‖ ≤
      B*((n:ℝ)+1)⁻¹*(∫ x,weakGradient m u x ∂m) := by
    have H := norm_integral_le_of_norm_le (f := fun x => φ x*gamma m u (radialCutoff o n) x)
      (hD.const_mul (B*((n:ℝ)+1)⁻¹)) (by
        filter_upwards [abs_gamma_lipschitz_le hfinite hpar hu.1.2.1
          (radialCutoff_lipschitz o n)] with x hx
        change |φ x*gamma m u (radialCutoff o n) x| ≤ B*((n:ℝ)+1)⁻¹*weakGradient m u x
        rw [abs_mul]
        simp only [NNReal.coe_inv, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] at hx
        have hb0 : 0 ≤ B := (abs_nonneg (φ x)).trans (hB x)
        exact (mul_le_mul (hB x) hx (abs_nonneg _) hb0).trans_eq (by ring))
    simpa only [integral_const_mul] using H
  have hc0 : Tendsto (fun n => ∫ x,φ x*gamma m u (radialCutoff o n) x ∂m) atTop (𝓝 0) := by
    apply squeeze_zero_norm hcross
    have H := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul B).mul_const (∫ x,weakGradient m u x ∂m)
    simpa only [one_div,mul_zero,zero_mul] using H
  have H := ((integral_radialCutoff_tendsto o hγ).neg.sub hc0)
  simp only [sub_zero] at H
  simp_rw [← he] at H
  exact tendsto_nhds_unique (integral_radialCutoff_tendsto o hAφ) H
end WeakHessian

end
end InlinedFile0

end OAI
