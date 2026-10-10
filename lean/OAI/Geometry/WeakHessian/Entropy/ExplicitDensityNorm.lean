import Mathlib
import OAI.Geometry.WeakHessian.Entropy.DensityCurve

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma IsTestPlan.exists_L2_density_curve_bound (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {B : ℝ≥0} (hB : ∀ t : Time,π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m) :
    ∃ u : Time → Lp ℝ 2 m, StronglyMeasurable u ∧
      (∀ t, ∀ᵐ x ∂m,0 ≤ u t x) ∧ (∀ t, ∀ᵐ x ∂m,|u t x| ≤ B) ∧
      (∀ t,Integrable (u t) m) ∧ (∀ t,∫ x,u t x ∂m = 1) ∧
      (∀ t,densityMeasure m (u t) = π.map (fun γ => γ t)) ∧
      (∀ t,‖u t‖^2 ≤ (B : ℝ)) := by
  classical
  let : IsProbabilityMeasure π := hπ.1
  choose u hun hub hui hum hul hunorm using fun t => exists_compressedDensity (hB t)
  have hm (t : Time) : ∫ x,u t x ∂m = 1 := by
    simpa [Measure.real,Measure.map_apply (continuous_eval_const t).measurable MeasurableSet.univ] using hum t
  have hnorm (t : Time) : ‖u t‖^2 ≤ (B : ℝ) := by
    simpa [Measure.real,Measure.map_apply (continuous_eval_const t).measurable MeasurableSet.univ] using hunorm t
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hc := hπ.continuous_density_inner hfin hb hun hul
  exact ⟨u,stronglyMeasurable_of_inner_continuous hc,hun,hub,hui,hm,hul,hnorm⟩

omit [MetricSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma norm_toLp_sq_le_smul_measure {ν : Measure X} {C : ℝ≥0}
    (hν : ν ≤ (C : ℝ≥0∞) • m) {f : X → ℝ} (hf : MemLp f 2 m)
    (hfν : MemLp f 2 ν) :
    ‖hfν.toLp f‖^2 ≤ (C:ℝ)*‖hf.toLp f‖^2 := by
  rw [norm_toLp_sq_eq_integral,norm_toLp_sq_eq_integral]
  have H := integral_mono_measure hν (ae_of_all _ fun x => sq_nonneg (f x))
    (hf.integrable_sq.smul_measure ENNReal.coe_ne_top)
  simpa only [integral_smul_measure,ENNReal.coe_toReal,smul_eq_mul] using H

lemma norm_toLp_le_smul_measure_loose {ν : Measure X} {C : ℝ≥0}
    (hC : (1:ℝ) ≤ C) (hν : ν ≤ (C : ℝ≥0∞) • m)
    {f : X → ℝ} (hf : MemLp f 2 m) (hfν : MemLp f 2 ν) :
    ‖hfν.toLp f‖ ≤ (C:ℝ)*(‖hf.toLp f‖+1) := by
  have H := norm_toLp_sq_le_smul_measure hν hf hfν
  have hC0 := C.coe_nonneg
  have hfn := norm_nonneg (hf.toLp f)
  have hfnν := norm_nonneg (hfν.toLp f)
  have HC : (C:ℝ) ≤ (C:ℝ)^2 := by nlinarith
  have Hsq := mul_le_mul_of_nonneg_right HC (sq_nonneg ‖hf.toLp f‖)
  have Hsq' : (C:ℝ)^2*‖hf.toLp f‖^2 ≤ ((C:ℝ)*(‖hf.toLp f‖+1))^2 := by
    nlinarith [mul_nonneg (sq_nonneg (C:ℝ)) hfn]
  exact (sq_le_sq₀ hfnν (by positivity)).mp (H.trans (Hsq.trans Hsq'))

lemma norm_product_of_compression {ν : Measure X} {E B : ℝ≥0}
    (hE : (1:ℝ) ≤ E) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {ξ : Lp ℝ 2 ν} (hξ : ‖ξ‖^2 ≤ (B:ℝ)*(E:ℝ))
    {f : X → ℝ} (hf : MemLp f 2 m) (hfν : MemLp f 2 ν) :
    ‖ξ‖*‖hfν.toLp f‖ ≤ ((B:ℝ)+1)*(‖hf.toLp f‖+1)*(E:ℝ)^2 := by
  have hξn := norm_nonneg ξ
  have hB := B.coe_nonneg
  have hEn := E.coe_nonneg
  have hξb : ‖ξ‖ ≤ ((B:ℝ)+1)*(E:ℝ) := by
    apply (sq_le_sq₀ hξn (by positivity)).mp
    apply hξ.trans
    have h1 : (B:ℝ) ≤ ((B:ℝ)+1)^2 := by nlinarith [sq_nonneg (B:ℝ)]
    have h2 : (E:ℝ) ≤ (E:ℝ)^2 := by nlinarith
    have H := mul_le_mul h1 h2 hEn (sq_nonneg ((B:ℝ)+1))
    simpa only [mul_pow] using H
  have H := mul_le_mul hξb (norm_toLp_le_smul_measure_loose hE hν hf hfν)
    (norm_nonneg _) (by positivity : 0 ≤ ((B:ℝ)+1)*(E:ℝ))
  convert H using 1
  ring

end WeakHessian

end
end

end OAI
