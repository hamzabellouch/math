import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
namespace YauCounterexamples

theorem gaussianPDF_standard_le_one (m x : ℝ) : gaussianPDF m 1 x ≤ 1 := by
  rw [gaussianPDF, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one]
  have hexp : Real.exp (-(x - m) ^ 2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hroot
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x - m) ^ 2 / 2) ≤
        (Real.sqrt (2 * Real.pi))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 1 := by simpa using hinv

theorem gaussianReal_standard_le_volume (m : ℝ) : gaussianReal m 1 ≤ volume := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  calc
    volume.withDensity (gaussianPDF m 1) ≤ volume.withDensity (fun _ => 1) :=
      withDensity_mono (Filter.Eventually.of_forall (gaussianPDF_standard_le_one m))
    _ = volume := by simp

theorem finite_pi_measure_mono {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ ν : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  have hle : (Measure.pi μ).toOuterMeasure ≤ OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro s _
    rw [Measure.coe_toOuterMeasure, Measure.pi_pi]
    exact Finset.prod_le_prod (fun index _ => h index (s index))
  apply Measure.le_iff.mpr
  intro s hs
  conv_rhs => rw [Measure.pi, toMeasure_apply _ _ hs]
  exact hle s

theorem gaussian_pi_le_volume {ι : Type*} [Fintype ι] (m : ι → ℝ) :
    Measure.pi (fun i => gaussianReal (m i) 1) ≤ (volume : Measure (ι → ℝ)) :=
  finite_pi_measure_mono _ _ (fun i => gaussianReal_standard_le_volume (m i))

theorem gaussian_affine_map_le {ι : Type*} [Fintype ι]
    (m b : ι → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hL : LinearMap.det L ≠ 0) :
    (Measure.pi (fun i => gaussianReal (m i) 1)).map (fun x => L x + b) ≤
      ENNReal.ofReal (abs (LinearMap.det L)⁻¹) • (volume : Measure (ι → ℝ)) := by
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hb : Measurable (fun x : ι → ℝ => x + b) := measurable_id.add measurable_const
  calc
    (Measure.pi (fun i => gaussianReal (m i) 1)).map (fun x => L x + b) ≤
        volume.map (fun x => L x + b) :=
      Measure.map_mono (gaussian_pi_le_volume m) (hLm.add measurable_const)
    _ = ENNReal.ofReal (abs (LinearMap.det L)⁻¹) • volume := by
      rw [show (fun x => L x + b) = (fun x => x + b) ∘ L from rfl,
        ← Measure.map_map hb hLm, Real.map_linearMap_volume_pi_eq_smul_volume_pi hL,
        Measure.map_smul _ hb.aemeasurable, map_add_right_eq_self]

theorem gaussian_affine_smallBall {ι : Type*} [Fintype ι]
    (m b c : ι → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hL : LinearMap.det L ≠ 0)
    (r : ℝ) (hr : 0 ≤ r) :
    (Measure.pi (fun i => gaussianReal (m i) 1))
      ((fun x => L x + b) ⁻¹' Metric.closedBall c r) ≤
      ENNReal.ofReal (abs (LinearMap.det L)⁻¹) *
        (ENNReal.ofReal (2 * r)) ^ Fintype.card ι := by
  have hm : Measurable (fun x => L x + b) :=
    L.continuous_of_finiteDimensional.measurable.add measurable_const
  rw [← Measure.map_apply hm measurableSet_closedBall]
  calc
    _ ≤ (ENNReal.ofReal (abs (LinearMap.det L)⁻¹) • volume) (Metric.closedBall c r) :=
      gaussian_affine_map_le m b L hL _
    _ = _ := by
      rw [Measure.smul_apply, smul_eq_mul, volume_pi_closedBall c hr]
      simp [Real.volume_closedBall]

theorem gaussian_independent_smallBall {ι : Type*} [Fintype ι]
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (g : Ω → (ι → ℝ)) (hg : Measurable g)
    (m c : ι → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hL : LinearMap.det L ≠ 0)
    (r : ℝ) (hr : 0 ≤ r) :
    (ν.prod (Measure.pi (fun i => gaussianReal (m i) 1)))
      {w | L w.2 + g w.1 ∈ Metric.closedBall c r} ≤
      ENNReal.ofReal (abs (LinearMap.det L)⁻¹) *
        (ENNReal.ofReal (2 * r)) ^ Fintype.card ι := by
  have hmeas : Measurable (fun w : Ω × (ι → ℝ) => L w.2 + g w.1) :=
    (L.continuous_of_finiteDimensional.measurable.comp measurable_snd).add
      (hg.comp measurable_fst)
  change (ν.prod (Measure.pi (fun i => gaussianReal (m i) 1)))
    ((fun w : Ω × (ι → ℝ) => L w.2 + g w.1) ⁻¹' Metric.closedBall c r) ≤ _
  rw [Measure.prod_apply (hmeas measurableSet_closedBall)]
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (abs (LinearMap.det L)⁻¹) *
        (ENNReal.ofReal (2 * r)) ^ Fintype.card ι ∂ν := by
      apply lintegral_mono
      intro w
      exact gaussian_affine_smallBall m (g w) c L hL r hr
    _ = _ := by simp

end YauCounterexamples

end

end OAI
