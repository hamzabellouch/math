import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.Piecewise
import OAI.Geometry.WeakHessian.Sobolev.Minimal
import OAI.Geometry.WeakHessian.Sobolev.CompContDiff

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
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
lemma localSobolev_of_lipschitz (hfinite : FiniteOnBoundedSets m) {f : X → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) : LocalSobolev m f := by
  refine ⟨?_, (lipschitz_isLocalWeakUpperGradient hfinite hf).exists_minimal
    hf.continuous.aemeasurable hfinite⟩
  intro o R _hR
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      hfinite (Metric.ball o R) Metric.isBounded_ball⟩
  apply MemLp.of_bound hf.continuous.aestronglyMeasurable.restrict (|f o| + L * R)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [Real.norm_eq_abs]
  calc
    |f x| ≤ |f o| + |f x - f o| := by
      simpa only [sub_add_cancel] using (abs_add_le (f x - f o) (f o)).trans_eq (add_comm _ _)
    _ ≤ |f o| + L * dist x o := by gcongr; exact hf.dist_le_mul x o
    _ ≤ |f o| + L * R := by gcongr; exact hx.le

lemma weakGradient_zero_off_support {f : X → ℝ} (hf : LocalSobolev m f)
    :
    ∀ᵐ x ∂m, x ∉ tsupport f → weakGradient m f x = 0 := by
  have hz : LocalSobolev m (fun _ : X => (0 : ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero, _, isMinimalLocalWeakUpperGradient_const 0⟩
  have heq : ∀ᵐ x ∂m, x ∈ (tsupport f)ᶜ → f x = 0 :=
    ae_of_all _ fun _ hx => image_eq_zero_of_notMem_tsupport hx
  filter_upwards [weakGradient_locality hf hz (isClosed_tsupport f).measurableSet.compl heq,
    weakGradient_const (m := m) 0] with x h₁ h₂ hx
  exact (h₁ hx).trans h₂

lemma sobolev_of_lipschitz_compactSupport (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hc : HasCompactSupport f) :
    Sobolev m f := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
      hfinite _ Metric.isBounded_ball⟩⟩
  have hfl := localSobolev_of_lipschitz hfinite hf
  refine ⟨hf.continuous.memLp_of_hasCompactSupport hc, hfl, ?_⟩
  let : IsFiniteMeasure (m.restrict (tsupport f)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hc.measure_lt_top (μ := m)⟩
  have hI : MemLp ((tsupport f).indicator (fun _ : X => (L : ℝ))) 2 m :=
    (memLp_indicator_iff_restrict (isClosed_tsupport f).measurableSet).mpr (memLp_const (L : ℝ))
  apply hI.mono (weakGradient_isMinimal hfl.2).1.1.aestronglyMeasurable
  filter_upwards [weakGradient_zero_off_support hfl,
    weakGradient_le_lipschitz hfinite hf, weakGradient_nonneg (m := m) f] with x hz hL hn
  by_cases hx : x ∈ tsupport f
  · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hn,
      abs_of_nonneg L.coe_nonneg] using hL
  · simp only [Set.indicator_of_notMem hx, hz hx, norm_zero, le_rfl]

lemma Sobolev.mul_exp (hfinite : FiniteOnBoundedSets m) {f V : X → ℝ}
    (hf : Sobolev m f) {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hVB : ∀ᵐ x ∂m, V x ≤ B) : Sobolev m (fun x => f x * Real.exp (V x)) := by
  have hVl := localSobolev_of_lipschitz hfinite hV
  have hD := (weakGradient_isMinimal hVl.2).1.exp hV.continuous.aemeasurable hVB
  have hexpB : ∀ᵐ x ∂m, |Real.exp (V x)| ≤ Real.exp B := by
    filter_upwards [hVB] with x hx
    simpa only [abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx
  have hel : LocalSobolev m (fun x => Real.exp (V x)) :=
    ⟨locallyL2_of_bounded hfinite (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hexpB),
      hD.exists_minimal (Real.continuous_exp.comp hV.continuous).aemeasurable hfinite⟩
  apply hf.mul_bounded hfinite hel hexpB
  filter_upwards [(weakGradient_isMinimal hel.2).2 _ hD,
    weakGradient_le_lipschitz hfinite hV, hVB,
    weakGradient_nonneg (m := m) (fun x => Real.exp (V x))] with x hx hL hB hn
  rw [abs_of_nonneg hn]
  exact hx.trans ((mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hB) L.coe_nonneg))

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
