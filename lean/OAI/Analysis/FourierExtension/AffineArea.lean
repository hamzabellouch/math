import Mathlib
import OAI.Analysis.FourierExtension.GraphBounds
import OAI.Analysis.FourierExtension.ChartMeasure

namespace OAI

/-! Fourier bounds for affine graph area measures. -/

open MeasureTheory
open scoped NNReal ENNReal ContDiff
noncomputable section
open Filter
open scoped Topology ContDiff
open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProductSpace ENNReal
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
open Set Filter
open scoped ENNReal InnerProductSpace
open scoped FourierTransform SchwartzMap ENNReal
open scoped ENNReal FourierTransform InnerProductSpace
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
open scoped ENNReal NNReal

namespace DiagonalExtension.AffineGraph
open MeasureTheory Set ConvexRadial
open scoped ENNReal NNReal
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]

theorem area_L4 (A : GraphSpace ≃L[ℝ] Y) (a : Y)
    {φ : E2 → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hell : ∀ x v : E2, c * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v)
    (R : ℝ) (κ : ℝ≥0) : ∃ C : ℝ≥0, ∀ μ : Measure Y,
      μ ≤ ((κ : ℝ≥0∞) • (Measure.hausdorffMeasure 2 : Measure Y)).restrict
        ((fun u => a + A (graphEmbedding φ u)) '' Metric.closedBall 0 R) →
      ∀ f : Y → ℂ, MemLp f 2 μ →
      MemLp (fun x => ∫ y, f y * (Real.fourierChar (-inner ℝ y x) : ℂ) ∂μ) 4 volume ∧
      eLpNorm (fun x => ∫ y, f y * (Real.fourierChar (-inner ℝ y x) : ℂ) ∂μ) 4 volume ≤
        (C : ℝ≥0∞) * eLpNorm f 2 μ := by
  let Γ : E2 → Y := fun u => a + A (graphEmbedding φ u)
  let P := WithLp.prodContinuousLinearEquiv 2 ℝ E2 ℝ
  let π : Y → E2 := fun y => (P (A.symm (y-a))).1
  have hΓsmooth : ContDiff ℝ ∞ Γ := by
    apply contDiff_const.add
    apply A.contDiff.comp
    exact P.symm.contDiff.comp (contDiff_id.prodMk hφ)
  have hπ : Measurable π := by dsimp [π]; fun_prop
  have hleft (u : E2) : π (Γ u) = u := by
    simp [π,Γ,P,graphEmbedding]
  obtain ⟨L,hL⟩ := hΓsmooth.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : E2) R) (isCompact_closedBall (0 : E2) R)
  let C : ℝ≥0∞ :=
    (ENNReal.ofReal (Real.pi/c) * (haarFactor A : ℝ≥0∞)) ^ (1/4 : ℝ) *
      ((κ : ℝ≥0∞) * (L : ℝ≥0∞)^2 * (ChartMeasure.dimensionFactor E2 : ℝ≥0∞)) ^ (1/2 : ℝ)
  have hC : C ≠ (⊤ : ℝ≥0∞) := by dsimp [C]; finiteness
  refine ⟨C.toNNReal,?_⟩
  intro μ hμ f hf
  obtain ⟨g,hg,hgc,hgi,hgb,hpair⟩ := ChartMeasure.exists_graph_density
    (by simp [E2]) hΓsmooth.continuous hπ (fun u _ => hleft u) hL
    (isCompact_closedBall (0 : E2) R) hμ hf
  have he : (fun x => ∫ y, f y * (Real.fourierChar (-inner ℝ y x) : ℂ) ∂μ) =
      GraphFourier.transform Γ g := by
    ext x
    exact (hpair _ (GraphFourier.character_continuous x)
      ⟨1,fun y => by simp only [Circle.norm_coe,le_rfl]⟩).symm
  obtain ⟨hm,hb⟩ := L4 A a hφ hc hell hg hgc
  rw [he,ENNReal.coe_toNNReal hC]
  refine ⟨hm,hb.trans ?_⟩
  simpa only [C,mul_assoc] using
    mul_le_mul_right hgb ((ENNReal.ofReal (Real.pi/c) * (haarFactor A : ℝ≥0∞)) ^ (1/4 : ℝ))

end DiagonalExtension.AffineGraph

end

end OAI
