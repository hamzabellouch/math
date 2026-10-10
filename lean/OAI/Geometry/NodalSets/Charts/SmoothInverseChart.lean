import OAI.Geometry.NodalSets.Elliptic.TargetEmbedding

namespace OAI

namespace Yau.Geometry
open Manifold
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma inverse_chart_smooth_at (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    ContMDiffAt 𝓘(ℝ,E) I ∞ (extChartAt I p).symm y := by
  exact (contMDiffOn_extChartAt_symm p y hy).contMDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hy)

lemma smooth_inverse_chart_comp (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) ∞ f)
    (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    ContDiffAt ℝ ∞ (f ∘ (extChartAt I p).symm) y := by
  exact ((hf _).comp y (inverse_chart_smooth_at p hy)).contDiffAt

lemma inverse_chart_comp_derivative (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) ∞ f)
    (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    fderiv ℝ (f ∘ (extChartAt I p).symm) y =
      (mfderiv I 𝓘(ℝ,F) f ((extChartAt I p).symm y)).comp
        (mfderiv 𝓘(ℝ,E) I (extChartAt I p).symm y) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp y ((hf _).mdifferentiableAt (by simp))
    ((inverse_chart_smooth_at p hy).mdifferentiableAt (by simp))

lemma smooth_inverse_chart_derivative (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) ∞ f)
    (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    ContDiffAt ℝ ∞ (fderiv ℝ (f ∘ (extChartAt I p).symm)) y :=
  (smooth_inverse_chart_comp f hf p hy).fderiv_right (by simp)

end
end Yau.Geometry

end OAI
