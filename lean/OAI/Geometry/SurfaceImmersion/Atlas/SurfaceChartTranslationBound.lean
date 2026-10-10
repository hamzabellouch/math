import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceCoordinateTranslation

namespace OAI

/-! Uniform chart derivative bounds for a fixed scalar translation family. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance chartScalarDerivNormed : NormedAddCommGroup (Base →L[ℝ] ℝ) := inferInstance
local instance chartScalarDerivSpace : NormedSpace ℝ (Base →L[ℝ] ℝ) := inferInstance

lemma surface_chart_translation_derivative (p : M)
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (a : ProjectionTarget 3) {x : Base} (hx : x ∈ (chart p).target) :
    fderiv ℝ (surfaceTranslation f χ a ∘ (chart p).symm) x =
      fderiv ℝ (f ∘ (chart p).symm) x+
        (fderiv ℝ (χ ∘ (chart p).symm) x).smulRight a := by
  have hF : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  have hC : ContDiffOn ℝ ∞ (χ ∘ (chart p).symm) (chart p).target :=
    (hχ.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  exact (((hF.contDiffAt ((chart p).open_target.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.add
    (((hC.contDiffAt ((chart p).open_target.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.smul_const a)).fderiv

theorem compact_chart_translation_bound (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    {S : Set Base} (hS : IsCompact S) (hST : S ⊆ (chart p).target)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {f : M → ProjectionTarget 3},
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f →
      ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ x ∈ S,
        ‖fderiv ℝ (surfaceTranslation f χ a ∘ (chart p).symm) x-
          fderiv ℝ (f ∘ (chart p).symm) x‖ < ε := by
  have hC : ContDiffOn ℝ ∞ (χ ∘ (chart p).symm) (chart p).target :=
    (hχ.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  have hD : ContinuousOn (fderiv ℝ (χ ∘ (chart p).symm)) S :=
    (hC.continuousOn_fderiv_of_isOpen (chart p).open_target (by simp)).mono hST
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hD
  let B := max C 0+1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right C 0]
  refine ⟨ε/B,div_pos hε hB,?_⟩
  intro f hf a ha x hx
  rw [surface_chart_translation_derivative p hf hχ a (hST hx),add_sub_cancel_left,
    ContinuousLinearMap.norm_smulRight_apply]
  have hb : ‖fderiv ℝ (χ ∘ (chart p).symm) x‖ ≤ B :=
    (hC x hx).trans (by dsimp [B]; linarith [le_max_left C 0])
  calc
    _ ≤ B*‖a‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg a)
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hB).mp ha

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
