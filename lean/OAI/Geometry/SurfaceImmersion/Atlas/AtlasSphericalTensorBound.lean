import OAI.Geometry.SurfaceImmersion.Atlas.EuclideanChartRead
import OAI.Geometry.SurfaceImmersion.Geometry.SphericalTensorBound

namespace OAI

/-! The tensors used for every finite-point correction have one bound,
fixed by the original immersion and its finite atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma euclideanChartRead_compact (i : A.centers) (F : M → Space) :
    HasCompactSupport (A.euclideanChartRead i F) :=
  (localize_compact (i : M) (A.outer_support i) F).comp_homeomorph
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph

theorem uniform_spherical_correction_tensor {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : A.centers) (p : M), A.weight i p ≠ 0 →
      ‖sphericalSecondFormCLM (A.euclideanChartRead i F) (chartAt Plane (i : M) p)‖ ≤ K := by
  classical
  have hb (i : A.centers) : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : M, A.weight i p ≠ 0 →
      ‖sphericalSecondFormCLM (A.euclideanChartRead i F) (chartAt Plane (i : M) p)‖ ≤ K := by
    let f := A.euclideanChartRead i F
    have hf := A.euclideanChartRead_smooth i hF
    have hc := A.euclideanChartRead_compact i F
    have hd := hf.fderiv_right (m := ∞) (by simp)
    have hdd := hd.fderiv_right (m := ∞) (by simp)
    obtain ⟨C₁,h₁⟩ := hd.continuous.bounded_above_of_compact_support (hc.fderiv ℝ)
    obtain ⟨C₂,h₂⟩ := hdd.continuous.bounded_above_of_compact_support ((hc.fderiv ℝ).fderiv ℝ)
    have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (h₁ 0)
    have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans (h₂ 0)
    refine ⟨C₂+C₁^2,by positivity,?_⟩
    intro p hp
    apply norm_sphericalSecondFormCLM_of_bounds (h₁ _) (h₂ _)
    have he := (A.euclideanChartRead_germ i F hp).eq_of_nhds
    have hps : p ∈ (chartAt Plane (i : M)).source := by
      simpa only [chart_source] using A.weight_support i (subset_tsupport _ hp)
    simp only [Function.comp_apply,(chartAt Plane (i : M)).left_inv hps] at he
    exact (congrArg norm he).trans (hunit p)
  choose K hK hb using hb
  refine ⟨∑ i, K i,Finset.sum_nonneg (fun i _ => hK i),?_⟩
  intro i p hp
  exact (hb i p hp).trans (Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
