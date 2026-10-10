import OAI.Geometry.SurfaceImmersion.Atlas.EuclideanChartRead
import OAI.Geometry.SurfaceImmersion.Correction.FiniteCorrectionGerms

namespace OAI

/-! Finite spherical jet corrections on the actual surface. The disjoint
coordinate balls are chosen before restoring and normalizing the corrections. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.SphericalJets

lemma sphericalSecondForm_congr_germ {F G : Plane → Space} {p : Plane}
    (h : F =ᶠ[𝓝 p] G) (v w : Plane) :
    sphericalSecondForm F p v w = sphericalSecondForm G p v w := by
  simp only [sphericalSecondForm,secondForm,normalSpace,h.eq_of_nhds,h.fderiv_eq,
    h.fderiv.fderiv_eq]

end ClosedSurfaceR4.SphericalJets
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def finiteSurfaceQuadratic (P : Finset M) (c : P → A.centers) (r : P → ℝ)
    (F : M → Space) : M → Space := fun x => ∑ p : P,
  euclideanRestore (c p : M) (A.outer (c p))
    (scaledQuadraticCutoff (sphericalSecondFormCLM (A.euclideanChartRead (c p) F)
      (chartAt Plane (c p : M) p)) (chartAt Plane (c p : M) p) (r p)) x

omit [CompactSpace M] [T2Space M] in
lemma finiteSurfaceQuadratic_smooth (P : Finset M) (c : P → A.centers) (r : P → ℝ)
    (F : M → Space) :
    ContMDiff planeModel spaceModel ∞ (A.finiteSurfaceQuadratic P c r F) := by
  apply ContMDiff.sum
  intro p _
  exact euclideanRestore_smooth _ (A.outer_smooth _) (by simpa only [chart_source]
    using (A.outer_support (c p))) (scaledQuadraticCutoff_smooth _ _ _)

omit [CompactSpace M] in
lemma finiteSurfaceQuadratic_chart_germ (P : Finset M) (c : P → A.centers) (r : P → ℝ)
    (F : M → Space) (hc : ∀ p, A.weight (c p) p ≠ 0) (hr : ∀ p, 0 < r p)
    (hball : ∀ p, closedBall (chartAt Plane (c p : M) p) (r p) ⊆
      (chartAt Plane (c p : M)).target)
    (hdisj : Pairwise fun p q : P =>
      Disjoint ((chartAt Plane (c p : M)).symm '' closedBall (chartAt Plane (c p : M) p) (r p))
        ((chartAt Plane (c q : M)).symm '' closedBall (chartAt Plane (c q : M) q) (r q)))
    (p : P) :
    (fun y => A.finiteSurfaceQuadratic P c r F ((chartAt Plane (c p : M)).symm y))
      =ᶠ[𝓝 (chartAt Plane (c p : M) p)]
      scaledQuadraticCutoff (sphericalSecondFormCLM (A.euclideanChartRead (c p) F)
        (chartAt Plane (c p : M) p)) (chartAt Plane (c p : M) p) (r p) := by
  classical
  let q (p : P) := scaledQuadraticCutoff
    (sphericalSecondFormCLM (A.euclideanChartRead (c p) F) (chartAt Plane (c p : M) p))
    (chartAt Plane (c p : M) p) (r p)
  let Q (p : P) := euclideanRestore (c p : M) (A.outer (c p)) (q p)
  let K (p : P) := (chartAt Plane (c p : M)).symm ''
    closedBall (chartAt Plane (c p : M) p) (r p)
  have hps : (p : M) ∈ (chartAt Plane (c p : M)).source := by
    simpa only [chart_source] using A.weight_support (c p) (subset_tsupport _ (hc p))
  have hpt := (chartAt Plane (c p : M)).map_source hps
  have hpK : (p : M) ∈ K p := ⟨chartAt Plane (c p : M) p,
    mem_closedBall_self (hr p).le,(chartAt Plane (c p : M)).left_inv hps⟩
  have he : A.finiteSurfaceQuadratic P c r F =ᶠ[𝓝 (p : M)] Q p :=
    finite_sum_germ_of_disjoint_supports Finset.univ Q K
      (fun q _ => euclideanRestore_tsupport _ _ (isCompact_closedBall _ _) (hball q)
        (scaledQuadraticCutoff_tsupport _ _ (hr q)))
      (fun p _ q _ hpq => hdisj hpq) (Finset.mem_univ p) hpK
  have ht : Tendsto (chartAt Plane (c p : M)).symm (𝓝 (chartAt Plane (c p : M) p))
      (𝓝 (p : M)) := by
    have hh := ((chartAt Plane (c p : M)).continuousOn_symm _ hpt).continuousAt
      ((chartAt Plane (c p : M)).open_target.mem_nhds hpt)
    simpa only [(chartAt Plane (c p : M)).left_inv hps] using hh.tendsto
  exact (he.comp_tendsto ht).trans
    (euclideanRestore_chart_germ _ _ _ hpt (A.outer_one_chart_germ (c p) (hc p)))

theorem finiteSurfaceQuadratic_flattening (P : Finset M) (c : P → A.centers) (r : P → ℝ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (hunit : ∀ p, ‖F p‖ = 1) (hc : ∀ p, A.weight (c p) p ≠ 0) (hr : ∀ p, 0 < r p)
    (hball : ∀ p, closedBall (chartAt Plane (c p : M) p) (r p) ⊆
      (chartAt Plane (c p : M)).target)
    (hdisj : Pairwise fun p q : P =>
      Disjoint ((chartAt Plane (c p : M)).symm '' closedBall (chartAt Plane (c p : M) p) (r p))
        ((chartAt Plane (c q : M)).symm '' closedBall (chartAt Plane (c q : M) q) (r q))) :
    let G := radialNormalize ∘ (F + A.finiteSurfaceQuadratic P c r F)
    ∀ p : P, G p = F p ∧
      fderiv ℝ (G ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) =
        fderiv ℝ (F ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) ∧
      ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (c p : M)).symm)
        (chartAt Plane (c p : M) p) v w = 0 := by
  intro G p
  let x := chartAt Plane (c p : M) p
  let f := A.euclideanChartRead (c p) F
  let q := scaledQuadraticCutoff (sphericalSecondFormCLM f x) x (r p)
  have hf := A.euclideanChartRead_smooth (c p) hF
  have he := A.euclideanChartRead_germ (c p) F (hc p)
  have hu : ∀ᶠ y in 𝓝 x, ‖f y‖ = 1 :=
    he.mono fun y hy => (congrArg norm hy).trans (hunit _)
  obtain ⟨hq0,hq1,hq2⟩ := scaledQuadraticCutoff_jets (sphericalSecondFormCLM f x)
    (fun v w => sphericalSecondForm_symmetric hf x v w) x (hr p)
  obtain ⟨hg0,hg1,hg2⟩ := normalized_spherical_flattening hf
    (scaledQuadraticCutoff_smooth _ _ _) hu hq0 hq1 hq2
  have hq := A.finiteSurfaceQuadratic_chart_germ P c r F hc hr hball hdisj p
  have hg : G ∘ (chartAt Plane (c p : M)).symm =ᶠ[𝓝 x] radialNormalize ∘ (f+q) := by
    filter_upwards [he,hq] with y hy hqy
    change radialNormalize (F ((chartAt Plane (c p : M)).symm y) +
      A.finiteSurfaceQuadratic P c r F ((chartAt Plane (c p : M)).symm y)) = _
    simp only [Function.comp_apply] at hy
    rw [← hy,hqy]
    rfl
  have hps : (p : M) ∈ (chartAt Plane (c p : M)).source := by
    simpa only [chart_source] using A.weight_support (c p) (subset_tsupport _ (hc p))
  refine ⟨?_,hg.fderiv_eq.trans (hg1.trans he.fderiv_eq),?_⟩
  · have hv := hg.eq_of_nhds.trans (hg0.trans he.eq_of_nhds)
    simpa only [Function.comp_apply,x,(chartAt Plane (c p : M)).left_inv hps] using hv
  · intro v w
    exact (sphericalSecondForm_congr_germ hg v w).trans (hg2 v w)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
