import OAI.Geometry.Immersion.ClosedSurface.MetricModel
import OAI.Geometry.SurfaceImmersion.Correction.ExactCorrectionLimit

namespace OAI

/-!
# The correction-series limit on the surface

The bounds are imposed on smooth coordinate representatives on a fixed
neighborhood of each point. They may depend on the chart, and are only
eventual in the correction index for each derivative order.
-/

noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

open Filter Manifold
open scoped Topology ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def manifoldPartialMap (F : M → Space) (U : ℕ → M → Space) (N : ℕ) (x : M) : Space :=
  F x + ∑ n ∈ Finset.range N, U n x

def manifoldLimitMap (F : M → Space) (U : ℕ → M → Space) (x : M) : Space :=
  F x + ∑' n, U n x

/-- A smooth local representative gives both smoothness and the manifold
derivative at the center of its chart. -/
lemma local_representative_derivative {F : M → Space} {K : Plane → Space} (p : M)
    (hK : ContDiff ℝ ∞ K)
    (heq : F =ᶠ[𝓝 p] K ∘ extChartAt planeModel p) :
    ContMDiffAt planeModel spaceModel ∞ F p ∧
      mfderiv planeModel spaceModel F p =
        fderiv ℝ K (extChartAt planeModel p p) := by
  have hs : ContMDiffAt planeModel spaceModel ∞
      (K ∘ extChartAt planeModel p) p :=
    hK.contMDiff.contMDiffAt.comp p contMDiffAt_extChartAt
  refine ⟨hs.congr_of_eventuallyEq heq, ?_⟩
  have hd := heq.mfderiv_eq (I := planeModel) (I' := spaceModel)
  rw [mfderiv_comp p (hK.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiffAt_extChartAt (I := planeModel) (x := p) (n := ∞)).mdifferentiableAt
      (by simp)), mfderiv_eq_fderiv, mfderiv_extChartAt_self] at hd
  change (mfderiv planeModel spaceModel F p : Plane →L[ℝ] Space) =
    (ContinuousLinearMap.id ℝ Space).comp
      ((fderiv ℝ K (extChartAt planeModel p p)).comp
        (ContinuousLinearMap.id ℝ Plane)) at hd
  simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using hd

/-- Chartwise summable correction bounds give a smooth limit and convergence
of the actual manifold derivatives of its finite stages. -/
theorem manifold_correction_limit
    {F : M → Space} {U : ℕ → M → Space}
    (K : M → Plane → Space) (A : M → ℕ → Plane → Space)
    (ρ : M → ℕ → ℝ)
    (hK : ∀ p, ContDiff ℝ ∞ (K p))
    (hA : ∀ p n, ContDiff ℝ ∞ (A p n))
    (hρ : ∀ p, Summable (ρ p))
    (hbound : ∀ p m, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (A p n) x‖ ≤ ρ p n)
    (heq : ∀ p, ∀ᶠ x in 𝓝 p,
      F x = K p (extChartAt planeModel p x) ∧
      ∀ n, U n x = A p n (extChartAt planeModel p x)) :
    ContMDiff planeModel spaceModel ∞ (manifoldLimitMap F U) ∧
      ∀ p, Tendsto (fun N => mfderiv planeModel spaceModel
        (manifoldPartialMap F U N) p) atTop
        (𝓝 (mfderiv planeModel spaceModel (manifoldLimitMap F U) p)) := by
  have hl (p : M) : manifoldLimitMap F U =ᶠ[𝓝 p]
      limitMap (K p) (A p) ∘ extChartAt planeModel p := by
    filter_upwards [heq p] with x hx
    simp only [manifoldLimitMap, limitMap, Function.comp_apply, hx.1, hx.2]
  have hs (p : M) := local_representative_derivative p
    (smooth_limitMap (hK p) (hA p) (hρ p) (hbound p)) (hl p)
  refine ⟨fun p => (hs p).1, ?_⟩
  intro p
  have hf (N : ℕ) : mfderiv planeModel spaceModel
      (manifoldPartialMap F U N) p =
      fderiv ℝ (partialMap (K p) (A p) N) (extChartAt planeModel p p) := by
    apply (local_representative_derivative p
      ((hK p).add (ContDiff.sum (fun n _ => hA p n))) ?_).2
    filter_upwards [heq p] with x hx
    simp only [manifoldPartialMap, Function.comp_apply, hx.1, hx.2]
  simp_rw [hf, (hs p).2]
  exact tendsto_fderiv_partialMap (hK p) (hA p) (hρ p) (hbound p) _

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
/-- Once the constructed finite stages have vanishing metric defect, the
chartwise correction estimates produce an isometric immersion of the surface.
The existence of such corrections is a separate construction. -/
theorem manifold_limit_isometric
    {F : M → Space} {U : ℕ → M → Space}
    (K : M → Plane → Space) (A : M → ℕ → Plane → Space)
    (ρ : M → ℕ → ℝ)
    (hK : ∀ p, ContDiff ℝ ∞ (K p))
    (hA : ∀ p n, ContDiff ℝ ∞ (A p n))
    (hρ : ∀ p, Summable (ρ p))
    (hbound : ∀ p m, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (A p n) x‖ ≤ ρ p n)
    (heq : ∀ p, ∀ᶠ x in 𝓝 p,
      F x = K p (extChartAt planeModel p x) ∧
      ∀ n, U n x = A p n (extChartAt planeModel p x))
    (g : SmoothMetric M)
    (hmetric : ∀ p (v w : TangentSpace planeModel p), Tendsto
      (fun N => @inner ℝ Space _
        (mfderiv planeModel spaceModel (manifoldPartialMap F U N) p v : Space)
        (mfderiv planeModel spaceModel (manifoldPartialMap F U N) p w : Space))
      atTop (𝓝 (g.inner p v w))) :
    IsSmoothIsometricImmersion M g (manifoldLimitMap F U) := by
  obtain ⟨hs, hd⟩ := manifold_correction_limit K A ρ hK hA hρ hbound heq
  refine ⟨hs, ?_⟩
  intro p v w
  have hd' : Tendsto (fun N => (mfderiv planeModel spaceModel
      (manifoldPartialMap F U N) p : Plane →L[ℝ] Space)) atTop
      (𝓝 (mfderiv planeModel spaceModel (manifoldLimitMap F U) p : Plane →L[ℝ] Space)) := hd p
  have hv := ((ContinuousLinearMap.apply ℝ Space (show Plane from v)).continuous.tendsto _).comp hd'
  have hw := ((ContinuousLinearMap.apply ℝ Space (show Plane from w)).continuous.tendsto _).comp hd'
  exact tendsto_nhds_unique (hv.inner hw) (hmetric p v w)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
