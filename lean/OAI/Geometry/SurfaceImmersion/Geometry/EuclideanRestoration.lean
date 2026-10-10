import OAI.Geometry.SurfaceImmersion.Correction.ManifoldSmoothing
import OAI.Geometry.SurfaceImmersion.Atlas.FinitePointChartBalls

namespace OAI

/-! Restore a compactly supported Euclidean chart correction. The support
and germ formulas are used in finite-point spherical preparation. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def euclideanRestore (p : M) (χ : M → ℝ) (h : Plane → Space) : M → Space :=
  restore p χ (h ∘ (EuclideanSpace.equiv (Fin 2) ℝ).symm)

lemma euclideanRestore_eq (p : M) (χ : M → ℝ) (h : Plane → Space) :
    euclideanRestore p χ h = (chartAt Plane p).source.indicator
      (fun x => χ x • h (chartAt Plane p x)) := by
  funext x
  by_cases hx : x ∈ (chartAt Plane p).source
  · simp [euclideanRestore,restore,chart,hx]
  · simp [euclideanRestore,restore,chart,hx]

lemma euclideanRestore_smooth [IsManifold planeModel ∞ M] (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hχs : tsupport χ ⊆ (chartAt Plane p).source) {h : Plane → Space}
    (hh : ContDiff ℝ ∞ h) : ContMDiff planeModel spaceModel ∞ (euclideanRestore p χ h) := by
  exact restore_smooth p hχ (by simpa only [chart_source] using hχs)
    (hh.comp (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff)

lemma euclideanRestore_tsupport [T2Space M] (p : M) (χ : M → ℝ) {h : Plane → Space}
    {K : Set Plane} (hK : IsCompact K) (hKt : K ⊆ (chartAt Plane p).target)
    (hs : tsupport h ⊆ K) :
    tsupport (euclideanRestore p χ h) ⊆ (chartAt Plane p).symm '' K := by
  have hclosed : IsClosed ((chartAt Plane p).symm '' K) :=
    (hK.image_of_continuousOn ((chartAt Plane p).continuousOn_symm.mono hKt)).isClosed
  apply closure_minimal _ hclosed
  intro x hx
  by_contra hn
  rw [euclideanRestore_eq] at hx
  by_cases hxs : x ∈ (chartAt Plane p).source
  · have hh : h (chartAt Plane p x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hn ⟨chartAt Plane p x,hs hmem,(chartAt Plane p).left_inv hxs⟩
    exact hx (by simp [indicator_of_mem hxs,hh])
  · exact hx (indicator_of_notMem hxs _)

lemma euclideanRestore_chart_germ (p : M) (χ : M → ℝ) (h : Plane → Space)
    {x : Plane} (hx : x ∈ (chartAt Plane p).target)
    (hχ : (fun y => χ ((chartAt Plane p).symm y)) =ᶠ[𝓝 x] (fun _ => (1 : ℝ))) :
    (fun y => euclideanRestore p χ h ((chartAt Plane p).symm y)) =ᶠ[𝓝 x] h := by
  filter_upwards [(chartAt Plane p).open_target.mem_nhds hx,hχ] with y hy hχy
  rw [euclideanRestore_eq,indicator_of_mem ((chartAt Plane p).map_target hy),
    hχy,one_smul,(chartAt Plane p).right_inv hy]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
