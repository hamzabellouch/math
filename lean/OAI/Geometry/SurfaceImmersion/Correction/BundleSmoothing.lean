import OAI.Geometry.SurfaceImmersion.Correction.SmoothingLocalSections
import OAI.Geometry.SurfaceImmersion.Correction.ManifoldSmoothing

namespace OAI

/-! An actual finite-atlas smoothing operator on smooth vector-bundle sections. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

/-- Fiber coordinates, used only on the corresponding base chart. -/
def bundleComponent (i : A.centers) (u : ∀ x, E x) (x : M) : F :=
  (e i).continuousLinearMapAt ℝ x (u x)

def bundleLocalize (i : A.centers) (u : ∀ x, E x) : Base → F :=
  localize (i : M) (A.weight i) (A.bundleComponent e i u)

def bundleRestore (i : A.centers) (h : Base → F) (x : M) : E x :=
  A.outer i x • (e i).symmL ℝ x (h (chart (i : M) x))

def bundleSmooth (r : ℕ) (s : ℝ) (u : ∀ x, E x) (x : M) : E x :=
  ∑ i : A.centers, A.bundleRestore e i (finiteSmooth r s (A.bundleLocalize e i u)) x

variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

lemma bundleComponent_smooth_on (i : A.centers) {u : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x))) :
    ContMDiffOn planeModel 𝓘(ℝ, F) ∞ (A.bundleComponent e i u) (chart (i : M)).source := by
  have h := ((e i).contMDiffOn_section_iff (chart (i : M)).open_source (hdomain i)).mp
    hu.contMDiffOn
  apply h.congr
  intro x hx
  exact (e i).continuousLinearMapAt_apply_of_mem ℝ (hdomain i hx) (u x)

variable [CompactSpace M]

lemma bundleLocalize_smooth (i : A.centers) {u : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x))) :
    ContDiff ℝ ∞ (A.bundleLocalize e i u) :=
  localize_smooth_on (i : M) (A.weight_smooth i) (A.weight_support i)
    (A.bundleComponent_smooth_on e hdomain i hu)

omit [CompactSpace M] in
lemma bundleRestore_smooth (i : A.centers) {h : Base → F} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (A.bundleRestore e i h x)) := by
  have hsec : ContMDiffOn planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x ((e i).symmL ℝ x (h (chart (i : M) x))))
      (chart (i : M)).source := by
    apply ((e i).contMDiffOn_section_iff (chart (i : M)).open_source (hdomain i)).mpr
    apply (hh.contMDiff.comp_contMDiffOn (chart_smooth (i : M))).congr
    intro x hx
    rw [← (e i).continuousLinearMapAt_apply_of_mem ℝ (hdomain i hx),
      (e i).continuousLinearMapAt_symmL (hdomain i hx)]
    rfl
  exact (A.outer_smooth i).contMDiffOn.smul_section_of_tsupport
    (chart (i : M)).open_source (A.outer_support i) hsec

/-- Smoothing produces a smooth section of the original bundle. -/
theorem bundleSmooth_smooth (r : ℕ) {s : ℝ} (hs : 0 < s) {u : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (A.bundleSmooth e r s u x)) := by
  apply ContMDiff.sum_section
  intro i _
  exact A.bundleRestore_smooth e hdomain i
    (finiteSmooth_smooth r hs (A.bundleLocalize_smooth e hdomain i hu))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
