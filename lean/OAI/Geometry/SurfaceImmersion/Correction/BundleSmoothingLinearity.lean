import OAI.Geometry.SurfaceImmersion.Correction.BundleSmoothingIdentity

namespace OAI

/-! Linearity of the concrete finite-atlas bundle smoother. -/
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

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

lemma bundleLocalize_add (i : A.centers) (u v : ∀ x, E x) :
    A.bundleLocalize e i (u + v) = A.bundleLocalize e i u + A.bundleLocalize e i v := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target <;>
    simp [bundleLocalize, localize, bundleComponent, hx, smul_add]

lemma bundleLocalize_smul (i : A.centers) (a : ℝ) (u : ∀ x, E x) :
    A.bundleLocalize e i (a • u) = a • A.bundleLocalize e i u := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target <;>
    simp [bundleLocalize, localize, bundleComponent, hx, smul_smul, mul_comm]

lemma bundleRestore_add (i : A.centers) (f g : Base → F) :
    A.bundleRestore e i (f + g) = A.bundleRestore e i f + A.bundleRestore e i g := by
  funext x
  simp only [bundleRestore, Pi.add_apply, map_add, smul_add]

lemma bundleRestore_smul (i : A.centers) (a : ℝ) (f : Base → F) :
    A.bundleRestore e i (a • f) = a • A.bundleRestore e i f := by
  funext x
  simp only [bundleRestore, Pi.smul_apply, map_smul, smul_smul]
  rw [mul_comm]

lemma bundleSmooth_smul (r : ℕ) (s a : ℝ) (u : ∀ x, E x) :
    A.bundleSmooth e r s (a • u) = a • A.bundleSmooth e r s u := by
  funext x
  simp only [bundleSmooth, A.bundleLocalize_smul, finiteSmooth_smul,
    A.bundleRestore_smul, Pi.smul_apply, Finset.smul_sum]

variable [ContMDiffVectorBundle ∞ F E planeModel] [CompactSpace M]
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

lemma bundleSmooth_add (r : ℕ) {s : ℝ} (hs : 0 < s) {u v : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x)))
    (hv : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (v x))) :
    A.bundleSmooth e r s (u + v) = A.bundleSmooth e r s u + A.bundleSmooth e r s v := by
  funext x
  simp only [bundleSmooth, A.bundleLocalize_add]
  have hi (i : A.centers) := finiteSmooth_add r hs
    (A.bundleLocalize_smooth e hdomain i hu) (A.bundleLocalize_smooth e hdomain i hv)
  simp only [hi, A.bundleRestore_add, Pi.add_apply, Finset.sum_add_distrib]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
