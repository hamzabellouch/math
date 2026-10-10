import OAI.Geometry.SurfaceImmersion.Correction.ManifoldSmoothing

namespace OAI

/-! The global smoothing construction is linear on smooth maps. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_add (p : M) (ψ : M → ℝ) (f g : M → V) :
    localize p ψ (f + g) = localize p ψ f + localize p ψ g := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_add]

lemma localize_smul (p : M) (ψ : M → ℝ) (a : ℝ) (f : M → V) :
    localize p ψ (a • f) = a • localize p ψ f := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_smul, mul_comm]

lemma restore_add (p : M) (χ : M → ℝ) (f g : Base → V) :
    restore p χ (f + g) = restore p χ f + restore p χ g := by
  funext x
  by_cases hx : x ∈ (chart p).source <;> simp [restore, hx, smul_add]

lemma restore_smul (p : M) (χ : M → ℝ) (a : ℝ) (f : Base → V) :
    restore p χ (a • f) = a • restore p χ f := by
  funext x
  by_cases hx : x ∈ (chart p).source <;> simp [restore, hx, smul_smul, mul_comm]

variable [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma smooth_smul (r : ℕ) (s a : ℝ) (f : M → V) :
    A.smooth r s (a • f) = a • A.smooth r s f := by
  unfold smooth
  simp_rw [localize_smul, finiteSmooth_smul, restore_smul]
  rw [Finset.smul_sum]

variable [CompactSpace M]

lemma smooth_add (r : ℕ) {s : ℝ} (hs : 0 < s) {f g : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) ∞ f) (hg : ContMDiff planeModel 𝓘(ℝ, V) ∞ g) :
    A.smooth r s (f + g) = A.smooth r s f + A.smooth r s g := by
  unfold smooth
  simp_rw [localize_add]
  have heq (i : A.centers) := finiteSmooth_add r hs
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hg)
  simp_rw [heq, restore_add]
  rw [Finset.sum_add_distrib]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
