import OAI.Geometry.SurfaceImmersion.Atlas.AtlasWeightedBounds
import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionApproximation

namespace OAI

/-! Uniform value and first-jet consequences of the fixed atlas norms. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma weightedBound_uniform_norm {f : M → Space} {C : ℝ}
    (hb : A.WeightedBound 1 0 C f) (p : M) :
    ‖f p‖ ≤ (Fintype.card A.centers : ℝ)*C := by
  have hpiece (i : A.centers) : ‖(A.weight i p)^2 • f p‖ ≤ C := by
    by_cases hp : p ∈ (chart (i : M)).source
    · have hh := (hb i).norm_le (mem_univ (chart (i : M) p))
      rw [localize_chart (i : M) (A.weight i) f hp] at hh
      exact hh
    · have hz : A.weight i p = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (A.weight_support i h))
      have hC : 0 ≤ C := (norm_nonneg _).trans ((hb i).norm_le (mem_univ 0))
      simpa [hz] using hC
  have he : f p = ∑ i : A.centers, (A.weight i p)^2 • f p := by
    rw [← Finset.sum_smul,A.partition,one_smul]
  rw [he]
  calc
    _ ≤ ∑ i : A.centers, ‖(A.weight i p)^2 • f p‖ := norm_sum_le _ _
    _ ≤ ∑ _i : A.centers, C := Finset.sum_le_sum (fun i _ => hpiece i)
    _ = (Fintype.card A.centers : ℝ)*C := by simp

lemma weightedBound_C1 {f : M → Space} {C : ℝ}
    (hb : A.WeightedBound 1 1 C f) : A.C1Bound C f := by
  intro i x
  refine ⟨(hb i).norm_le (mem_univ x),?_⟩
  have hh := hb i 1 le_rfl x (mem_univ x)
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,norm_iteratedFDeriv_one] using hh

variable [CompactSpace M]

theorem weighted_immersion_tolerance {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 ε (G-F) →
      ∀ p, Function.Injective (mfderiv planeModel spaceModel G p) := by
  obtain ⟨ε,hε,hs⟩ := A.immersion_C1_tolerance (hF.of_le (by simp)) hI
  exact ⟨ε,hε,fun G hG hb => hs G (hG.of_le (by simp)) (A.weightedBound_C1 hb)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
