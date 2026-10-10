import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceCrosscapPreparation
import OAI.Geometry.SurfaceImmersion.Correction.FiniteCorrectionGerms

namespace OAI

/-! Finite supported replacements on a surface agree with the selected
replacement near its support and with the original map elsewhere. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem finite_disjoint_surface_replacement {ι : Type*} [Fintype ι]
    (f : M → ProjectionTarget 3)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (g : ι → M → ProjectionTarget 3)
    (hg : ∀ i, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (g i))
    (K : ι → Set M) (hs : ∀ i, tsupport (g i-f) ⊆ K i)
    (hd : Pairwise fun i j => Disjoint (K i) (K j)) :
    ∃ F : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F ∧
      (∀ i p, p ∈ K i → F =ᶠ[𝓝 p] g i) ∧
      (∀ p, (∀ i, p ∉ K i) → F =ᶠ[𝓝 p] f) := by
  classical
  let F : M → ProjectionTarget 3 := fun x => f x + ∑ i, (g i x-f x)
  have hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F :=
    hf.add (ContMDiff.sum fun i _ => (hg i).sub hf)
  refine ⟨F,hF,?_,?_⟩
  · intro i p hp
    have he := SphericalJets.finite_sum_germ_of_disjoint_supports Finset.univ
      (fun i => g i-f) K (fun j _ => hs j)
      (fun j _ k _ hjk => hd hjk) (Finset.mem_univ i) hp
    filter_upwards [he] with x hx
    change f x + ∑ j, (g j x-f x) = g i x
    change (∑ j, (g j x-f x)) = g i x-f x at hx
    rw [hx]
    abel
  · intro p hp
    have he : ∀ᶠ x in 𝓝 p, ∀ i ∈ (Finset.univ : Finset ι), (g i-f) x = 0 := by
      apply (eventually_all_finset Finset.univ).mpr
      intro i _
      exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hp i (hs i h))
    filter_upwards [he] with x hx
    change f x + ∑ i, (g i x-f x) = f x
    have hz : ∑ i, (g i x-f x) = 0 := Finset.sum_eq_zero fun i hi => hx i hi
    rw [hz,add_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
