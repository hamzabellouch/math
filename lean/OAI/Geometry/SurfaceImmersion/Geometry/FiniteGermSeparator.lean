import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceCrosscapPreparation
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-! A smooth separator for a pair of distinct surface points, constant
near every point of a fixed finite set. It supports translation patches
without altering the prepared crosscap jets. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem finite_germ_separator (S : Finset M) (x y : M) (hxy : x ≠ y) :
    ∃ χ : M → ℝ, ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧
      (∀ p, χ p ∈ Icc 0 1) ∧ χ =ᶠ[𝓝 x] (fun _ => 1) ∧
      χ =ᶠ[𝓝 y] (fun _ => 0) ∧
      ∀ p ∈ S, (χ =ᶠ[𝓝 p] (fun _ => 0)) ∨ (χ =ᶠ[𝓝 p] (fun _ => 1)) := by
  classical
  let A : Set M := ((S.erase x : Finset M) : Set M) ∪ {y}
  have hA : IsClosed A := (S.erase x).finite_toSet.isClosed.union isClosed_singleton
  have hdis : Disjoint A ({x} : Set M) := by
    rw [Set.disjoint_singleton_right]
    rintro (hx | hx)
    · exact (Finset.mem_erase.mp hx).1 rfl
    · exact hxy (mem_singleton_iff.mp hx)
  obtain ⟨χ,hχ0,hχ1,hχrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    planeModel hA isClosed_singleton hdis (n := (⊤ : ℕ∞))
  have h1 : (χ : M → ℝ) =ᶠ[𝓝 x] (fun _ => 1) :=
    hχ1.filter_mono (nhds_le_nhdsSet (mem_singleton x))
  have h0 (p : M) (hp : p ∈ A) : (χ : M → ℝ) =ᶠ[𝓝 p] (fun _ => 0) :=
    hχ0.filter_mono (nhds_le_nhdsSet hp)
  refine ⟨χ,χ.contMDiff,hχrange,h1,h0 y (Or.inr (mem_singleton y)),?_⟩
  intro p hp
  by_cases hpx : p = x
  · exact Or.inr (hpx ▸ h1)
  · exact Or.inl (h0 p (Or.inl (Finset.mem_erase.mpr ⟨hpx,hp⟩)))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
