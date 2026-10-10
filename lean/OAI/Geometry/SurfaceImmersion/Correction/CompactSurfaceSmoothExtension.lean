import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcParameterExtension

namespace OAI

/-! Extend a smooth function from an open surface neighborhood of a
compact set, retaining its actual germ on a smaller neighborhood. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_surface_smooth_extension {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : M → E}
    (hf : ContMDiffOn planeModel 𝓘(ℝ,E) ∞ f U) :
    ∃ (g : M → E) (V : Set M), ContMDiff planeModel 𝓘(ℝ,E) ∞ g ∧
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn g f V := by
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace Plane M
  obtain ⟨V,hV,hKV,hVU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  let C : M → Set E := fun x => if x ∈ closure V then {f x} else univ
  have hC : ∀ x, Convex ℝ (C x) := by
    intro x
    dsimp only [C]
    split_ifs
    · exact convex_singleton _
    · exact convex_univ
  have hloc : ∀ x : M, ∃ W ∈ 𝓝 x, ∃ q : M → E,
      ContMDiffOn planeModel 𝓘(ℝ,E) ∞ q W ∧ ∀ y ∈ W, q y ∈ C y := by
    intro x
    by_cases hx : x ∈ closure V
    · refine ⟨U,hU.mem_nhds (hVU hx),f,hf,?_⟩
      intro y hy
      dsimp only [C]
      split_ifs <;> simp
    · refine ⟨(closure V)ᶜ,isClosed_closure.isOpen_compl.mem_nhds hx,fun _ => 0,contMDiffOn_const,?_⟩
      intro y hy
      have hy' : y ∉ closure V := hy
      simp [C,hy']
  obtain ⟨g,hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local planeModel hC hloc
  refine ⟨g,V,g.contMDiff,hV,hKV,subset_closure.trans hVU,?_⟩
  intro x hx
  have h := hg x
  simpa [C,subset_closure hx] using h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
