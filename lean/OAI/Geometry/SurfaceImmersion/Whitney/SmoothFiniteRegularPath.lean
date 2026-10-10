import OAI.Geometry.SurfaceImmersion.Whitney.SmoothOrderedArc

namespace OAI

/-! A finite embedded regular-piece path can be smoothed inside any open
set containing its interior. All new points lie in a compact subset of
that open set, while its two endpoints remain fixed. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {p q : M} {γ : Path p q}

theorem smooth_finite_regular_path (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) {O : Set M} (hO : IsOpen O)
    (hγO : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ O) :
    ∃ (P : SmoothCompactArc planeModel M) (K : Set M),
      IsCompact K ∧ K ⊆ O ∧ P.curve P.start = p ∧ P.curve P.finish = q ∧
      P.curve '' Icc P.start P.finish ⊆ range γ ∪ K := by
  obtain ⟨n,T,hT,hTi,B,horder,hsep,hdis,hreg⟩ := ordered_corner_bridges_interior hγ hi hO hγO
  cases n with
  | zero =>
    have hreg' : ∀ t ∈ Ioo (0:ℝ) 1,
        ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
        Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
      intro t ht
      apply hreg t ht
      rintro ⟨i,_⟩
      exact Fin.elim0 i
    obtain ⟨P,hPs,hPf,hPi⟩ := smooth_regular_path hγ hi hreg'
    exact ⟨P,∅,isCompact_empty,empty_subset _,hPs,hPf,fun x hx => Or.inl (hPi hx)⟩
  | succ n =>
    obtain ⟨P,hPs,hPf,hPi⟩ := smooth_ordered_arc hγ hi T hT hTi B horder hsep hdis hreg
    let K := ⋃ i, (B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish
    have hK : IsCompact K := isCompact_iUnion (fun i =>
      isCompact_Icc.image_of_continuousOn ((B i).arc.smooth.continuousOn.mono (B i).arc.interval_subset))
    have hKO : K ⊆ O := by
      intro x hx
      obtain ⟨i,s,hs,rfl⟩ := mem_iUnion.mp hx
      exact (B i).image_subset hs
    exact ⟨P,K,hK,hKO,hPs,hPf,hPi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
