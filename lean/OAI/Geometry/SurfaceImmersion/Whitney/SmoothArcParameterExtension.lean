import OAI.Geometry.SurfaceImmersion.Whitney.CompactArcLocalNeighborhood
import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceCurveCoordinates

namespace OAI

/-! The parameter of a compact embedded regular source arc extends to
an actual globally smooth real function on the surface. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem smooth_arc_parameter_extension (P : SmoothCompactArc planeModel M) :
    ∃ F : M → ℝ, ContMDiff planeModel 𝓘(ℝ) ∞ F ∧
      ∀ t ∈ Icc P.start P.finish, F (P.curve t) = t := by
  let K := P.curve '' Icc P.start P.finish
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (P.smooth.continuousOn.mono P.interval_subset)
  let C : M → Set ℝ := fun x => {v | ∀ t ∈ Icc P.start P.finish, P.curve t = x → v = t}
  have hC : ∀ x, Convex ℝ (C x) := by
    intro x a ha b hb α β hα hβ hsum t ht he
    rw [ha t ht he,hb t ht he]
    simp only [smul_eq_mul,← add_mul,hsum,one_mul]
  have hloc : ∀ x : M, ∃ V ∈ 𝓝 x, ∃ g : M → ℝ,
      ContMDiffOn planeModel 𝓘(ℝ) ∞ g V ∧ ∀ y ∈ V, g y ∈ C y := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨t,ht,rfl⟩ := hx
      obtain ⟨c,U,hU,htU,_,hcs,_,hcoords⟩ := surface_curve_coordinates
        P.domain_open P.smooth (P.interval_subset ht) (P.regular t (P.interval_subset ht))
      obtain ⟨V,hV,htV,hVc,hVU⟩ := P.local_neighborhood ht hU htU c.open_source (hcoords t htU).1
      refine ⟨V,hV.mem_nhds htV,fun y => c y 1,?_,?_⟩
      · exact (contDiff_apply ℝ ℝ (1:Fin 2)).contMDiff.comp_contMDiffOn (hcs.mono hVc)
      · intro y hy u hu he
        have huV : P.curve u ∈ V := he ▸ hy
        have hh := (hcoords u (hVU u hu huV)).2
        change c y 1 = u
        rw [← he,hh]
        simp
    · refine ⟨Kᶜ,hK.isClosed.isOpen_compl.mem_nhds hx,fun _ => 0,contMDiffOn_const,?_⟩
      intro y hy t ht he
      exact False.elim (hy ⟨t,ht,he⟩)
  obtain ⟨F,hF⟩ := exists_contMDiffMap_forall_mem_convex_of_local planeModel hC hloc
  exact ⟨F,F.contMDiff,fun t ht => hF (P.curve t) t ht rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
