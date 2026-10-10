import OAI.Geometry.SurfaceImmersion.Whitney.RegularPathCornerPieces

namespace OAI

/-! The first and last pieces of a finite embedded regular path give actual
regular smooth germs even at the two endpoints. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y : M} {γ : Path x y}
namespace RegularPathCover

theorem first_interval (P : RegularPathCover (J := J) γ) :
    ∃ (i : P.Index) (r : ℝ), 0 < r ∧ Icc 0 r ⊆ P.region i := by
  let _ := P.finite
  have hR : ∀ᶠ u in 𝓝[>] (0:ℝ), ∃ i, u ∈ P.region i := by
    filter_upwards [(eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hu hut
    exact P.cover ⟨u,⟨hut.le,hu.le⟩⟩
  obtain ⟨i,hi⟩ := frequently_exists.mp hR.frequently
  have h0i : (0:ℝ) ∈ P.region i := (P.closed i).mem_of_frequently_of_tendsto hi
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  obtain ⟨r,hri,hr⟩ := (hi.and_eventually self_mem_nhdsWithin).exists
  exact ⟨i,r,hr,(P.convex i).ordConnected.out h0i hri⟩

theorem last_interval (P : RegularPathCover (J := J) γ) :
    ∃ (i : P.Index) (l : ℝ), l < 1 ∧ Icc l 1 ⊆ P.region i := by
  let _ := P.finite
  have hL : ∀ᶠ u in 𝓝[<] (1:ℝ), ∃ i, u ∈ P.region i := by
    filter_upwards [(eventually_gt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hu hut
    exact P.cover ⟨u,⟨hu.le,hut.le⟩⟩
  obtain ⟨i,hi⟩ := frequently_exists.mp hL.frequently
  have h1i : (1:ℝ) ∈ P.region i := (P.closed i).mem_of_frequently_of_tendsto hi
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  obtain ⟨l,hli,hl⟩ := (hi.and_eventually self_mem_nhdsWithin).exists
  exact ⟨i,l,hl,(P.convex i).ordConnected.out hli h1i⟩

theorem first_regular_piece (P : RegularPathCover (J := J) γ)
    (hi : Function.Injective γ) :
    ∃ (A : SmoothCompactArc J M) (a b r : ℝ), 0 < r ∧ a ≠ 0 ∧
      ∀ u ∈ Icc 0 r, a*u+b ∈ A.domain ∧ γ.extend u = A.curve (a*u+b) := by
  obtain ⟨i,r,hr,hsub⟩ := P.first_interval
  refine ⟨P.arc i,P.slope i,P.offset i,r,hr,P.nonzero_slope_on_interval hi i hr hsub,?_⟩
  intro u hu
  have humem := hsub hu
  have hu01 := P.subset i humem
  refine ⟨(P.arc i).interval_subset (P.parameter i u humem),?_⟩
  rw [Path.extend_apply γ hu01]
  exact P.agree i ⟨u,hu01⟩ humem

theorem last_regular_piece (P : RegularPathCover (J := J) γ)
    (hi : Function.Injective γ) :
    ∃ (A : SmoothCompactArc J M) (a b l : ℝ), l < 1 ∧ a ≠ 0 ∧
      ∀ u ∈ Icc l 1, a*u+b ∈ A.domain ∧ γ.extend u = A.curve (a*u+b) := by
  obtain ⟨i,l,hl,hsub⟩ := P.last_interval
  refine ⟨P.arc i,P.slope i,P.offset i,l,hl,P.nonzero_slope_on_interval hi i hl hsub,?_⟩
  intro u hu
  have humem := hsub hu
  have hu01 := P.subset i humem
  refine ⟨(P.arc i).interval_subset (P.parameter i u humem),?_⟩
  rw [Path.extend_apply γ hu01]
  exact P.agree i ⟨u,hu01⟩ humem

end RegularPathCover
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
