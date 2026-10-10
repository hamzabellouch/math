import OAI.Geometry.SurfaceImmersion.Whitney.FiniteRegularPathCover

namespace OAI

/-! At each interior parameter, a finite interval cover supplies actual
regular smooth pieces on both sides, including their common endpoint. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y : M} {γ : Path x y}
namespace RegularPathCover

theorem one_sided_intervals (P : RegularPathCover (J := J) γ) {t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) 1) :
    ∃ (i j : P.Index) (l r : ℝ), l < t ∧ t < r ∧
      Icc l t ⊆ P.region i ∧ Icc t r ⊆ P.region j := by
  let _ := P.finite
  have hL : ∀ᶠ u in 𝓝[<] t, ∃ i, u ∈ P.region i := by
    filter_upwards [(eventually_gt_nhds ht.1).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hu hut
    exact P.cover ⟨u,⟨hu.le,hut.le.trans ht.2.le⟩⟩
  have hR : ∀ᶠ u in 𝓝[>] t, ∃ i, u ∈ P.region i := by
    filter_upwards [(eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hu hut
    exact P.cover ⟨u,⟨ht.1.le.trans hut.le,hu.le⟩⟩
  obtain ⟨i,hi⟩ := frequently_exists.mp hL.frequently
  obtain ⟨j,hj⟩ := frequently_exists.mp hR.frequently
  have hti : t ∈ P.region i := (P.closed i).mem_of_frequently_of_tendsto hi
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  have htj : t ∈ P.region j := (P.closed j).mem_of_frequently_of_tendsto hj
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  obtain ⟨l,hli,hlt⟩ := (hi.and_eventually self_mem_nhdsWithin).exists
  obtain ⟨r,hrj,htr⟩ := (hj.and_eventually self_mem_nhdsWithin).exists
  exact ⟨i,j,l,r,hlt,htr,(P.convex i).ordConnected.out hli hti,
    (P.convex j).ordConnected.out htj hrj⟩

theorem nonzero_slope_on_interval (P : RegularPathCover (J := J) γ)
    (hγ : Function.Injective γ) (i : P.Index) {l r : ℝ}
    (hlr : l < r) (hsub : Icc l r ⊆ P.region i) : P.slope i ≠ 0 := by
  intro hz
  have hl := hsub (left_mem_Icc.mpr hlr.le)
  have hr := hsub (right_mem_Icc.mpr hlr.le)
  let lI : I := ⟨l,P.subset i hl⟩
  let rI : I := ⟨r,P.subset i hr⟩
  have he : γ lI = γ rI := by rw [P.agree i lI hl,P.agree i rI hr,hz]; simp
  have hh := congrArg (fun t : I => (t:ℝ)) (hγ he)
  exact hlr.ne hh

theorem one_sided_regular_pieces (P : RegularPathCover (J := J) γ)
    (hγ : Function.Injective γ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    ∃ (A B : SmoothCompactArc J M) (a b c d l r : ℝ),
      l < t ∧ t < r ∧ a ≠ 0 ∧ c ≠ 0 ∧
      (∀ u ∈ Icc l t, a*u+b ∈ A.domain ∧ γ.extend u = A.curve (a*u+b)) ∧
      (∀ u ∈ Icc t r, c*u+d ∈ B.domain ∧ γ.extend u = B.curve (c*u+d)) := by
  obtain ⟨i,j,l,r,hlt,htr,hL,hR⟩ := P.one_sided_intervals ht
  refine ⟨P.arc i,P.arc j,P.slope i,P.offset i,P.slope j,P.offset j,l,r,
    hlt,htr,P.nonzero_slope_on_interval hγ i hlt hL,P.nonzero_slope_on_interval hγ j htr hR,?_,?_⟩
  · intro u hu
    have humem := hL hu
    have hu01 := P.subset i humem
    refine ⟨(P.arc i).interval_subset (P.parameter i u humem),?_⟩
    rw [Path.extend_apply γ hu01]
    exact P.agree i ⟨u,hu01⟩ humem
  · intro u hu
    have humem := hR hu
    have hu01 := P.subset j humem
    refine ⟨(P.arc j).interval_subset (P.parameter j u humem),?_⟩
    rw [Path.extend_apply γ hu01]
    exact P.agree j ⟨u,hu01⟩ humem

end RegularPathCover
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
