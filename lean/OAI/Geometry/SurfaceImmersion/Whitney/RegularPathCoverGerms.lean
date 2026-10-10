import OAI.Geometry.SurfaceImmersion.Whitney.FiniteRegularPathCover
import Mathlib.Topology.Order.Compact

namespace OAI

/-! An embedded finite regular path has genuine regular smooth arc germs
outside a finite set of parameter values. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y : M} {γ : Path x y}
namespace RegularPathCover

theorem region_eq_interval (P : RegularPathCover (J := J) γ) (i : P.Index)
    (hne : (P.region i).Nonempty) :
    P.region i = Icc (sInf (P.region i)) (sSup (P.region i)) := by
  apply eq_Icc_of_connected_compact
  · exact ⟨hne,(P.convex i).isPreconnected⟩
  · exact isCompact_Icc.of_isClosed_subset (P.closed i) (P.subset i)

theorem regular_germs_outside_finite (P : RegularPathCover (J := J) γ)
    (hγ : Function.Injective γ) :
    ∃ S : Set ℝ, S.Finite ∧ ∀ t ∈ Ioo (0:ℝ) 1, t ∉ S →
      ∃ (A : SmoothCompactArc J M) (a b : ℝ), a ≠ 0 ∧
        a*t+b ∈ A.domain ∧ γ.extend =ᶠ[𝓝 t] (fun u => A.curve (a*u+b)) := by
  let _ := P.finite
  let S := range (fun i => sInf (P.region i)) ∪ range (fun i => sSup (P.region i))
  refine ⟨S,(finite_range _).union (finite_range _),?_⟩
  intro t ht htS
  let tI : I := ⟨t,⟨ht.1.le,ht.2.le⟩⟩
  obtain ⟨i,hi⟩ := P.cover tI
  have heq := P.region_eq_interval i ⟨t,hi⟩
  have hti : t ∈ Ioo (sInf (P.region i)) (sSup (P.region i)) := by
    have htcc : t ∈ Icc (sInf (P.region i)) (sSup (P.region i)) := heq ▸ hi
    refine ⟨lt_of_le_of_ne htcc.1 ?_,lt_of_le_of_ne htcc.2 ?_⟩
    · intro he
      exact htS (Or.inl ⟨i,he⟩)
    · intro he
      exact htS (Or.inr ⟨i,he.symm⟩)
  have hlr : sInf (P.region i) < sSup (P.region i) := hti.1.trans hti.2
  have hlmem : sInf (P.region i) ∈ P.region i := heq.symm.subset (left_mem_Icc.mpr hlr.le)
  have hrmem : sSup (P.region i) ∈ P.region i := heq.symm.subset (right_mem_Icc.mpr hlr.le)
  let l : I := ⟨sInf (P.region i),P.subset i hlmem⟩
  let r : I := ⟨sSup (P.region i),P.subset i hrmem⟩
  have ha : P.slope i ≠ 0 := by
    intro hz
    have hsame : γ l = γ r := by rw [P.agree i l hlmem,P.agree i r hrmem,hz]; simp
    have hval := congrArg (fun u : I => (u:ℝ)) (hγ hsame)
    exact hlr.ne hval
  refine ⟨P.arc i,P.slope i,P.offset i,ha,(P.arc i).interval_subset (P.parameter i t hi),?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds hti,isOpen_Ioo.mem_nhds ht] with u hu hu01
  have humem : u ∈ P.region i := by rw [heq]; exact ⟨hu.1.le,hu.2.le⟩
  rw [Path.extend_apply γ ⟨hu01.1.le,hu01.2.le⟩]
  exact P.agree i ⟨u,⟨hu01.1.le,hu01.2.le⟩⟩ humem

end RegularPathCover
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
