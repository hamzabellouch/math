import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleArc

namespace OAI

/-! Continue a compact smooth double arc through an actual next chart.
The chart orientation is forced by the disjointness of the two arc interiors. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3}
namespace SmoothDoubleArc

theorem append_chart (P : SmoothDoubleArc f)
    (Q : SmoothCompactArc (planeModel.prod planeModel) (M × M))
    (c : SmoothDoubleChart f) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hQ : ∀ t, Q.curve t = (c.coord.symm (s*t)).val)
    (hsource : P.lift P.arc.finish ∈ c.coord.source)
    (hstart : Q.start = s*c.coord (P.lift P.arc.finish))
    (hfinish : s*Q.finish ∈ c.coord.target)
    (hcross : ∀ u ∈ Icc P.arc.start P.arc.finish, ∀ v ∈ Ioc Q.start Q.finish,
      P.arc.curve u ≠ Q.curve v) :
    ∃ R : SmoothDoubleArc f,
      R.arc.curve '' Icc R.arc.start R.arc.finish =
        P.arc.curve '' Icc P.arc.start P.arc.finish ∪ Q.curve '' Icc Q.start Q.finish ∧
      R.lift R.arc.start = P.lift P.arc.start ∧
      R.lift R.arc.finish = c.coord.symm (s*Q.finish) := by
  have hx : P.sign*P.parameter P.arc.finish ∈ c.overlap P.tail := by
    refine ⟨P.tail_target,?_⟩
    change P.tail.coord.symm (P.sign*P.parameter P.arc.finish) ∈ c.coord.source
    rw [← P.tail_germ.eq_of_nhds]
    exact hsource
  obtain ⟨U,h,hU,hxU,hhs,hhn,hval,heq⟩ :=
    P.tail.reparameterized_transition c P.sign_eq hs P.parameter
      P.parameter_smooth P.inverse_smooth hx
  have ha : h P.arc.finish = Q.start := by
    rw [hval,← P.tail_germ.eq_of_nhds,← hstart]
  have hmatch : P.arc.curve =ᶠ[𝓝 P.arc.finish] Q.curve ∘ h := by
    filter_upwards [P.tail_germ,heq] with t ht ht'
    change P.arc.curve t = Q.curve (h t)
    rw [P.curve_eq,hQ,ht,ht']
  have hpos : 0 < deriv h P.arc.finish :=
    arc_join_deriv_pos P.arc.start_lt_finish Q.start_lt_finish
      ((hhs.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)) hhn ha hmatch hcross
  obtain ⟨A,e,hes,hei,hem,hea,hAstart,hAfinish,hAcurve,hAimage⟩ :=
    P.arc.join Q hU hhs hxU hpos ha hmatch hcross
  have hcut : P.arc.finish < A.finish := by
    rw [hAfinish]
    apply hem.lt_iff_lt.mp
    rw [e.apply_symm_apply,hea]
    exact Q.start_lt_finish
  let L : ℝ → surfaceDoublePairs f := joinedCurve P.arc.finish P.lift
    (fun t => c.coord.symm (s*e t))
  have hcurve : ∀ t, A.curve t = (L t).val := by
    intro t
    rw [hAcurve]
    dsimp only [L,joinedCurve,Function.comp_apply]
    split_ifs with ht
    · exact P.curve_eq t
    · exact hQ (e t)
  have htail : L =ᶠ[𝓝 A.finish] (fun t => c.coord.symm (s*e t)) :=
    joinedCurve_germ_right P.arc.finish P.lift (fun t => c.coord.symm (s*e t)) hcut
  have htarget : s*e A.finish ∈ c.coord.target := by
    rw [hAfinish,e.apply_symm_apply]
    exact hfinish
  let R : SmoothDoubleArc f := ⟨A,L,hcurve,c,s,hs,e,hes,hei,hem,htail,htarget⟩
  refine ⟨R,hAimage,?_,?_⟩
  · change L A.start = P.lift P.arc.start
    rw [hAstart]
    dsimp only [L,joinedCurve]
    rw [ite_eq_left P.arc.start_lt_finish.le]
  · change L A.finish = c.coord.symm (s*Q.finish)
    dsimp only [L,joinedCurve]
    rw [ite_eq_right (not_le.mpr hcut),hAfinish,e.apply_symm_apply]

end SmoothDoubleArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
