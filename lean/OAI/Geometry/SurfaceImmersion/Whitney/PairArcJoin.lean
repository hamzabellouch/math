import OAI.Geometry.SurfaceImmersion.Correction.PairCurveSmoothParameter
import OAI.Geometry.SurfaceImmersion.Geometry.LocalParameterTransition
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc
import OAI.Geometry.SurfaceImmersion.Whitney.ArcJoinOrientation

namespace OAI

/-! Two compact regular pair arcs meeting in the actual transverse double
locus can be joined smoothly. Their disjoint interiors force the orientation. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3}

lemma compact_pair_arc_regular
    (P : SmoothCompactArc (planeModel.prod planeModel) (M × M)) {x : ℝ} (hx : x ∈ P.domain) :
    Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (P.curve t).1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (P.curve t).2) x)) := by
  have hP := P.smooth.contMDiffAt (P.domain_open.mem_nhds hx)
  have he := mfderiv_prodMk ((contMDiffAt_fst.comp x hP).mdifferentiableAt (by simp))
    ((contMDiffAt_snd.comp x hP).mdifferentiableAt (by simp))
  exact he ▸ P.regular x hx

variable [IsManifold planeModel ∞ M] [T2Space M]

theorem join_pair_arcs
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (P Q : SmoothCompactArc (planeModel.prod planeModel) (M × M))
    (p : surfaceDoublePairs f) (hp : p.val = P.curve P.finish) (hq : p.val = Q.curve Q.start)
    (hPgood : ∀ᶠ t in 𝓝 P.finish, P.curve t ∈ surfaceDoublePairs f)
    (hQgood : ∀ᶠ t in 𝓝 Q.start, Q.curve t ∈ surfaceDoublePairs f)
    (hcross : ∀ u ∈ Icc P.start P.finish, ∀ v ∈ Ioc Q.start Q.finish, P.curve u ≠ Q.curve v) :
    ∃ (R : SmoothCompactArc (planeModel.prod planeModel) (M × M)) (e : ℝ ≃ₜ ℝ),
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ StrictMono e ∧
      R.start = P.start ∧ R.finish = e.symm Q.finish ∧
      R.curve '' Icc R.start R.finish = P.curve '' Icc P.start P.finish ∪ Q.curve '' Icc Q.start Q.finish ∧
      R.curve R.start = P.curve P.start ∧ R.curve R.finish = Q.curve Q.finish ∧
      R.curve =ᶠ[𝓝 R.start] P.curve ∧ R.curve =ᶠ[𝓝 R.finish] Q.curve ∘ e := by
  obtain ⟨c,hpc⟩ := exists_smooth_double_chart hf p (hreg _ _ p.property.1 p.property.2)
  have hxP : P.finish ∈ P.domain := P.interval_subset (right_mem_Icc.mpr P.start_lt_finish.le)
  have hxQ : Q.start ∈ Q.domain := Q.interval_subset (left_mem_Icc.mpr Q.start_lt_finish.le)
  obtain ⟨U,h,hU,haU,_,hhs,hhn,hval,hPinv⟩ := c.smooth_pair_curve_parameter P.domain_open P.smooth
    hxP p hp hpc (compact_pair_arc_regular P hxP) hPgood
  obtain ⟨V,k,hV,hbV,_,hks,hkn,kval,hQinv⟩ := c.smooth_pair_curve_parameter Q.domain_open Q.smooth
    hxQ p hq hpc (compact_pair_arc_regular Q hxQ) hQgood
  obtain ⟨H,hHs,hHa,hHn,htrans⟩ := local_parameter_transition hU hV haU hbV hhs hks hhn hkn (hval.trans kval.symm)
  have hHt : Tendsto H (𝓝 P.finish) (𝓝 Q.start) := by
    rw [← hHa]
    exact (hHs.contDiffAt (hU.mem_nhds haU)).continuousAt
  have hQcomp := hQinv.comp_tendsto hHt
  have hmatch : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ H := by
    filter_upwards [hPinv,hQcomp,htrans] with t ht ht' he
    change P.curve t = Q.curve (H t)
    rw [ht,he]
    exact ht'.symm
  have hpos := arc_join_deriv_pos P.start_lt_finish Q.start_lt_finish
    ((hHs.contDiffAt (hU.mem_nhds haU)).differentiableAt (by simp)) hHn hHa hmatch hcross
  obtain ⟨R,e,hes,hei,hem,hea,hRs,hRf,hRc,hRi⟩ :=
    P.join Q hU hHs haU hpos hHa hmatch hcross
  have hcut : P.finish < R.finish := by
    rw [hRf]
    apply hem.lt_iff_lt.mp
    rw [e.apply_symm_apply,hea]
    exact Q.start_lt_finish
  have hleft : R.curve =ᶠ[𝓝 R.start] P.curve := by
    rw [hRc]
    exact joinedCurve_germ_left P.finish P.curve (Q.curve ∘ e) (hRs ▸ P.start_lt_finish)
  have hright : R.curve =ᶠ[𝓝 R.finish] Q.curve ∘ e := by
    rw [hRc]
    exact joinedCurve_germ_right P.finish P.curve (Q.curve ∘ e) hcut
  refine ⟨R,e,hes,hei,hem,hRs,hRf,hRi,?_,?_,hleft,hright⟩
  · exact hleft.eq_of_nhds.trans (congrArg P.curve hRs)
  · have heR : e R.finish = Q.finish := by rw [hRf,e.apply_symm_apply]
    exact hright.eq_of_nhds.trans (congrArg Q.curve heR)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
