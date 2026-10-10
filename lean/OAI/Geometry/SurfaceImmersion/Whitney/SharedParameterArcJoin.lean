import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc
import OAI.Geometry.SurfaceImmersion.Whitney.CornerParameterOrientation

namespace OAI

/-! Actual arc joining through two forward smooth germs of the same
underlying path parameter. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

 theorem join_shared_parameter_arcs (f : ℝ → M) (P Q : SmoothCompactArc planeModel M)
    (p q : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hdp : 0 < deriv p P.finish) (hdq : 0 < deriv q Q.start)
    (hpq : p P.finish = q Q.start)
    (hP : P.curve =ᶠ[𝓝 P.finish] f ∘ p)
    (hQ : Q.curve =ᶠ[𝓝 Q.start] f ∘ q)
    (hcross : ∀ s ∈ Icc P.start P.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.curve s ≠ Q.curve t) :
    ∃ (R : SmoothCompactArc planeModel M) (e : ℝ ≃ₜ ℝ),
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ StrictMono e ∧
      R.start = P.start ∧ R.finish = e.symm Q.finish ∧
      R.curve '' Icc R.start R.finish = P.curve '' Icc P.start P.finish ∪ Q.curve '' Icc Q.start Q.finish ∧
      R.curve R.start = P.curve P.start ∧ R.curve R.finish = Q.curve Q.finish ∧
      R.curve =ᶠ[𝓝 R.start] P.curve ∧ R.curve =ᶠ[𝓝 R.finish] Q.curve ∘ e := by
  obtain ⟨E,hEs,hEi,hEm,hEq⟩ := increasing_smooth_germ_diffeomorphism hq Q.start hdq
  let k : ℝ → ℝ := E.symm ∘ p
  have hks : ContDiff ℝ ∞ k := hEi.comp hp
  have hkvalue : k P.finish = Q.start := by
    change E.symm (p P.finish) = Q.start
    rw [hpq,← hEq.eq_of_nhds,E.symm_apply_apply]
  have hkpos : 0 < deriv k P.finish := by
    have hd := ((hEi.differentiable (by simp) (p P.finish)).hasDerivAt).comp P.finish
      ((hp.differentiable (by simp) P.finish).hasDerivAt)
    rw [hd.deriv]
    exact mul_pos (smooth_homeomorph_inverse_deriv_pos E hEs hEi hEm _) hdp
  have hkt : Tendsto k (𝓝 P.finish) (𝓝 Q.start) := by
    rw [← hkvalue]
    exact hks.continuous.continuousAt
  have hmatch : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ k := by
    filter_upwards [hP,hQ.comp_tendsto hkt,hEq.comp_tendsto hkt] with x hx hqx heqx
    dsimp only [Function.comp_apply] at heqx
    have heqp : q (k x) = p x := by
      rw [← heqx]
      exact E.apply_symm_apply (p x)
    change P.curve x = Q.curve (k x)
    dsimp only [Function.comp_apply] at hx hqx
    rw [hx,hqx,heqp]
  obtain ⟨R,e,hes,hei,hem,hea,hRs,hRf,hRc,hRi⟩ :=
    P.join Q isOpen_univ hks.contDiffOn (mem_univ _) hkpos hkvalue hmatch hcross
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
