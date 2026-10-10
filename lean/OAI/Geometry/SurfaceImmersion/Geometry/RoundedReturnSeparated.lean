import OAI.Geometry.SurfaceImmersion.Whitney.RoundedReturnArc

namespace OAI

/-! Both vertical orders of two separated graphs admit the same regular rounding. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma roundedReturnCurve_opposite_ne_of_ne {f g : ℝ → ℝ} {a b t : ℝ}
    (ht : 0 < t) (hgap : f (a+b*t^2) ≠ g (a+b*t^2)) :
    roundedReturnCurve f g a b (-t) ≠ roundedReturnCurve f g a b t := by
  intro he
  have hy := congrFun he 1
  change (1-centeredSmoothStep (-t))*f (a+b*(-t)^2)+centeredSmoothStep (-t)*g (a+b*(-t)^2) =
    (1-centeredSmoothStep t)*f (a+b*t^2)+centeredSmoothStep t*g (a+b*t^2) at hy
  rw [neg_sq] at hy
  have hn := mul_ne_zero
    (sub_ne_zero.mpr (ne_of_gt (centeredSmoothStep_opposite_lt ht)))
    (sub_ne_zero.mpr hgap.symm)
  apply hn
  nlinarith [hy]

lemma roundedReturnCurve_regular_of_ne {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {a b : ℝ} (hb : b ≠ 0) (hgap : f a ≠ g a) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) (roundedReturnCurve f g a b) t) := by
  by_cases ht : t = 0
  · subst t
    apply plane_curve_regular_of_hasDerivAt
      (roundedReturnCurve_hasDerivAt_zero (hf.differentiable (by simp) a) (hg.differentiable (by simp) a))
      (i := 1)
    exact sub_ne_zero.mpr hgap.symm
  · have hx : HasDerivAt (fun u : ℝ => a+b*u^2) (2*b*t) t := by
      convert (((hasDerivAt_id t).pow 2).const_mul b).const_add a using 1
      · rfl
      · dsimp only [id_eq]
        ring
    have hC := (roundedReturnCurve_smooth hf hg a b).differentiable (by simp) t
    have hc0 := hasDerivAt_pi.mp hC.hasDerivAt 0
    have hcoord : deriv (roundedReturnCurve f g a b) t 0 = 2*b*t := hc0.unique hx
    apply plane_curve_regular_of_hasDerivAt hC.hasDerivAt (i := 0)
    rw [hcoord]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hb) ht

lemma roundedReturnCurve_injective_of_ne {f g : ℝ → ℝ} {a b T : ℝ}
    (hb : b ≠ 0) (hgap : ∀ t ∈ Icc (-T) T, f (a+b*t^2) ≠ g (a+b*t^2)) :
    (Icc (-T) T).InjOn (roundedReturnCurve f g a b) := by
  intro s hs t ht he
  have hx := congrFun he 0
  change a+b*s^2 = a+b*t^2 at hx
  have hsq : s^2 = t^2 := by
    apply mul_left_cancel₀ hb
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
  · exact heq
  rcases lt_trichotomy 0 t with hp | hz | hn
  · exact False.elim (roundedReturnCurve_opposite_ne_of_ne hp (hgap _ ht) (heq ▸ he))
  · simpa only [← hz,neg_zero] using heq
  · have hps : 0 < s := by linarith
    apply False.elim
    apply roundedReturnCurve_opposite_ne_of_ne hps (hgap _ hs)
    have hts : t = -s := by linarith
    simpa only [hts] using he.symm

theorem rounded_return_arc_of_ne {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {a b : ℝ} (hb : b ≠ 0)
    (hgap : ∀ t ∈ Icc (-2:ℝ) 2, f (a+b*t^2) ≠ g (a+b*t^2)) :
    ∃ P : SmoothCompactArc 𝓘(ℝ,Base) Base,
      P.start = -2 ∧ P.finish = 2 ∧ P.curve = roundedReturnCurve f g a b ∧
      P.curve =ᶠ[𝓝 P.start] (fun t => ![a+b*t^2,f (a+b*t^2)]) ∧
      P.curve =ᶠ[𝓝 P.finish] (fun t => ![a+b*t^2,g (a+b*t^2)]) := by
  have hgap0 : f a ≠ g a := by simpa using hgap 0 (by norm_num)
  let P : SmoothCompactArc 𝓘(ℝ,Base) Base :=
    ⟨roundedReturnCurve f g a b,-2,2,by norm_num,univ,isOpen_univ,subset_univ _,
      (roundedReturnCurve_smooth hf hg a b).contMDiff.contMDiffOn,
      fun t _ => roundedReturnCurve_regular_of_ne hf hg hb hgap0 t,
      roundedReturnCurve_injective_of_ne hb hgap⟩
  refine ⟨P,rfl,rfl,rfl,?_,?_⟩
  · filter_upwards [eventually_lt_nhds (show (-2:ℝ) < -1 by norm_num)] with t ht
    exact roundedReturnCurve_left ht.le
  · filter_upwards [eventually_gt_nhds (show (1:ℝ) < 2 by norm_num)] with t ht
    exact roundedReturnCurve_right ht.le

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
