import OAI.Geometry.SurfaceImmersion.Correction.CenteredSmoothStep

namespace OAI

/-! An explicit embedded U-turn between disjoint graph branches. It is
flatly equal to the lower and upper graphs at the two ends. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def roundedReturnCurve (f g : ℝ → ℝ) (a b t : ℝ) : Base :=
  ![a+b*t^2,(1-centeredSmoothStep t)*f (a+b*t^2)+centeredSmoothStep t*g (a+b*t^2)]

lemma roundedReturnCurve_smooth {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (a b : ℝ) : ContDiff ℝ ∞ (roundedReturnCurve f g a b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun t : ℝ => a+b*t^2)
    fun_prop
  · change ContDiff ℝ ∞ (fun t : ℝ =>
      (1-centeredSmoothStep t)*f (a+b*t^2)+centeredSmoothStep t*g (a+b*t^2))
    exact ((contDiff_const.sub centeredSmoothStep_smooth).mul (hf.comp (by fun_prop))).add
      (centeredSmoothStep_smooth.mul (hg.comp (by fun_prop)))

lemma roundedReturnCurve_left {f g : ℝ → ℝ} {a b t : ℝ} (ht : t ≤ -1) :
    roundedReturnCurve f g a b t = ![a+b*t^2,f (a+b*t^2)] := by
  simp [roundedReturnCurve,centeredSmoothStep_zero ht]

lemma roundedReturnCurve_right {f g : ℝ → ℝ} {a b t : ℝ} (ht : 1 ≤ t) :
    roundedReturnCurve f g a b t = ![a+b*t^2,g (a+b*t^2)] := by
  simp [roundedReturnCurve,centeredSmoothStep_one ht]

lemma roundedReturnCurve_coordinate_bound {f g : ℝ → ℝ} {a b T t : ℝ}
    (hb : 0 ≤ b) (ht : t ∈ Icc (-T) T) :
    (roundedReturnCurve f g a b t) 0 ∈ Icc a (a+b*T^2) := by
  change a+b*t^2 ∈ Icc a (a+b*T^2)
  have hsq : t^2 ≤ T^2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ T+t by linarith [ht.1])
    nlinarith
  constructor
  · nlinarith [mul_nonneg hb (sq_nonneg t)]
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hb)

lemma roundedReturnCurve_opposite_ne {f g : ℝ → ℝ} {a b t : ℝ}
    (ht : 0 < t) (hgap : f (a+b*t^2) < g (a+b*t^2)) :
    roundedReturnCurve f g a b (-t) ≠ roundedReturnCurve f g a b t := by
  intro he
  have hy := congrFun he 1
  change (1-centeredSmoothStep (-t))*f (a+b*(-t)^2)+centeredSmoothStep (-t)*g (a+b*(-t)^2) =
    (1-centeredSmoothStep t)*f (a+b*t^2)+centeredSmoothStep t*g (a+b*t^2) at hy
  rw [neg_sq] at hy
  have hp := mul_pos (sub_pos.mpr (centeredSmoothStep_opposite_lt ht)) (sub_pos.mpr hgap)
  nlinarith

theorem roundedReturnCurve_injective {f g : ℝ → ℝ} {a b T : ℝ}
    (hb : 0 < b) (hgap : ∀ x ∈ Icc a (a+b*T^2), f x < g x) :
    (Icc (-T) T).InjOn (roundedReturnCurve f g a b) := by
  intro s hs t ht he
  have hx := congrFun he 0
  change a+b*s^2 = a+b*t^2 at hx
  have hsq : s^2 = t^2 := by nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
  · exact heq
  rcases lt_trichotomy 0 t with hp | hz | hn
  · have hgap' := hgap _ (roundedReturnCurve_coordinate_bound (f := f) (g := g) hb.le ht)
    exact False.elim (roundedReturnCurve_opposite_ne hp hgap' (heq ▸ he))
  · simpa only [← hz,neg_zero] using heq
  · have hps : 0 < s := by linarith
    have hgap' := hgap _ (roundedReturnCurve_coordinate_bound (f := f) (g := g) hb.le hs)
    apply False.elim
    apply roundedReturnCurve_opposite_ne hps hgap'
    have hts : t = -s := by linarith
    simpa only [hts] using he.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
