import Mathlib.Topology.Algebra.Polynomial
import OAI.MathematicalPhysics.Transonic.Exterior.WindowSound
import OAI.MathematicalPhysics.Transonic.Shooting.AxisBarriersCore

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorPolynomial
open Set Polynomial AxisBarriers
open scoped ContDiff

def segmentField (sigma kappa d : ℝ) (p : ℝ×ℝ) : ℝ :=
  (d/256)*N kappa (1+d/256*p.1) p.2/D sigma (1+d/256*p.1) p.2

lemma window_D_neg {sigma kappa d : ℝ} {u : PowerSeries ℝ}
    (W : AdmissibleWindow sigma kappa d u) (hs : 0 ≤ sigma)
    {x v : ℝ} (hx : x∈Icc (0:ℝ) 1) (hv : 1<v) : D sigma (1+d/256*x) v<0 := by
  have hh : 0<d/256 := by exact div_pos W.dpos (by norm_num)
  have hz : 1≤1+d/256*x := by nlinarith [mul_nonneg hh.le hx.1]
  have hz1 : 1+d/256*x≤1+d/256 := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hx.2)]
  have hs1 : sigma*(1+d/256*x)^2<1 := by
    have hsq : (1+d/256*x)^2≤(1+d/256)^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hsq hs).trans_lt W.subsonic
  exact mul_neg_of_pos_of_neg (mul_pos (by linarith) (by linarith)) (by nlinarith)

lemma segment_smooth {sigma kappa d a c q : ℝ} {u : PowerSeries ℝ}
    (W : AdmissibleWindow sigma kappa d u) (hs : 0 ≤ sigma)
    (ha : 0≤a) (hc : 1<c) :
    ContDiffOn ℝ ∞ (segmentField sigma kappa d) (Icc a 1 ×ˢ Icc c q) := by
  intro p hp
  have hn : D sigma (1+d/256*p.1) p.2≠0 :=
    ne_of_lt (window_D_neg W hs ⟨ha.trans hp.1.1,hp.1.2⟩ (hc.trans_le hp.2.1))
  apply ContDiffAt.contDiffWithinAt
  unfold segmentField N D at *
  fun_prop

lemma window_lower_strict {sigma kappa d : ℝ} {u : PowerSeries ℝ}
    (W : AdmissibleWindow sigma kappa d u) (hs : 0 ≤ sigma)
    {x : ℝ} (hx : x∈Ioc (0:ℝ) 1) :
    deriv (fun x => (lowerPoly u d).eval x) x <
      segmentField sigma kappa d (x,(lowerPoly u d).eval x) := by
  have hd := window_D_neg W hs ⟨hx.1.le,hx.2⟩ (W.range x hx).1
  have hr := W.strict x hx
  rw [show -d/256=-(d/256) by ring,eval_residual_lower (d/256) sigma kappa (3/5)] at hr
  have hr' : 0<D sigma (1+d/256*x) ((lowerPoly u d).eval x)*
    deriv (fun x => (lowerPoly u d).eval x) x-
    (d/256)*N kappa (1+d/256*x) ((lowerPoly u d).eval x) := by
      simpa only [D,N,lowerPoly,mul_assoc] using hr
  change _ < _ / D sigma (1+d/256*x) ((lowerPoly u d).eval x)
  apply (lt_div_iff_of_neg hd).mpr
  linarith

lemma exists_window_segment {sigma kappa d a u0 : ℝ} {u : PowerSeries ℝ}
    (W : AdmissibleWindow sigma kappa d u) (hs : 0 ≤ sigma)
    (ha : 0<a) (ha1 : a≤1)
    (hstart : (lowerPoly u d).eval a≤u0) (hu0 : u0<Real.sqrt (5/3)) :
    ∃ v : ℝ → ℝ, v a=u0 ∧ ContinuousOn v (Icc a 1) ∧
      (∀ x∈Icc a 1, (lowerPoly u d).eval x≤v x ∧ v x<Real.sqrt (5/3)) ∧
      ∀ x∈Icc a 1, HasDerivWithinAt v (segmentField sigma kappa d (x,v x)) (Icc a 1) x := by
  let P := lowerPoly u d
  obtain ⟨xm,hxm,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr ha1) P.continuous.continuousOn
  have hxm0 : 1<P.eval xm := (W.range xm ⟨ha.trans_le hxm.1,hxm.2⟩).1
  let c := (1+P.eval xm)/2
  have hc : 1<c := by dsimp [c];linarith
  have hq : (6/5:ℝ)<Real.sqrt (5/3) := by
    have he := Real.sq_sqrt (by norm_num : (0:ℝ)≤5/3)
    have hn := Real.sqrt_nonneg (5/3:ℝ)
    nlinarith
  have hct : c≤Real.sqrt (5/3) := by
    have hm := (W.range xm ⟨ha.trans_le hxm.1,hxm.2⟩).2
    dsimp [c];linarith
  apply RegularContinuation.exists_between_lower_equilibrium ha1 hct
    ((segment_smooth W hs ha.le hc).of_le (by norm_num))
    (fun x => P.eval x) (fun x => P.derivative.eval x)
    (fun x _ => P.hasDerivAt x) ?_ ?_ ?_ hstart hu0
  · intro x hx
    have hm := hmin hx
    have hr := W.range x ⟨ha.trans_le hx.1,hx.2⟩
    dsimp [c] at *
    exact ⟨by linarith,hr.2.le.trans hq.le⟩
  · intro x hx
    simpa only [Polynomial.deriv] using window_lower_strict W hs ⟨ha.trans_le hx.1,hx.2⟩
  · intro x hx
    have he := Real.sq_sqrt (by norm_num : (0:ℝ)≤5/3)
    unfold segmentField N
    rw [he]
    norm_num

end SepticProfile.ExteriorPolynomial

end
end

end OAI
