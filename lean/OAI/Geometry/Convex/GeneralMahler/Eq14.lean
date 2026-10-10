import OAI.Geometry.Convex.GeneralMahler.Variation
import OAI.Geometry.Convex.GeneralMahler.Contact

namespace OAI
/-! Variation identities. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler
open Profile Layers rightLayer
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)

lemma var_eq {b c:ℝ→ℝ} (hb:TestF b) (hc:TestF c) :
    q.Lr.Q (Nr b) (Nr c) - q.s0*stdL.Q (Nr b) (Nr c)=
    ∫ x,(variationK q.dr b c x+variationK q.dr c b x) := by
  have he (b c) (hb:TestF b) (hc:TestF c) :
      (∫ x,variationK q.dr b c x)= (∫ x,variationK q.Lr.r b c x)-
      q.s0*(∫ x,variationK stdL.r b c x) := by
    rw [← integral_const_mul,← integral_sub]
    · congr 1; ext x; unfold variationK dr
      change _=_-q.s0*(a x*p (-x)*_ - p x*p (-x)*_)
      simp only [Lr,neg_p]; ring
    · exact varI q.Lr.arM q.Lr.prM hb hc
    exact (varI stdL.arM stdL.prM hb hc).const_mul _
  have hi (b c) (hb:TestF b) (hc:TestF c) := varI q.arDelta_moment q.prDelta_moment hb hc
  rw [integral_add (hi _ _ hb hc) (hi _ _ hc hb),q.Lr.Q_var hb hc,stdL.Q_var hb hc,
    he _ _ hb hc,he _ _ hc hb]
  ring

lemma eq14 {b c w} (hb:TestF b) (hc:TestF c) (hw:TestF w)
    (hv:∀ x,deriv w x=deriv (Nr b) x*c x+deriv (Nr c) x*b x) :
    q.Lr.Q (Nr b) (Nr c) - q.s0*stdL.Q (Nr b) (Nr c)=
      (∫ x,q.dm x*w x)+q.delt (fun x=>deriv b x*deriv c x) := by
  let F := fun x=>b x*c x
  let H := fun x=>Nr b x*c x+Nr c x*b x
  let t := fun x=>deriv b x*deriv c x
  let J := fun x=>Nr b x*deriv c x+Nr c x*deriv b x
  have hH : TestF H := ((nr_test hb).mul hc).add ((nr_test hc).mul hb)
  have hF : TestF F := hb.mul hc
  have ht : TestF t := hb.der.mul hc.der
  have he (x:ℝ) : deriv w x=deriv H x-J x := by
    have h := ((((nr_test hb).diff x).hasDerivAt.fun_mul (hc.diff x).hasDerivAt).fun_add
      (((nr_test hc).diff x).hasDerivAt.fun_mul (hb.diff x).hasDerivAt)).deriv
    rw [hv,show deriv H x= _ from h]; unfold J; ring
  have dF (x:ℝ) : deriv F x=deriv b x*c x+b x*deriv c x :=
    ((hb.diff x).hasDerivAt.fun_mul (hc.diff x).hasDerivAt).deriv
  have hh (x:ℝ) : H x=N2 F x+2*t x := by
    have hs : deriv (deriv F) x = deriv (deriv b) x*c x+deriv b x*deriv c x+
        (deriv b x*deriv c x+b x*deriv (deriv c) x) := by
      rw [funext dF]
      exact ((((hb.der.diff x).hasDerivAt.fun_mul (hc.diff x).hasDerivAt)).fun_add
        ((hb.diff x).hasDerivAt.fun_mul (hc.der.diff x).hasDerivAt)).deriv
    unfold H N2 N Nr
    simp only [Profile.N,dF,hs]
    unfold F t; ring
  have hj (x) : J x=deriv F x+shiftD t x := by
    unfold shiftD J; rw [dF,show deriv t x=_ from ((hb.der.diff x).hasDerivAt.fun_mul (hc.der.diff x).hasDerivAt).deriv]
    unfold Nr N t; ring
  let P := fun x=> variationK q.dr b c x+variationK q.dr c b x
  let V := fun x=> q.pb x*N2 F x+q.rk x*deriv F x
  let U := fun x=> 2*(q.pb x*t x)+q.rk x*shiftD t x
  have hp (x:ℝ) : P x+q.hDel x*deriv w x+V x+U x =
      q.dm x*H x+q.hDel x*deriv H x := by
    unfold P V U variationK
    have h := he x
    rw [h,q.dm_eq]
    rw [show N2 F x=H x-2*t x by linarith [hh x],show shiftD t x=J x-deriv F x by linarith [hj x]]
    unfold J H rk
    ring
  have hz := q.eq12 hF
  have hd := q.delta_eq ht
  have hs : TestF (shiftD t) := (((TestF.const _).mul TestF.id).mul ht).sub ht.der
  have hd' : q.delt t= -(∫ x,U x) := by
    rw [hd]; unfold U; rw [integral_add,integral_const_mul]
    · exact (q.pb_m.int_test ht).const_mul _
    exact q.rk_m.int_test hs
  have iP : Integrable P := (varI q.arDelta_moment q.prDelta_moment hb hc).add
    (varI q.arDelta_moment q.prDelta_moment hc hb)
  have iV : Integrable V := (q.pb_m.int_test (N2_test hF)).add (q.rk_m.int_test hF.der)
  have iU : Integrable U := ((q.pb_m.int_test ht).const_mul _).add
    (q.rk_m.int_test hs)
  have ih := q.hd_m.int_test hw.der
  have heq : (∫ x,P x+q.hDel x*deriv w x+V x+U x) = 0 := by
    simp_rw [hp]
    rw [integral_add (q.dm_m.int_test hH) (q.hd_m.int_test hH.der),q.hd_test hH]; ring
  rw [integral_add,integral_add,integral_add iP ih] at heq
  · rw [q.var_eq hb hc,q.hd_test hw]
    change (∫ x,P x)=_+q.delt t
    rw [hd']
    change (∫ x,V x)=0 at hz
    linarith
  all_goals first | exact iP.add ih | exact iV | exact iU | exact (iP.add ih).add iV
end ProjField
end GeneralMahler

end

end OAI
