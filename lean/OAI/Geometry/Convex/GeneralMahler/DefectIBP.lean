import OAI.Geometry.Convex.GeneralMahler.DefectLayer

namespace OAI
/-! Scalar layer δ integration identities (including Eq 12). -/
noncomputable section
open MeasureTheory Filter Set Real Metric
open scoped Topology ENNReal NNReal
namespace GeneralMahler
open Profile Layers
lemma rapid_ftc {f g:ℝ→ℝ} (hf:rapid f) (hd:∀ x,HasDerivAt f (g x) x) (hi:Integrable g) :
    (∫ x,g x)=0 := by
  simpa using integral_of_hasDerivAt_of_tendsto hd hi hf.tail_limit_bot hf.tail_limit
lemma MomentF.int_test {f g:ℝ→ℝ} (hf:MomentF f) (hg:TestF g) :
    Integrable fun x=> f x*g x := hf g hg.cont.measurable hg.poly
lemma N2_test {f:ℝ→ℝ} (hf:TestF f) : TestF (N2 f) :=
  ((TestF.id.mul hf.der).sub hf.der.der).add ((TestF.const 2).mul hf)
variable {m:ℕ}
namespace ProjField
variable (q:ProjField m)
def pb (x:ℝ) := p x*q.dB x
def ab (x:ℝ) := a x*q.dB x
def rk (x:ℝ) := p x*q.dr x+q.hDel x
lemma Bt_d (x:ℝ) : HasDerivAt q.Bt (-q.r1 x) x := by
  have h := (q.Bt_cd.differentiable (by norm_num)).differentiableAt (x:=x)
  simp only [r1,neg_neg]; exact h.hasDerivAt
lemma dB_d (x:ℝ) : HasDerivAt q.dB (-q.dr x) x := by
  convert ((q.Bt_d x).sub (((d_a (-x)).comp x (hasDerivAt_neg' x)).const_mul q.s0)) using 1
  all_goals first | rfl | (rw [neg_p]; unfold dr; ring)
lemma hd_d (x:ℝ) : HasDerivAt q.hDel (q.dm x) x := (q.H_deriv x).sub ((d_p x).const_mul _)
lemma dm_eq (x:ℝ) : q.dm x=q.pb x+a x*q.dr x := by
  unfold dm pb layerW dr dB
  rw [← a0_id x]; ring
lemma ab_d (x:ℝ) : HasDerivAt q.ab (q.pb x-a x*q.dr x) x := by
  convert (d_a x).mul (q.dB_d x) using 1
  all_goals first | rfl | (unfold pb; ring)
lemma pb_d (x:ℝ) : HasDerivAt q.pb (phi x*q.dB x-p x*q.dr x) x := by
  convert (d_p x).mul (q.dB_d x) using 1
  all_goals first | rfl | ring
lemma dB_c : Continuous q.dB := continuous_iff_continuousAt.mpr fun x=>(q.dB_d x).continuousAt
lemma hd_c : Continuous q.hDel := continuous_iff_continuousAt.mpr fun x=>(q.hd_d x).continuousAt

variable [NeZero m]

lemma pb_m : MomentF q.pb := .of_rapid q.pB_tail (cp.mul q.dB_c).measurable
lemma ab_m : MomentF q.ab := .of_rapid q.aB_tail (ca.mul q.dB_c).measurable
lemma hd_m : MomentF q.hDel := .of_rapid q.hd_tail q.hd_c.measurable
lemma dm_m : MomentF q.dm := by
  rw [show q.dm=_ from funext q.dm_eq]
  exact q.pb_m.add q.arDelta_moment
lemma rk_m : MomentF q.rk := q.prDelta_moment.add q.hd_m

lemma mass : (∫ x,q.pb x)=0 ∧ (∫ x,a x*q.dr x)=0 := by
  have he := rapid_ftc (f:=q.ab) q.aB_tail q.ab_d
    (q.pb_m.inte.sub q.arDelta_moment.inte)
  have hi := rapid_ftc q.hd_tail q.hd_d q.dm_m.inte
  rw [integral_sub q.pb_m.inte q.arDelta_moment.inte] at he
  simp_rw [q.dm_eq] at hi
  rw [integral_add q.pb_m.inte q.arDelta_moment.inte] at hi
  constructor <;> linarith

lemma hd_test {f:ℝ→ℝ} (hf:TestF f) :
    (∫ x,q.dm x*f x)= -(∫ x,q.hDel x*deriv f x) := by
  have h (x:ℝ) : HasDerivAt (fun x=>q.hDel x*f x) (q.dm x*f x+q.hDel x*deriv f x) x :=
    (q.hd_d x).fun_mul (hf.diff x).hasDerivAt
  have he := rapid_ftc (q.hd_tail.product hf.poly) h
    ((q.dm_m.int_test hf).add (q.hd_m.int_test hf.der))
  rw [integral_add (q.dm_m.int_test hf) (q.hd_m.int_test hf.der)] at he
  linarith

lemma eq12 {f:ℝ→ℝ} (hf:TestF f) :
    (∫ x,q.pb x*N2 f x+q.rk x*deriv f x)=0 := by
  let g := fun x=>(q.ab x+q.hDel x)*f x-q.pb x*deriv f x
  have hr : rapid g :=
    ((q.aB_tail.rfadd q.hd_tail).product hf.poly).rfsub (q.pB_tail.product hf.der.poly)
  have hd (x:ℝ) : HasDerivAt g (q.pb x*N2 f x+q.rk x*deriv f x) x := by
    convert ((((q.ab_d x).fun_add (q.hd_d x)).fun_mul (hf.diff x).hasDerivAt).fun_sub
      ((q.pb_d x).fun_mul (hf.der.diff x).hasDerivAt)) using 1
    rw [q.dm_eq]
    unfold rk N2 N ab pb a
    ring
  apply rapid_ftc hr hd
  exact (q.pb_m.int_test (N2_test hf)).add (q.rk_m.int_test hf.der)

def shiftD (f:ℝ→ℝ) := fun x=>2*x*f x-deriv f x
lemma delta_eq {f:ℝ→ℝ} (hf:TestF f) :
    q.delt f = -(2*(∫ x,q.pb x*f x)+∫ x,q.rk x*shiftD f x) := by
  have he : TestF (shiftD f) :=
    (((TestF.const 2).mul TestF.id).mul hf).sub hf.der
  have hi := q.rk_m.int_test he
  have hu : (fun x=>2*p x*q.dB x*f x)=fun x=>2*(q.pb x*f x) := by ext; unfold pb; ring
  unfold delt; simp_rw [congrFun hu]
  change -(∫ x,2*(q.pb x*f x)+q.rk x*shiftD f x)=_
  rw [integral_add,integral_const_mul]
  · exact (q.pb_m.int_test hf).const_mul _
  exact hi

lemma delta_d : q.delt Profile.d= -(∫ x,q.rk x*deriv Profile.v x) := by
  have h := q.eq12 g_test
  simp_rw [Profile.n_identity] at h
  have hi := q.pb_m.int_test Profile.d_test
  have hh := q.rk_m.int_test g_test.der
  have hv := q.rk_m.int_test v_test.der
  rw [integral_add hi hh] at h
  rw [q.delta_eq d_test]
  have he (x) : q.rk x*shiftD d x=q.rk x*deriv Profile.v x+2*(q.rk x*deriv g x) := by
    unfold shiftD; rw [(Profile.dd x).deriv]; ring
  simp_rw [he]; rw [integral_add hv (hh.const_mul _),integral_const_mul]
  linarith
end ProjField
end GeneralMahler

end

end OAI
