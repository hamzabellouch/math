import OAI.Geometry.Convex.GeneralMahler.ScalarForm
import OAI.Geometry.Convex.GeneralMahler.Eq13

namespace OAI
/-! §04 profile quadratic identity. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ} [NeZero m]

namespace ProjField
omit [NeZero m] in
lemma tw_add {B:FieldMat m} {f j:ℝ→ℝ} (W:Mat m) (hf:TestF f) (hj:TestF j) :
    LDel B W (fun x=> f x+j x)=LDel B W f+LDel B W j := by
  have h : (fun x=> f x) = fun x=> (f x+j x)-j x := by ext; ring
  have he := Delta_sub B W (hf.add hj) hj
  rw [← h] at he; linarith

variable (q:ProjField m)

lemma evId (x:Rn m) : q.FL.eval (fun x=> x) x=q.Lmat x := by
  unfold FieldMat.eval
  rw [cfc_id' ℝ _ (show IsSelfAdjoint (q.FL.A x) from q.FL.sym x)]; rfl

lemma Pb_sq {l} (hl:TestF l) (W:Mat m) :
    Pt W (q.FL.eval l) (q.FL.eval l)=etw W (q.FL.eval (fun x=>l x*l x)) := by
  unfold Pt Pj etw et
  have he (A:Mat m): jprod A A=A*A := by unfold jprod; module
  simp_rw [he,FieldMat.eval_mul _ hl hl]

lemma form_sq {l} (hl:TestF l) :
    q.Dnorm l+q.Jtest q.covMat l =
      q.delt (fun z=>l z^2)-LDel q.FL q.covMat (ps (fun z=> l z^2))+
      2*q.be q.FL q.covMat (fl l) (pl l)+q.Ct (fl l) (fl l) := by
  let f := fl l
  let b := pl l
  let h := fun x=>l x^2
  let W := q.covMat
  have hf : TestF f := fl_test hl
  have hb : TestF b := pl_test hl
  have ht : TestF h := by simp_rw [h,pow_two]; exact hl.mul hl
  let w := prim (fun x=>f x*deriv b x)
  let v := prim (fun x=>deriv f x*b x+deriv f x*b x)
  have hw := p_test (hf.mul hb.der)
  have hv := p_test ((hf.der.mul hb).add (hf.der.mul hb))
  have dw (x) : deriv w x=f x*deriv b x := (prim_d (hf.mul hb.der) x).deriv
  have dv (x) : deriv v x=deriv (Nr b) x*b x+deriv (Nr b) x*b x :=
    (prim_d ((hf.der.mul hb).add (hf.der.mul hb)) x).deriv
  let F := fun x=>b x*b x+x*pl h x
  have Ht := pl_test ht
  have HI := TestF.id.mul Ht
  have HB := hb.mul hb
  have FF : TestF F := HB.add HI
  let L := LDel q.FL W

  have hd1 : q.Idw (fun x=>v x-2*(f x*b x)) = q.Idw (fun x=> -(2*w x)) := by
    apply Id_ext _ (hv.sub ((TestF.const _).mul (hf.mul hb))) (((TestF.const _).mul hw).neg)
    funext x
    have hx := ((hf.diff x).hasDerivAt.fun_mul (hb.diff x).hasDerivAt).const_mul 2
    have he := (((hv.diff x).hasDerivAt).fun_sub hx).deriv
    have hh : deriv (fun x=> -(2*w x)) x= -(2*deriv w x) :=
      (((hw.diff x).hasDerivAt.const_mul 2).neg).deriv
    rw [he,hh,dv,dw]
    change _+_-_=_; dsimp only [f,fl,b]; ring
  have IdH : q.Idw v-2*q.Idw (fun x=>f x*b x) = - (2*q.Idw w) := by
    have ha : (fun x=> -(2*w x))=fun x=> -2*w x := by ext; ring
    rw [q.Id_sub hv ((TestF.const _).mul (hf.mul hb)), q.Id_cmul, ha, q.Id_cmul] at hd1
    linarith

  have hd2 : L (fun x=>F x-2*w x)= L (fun x=> - (ps h x)) := by
    apply L_ext _ _ (FF.sub ((TestF.const _).mul hw)) (ps_test ht).neg
    funext x
    have he := (((((hb.diff x).hasDerivAt).fun_mul (hb.diff x).hasDerivAt).fun_add
      ((hasDerivAt_id' x).fun_mul (Ht.diff x).hasDerivAt)).fun_sub
      ((hw.diff x).hasDerivAt.const_mul 2)).deriv
    have HH : deriv (fun x=> -ps h x) x= -deriv (ps h) x :=
      (((ps_test ht).diff x).hasDerivAt.neg).deriv
    change deriv (fun x=>F x-2*w x) x=_ at he
    rw [he,HH,dw,ps_d ht x]
    unfold f fl Nr N b
    simp only [pl_d ht,pl_d hl]
    have hi : deriv h x= deriv l x*l x + l x*deriv l x := by
      unfold h; simp_rw [pow_two]
      exact ((hl.diff x).hasDerivAt.fun_mul (hl.diff x).hasDerivAt).deriv
    rw [hi]
    unfold h; ring
  have LdH : L F-2*L w= -L (ps h) := by
    have he : (fun x=> -ps h x) = fun x=> (-1)*ps h x := by ext; ring
    unfold L at *
    rw [Delta_sub _ _ FF ((TestF.const _).mul hw),L_cmul _ _ _ hw,he,
      L_cmul _ _ _ (ps_test ht)] at hd2
    linarith

  have hgas : ga F=ga (fun x=> f x*b x) := by
    have hh := ga_parts Ht
    rw [pl_d ht] at hh
    unfold F; rw [ga_add HB HI,hh, show f=Nr b from rfl,
      ga_nr_parts hb hb,show deriv b=l from pl_d hl]
    simp_rw [h,pow_two]

  have heq := q.eq14 hb hb hv dv
  rw [rightLayer.Q0_cov hb (nr_test hb)] at heq
  have hu : (fun x=>deriv b x*deriv b x)=h := by simp only [b,pl_d hl,h,pow_two]
  rw [hu] at heq
  change q.Lr.Q f f-q.s0*ga (fun x=>f x*b x)=q.Idw v+q.delt h at heq
  have hi : Pt W (q.FL.eval b) (q.FL.eval b)+
      etw W (fun x=> q.Lmat x*q.FL.eval (pl h) x) = L F + q.s0*ga F := by
    have he (x) : q.Lmat x*q.FL.eval (pl h) x=q.FL.eval (fun x=> x*pl h x) x := by
      rw [FieldMat.eval_mul q.FL TestF.id Ht,q.evId]
    rw [Pb_sq q hb]; simp_rw [he]; rw [L_formula _ W HB,L_formula _ W HI]
    unfold L F; rw [tw_add W HB HI, ga_add HB HI]; change _=_
    rw [show trN W=q.s0 from rfl]; ring
  have hg := fl_ga hl
  have hcov := q.eq13 hf hf hg hg
  have hpa := q.f_pair16 q.FL hf hb hg hw dw
  have hk := q.dm_e (hf.mul hb)
  have h1 := (q.H_K_split hl).tsum_eq
  change q.Dnorm l= _ at h1
  unfold Jtest
  change q.Dnorm _+ (_-q.dirF W l) = q.delt h-L (ps h)+2*q.be q.FL W f b+q.Ct f f
  change Pt W _ _=q.Iw (fun x=>f x*b x)+(L w-q.Idw w)-q.be q.FL W f b at hpa
  rw [hgas] at hi; rw [h1]; dsimp only [W,h,f,b] at *; linarith
end ProjField
end GeneralMahler

end

end OAI
