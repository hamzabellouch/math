import OAI.Geometry.Convex.GeneralMahler.LowDegree

namespace OAI
/-! Linear profile identity, first part of Eq17. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m)
theorem form_lin {l:ℝ→ℝ} (hl:TestF l) :
    q.delt l=LDel q.FL q.covMat (ps l)+ q.sigma l-
      2*q.be q.FL q.covMat (fun x=>x) (pl l) -q.be q.FL q.covMat (fl l) (fun x=>x)
      -2*q.Ct (fun x=>x) (fl l) := by
  let i := fun x:ℝ=>x
  let k := fun x:ℝ=>(1/2:ℝ)*x
  let b := pl l
  let f := fl l
  let W := q.covMat
  let A := LDel q.FL W
  have hf : TestF f := fl_test hl
  have hb : TestF b := pl_test hl
  have ht := ps_test hl
  have hi : TestF i := TestF.id
  have hk : TestF k := (TestF.const _).mul hi
  have dk : deriv k=fun _=>1/2 := by
    ext x; unfold k; convert (((hasDerivAt_id' x).const_mul (1/2:ℝ)).deriv) using 1 ; ring
  have di : deriv i=fun _=>1 := by ext; simp [i]
  have K : Nr k=i := by
    unfold Nr N; rw [dk]; ext x; unfold k i; simp; ring
  let w := prim f
  let v := prim (fun x=>b x+deriv f x*k x)
  let u := prim b
  have hw := p_test hf
  have hv := p_test (hb.add (hf.der.mul hk))
  have hu := p_test hb
  have du : deriv u=b := funext fun x=> (prim_d hb x).deriv
  have dw : deriv w=f := funext fun x=> (prim_d hf x).deriv
  have dv (x:ℝ) : deriv v x=deriv (Nr k) x*b x+deriv (Nr b) x*k x := by
    rw [K,di]
    have he := (prim_d (hb.add (hf.der.mul hk)) x).deriv
    simp only [one_mul]; exact he

  let I := fun x=> f x*x
  have ih := hf.mul hi
  have h₁ : q.Iw I-2*q.Lr.Q i f=q.Idw (ps l)-q.delt l := by
    have hh := q.eq14 hk hb hv dv
    rw [K,rightLayer.Q0_cov hb hi] at hh
    change q.Lr.Q i f-q.s0*ga (fun x=>i x*b x)=q.Idw v+q.delt _ at hh
    have hz : (fun x=>deriv k x*deriv b x) =fun x=>(1/2:ℝ)*l x := by rw [dk,show deriv b=l from pl_d hl]
    rw [hz,q.delt_scale _ hl] at hh
    have hd := q.dm_e ih
    have he : ga I=2*ga (fun x=>i x*b x) := by
      have HH : ga (fun x=>deriv b x*deriv i x) = ga (deriv b) := by rw [di]; simp
      change ga (fun x=>Nr b x*i x)=_
      rw [ga_nr_parts hb hi,HH, ← ga_parts hb]
      rw [ga_prod_comm b i]
      change ga _+ga (fun x=>i x*b x)=_
      ring
    have ht' : q.Idw (fun x=> I x-2*v x)=q.Idw (ps l) := by
      apply q.Id_ext (ih.sub ((TestF.const _).mul hv)) ht
      ext x
      have hd := ((((hf.diff x).hasDerivAt.fun_mul (hi.diff x).hasDerivAt)).fun_sub
        ((hv.diff x).hasDerivAt.const_mul 2)).deriv
      change deriv (fun x=>f x*i x-2*v x) x=_
      rw [hd,dv,K,ps_d hl,di]
      unfold f b i k fl; ring
    rw [q.Id_sub ih ((TestF.const _).mul hv),q.Id_cmul] at ht'
    change q.Idw I=q.Iw I-q.s0*ga I at hd
    rw [he] at hd; linarith
  have hh : deriv (fun x=>w x-ps l x)=deriv (fun x=>2*u x) := by
    ext x
    rw [((hw.diff x).hasDerivAt.fun_sub (ht.diff x).hasDerivAt).deriv,
      ((hu.diff x).hasDerivAt.const_mul 2).deriv,du,dw,ps_d hl]
    unfold b f; ring
  have he := L_ext q.FL W (hw.sub ht) ((TestF.const _).mul hu) hh
  rw [Delta_sub _ W hw ht,L_cmul q.FL W _ hu] at he
  have hx := q.Id_ext (hw.sub ht) ((TestF.const _).mul hu) hh
  rw [q.Id_sub hw ht,q.Id_cmul] at hx
  have hvu := q.h_weighted hu
  change etw W (q.Hmat u) = q.Idw u at hvu
  rw [q.etw16a q.FL W hu,du,q.MB_id] at hvu

  have hcov := q.eq13 hi hf Profile.id_ga (fl_ga hl)
  change KP W q.Amat (q.Hmat f)=_ at hcov
  have ho : ∀ x,deriv w x=f x*deriv i x := by rw [di,dw]; simp
  have hpa := q.f_pair16 (B:=q.FL) hf hi (fl_ga hl) hw ho
  rw [show q.FL.eval i=q.Lmat from funext q.evId,pt_sym] at hpa
  have hk := q.k_l W (q.regH hf)
  have hq := q.kpR W (q.regH hf)
  have hy := (q.sig_split hl).tsum_eq
  change Pt W q.Lmat (q.Hmat f)=q.Iw I+(A w-q.Idw w)-q.be q.FL W f i at hpa
  unfold sigma; rw [hy]
  linarith
end ProjField
end GeneralMahler

end

end OAI
