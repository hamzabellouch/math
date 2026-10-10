import OAI.Geometry.Convex.GeneralMahler.Eq18

namespace OAI
/-! Parity of Gaussian fields and coefficient projections. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

lemma map_deriv_odd {f:ℝ→ℝ} (hf:TestF f) (h:Function.Odd f) :
    Function.Even (deriv f) := by
  intro x
  have hh := ((hf.diff (-x)).hasDerivAt.comp x (hasDerivAt_neg' x))
  have he : f ∘ (fun x:ℝ=> -x)= -f := funext h
  rw [he] at hh
  have hi := hh.unique ((hf.diff x).hasDerivAt.neg)
  linarith
lemma map_deriv_even {f:ℝ→ℝ} (hf:TestF f) (h:Function.Even f) :
    Function.Odd (deriv f) := by
  intro x
  have hh := ((hf.diff (-x)).hasDerivAt.comp x (hasDerivAt_neg' x))
  have he : f ∘ (fun x:ℝ=> -x)= f := funext h
  rw [he] at hh
  have hi := hh.unique (hf.diff x).hasDerivAt; linarith

lemma pl_odd (f:ℝ→ℝ) (hf:TestF f) (hh:Function.Even f) :
    Function.Odd (pl f) := by
  have h : Function.Odd (prim f) := by
    intro x
    let g := fun y=>prim f (-y)+prim f y
    have he (t:ℝ) : HasDerivAt g 0 t := by
      convert (((prim_d hf (-t)).comp t (hasDerivAt_neg' t)).add (prim_d hf t)) using 1
      all_goals first | rfl | (rw [hh]; ring)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => he z)
      (continuous_const.intervalIntegrable 0 x)
    simp only [intervalIntegral.integral_zero,g,neg_zero,show prim f 0=0 from by simp [prim] ] at h
    linarith
  have he : ga (prim f)=0 := by
    let g := fun x=>phi x*prim f x
    have ht : (fun x:ℝ=>g (-x))=fun x=> -g x := by ext x; unfold g; rw [h,neg_phi]; ring
    have hi := integral_neg_eq_self g volume
    rw [ht,integral_neg] at hi; change (∫ x,g x)=0; linarith
  intro x; rw [pl,pl,h,he]; ring
lemma fl_odd (f:ℝ→ℝ) (hf:TestF f) (h:Function.Even f) :
    Function.Odd (fl f) := by
  let b:= pl f
  have h' := pl_test hf
  have hh := pl_odd f hf h
  have hv := map_deriv_odd h' hh
  intro x; unfold fl Nr N
  rw [hh,hv,map_deriv_even h'.der hv]; ring
lemma Hneg (n:ℕ) : ∀ x,H n (-x)=(-1)^n*H n x := by
  induction n with
  | zero=> simp [H]
  | succ n ih=>
    intro x
    have he : H n ∘ (fun x:ℝ=> -x)=fun x=> (-1)^n*H n x := funext ih
    have h := ((ht n).diff (-x)).hasDerivAt.comp x (hasDerivAt_neg' x)
    rw [he] at h
    have hh := h.unique (((ht n).diff x).hasDerivAt.const_mul ((-1)^n))
    simp only [H,ih,pow_succ]
    have hb : deriv (H n) (-x)= -((-1)^n*deriv (H n) x) := by linarith
    rw [hb]; ring
lemma MMneg (a:MI m) (x:Rn m) : MM a (-x)=(-1)^(deg a)*MM a x := by
  unfold MM
  simp only [show ∀ i:Fin m,(-x) i= -(x i) from fun _=>rfl,Hneg,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,deg]

namespace ProjField
variable (q:ProjField m)
lemma Lneg (x:Rn m) : q.Lmat (-x) = -q.Lmat x := by simp_rw [← q.ell_eq,_root_.map_neg]

section
variable [NeZero m]

lemma BoEval {f:ℝ→ℝ} (hf:Function.Odd f) :
    Function.Odd (q.FL.eval f) := by
  intro x
  let B:=q.FL
  let u:= B.Fr x
  have he : B.A (-x)= -B.A x := q.Lneg x
  have hu : u.loc (B.A (-x))= -u.loc (B.A x) := by
    rw [he]; simp [Frm.loc]
  have h (i): u.eig (B.A (-x)) i= -u.eig (B.A x) i := by unfold Frm.eig; rw [hu]; rfl
  have ht : u.Dgn (B.A (-x)) := by
    unfold Frm.Dgn
    rw [hu,show u.loc (B.A x)=_ from B.Fr_D x]
    ext i j; by_cases hh:i=j
    · subst j; simp [h]; rfl
    simp [hh]
  apply u.loc_inj
  change u.loc (cfc f (B.A (-x)))=u.loc (-cfc f (B.A x))
  rw [show u.loc (-cfc f (B.A x)) = -u.loc (cfc f (B.A x)) from by simp [Frm.loc],
    u.loc_cfc (B.sym x) (B.Fr_D x),u.loc_cfc (B.sym (-x)) ht]
  ext i j
  by_cases hi:i=j
  · subst j; simp [h]; apply hf
  simp [hi]

end

lemma cf_ref (f:Rn m→Mat m) (a:MI m) :
    cof (fun x=>f (-x)) a=(-1:ℝ)^(deg a) • cof f a := by
  unfold cof
  rw [← integral_smul,normal_integral,normal_integral]; rw [← integral_neg_eq_self (fun x=> nDensity x • MM a x • f (-x)) volume]; simp_rw [MMneg,mul_smul,neg_neg,nDensity,norm_neg]
lemma cf_s (f:Rn m→Mat m) (a:MI m) (c:ℝ) :
    cof (fun x=>c • f x) a=c • cof f a := by
  unfold cof; rw [← integral_smul]; congr 1; funext x; rw [smul_comm]
lemma cof_odd_zero (f:Rn m→Mat m) (a:MI m) (he:Even (deg a)) (hh:Function.Odd f) :
    cof f a=0 := by
  have hi : (fun x=>f (-x))= fun x=> (-1:ℝ) • f x := funext fun x=>by rw [hh];simp
  have ht := cf_ref f a
  rw [hi,cf_s, he.neg_one_pow] at ht
  simp only [neg_smul,one_smul] at ht
  ext i j
  have hi := congrFun (congrFun ht i) j
  change - (cof f a i j)=_ at hi; change _=0
  linarith
variable [NeZero m]

def Ro (x:Rn m) := (1/2:ℝ) • (q.RR x-q.RR (-x))
lemma re_ref : regular fun x=>q.RR (-x) := ⟨q.R_reg.p.comp PolyBound.id.neg,by
  have he : StronglyMeasurable q.RR := q.A_SM.sub q.L_cont.stronglyMeasurable
  exact (he.comp_measurable measurable_neg).aestronglyMeasurable⟩
lemma Ro_reg : regular q.Ro :=
  (show regular (fun x=>q.RR x-q.RR (-x)) from ⟨q.R_reg.p.sub q.re_ref.p,
    q.R_reg.meas.sub q.re_ref.meas⟩).smul ⟨PolyBound.const _,aestronglyMeasurable_const⟩
lemma coRo (a:MI m) :
    cof q.Ro a= if Even (deg a) then 0 else cof q.RR a := by
  change cof (fun x=>(_ : ℝ) • _) a=_
  rw [cf_s,cof_subm q.R_reg q.re_ref,cf_ref]
  split_ifs with hh
  · simp [hh.neg_one_pow]
  have he : Odd (deg a) := Nat.not_even_iff_odd.mp hh
  rw [he.neg_one_pow]; module

lemma bal_cf (h:q.avgA=0) (a:MI m) (hd:deg a < 2) : cof q.RR a=0 := by
  unfold RR
  rw [cof_subm q.a_reg q.l_reg]
  by_cases hh:a=0
  · subst a; rw [q.coL_o (by simp [deg])]
    unfold cof; simp_rw [Mzero]; simp only [one_smul,sub_zero]; exact h
  obtain ⟨i,hi⟩ : ∃ i,a i≠0 := by by_contra! hb; exact hh (funext hb)
  set b := decM a i
  have he : a=inc b i := (inc_dec a i hi).symm
  have hb : b=0 := by
    rw [he,deg_inc] at hd
    apply (dz b).mp; omega
  rw [hb] at he
  rw [he,q.coL]
  have ht : cof q.Amat (inc 0 i)=q.M i := by
    unfold cof; simp_rw [Mi1]; rfl
  rw [ht,Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp
  intro j hj hj'
  have hh : inc (0:MI m) i≠ inc 0 j := by
    intro hi
    have he := congrFun hi i
    simp [inc, Ne.symm hj'] at he
  simp [hh]
end ProjField
end GeneralMahler

end

end OAI
