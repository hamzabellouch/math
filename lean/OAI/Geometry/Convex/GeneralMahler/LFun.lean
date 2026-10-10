import OAI.Geometry.Convex.GeneralMahler.BiWeight

namespace OAI
/-! ℒ evaluation; linearity and spectral form. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

lemma Bwt.indef {f:Plane→ℝ} (hf:Bwt f) : Bwt (bInt f) := by
  rw [show bInt f=_ from funext hf.bar_eq]
  apply Bwt.mul _ hf.bar
  exact (Bwt.snd TestF.id).sub (Bwt.fst TestF.id)

namespace FieldMat
variable (B:FieldMat m)
def bmat (f:Plane→ℝ) (z:ℝ) (x:Rn m) := B.eval (fun y=>f (z,y)) x
omit [NeZero m] in
lemma bmat_loc (f:Plane→ℝ) (z x) :
    (B.Fr x).loc (B.bmat f z x)=Matrix.diagonal (fun i=>f (z,B.ev x i)) := B.evfrm ..

omit [NeZero m] in
lemma bsmb {f:Plane→ℝ} (hf:Bwt f) :
    StronglyMeasurable (B.bmat f).uncurry :=
  (B.theta_gen_meas (f:=fun x y=>f (x,y)) (by exact hf.c.measurable)).stronglyMeasurable
lemma p_bmat {f:Plane→ℝ} (hf:Bwt f) :
    PolyBound (B.bmat f).uncurry := by
  let u := fun w:ℝ×Rn m=> B.Fr w.2
  let D := fun w:ℝ×Rn m=>Matrix.diagonal (fun i=>f (w.1,B.ev w.2 i))
  have he (w:ℝ×Rn m): (B.bmat f).uncurry w=(u w).val*D w*star (u w).val :=
    B.evfrm' w.2 _
  rw [funext he]
  have hp : PolyBound D := by
    apply mat_poly
    intro i j
    have hg : PolyBound (fun w:ℝ×Rn m=> f (w.1,B.ev w.2 i)) :=
      hf.p.comp (PolyBound.fst.prodMk
        ((poly_eig B.poly B.Fr i).comp PolyBound.snd))
    by_cases hi:i=j
    · subst j; simpa only [D,Matrix.diagonal_apply_eq] using hg
    · unfold D; simp_rw [Matrix.diagonal_apply_ne _ hi]; exact PolyBound.const _
  exact ((unitPoly u).mul hp).mul (unitStarPoly u)
end FieldMat

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)
def lk (f:Plane→ℝ) (z:ℝ) (x:Rn m) :=
  Pj W (q.EZ B z x) (B.bmat (bInt f) z x)
def LLw (f:Plane→ℝ) :=
  ∫ x,(∫ z,q.lk B W f z x) ∂normal m

lemma lkMS {f} (hf:Bwt f) :
    mixed (q.lk B W f) ∧ StronglyMeasurable (q.lk B W f).uncurry := by
  have he := pj_M W (q.eM B) (B.p_bmat hf.indef)
  have hh := (pj_cont W).comp_stronglyMeasurable ((q.eSM B).prodMk (B.bsmb hf.indef))
  exact ⟨he,hh⟩
lemma lk_slice_i {f} (hf:Bwt f) (x) : Integrable fun z=>q.lk B W f z x := by
  have he := q.lkMS B W hf
  exact mixed_integrable_left he.1 x
    ((he.2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
lemma Lbar_i {f} (hf:Bwt f) : Integrable (fun x=>∫ z,q.lk B W f z x) (normal m) := by
  have he := q.lkMS B W hf
  exact (mixed_integrable (μ:=volume) (ν:=normal m) he.1 he.2.aestronglyMeasurable).integral_prod_right

omit [NeZero m] in
lemma lk_add {f g} (hf:Bwt f) (hg:Bwt g) (z x) :
    q.lk B W (fun u=>f u+g u) z x=q.lk B W f z x + q.lk B W g z x := by
  unfold lk; simp_rw [← pJ_eq]
  have he (u:Plane) : bInt (fun u=>f u+g u) u=bInt f u+bInt g u :=
    intervalIntegral.integral_add ((hf.c.comp (continuous_const.prodMk continuous_id)).intervalIntegrable ..)
      ((hg.c.comp (continuous_const.prodMk continuous_id)).intervalIntegrable ..)
  have hh : B.bmat (bInt (fun u=>f u+g u)) z x=B.bmat (bInt f) z x+B.bmat (bInt g) z x := by
    apply (B.Fr x).loc_inj; rw [Frm.loc_add,B.bmat_loc,B.bmat_loc,B.bmat_loc]
    ext i j
    by_cases h:i=j
    · subst j; simp [he]
    simp [h]
  rw [hh,_root_.map_add]
lemma Lbar_add {f g} (hf:Bwt f) (hg:Bwt g) :
    q.LLw B W (fun u=>f u+g u)=q.LLw B W f+q.LLw B W g := by
  unfold LLw; simp_rw [q.lk_add B W hf hg, integral_add (q.lk_slice_i B W hf _) (q.lk_slice_i B W hg _)]
  rw [integral_add (q.Lbar_i B W hf) (q.Lbar_i B W hg)]
omit [NeZero m] in
lemma Lbar_scale (f:Plane→ℝ) (a:ℝ) :
    q.LLw B W (fun u=>a*f u)=a*q.LLw B W f := by
  have he (x) : bInt (fun u=>a*f u) x=a*bInt f x := by unfold bInt; rw [intervalIntegral.integral_const_mul]
  have hp (z x) : B.bmat (bInt (fun u=>a*f u)) z x=a • B.bmat (bInt f) z x := by
    apply (B.Fr x).loc_inj; rw [Frm.loc_smul,B.bmat_loc,B.bmat_loc]
    ext i j; by_cases h:i=j
    · subst j; simp [he]
    simp [h]
  unfold LLw lk
  simp_rw [hp,← pJ_eq,_root_.map_smul,smul_eq_mul,integral_const_mul]

lemma Lbar_sub {f g} (hf:Bwt f) (hg:Bwt g) :
    q.LLw B W (fun u=>f u-g u)=q.LLw B W f-q.LLw B W g := by
  have he : f=fun u=>f u-g u+g u := by funext u; ring
  have hh := q.Lbar_add B W (hf.sub hg) hg
  rw [← he] at hh
  linarith

omit [NeZero m] in
lemma Le_id {f j} (_hf:TestF f) (hj:TestF j) :
    q.LLw B W (fun u=>deriv f u.1*deriv j u.2) = q.be B W f j := by
  let h := fun u:Plane=> deriv f u.1*deriv j u.2
  have he (u:Plane) : bInt h u=deriv f u.1*(j u.2-j u.1) := by
    unfold bInt h
    dsimp only; rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_deriv_eq_sub]
    · exact fun x _=>hj.diff x
    exact hj.der.cont.intervalIntegrable ..
  have h₁ (z x) : B.bmat (bInt h) z x = deriv f z • B.eVal j z x := by
    let u:=B.Fr x
    apply u.loc_inj; rw [u.loc_smul, show u.loc (B.bmat (bInt h) z x)=_ from B.bmat_loc ..,
      FieldMat.eVal,u.loc_sub,u.loc_smul,u.loc_one,show u.loc (B.eval j x)=_ from B.evfrm x j]
    ext i k
    by_cases hh:i=k
    · subst k; simp [he]
    simp [hh]
  unfold LLw be
  change (∫ x,(∫ z,q.lk B W h z x) ∂normal m)= _
  have h₂ (x z) : q.lk B W h z x=q.betaK B W f j z x := by
    unfold lk betaK zE; rw [h₁]
    have hi := pj_scale 1 (deriv f z) W (q.EZ B z x) (B.eVal j z x)
    have hj := pj_scale (deriv f z) 1 W (q.EZ B z x) (B.eVal j z x)
    simp only [one_mul,one_smul] at hi hj
    rw [hi,hj]
  simp_rw [h₂]
end ProjField
end GeneralMahler

end

end OAI
