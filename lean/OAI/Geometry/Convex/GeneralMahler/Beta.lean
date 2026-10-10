import OAI.Geometry.Convex.GeneralMahler.EvalGap

namespace OAI
/-! §04 Eq15, threshold comparison. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

lemma pj_cont (W:Mat m) : Continuous (Pj W).uncurry := by
  change Continuous (fun p:Mat m × Mat m=>Pj W p.1 p.2)
  have he : Continuous (trN:Mat m→ℝ) := by simp_rw [← funext trL_apply]; exact trL.continuous
  unfold Pj jprod
  fun_prop

lemma pj_p {X:Type*} [NormedAddCommGroup X] {f g:X→Mat m}
    (hf:PolyBound f) (hg:PolyBound g) (W:Mat m) :
    PolyBound fun x=>Pj W (f x) (g x) := by
  let h := fun x=> ‖etL W‖*‖g x‖
  have hh : PolyBound h := (PolyBound.const _).mul hg.norm
  apply PolyBound.of_prod_le hf hh
  intro x
  apply pj_norm.trans
  unfold h; rw [Real.norm_of_nonneg (by positivity)]; exact le_of_eq (by ring)
lemma pj_M (W:Mat m) {X Y:Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {f g:X→Y→Mat m} (hf:mixed f) (hg:PolyBound g.uncurry) :
    mixed (fun x y=>Pj W (f x y) (g x y)) := by
  let h := fun x y=> ‖etL W‖*‖g x y‖
  apply hf.product (g:=h)
    (show PolyBound h.uncurry from (PolyBound.const _).mul hg.norm)
  intro x y; apply pj_norm.trans
  unfold h; rw [Real.norm_of_nonneg (by positivity)]; exact le_of_eq (by ring)

namespace ProjField
variable [NeZero m] (q:ProjField m) (B:FieldMat m) (W:Mat m)
def betaK (f j:ℝ→ℝ) (z:ℝ) (x:Rn m) := Pj W (q.zE B f z x) (B.eVal j z x)
def be (f j:ℝ→ℝ) := ∫ x,(∫ z,q.betaK B W f j z x) ∂normal m
def nTK (f j:ℝ→ℝ) (u:Plane) (x:Rn m) := deriv f u.1 * deriv j u.2 * trN (W*q.edge.NTm u x)
def Nt (f j:ℝ→ℝ) := ∫ x,(∫ u:Plane,q.nTK W f j u x) ∂normal m

lemma bMS {f j} (hf:TestF f) (hj:TestF j) : mixed (q.betaK B W f j) ∧
    StronglyMeasurable (q.betaK B W f j).uncurry :=
  by
    have hi := pj_M W (g:=B.eVal j) (q.zm B hf) (B.pEval hj)
    have hh := (pj_cont W).comp_stronglyMeasurable
      ((q.zSM B f).prodMk (B.smEval hj))
    exact ⟨hi,hh⟩

lemma nMS {f j} (hf:TestF f) (hj:TestF j) : mixed (q.nTK W f j) ∧
    StronglyMeasurable (q.nTK W f j).uncurry := by
  let h := fun u:Plane=>deriv f u.1*deriv j u.2
  let l := etL W
  have hm : mixed fun u x=> l (q.edge.NTm u x) := mixed_proj q.edge.nt_mixed l
  have hu : Continuous h := (hf.der.cont.comp continuous_fst).mul (hj.der.cont.comp continuous_snd)
  have hh : PolyBound h := (hf.der.poly.comp PolyBound.fst).mul (hj.der.poly.comp PolyBound.snd)
  have he : q.nTK W f j = fun u x=>h u*l (q.edge.NTm u x) := by
    ext; unfold h l nTK; rw [etL_apply]
  rw [he]
  exact ⟨hm.product (g:=fun u _=>h u) (hh.comp PolyBound.fst) (fun u x=>by rw [norm_mul,mul_comm]),
    (hu.comp continuous_fst).stronglyMeasurable.mul
      ((l.continuous.measurable.comp q.edge.nt_meas).stronglyMeasurable)⟩

def RadiusE (x:Rn m) := q.edge.radius x + ‖B.A x‖
lemma ER_P : PolyBound (q.RadiusE B) := q.edge.r_poly.add B.poly.norm
lemma ER_hi (x) :
    q.edge.radius x ≤ q.RadiusE B x ∧ ‖B.A x‖ ≤ q.RadiusE B x :=
  ⟨le_add_of_nonneg_right (norm_nonneg _),le_add_of_nonneg_left (q.edge.r_pos _).le⟩
lemma beyond (x) {z:ℝ} (h:q.RadiusE B x < ‖z‖) : q.EZ B z x=0 := by
  have he := (q.ER_hi B x).1.trans_lt h
  have hf := B.theta_exact z x ((q.ER_hi B x).2.trans_lt h)
  have hi : q.edge.P z x=scalar m (st z) := by
    rw [Real.norm_eq_abs] at he; unfold st; split_ifs with hx
    · rw [abs_of_nonneg hx] at he; rw [q.edge.tend_pos z x he,scalar,one_smul]
    rw [abs_of_neg (lt_of_not_ge hx)] at he; rw [q.edge.tend_neg z x he,scalar,zero_smul]
  change q.edge.P z x-B.Θ z x=_
  rw [hi,sub_eq_zero.mp (show B.Θ z x-scalar m (st z)=0 from hf),sub_self]

def crossK (f j:ℝ→ℝ) (u:Plane) (x:Rn m) :=
  Pj W (q.zE B f u.1 x) (deriv j u.2 • B.EC u x)
lemma crossMS {f j} (hf:TestF f) (hj:TestF j) :
    mixed (q.crossK B W f j) ∧ StronglyMeasurable (q.crossK B W f j).uncurry := by
  let c := fun u:Plane × Rn m=> (u.1.1,u.2)
  let h := fun u:Plane × Rn m=> u.1.2
  have hc : PolyBound c := ((PolyBound.fst.comp PolyBound.fst).prodMk PolyBound.snd)
  have hh : PolyBound h := PolyBound.snd.comp PolyBound.fst
  have he := pj_p (((q.zm B hf).poly).comp hc)
    (((hj.der.poly).comp hh).smul B.Ep) W
  have hm : mixed (q.crossK B W f j) := by
    apply mixed.of_cutoff (f:=q.crossK B W f j) he (q.ER_P B)
    intro u x hx
    by_cases hu : q.RadiusE B x < ‖u.1‖
    · unfold crossK; rw [zE,q.beyond B x hu,smul_zero,← pJ_eq,_root_.map_zero]; rfl
    change _ < max _ _ at hx
    have ht : max ‖u.1‖ ‖B.A x‖ < ‖u.2‖ := by
      have hh := q.ER_hi B x; grind
    unfold crossK; rw [B.vanishEC x u ht,smul_zero,← pJ_eq,_root_.map_zero]
  have h₁ : Measurable c := by unfold c; fun_prop
  have h₂ : Continuous h := by unfold h; fun_prop
  have hi := (pj_cont W).comp_stronglyMeasurable (((q.zSM B f).comp_measurable h₁).prodMk
    (((hj.der.cont.comp h₂).stronglyMeasurable).smul B.Em))
  exact ⟨hm,hi⟩

lemma point_expand_f (x) (f:ℝ→ℝ) (u:Plane) (hu:u.1<u.2) :
    q.nTK W f f u x+Pj W (q.zE B f u.1 x) (q.zE B f u.2 x)=
    q.crossK B W f f u x+q.crossK B W f f u.swap x := by
  set y := u.1; set z:=u.2
  have hh := B.nest x y z hu.le
  unfold nTK Edge.NTm crossK zE
  rw [min_eq_left hu.le,max_eq_right hu.le,pj_scale,pj_scale,pj_scale]
  have HH : u.1<u.2:=hu
  have ha : B.EC u x=1-B.Θ z x := by simp [FieldMat.EC,jump,HH.le,z,scalar]
  have hb : B.EC u.swap x= -B.Θ y x := by simp [FieldMat.EC,jump,not_le_of_gt HH,y,scalar]
  rw [ha,hb]
  let a := q.Pmat y x; let b := q.Pmat z x
  let t := B.Θ y x; let w := B.Θ z x
  have h :
      Pj W a (1-b)+Pj W (a-t) (b-w)=Pj W (a-t) (1-w)+Pj W (b-w) (-t) := by
    unfold Pj jprod
    have hh₁ : t*w=t := hh.1
    have hh₂ : w*t=t := hh.2
    rw [← trN_add, ← trN_add,← mul_add,← mul_add,← smul_add,← smul_add]
    congr 3
    simp only [sub_mul,mul_sub,mul_one,one_mul,neg_mul,mul_neg,hh₁,hh₂]; abel
  change deriv f y*deriv f z*Pj W a (1-b)+ _= _
  change deriv f y*deriv f z*_+deriv f y*(deriv f z*Pj W (a-t) (b-w))=
    deriv f y*(deriv f z*Pj W (a-t) (1-w))+deriv f z*(deriv f y*Pj W (b-w) (-t))
  linear_combination deriv f y*deriv f z*h

lemma point_expand (x) (f:ℝ→ℝ) :
    ∀ᵐ u:Plane,q.nTK W f f u x+Pj W (q.zE B f u.1 x) (q.zE B f u.2 x)=
    q.crossK B W f f u x+q.crossK B W f f u.swap x := by
  filter_upwards [off_diag] with u hu
  rcases lt_or_gt_of_ne hu with h|h; exact q.point_expand_f B W x f u h
  have he := q.point_expand_f B W x f u.swap h
  rw [pj_sym] at he
  simpa [nTK, Edge.NTm, min_comm,max_comm,mul_comm,add_comm] using he

lemma square_pt {f:ℝ→ℝ} (hf:TestF f) (x:Rn m) :
    Pj W (q.MB B f x) (q.MB B f x)+ (∫ u:Plane,q.nTK W f f u x) =
      2*∫ z,q.betaK B W f f z x := by
  let U := fun z=> q.zE B f z x
  let g := fun u:Plane=> q.crossK B W f f u x
  let h := fun u:Plane=> q.nTK W f f u x
  let s := fun u:Plane=> PJ W (U u.1) (U u.2)
  have ig : Integrable g := mixed_integrable_left (q.crossMS B W hf hf).1 x
    (((q.crossMS B W hf hf).2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  have ih : Integrable h := mixed_integrable_left (q.nMS W hf hf).1 x
    (((q.nMS W hf hf).2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  have iu : Integrable U := q.zi B hf x
  have ih' : Integrable s :=
    by
      have he := iu.op_fst_snd (pj_cont W) ⟨‖etL W‖,(fun x y=> pj_norm)⟩ iu
      unfold s; simp_rw [pJ_eq]; exact he
  have he : (∫ u:Plane,(h u+s u))= ∫ u:Plane,(g u+g u.swap) := by
    apply integral_congr_ae
    filter_upwards [q.point_expand B W x f] with u hu
    simpa only [h,s,g,U,pJ_eq] using hu
  have hs : (∫ u,s u)=Pj W (q.MB B f x) (q.MB B f x) := by
    rw [q.mb_eq B hf,← pJ_eq]
    simp only [_root_.map_neg,_root_.neg_apply,neg_neg]
    exact integral_prod_bilin (PJ W) iu iu
  have ha : (∫ u,g u)=∫ z,q.betaK B W f f z x := by
    rw [show (volume:Measure Plane)=volume.prod volume from rfl,integral_prod _ ig]
    congr 1
    ext z
    unfold betaK g crossK
    simp_rw [← pJ_eq]
    rw [B.gap x z hf]; exact (PJ W _).integral_comp_comm (B.gapM x z hf)
  rw [integral_add ih ih',integral_add ig (show Integrable (fun u:Plane=>g u.swap) volume from ig.swap),
    show (∫ u:Plane,g u.swap)=∫ u,g u from integral_prod_swap _,hs,ha] at he
  linarith
lemma eq15 {f:ℝ→ℝ} (hf:TestF f) :
    Pt W (q.MB B f) (q.MB B f)= 2*q.be B W f f-q.Nt W f f := by
  have he (x) : Pj W (q.MB B f x) (q.MB B f x)=
      2*(∫ z,q.betaK B W f f z x)-(∫ u:Plane,q.nTK W f f u x) :=
    eq_sub_of_add_eq (q.square_pt B W hf x)
  unfold Pt be Nt; simp_rw [he]
  have ih := q.bMS B W hf hf
  have hf := q.nMS W hf hf
  rw [integral_sub,integral_const_mul]
  · exact ((mixed_integrable (μ:=volume) (ν:=normal m) ih.1 ih.2.aestronglyMeasurable).integral_prod_right).const_mul _
  exact (mixed_integrable (μ:=volume) (ν:=normal m) hf.1 hf.2.aestronglyMeasurable).integral_prod_right
end ProjField
end GeneralMahler

end

end OAI
