import OAI.Geometry.Convex.GeneralMahler.Frame.Sec

namespace OAI
/-! Derivative of spectral function of linear field. Avoid polynomial
approximation by exact secant identity and Borel frame compactness. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Asymptotics
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace Frm
def DL (u v:Frm m) (A B:Mat m) (g:Plane→ℝ) : Mat m →L[ℝ] Mat m :=
  LinearMap.toContinuousLinearMap (𝕜:=ℝ) {
    toFun := u.sec v A B g
    map_add' := u.sec_add v A B g
    map_smul' := u.sec_smul v A B g }
omit [NeZero m] in
lemma cont_DL (u:Frm m) (A:Mat m) {g:Plane→ℝ} (hg:Continuous g) :
    Continuous (fun v:Mat m × Frm m=> u.DL v.2 A v.1 g) := by
  rw [continuous_clm_apply]
  intro C
  let k := fun v:Mat m × Frm m=> v.2.val
  have hk : Continuous k := continuous_subtype_val.comp continuous_snd
  change Continuous fun v:Mat m × Frm m=> u.val*(u.secDiag v.2 A v.1 g C)*star (k v)
  have ha : Continuous fun v:Mat m × Frm m=> (u.secDiag v.2 A v.1 g C) := by
    apply continuous_matrix
    intro i j
    have hi : Continuous fun v:Mat m × Frm m=> v.2.eig v.1 j :=
      (continuous_apply _).comp (cdiag.comp cont_loc)
    exact (hg.comp (continuous_const.prodMk hi)).mul ((coeffMap i j).continuous.comp
      (continuous_const.mul hk))
  exact (continuous_const.mul ha).mul hk.star

omit [NeZero m] in
lemma DL_ind (u v w:Frm m) (A B:Mat m) (g:Plane→ℝ) (hv:v.Dgn B) (hw:w.Dgn B) :
    u.DL v A B g=u.DL w A B g := by
  ext C : 1
  exact u.sec_ind v w A B C g hv hw
end Frm

section p
variable {X:Type*} [NormedAddCommGroup X]

-- Tool: matrix-coordinate bounds for moderate functions
omit [NeZero m] in
lemma mat_poly {A:X→Mat m} (ha:∀ i j:Fin m,PolyBound (fun x=>A x i j)) :
    PolyBound A := by
  classical
  let b := fun i j:Fin m=> Matrix.single i j (1:ℝ)

  let h := fun i j (x:X)=> A x i j • b i j
  have he : A=fun x=>∑ i,∑ j,h i j x := by
    ext x i j; simp [h,b,Matrix.sum_apply,Matrix.single, ite_and]
  rw [he]
  apply p_sum (f:=fun i x=>∑ j,h i j x)
  intro i; exact p_sum (f:=h i) (fun j=> (ha i j).smul (PolyBound.const _)) _
lemma unitPoly (v:X→Frm m) :
    PolyBound (fun x=> (v x).val) := PolyBound.of_bound 1 (fun x=> le_of_eq
      (CStarRing.norm_of_mem_unitary (v x).property))
lemma unitStarPoly (v:X→Frm m) :
    PolyBound (fun x=> star (v x).val) := (unitPoly v).mono fun x=> by rw [norm_star]
lemma poly_eig {A:X→Mat m} (hA:PolyBound A) (u:X→Frm m) (i:Fin m) :
    PolyBound (fun x=> (u x).eig (A x) i) := by
  have he : PolyBound (fun x=> (u x).loc (A x)) :=
    ((unitStarPoly u).mul hA).mul (unitPoly u)
  exact (PolyBound.clm (coeffMap i i)).comp he
lemma poly_sec {A:X→Mat m} (hA:PolyBound A) {g:Plane→ℝ} (hg:PolyBound g)
    (v:X→Frm m) (C:Mat m) : PolyBound fun x=>(v x).sec (v x) (A x) (A x) g C := by
  let f := fun x=>(v x).secDiag (v x) (A x) (A x) g C
  have h : PolyBound f := by
    have he := ((unitStarPoly v).mul (PolyBound.const C)).mul (unitPoly v)
    apply mat_poly
    intro i j; exact (hg.comp ((poly_eig hA v i).prodMk (poly_eig hA v j))).mul
      ((PolyBound.clm (coeffMap i j)).comp he)
  exact ((unitPoly v).mul h).mul (unitStarPoly v)
lemma clm_poly_from {E F:Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
    {f:X→E→L[ℝ]F} (h:∀ y:E,PolyBound fun x=>f x y) : PolyBound f := by
  classical
  let b := Module.finBasis ℝ E
  let c := fun i=> (b.coord i).toContinuousLinearMap
  let g := fun i (x:X)=> (c i).smulRight (f x (b i))
  have he : f=fun x=> ∑ i,g i x := by
    ext x y
    conv_lhs => rw [← b.sum_repr y]
    simp only [_root_.map_sum,_root_.map_smul,_root_.sum_apply,g,ContinuousLinearMap.smulRight_apply]
    rfl
  rw [he]
  apply p_sum (f:=g)
  intro i
  exact (PolyBound.clm (ContinuousLinearMap.smulRightL ℝ E F (c i))).comp (h _)
end p
namespace ProjField
variable (q:ProjField m)
def ell : Rn m→L[ℝ] Mat m := q.L_linear.choose
omit [NeZero m] in
lemma ell_eq (x) : q.ell x=q.Lmat x := congrFun q.L_linear.choose_spec x
def Ld (x:Rn m) (f:ℝ→ℝ) : Rn m→L[ℝ]Mat m :=
  let u := q.FL.Fr x
  (u.DL u (q.Lmat x) (q.Lmat x) (bav (deriv f))).comp q.ell

lemma hasdl (x:Rn m) {f:ℝ→ℝ} (hf:TestF f) :
    HasFDerivAt (q.FL.eval f) (q.Ld x f) x := by
  let u := q.FL.Fr x
  let g := bav (deriv f)
  have hg := bav_con hf.der.cont
  let t := fun z=> (u.DL (q.FL.Fr z) (q.Lmat x) (q.Lmat z) g).comp q.ell
  have he (z:Rn m) :
      q.FL.eval f z-q.FL.eval f x=t z (z-x) := by
    let A := q.FL
    have hi := u.exact_sec (A.Fr z) (A.sym x) (A.sym z) (A.Fr_D x) (A.Fr_D z) hf
    have hh : A.eval f x-A.eval f z=u.DL (A.Fr z) (q.Lmat x) (q.Lmat z) g (q.Lmat x-q.Lmat z) := hi
    have hp : A.eval f x-A.eval f z=t z (x-z) := by rw [hh]; simp only [t,
      ContinuousLinearMap.comp_apply,_root_.map_sub,q.ell_eq]; rfl
    change A.eval f z-A.eval f x=_
    rw [show z-x= -(x-z) by abel,_root_.map_neg, ← hp,neg_sub]

  have hh : ContinuousAt t x := by
    apply tendsto_of_subseq_tendsto
    intro ns hn
    obtain ⟨v,ms,hms,h⟩ := CompactSpace.tendsto_subseq (fun n=> q.FL.Fr (ns n))
    have hA : Tendsto (fun n=> (q.Lmat (ns (ms n)),q.FL.Fr (ns (ms n)))) atTop
        (𝓝 (q.Lmat x,v)) :=
      ((q.L_cont.tendsto x).comp (hn.comp hms.tendsto_atTop)).prodMk_nhds h
    have hs : ∀ᶠ n in atTop,(q.Lmat (ns (ms n)),q.FL.Fr (ns (ms n)))∈
        {p:Mat m × Frm m|p.2.Dgn p.1} :=
      Eventually.of_forall fun n=> q.FL.Fr_D (ns (ms n))
    have hv := Frm.Dgn_closed.mem_of_tendsto hA hs
    let D := fun p:Mat m × Frm m=> (u.DL p.2 (q.Lmat x) p.1 g).comp q.ell
    have hi := Frm.cont_DL u (q.Lmat x) hg
    have hu := ((ContinuousLinearMap.compL ℝ (Rn m) (Mat m) (Mat m)).flip q.ell).continuous.comp hi
    have hd : Continuous D := hu
    have heq : t x = D (q.Lmat x,v) := by
      unfold t D
      have hx : v.Dgn (q.Lmat x) := hv
      have hi : (q.FL.Fr x).Dgn (q.Lmat x):=q.FL.Fr_D x
      rw [u.DL_ind _ v _ _ _ hi hx]
    refine ⟨ms,?_⟩
    have ha := hd.tendsto (q.Lmat x,v)
    have hu := ha.comp hA
    rw [← heq] at hu; exact hu
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,isLittleO_iff]
  intro c hc
  have hi : ContinuousAt (fun y=> ‖t (x+y)-t x‖) 0 := by
    let : IsTopologicalAddGroup (Rn m →L[ℝ] Mat m) :=
      ContinuousLinearMap.isTopologicalAddGroup
    let : ContinuousSub (Rn m →L[ℝ] Mat m) :=
      IsTopologicalAddGroup.to_continuousSub
    have hl : ContinuousAt (fun y=> t (x+y)) 0 :=
      ContinuousAt.comp_of_eq hh (continuousAt_const.add continuousAt_id) (add_zero _)
    have he : ContinuousAt (fun y=> t (x+y)-t x) 0 := hl.sub continuousAt_const
    have hb := continuous_norm (E:=Rn m →L[ℝ] Mat m)
    exact hb.continuousAt.comp he
  filter_upwards [hi.eventually (gt_mem_nhds (show ‖t (x+0)-t x‖<c by rw [add_zero, sub_self, show ‖(0:Rn m →L[ℝ] Mat m)‖=0 from norm_zero (E:=Rn m →L[ℝ] Mat m)]; exact hc))]
    with y hy
  change ‖q.FL.eval f (x+y)-q.FL.eval f x-q.Ld x f y‖≤_
  rw [he, add_comm x y,add_sub_cancel_right]
  change ‖(t (y+x)-t x) y‖≤_
  apply ((t (y+x)-t x).le_opNorm y).trans
  rw [add_comm y x]
  apply mul_le_mul_of_nonneg_right (le_of_lt hy) (norm_nonneg _)

lemma dPoly {f:ℝ→ℝ} (hf:TestF f) : PolyBound (fderiv ℝ (q.FL.eval f)) := by
  rw [show fderiv ℝ (q.FL.eval f)=_ from funext (fun x=>(q.hasdl x hf).fderiv)]
  apply clm_poly_from
  intro y; exact poly_sec q.L_poly (bav_bound hf.der.poly) q.FL.Fr (q.ell y)

lemma LD_reg (i:Fin m) {f} (hf:TestF f) :
    regular fun x=> fderiv ℝ (q.FL.eval f) x (e i) :=
  ⟨(PolyBound.clm (ContinuousLinearMap.apply ℝ _ (e i))).comp (q.dPoly hf),
    (((continuous_id.clm_apply continuous_const).comp_stronglyMeasurable
      ((by
        exact (measurable_fderiv ℝ (q.FL.eval f)).stronglyMeasurable)))).aestronglyMeasurable⟩

omit [NeZero m] in
lemma ell_M (i:Fin m) : q.ell (e i)=q.M i := by
  rw [q.ell_eq]
  simp [e,Lmat]
lemma mder_frame (i j k:Fin m) {f:ℝ→ℝ} (hf:TestF f) (x:Rn m) :
    (q.FL.Fr x).loc (fderiv ℝ (q.FL.eval f) x (e i)) j k=
      bav (deriv f) (q.FL.ev x j,q.FL.ev x k)*(q.FL.Fr x).loc (q.M i) j k := by
  rw [(q.hasdl x hf).fderiv,Ld,ContinuousLinearMap.comp_apply,q.ell_M]
  apply Frm.sec_eq
end ProjField
end GeneralMahler

end

end OAI
