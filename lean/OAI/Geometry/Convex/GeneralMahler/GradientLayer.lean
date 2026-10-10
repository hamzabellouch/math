import OAI.Geometry.Convex.GeneralMahler.Hermite.Pair
import OAI.Geometry.Convex.GeneralMahler.Entropy

namespace OAI
/-! The centered fields W_f from §02,04. We use coefficient
derivatives (Hermite) as justified by differentiation by parts:
rather than interchanging weak derivatives, integrate the coefficient
identity using the layer cutoff bounds. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
def Xb (z:ℝ) (x:Rn m) := (1-st z) • q.XT z x
def Yb (z:ℝ) (x:Rn m) := st z • q.YT z x
lemma XPbound : PolyBound q.XT.uncurry := by
  have h := q.primalMap.yp
  simp_rw [show q.primalMap.y=q.XT from funext q.X_sc] at h; exact h
lemma YPbound : PolyBound q.YT.uncurry := by
  change PolyBound (fun u:ℝ×Rn m=>coneProj q.D (-(q.Z u.2+q.shift u.1)))
  have hp : PolyBound (fun u:ℝ×Rn m=> -(q.Z u.2+q.shift u.1)) :=
    (((PolyBound.clm q.root.toContinuousLinearMap).comp PolyBound.snd).add
      (q.s_poly.comp PolyBound.fst)).neg
  exact (PolyBound.lipschitz (coneProj_lip q.D)).comp hp

lemma XbM : mixed q.Xb := by
  let v := q.primalMap
  apply mixed.of_cutoff (show PolyBound q.Xb.uncurry from
    (((PolyBound.const (1:ℝ)).sub poly_st).comp PolyBound.fst).smul q.XPbound)
    (show PolyBound (fun x:Rn m=> v.M*(1+‖x‖)) from
      (PolyBound.const _).mul ((PolyBound.const _).add PolyBound.id.norm))
  intro z x hx
  unfold Xb st; split_ifs with h
  · simp
  rw [Real.norm_eq_abs,abs_of_neg (lt_of_not_ge h)] at hx
  have hi := v.zero_y z x hx
  rw [show v.y z= _ from q.X_sc _] at hi
  simp only [hi,smul_zero]
lemma YbM : mixed q.Yb := by
  let v := q.dualMap
  apply mixed.of_cutoff (show PolyBound q.Yb.uncurry from
    (poly_st.comp PolyBound.fst).smul q.YPbound)
    (show PolyBound (fun x:Rn m=> v.M*(1+‖x‖)) from
      (PolyBound.const _).mul ((PolyBound.const _).add PolyBound.id.norm))
  intro z x hx
  unfold Yb st; split_ifs with h
  · rw [Real.norm_of_nonneg h] at hx
    have hi := v.zero_y (-z) x (by simpa using hx)
    rw [show v.y (-z)= _ from q.Y_sc _,neg_neg] at hi
    simp only [hi,smul_zero]
  simp

def WW (z:ℝ) (x:Rn m) :=
  p z • q.Z x-q.XT z x + a z • q.U

omit [NeZero m] in
lemma WW_mean (z:ℝ) : (∫ x,q.WW z x ∂normal m)=0 := by
  have he : Integrable q.Z (normal m) := by
    have hZ : PolyBound q.Z := PolyBound.clm q.root.toContinuousLinearMap
    exact hZ.gaussian_integrable q.root.continuous.aestronglyMeasurable
  unfold WW
  have hi : Integrable (fun x=> p z • q.Z x) (normal m) := he.smul (p z)
  rw [integral_add,integral_sub hi (q.X_int z), q.XT_mean, integral_smul]
  · have he : (∫ x,q.Z x ∂normal m)=0 := by
      have h := affineN_mean q.root 0
      simpa only [affineN,Z,add_zero] using h
    rw [he]; simp
  · exact hi.sub (q.X_int z)
  exact integrable_const _

omit [NeZero m] in
lemma WW_eq (z x) :
    q.WW z x=(p z-st z) • q.Z x-q.Xb z x -q.Yb z x+
      (∫ y,q.Xb z y ∂normal m)+(∫ y,q.Yb z y ∂normal m) := by
  unfold WW Xb Yb
  rw [integral_smul,integral_smul,q.XT_mean,q.Y_mean,q.YT_sub]
  module
lemma WW_m : mixed q.WW := by
  let f := fun z x=> (p z-st z) • q.Z x
  have hp : PolyBound q.Z := PolyBound.clm q.root.toContinuousLinearMap
  have hf : mixed f := (mixed.of_rapid (Y:=Rn m) rapid_p).product (g:=fun _ x=>q.Z x)
    (show PolyBound (fun u:ℝ×Rn m=> q.Z u.2) from hp.comp PolyBound.snd) (fun x y=>by rw [show f x y= _ from rfl,norm_smul])
  have hx := mixed_integral_right q.XbM fun z=> (show Integrable (q.Xb z) (normal m)
    from (q.X_int z).smul (1-st z)).aestronglyMeasurable
  have hy := mixed_integral_right q.YbM fun z=> (show Integrable (q.Yb z) (normal m)
    from (q.Y_int z).smul (st z)).aestronglyMeasurable
  rw [show q.WW= _ from funext fun z=>funext fun x=>q.WW_eq z x]
  exact (((hf.sub q.XbM).sub q.YbM).add (mixed.of_rapid hx)).add (mixed.of_rapid hy)

omit [NeZero m] in
lemma WW_c : Continuous q.WW.uncurry :=
  (((cp.comp continuous_fst).smul (q.root.continuous.comp continuous_snd)).sub q.meas_XT).add
    ((ca.comp continuous_fst).smul continuous_const)
def WK (f:ℝ→ℝ) (z:ℝ) (x:Rn m) := deriv f z • q.WW z x
def WH (f:ℝ→ℝ) (x:Rn m) := ∫ z,q.WK f z x

omit [NeZero m] in
lemma WK_SM (f) : StronglyMeasurable (q.WK f).uncurry :=
  (((measurable_deriv f).comp measurable_fst).stronglyMeasurable).smul q.WW_c.stronglyMeasurable
lemma WK_m {f} (hf:TestF f) : mixed (q.WK f) := by
  let g := fun (z:ℝ) (_:Rn m)=> deriv f z
  apply q.WW_m.product (show PolyBound g.uncurry from hf.der.poly.comp PolyBound.fst)
  intro z x
  unfold WK g; rw [norm_smul,mul_comm]
lemma WH_reg {f} (hf:TestF f) : regular (q.WH f) :=
  ⟨poly_integral_left (q.WK_m hf) (fun _x=> (((q.WK_SM f).comp_measurable
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable)),
    (q.WK_SM f).integral_prod_left.aestronglyMeasurable⟩
lemma WH_mean {f} (hf:TestF f) : (∫ x,q.WH f x ∂normal m)=0 := by
  unfold WH
  rw [integral_integral_swap]
  · unfold WK; simp_rw [integral_smul,q.WW_mean]; simp
  exact (mixed_integrable (μ:=volume) (ν:=normal m) (q.WK_m hf)
    (q.WK_SM f).aestronglyMeasurable).swap

def act (i:Fin m) : Mat m→L[ℝ]Rn m :=
  (ContinuousLinearMap.apply ℝ (Rn m) (op q.S (HMode.e i))).comp opCLE.toContinuousLinearMap
omit [NeZero m] in
lemma act_eq (i) (A:Mat m) : q.act i A=op A (op q.S (HMode.e i)) := rfl

omit [NeZero m] in
lemma WWd (z:ℝ) :
    ∀ᵐ x∂normal m, HasFDerivAt (q.WW z)
      ((op (q.PD z x)).comp (op q.S)) x := by
    filter_upwards [q.XT_diff z] with x hx
    have hf := ((((q.root.hasFDerivAt).const_smul (p z)).sub hx).add_const (Layers.a z • q.U))
    have hl : (op (q.PD z x)).comp (op q.S)=p z•q.root.toContinuousLinearMap - (op (q.Pmat z x)).comp (op q.S) := by
      unfold PD
      rw [q.matrix_eq]
      change op (p z • 1 - _)*op q.S=p z•op q.S-op (q.Pmat z x)*op q.S
      rw [← _root_.map_mul,sub_mul,smul_mul_assoc,one_mul,_root_.map_sub,_root_.map_smul,_root_.map_mul]
    rw [hl]; exact hf
omit [NeZero m] in
lemma WW_lip (z:ℝ) : ∃ K,LipschitzWith K (q.WW z) := by
    obtain ⟨K,hk⟩ := q.XT_lipschitz z
    exact ⟨_, (((p z • q.root.toContinuousLinearMap).lipschitzWith).sub hk).add (LipschitzWith.const _)⟩
lemma WDer_p (z:ℝ) (i:Fin m) :
    PolyBound (fun x=> q.act i (q.PD z x)) := by
  have hh : PolyBound (q.PD z) :=
    (q.mixed_PD.poly).comp (f:=(fun x=>(z,x))) ((PolyBound.const z).prodMk PolyBound.id)
  exact (PolyBound.clm (q.act i)).comp hh
lemma WW_recur (z:ℝ) (i:Fin m) (a:MI m) :
    cof (fun x=> q.act i (q.PD z x)) a=sn (a i+1) • cof (q.WW z) (inc a i) := by
  obtain ⟨K,hk⟩ := q.WW_lip z
  let D := fun x=> (op (q.PD z x)).comp (op q.S)
  have hm : AEStronglyMeasurable (fun x=>q.act i (q.PD z x)) (normal m) :=
    ((q.act i).continuous.comp_stronglyMeasurable (q.PD_sm.comp_measurable
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have ht : (fun x=>D x (HMode.e i))=(fun x=>q.act i (q.PD z x)) := by funext x; rfl
  have hi := coef_raise (PolyBound.lipschitz hk) (PLip.lip hk) hk.continuous (D:=D) (q.WWd z) i
    (ht.symm ▸ q.WDer_p z i) (ht.symm ▸ hm) a
  rw [ht] at hi; exact hi

-- Linear coefficient interchange with layer integral, natural powers
omit [NeZero m] in
lemma cof_layer {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f:ℝ→Rn m→F} (hf:mixed f) (hm:StronglyMeasurable f.uncurry) (a:MI m) :
    cof (fun x=>∫ z,f z x) a=∫ z,cof (f z) a := by
  let g := fun z x=> MM a x • f z x
  have hh : StronglyMeasurable g.uncurry :=
    ((M_cont a).stronglyMeasurable.comp_measurable measurable_snd).smul hm
  have hg : mixed g := hf.product (g:=fun _ x=>MM a x)
    (show PolyBound (fun u:ℝ × Rn m=>MM a u.2) from (M_poly a).comp PolyBound.snd)
    (fun z x=>by unfold g; rw [norm_smul,mul_comm])
  unfold cof; simp_rw [← integral_smul]
  exact integral_integral_swap (mixed_integrable (μ:=volume) (ν:=normal m) hg hh.aestronglyMeasurable).swap

lemma WH_rec {f} (hf:TestF f) (i:Fin m) (a:MI m) :
    q.act i (cof (q.Hmat f) a)=sn (a i+1) • cof (q.WH f) (inc a i) := by
  let g := fun z x=> q.act i (q.kerH f z x)
  have hh (x) : q.act i (q.Hmat f x)=∫ z,g z x := ( (q.act i).integral_comp_comm
    (q.H_left_int hf.der.poly _)).symm
  have he : mixed g := (q.H_mixed hf.der.poly).product (g:=fun _ _=>‖q.act i‖)
    (show PolyBound (fun _:ℝ × Rn m=>‖q.act i‖) from PolyBound.const _)
    (fun z x=>by unfold g; rw [Real.norm_of_nonneg (norm_nonneg (q.act i)),mul_comm]; apply ContinuousLinearMap.le_opNorm)
  have hi (z) : cof (g z) a=sn (a i+1) • cof (q.WK f z) (inc a i) := by
    have h := q.WW_recur z i a
    have hf (v:Rn m→Rn m) (a:MI m) : cof (fun x=> deriv f z • v x) a=deriv f z • cof v a := by
      unfold cof; rw [← integral_smul]; congr 1; ext; rw [smul_comm]
    unfold WK g kerH; simp_rw [_root_.map_smul]
    rw [hf,hf,h,smul_comm]
  have hm : regular (q.Hmat f) := ⟨q.H_poly hf.der.poly,q.H_SM.aestronglyMeasurable⟩
  rw [cof_clm hm]
  simp_rw [hh]
  rw [cof_layer he (((q.act i).continuous).comp_stronglyMeasurable q.H_sm)]
  simp_rw [hi, integral_smul]
  rw [show cof (q.WH f) _=_ from cof_layer (q.WK_m hf) (q.WK_SM _) (inc a i)]
end ProjField
end GeneralMahler

end

end OAI
