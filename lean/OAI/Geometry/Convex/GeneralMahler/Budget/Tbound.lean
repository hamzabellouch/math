import OAI.Geometry.Convex.GeneralMahler.Budget.Eq19
import OAI.Geometry.Convex.GeneralMahler.Budget.Klimit

namespace OAI
/-! §05 the two layer estimates, retained penalties. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots

namespace Profile
def ap := bb+eta+(bb+eta-kar)*tmin
def lm := bb+eta+kar*tmin+1/8
def P0 (x:Plane) := 2*ap+2*bm*N2 qu x.1*N2 qu x.2+2*e₀*(2*tr)^2
def wwR (w:Plane) := tc*bAv Hh w - tr/2*(h₀+bAv Hh w^2/h₀)
def ww (w:Plane) := bAv (fun w=> HH w-P0 w) w+wwR w
def ww0 (w:Plane) := bAv (fun w=>Hh w^2) w / alpha
end Profile
variable {m:ℕ}
lemma uy_nn {x y z:ℝ} : 0 ≤ Uy x y z := by
  unfold Uy U slab
  apply mul_nonneg (abs_nonneg _)
  generalize (z-min x y)/ |y-x|=t
  split_ifs with h h'
  · unfold yk; have hp : 0 < -t := by linarith
    positivity
  · norm_num
  have hh : 0<t-1 := by linarith
  unfold yk; positivity
lemma ux_nn {x y z:ℝ} : 0 ≤ Ux x y z := by
  unfold Ux U slab
  apply mul_nonneg (abs_nonneg _)
  generalize (z-min x y)/ |y-x|=t
  split_ifs with h h'
  · unfold xk; have hp : 0 < -t := by linarith
    positivity
  · unfold gx; positivity
  have hh : 0<t-1 := by linarith
  unfold xk; positivity
lemma Bvpp : Bwt (fun u:Plane=>deriv (deriv v) u.2) := Bwt.snd v_test.der.der
lemma sq_wt {f} (hf:Bwt f) : Bwt (fun u=>f u^2) := by simpa [pow_two] using hf.mul hf
lemma bhj (h:LayerOK) : Bwt Hh := ((ProjField.H_ok h).add Bvpp).sub (Bwt.const _)
lemma P0_wt (h:LayerOK) : Bwt P0 := by
  have hp := N2_test h.q_test
  exact ((Bwt.const _).add (((Bwt.const _).mul (.fst hp)).mul (.snd hp))).add (Bwt.const _)
lemma Rwt (h:LayerOK) : Bwt wwR := by
  unfold wwR; simp only [div_eq_mul_inv]
  have ht := (bhj h).bar
  exact ((Bwt.const _).mul ht).sub ((Bwt.const _).mul ((Bwt.const _).add
    ((sq_wt ht).mul (Bwt.const _))))
lemma wwt (h:LayerOK) : Bwt ww :=
  ((ProjField.H_ok h).sub (P0_wt h)).bar.add (Rwt h)
lemma w0t (h:LayerOK) : Bwt ww0 := by
  unfold ww0; simp only [div_eq_mul_inv]
  exact ((sq_wt (bhj h)).bar.mul (Bwt.const _))
lemma trp : 0<Profile.tr := by norm_num [Profile.tr]
lemma alpha_p : 0<alpha := by norm_num [alpha]

lemma wpos (h:LayerOK) (v:Plane) : ww v > ww0 v ∧ 0≤ww0 v := by
  have hj := bhj h
  have hs := sq_wt hj
  have hx:= bar_sq Hh hj v
  let l := fun t=> (v.1,along v t)
  have hl : Continuous l := by unfold l along; fun_prop
  let a := fun t=> HH (l t)-P0 (l t)
  let b := fun t=> Hh (l t)
  let F := fun t=> a t+tc*b t - tr/2*(h₀+b t^2/h₀)-b t^2/alpha
  have HF (t:ℝ): 0<F t := by
    unfold F a b
    have hi := h.bh_layer (l t); unfold P0 ap; linarith
  have ha : Continuous a := ((ProjField.H_ok h).c.sub (P0_wt h).c).comp hl
  have hb : Continuous b := hj.c.comp hl
  have hF : Continuous F := by unfold F; fun_prop
  have he : 0< ∫ t in (0:ℝ)..1,F t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (a:= (0:ℝ)) (b:=1) (hF.intervalIntegrable ..) (fun x _=>HF x) ?_
  · refine ⟨?_,div_nonneg (le_trans (sq_nonneg _) hx) alpha_p.le⟩
    let H (f:ℝ→ℝ):=∫ t in (0:ℝ)..1,f t
    have he' : 0 < H a+tc* H b-tr/2*(h₀+H (fun t=>b t^2)/h₀)-H (fun t=>b t^2)/alpha := by
      unfold H
      unfold F at he
      rw [intervalIntegral.integral_sub,intervalIntegral.integral_sub,
        intervalIntegral.integral_add, intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add, intervalIntegral.integral_div,intervalIntegral.integral_div,
        intervalIntegral.integral_const] at he
      · simpa using he
      all_goals (apply Continuous.intervalIntegrable; fun_prop)
    change H (fun t=>a t)+(tc*H b-tr/2*(h₀+(H b)^2/h₀)) > H (fun t=>b t^2)/alpha
    change (H b)^2 ≤ H (fun t=>b t^2) at hx
    unfold Profile.tr h₀ at *
    linarith
  norm_num

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)

lemma BB_scale (f:Plane→ℝ) (c:ℝ) :
    q.BB B (fun w=>c*f w)=c*q.BB B f := by
  unfold BB; simp_rw [q.bm_scale,integral_const_mul]

section
variable [NeZero m]

lemma BB_add {f g} (hf:Bwt f) (hg:Bwt g) :
    q.BB B (fun x=>f x+g x)=q.BB B f+q.BB B g := by
  unfold BB; simp_rw [q.bm_add B,integral_add (q.bmh B hf _) (q.bmh B hg _)]
  rw [integral_add (q.bmah B hf) (q.bmah B hg)]
lemma BB_sub {f g} (hf:Bwt f) (hg:Bwt g) :
    q.BB B (fun x=>f x-g x)=q.BB B f-q.BB B g := by
  have h := q.BB_add B (hf.sub hg) hg
  rw [show (fun x=>f x-g x+g x)=f from by ext; ring] at h
  linarith
end

lemma BB_bar {f} (hf:Bwt f) : q.LLw B 1 f=q.BB B (bAv f) := by
  unfold LLw BB; simp_rw [q.LL_Bw B _ _ hf]
lemma BB1 : q.LLw B 1 (fun _=>1)=q.BB B (fun _=>1) := by
  rw [q.BB_bar B (Bwt.const 1)]; simp_rw [show bAv (fun _=>1)=fun _=>(1:ℝ)
    from funext bar_const]

lemma block_boxJ {T:Mat m} (ht:T∈specBox m tmin tmax) {V:Mat m} (hv:V.IsHermitian) :
    tc•V-(tr/2:ℝ)•(scalar m h₀+h₀⁻¹•(V*V)) ≤ jprod T V := by
  have hd : ‖T-scalar m tc‖ ≤ tr := by
    apply spectrum_norm_box trp.le (ht.1.sub (scalar_sym ..)) _ _
    · have hi : scalar m (-tr)+scalar m tc=scalar m tmin := by unfold scalar; rw [← add_smul]; norm_num [tmin,tr,tc]
      rw [le_sub_iff_add_le,hi]; exact ht.2.1
    have hi : scalar m tr+scalar m tc=scalar m tmax := by unfold scalar; rw [← add_smul]; norm_num [tmax,tr,tc]
    rw [_root_.sub_le_iff_le_add,hi]; exact ht.2.2
  have he : (tc•V-(tr/2:ℝ)•(scalar m h₀+h₀⁻¹•(V*V))).IsHermitian :=
    (hv.smul (by simp [IsSelfAdjoint])).sub (((scalar_sym ..).add
      ((sqPSD hv).posSemidef.1.smul (by simp [IsSelfAdjoint]))).smul (by simp [IsSelfAdjoint]))
  apply (op_order_iff he (jordan_sym ht.1 hv)).mpr
  intro x
  let y := op V x
  have h₁ : ⟪x,op (jprod T V) x⟫=⟪op T x,y⟫ := by
    simp only [jprod,_root_.map_add,_root_.map_mul,_root_.map_smul,
      _root_.smul_apply,_root_.mul_apply_eq_comp,_root_.add_apply,
      real_inner_smul_right,inner_add_right]
    rw [← op_iff_hermitian.mp ht.1,← op_iff_hermitian.mp hv]
    rw [real_inner_comm x]; ring
  let z := op T x-tc • x
  have h₂ : ‖z‖ ≤ tr*‖x‖ := by
    have hz : z=op (T-scalar m tc) x := by
      rw [_root_.map_sub,_root_.sub_apply,op_scalar]
    rw [hz]
    exact ((op (T-scalar m tc)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  have h := neg_le_of_abs_le (abs_real_inner_le_norm z y)
  unfold z at h h₂
  rw [inner_sub_left,real_inner_smul_left] at h
  rw [h₁]
  simp only [_root_.map_sub,_root_.map_smul,_root_.map_add,_root_.map_mul,
    _root_.sub_apply,_root_.smul_apply,_root_.add_apply,
    _root_.mul_apply_eq_comp,inner_sub_right,inner_add_right,real_inner_smul_right]
  rw [show op (1:Mat m) x=x from by rw [_root_.map_one]; rfl,← op_iff_hermitian.mp hv x (op V x),
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  change tc*⟪x,y⟫-tr/2*(h₀*_+h₀⁻¹*‖y‖^2)≤ _
  have heq := mul_le_mul_of_nonneg_right h₂ (norm_nonneg y)
  norm_num [h₀,Profile.tr] at *
  nlinarith [sq_nonneg (‖x‖-2*‖y‖)]

variable [NeZero m]

lemma limitB (ht:T∈specBox m tmin tmax) (hs:LayerOK) :
    -(q.LLw q.FL 1 (fun u=>HH u-P0 u))-q.LLw q.FL T Hh ≤
      (alpha*(Real.log 2 +1/4)/4)*Hcomm q.Lmat T -
        q.BB q.FL (fun u=> ww u-ww0 u) := by
  have hf := bhj hs
  have hm (z:ℝ) (l:Fin m→ℝ) (t:Mat m) (he:t∈specBox m tmin tmax) :
      Matrix.diagonal (fun i=> wwR (z,l i)) ≤ (1:ℝ) •
        jprod t (diagonal (fun i=> bAv Hh (z,l i))) := by
    rw [one_smul]
    let V := diagonal fun i=> bAv Hh (z,l i)
    apply le_trans _ (block_boxJ he (V:=V) (Matrix.isHermitian_diagonal_iff.mpr fun i=>rfl))
    apply le_of_eq
    unfold wwR V scalar
    rw [Matrix.diagonal_mul_diagonal]
    ext i j; by_cases h:i=j
    · subst j; simp; ring
    simp [h]
  have h := q.Klimit q.FL T ht hf (w0t hs) (Rwt hs) (fun _=>(wpos hs _).2)
    1 zero_le_one hm (fun x y z=>alpha*Uy x y z) (alpha*(Real.log 2+1/4))
    (fun x y=> by
      have h:= Uy_area x y
      refine ⟨h.1.const_mul _,?_⟩; rw [integral_const_mul,h.2]; ring)
    (fun _ _ _ _ _=>mul_nonneg alpha_p.le uy_nn)
    (fun x y z hx hy=> by
      rw [one_mul]; have h := (pairEst Hh hf hx hy).1
      unfold ww0
      convert h using 1
      unfold Om; field_simp [alpha]) (klm:=(1:ℝ)) zero_lt_one
  rw [q.BB_bar q.FL ((ProjField.H_ok hs).sub (P0_wt hs)), q.BB_sub q.FL (wwt hs) (w0t hs)]
  unfold ww; rw [q.BB_add q.FL (((H_ok hs).sub (P0_wt hs)).bar) (Rwt hs)]
  change q.BB _ _-_≤ 1*q.BB _ _+ _* Hcomm q.Lmat T at h
  linarith
end ProjField
end GeneralMahler

end

end OAI
