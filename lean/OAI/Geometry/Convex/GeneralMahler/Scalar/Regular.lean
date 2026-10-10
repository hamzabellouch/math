import OAI.Geometry.Convex.GeneralMahler.Scalar.Grid

namespace OAI
/-! Smooth growth and reflection for all profiles. -/
open Set Filter Real
noncomputable section
namespace GeneralMahler.SCal
open Profile Jet Tag Layers
variable {f:ℝ→ℝ}
lemma root_reg (h:TestF f) (d:ℝ) (he:0<d) (hh:∀ x,d≤f x) :
    TestF (fun x=> (√(f x))⁻¹) ∧ TestF (fun x=> √(f x)) := by
  let g:=fun x=> (√(f x))⁻¹
  have hp(x:ℝ):0<f x := lt_of_lt_of_le he (hh x)
  have hq(x:ℝ):0<√(f x):=Real.sqrt_pos.mpr (hp x)
  let F:=fun x=> √(f x)
  have hd (x): HasDerivAt F ((1/2*deriv f x)*g x) x := by
    convert (Real.hasDerivAt_sqrt (hp x).ne').comp x (h.diff x).hasDerivAt using 1
    all_goals first | rfl| (unfold g; ring)
  have hj (x): HasDerivAt g (((-(1/2)*deriv f x*g x)*g x)*g x) x := by
    convert (hd x).inv (hq x).ne' using 1
    all_goals first| rfl|(unfold g F; ring)
  have ht : TestF g:= by
    intro n; induction n with
    | zero=>
      have he : PolyBound g:= PolyBound.of_bound (√d)⁻¹ fun x=>by
        unfold g; rw [Real.norm_of_nonneg (inv_pos.mpr (hq _)).le]
        exact (inv_le_inv₀ (hq _) (Real.sqrt_pos.mpr he)).mpr (Real.sqrt_le_sqrt (hh _))
      exact ⟨he,continuous_iff_continuousAt.mpr fun x=>(hj x).continuousAt⟩
    | succ n ih=>
      exact Moderate.mk' hj (((((Moderate.const _ n).mul (h.der n)).mul ih).mul ih).mul ih)
  exact ⟨ht, TestF.of_d hd (((TestF.const _).mul h.der).mul ht)⟩
lemma q_reg (h:∀ x,(5:ℝ)/100 ≤ rad x): TestF qu := by
  have hi: TestF rad := (TestF.const _).sub d_test
  exact (TestF.const _).sub (root_reg hi (5/100) (by norm_num) h).2

lemma ua_reg: TestF angle := by
  let f:=fun x:ℝ=> 1+x^2
  have he: TestF f := (TestF.const _).add (sq_test TestF.id)
  let v:=fun x=> (√(1+(x/sb)^2))⁻¹
  have hv: TestF v:= by
    have hp : TestF (fun x:ℝ=>x/sb) := by
      simp only [div_eq_mul_inv]; apply TestF.id.mul (TestF.const _)
    apply (root_reg ((TestF.const _).add (sq_test hp)) 1 zero_lt_one _).1
    intro x; nlinarith
  apply TestF.of_d (g:= fun x=> omegaP*(v x*sb⁻¹)) _ ((TestF.const _).mul (hv.mul (TestF.const _)))
  intro x
  convert (((Real.hasDerivAt_arsinh (x/sb)).comp x ((hasDerivAt_id' x).div_const sb)).const_mul omegaP)
    using 1
  all_goals first|rfl|(unfold v;ring)
lemma ucs_reg: TestF uc ∧ TestF us := by
  let c:=fun x=>Real.cos (angle x)
  let s:=fun x=>Real.sin (angle x)
  have hc (x:ℝ):HasDerivAt c (-(s x*deriv angle x)) x:= by
    convert (Real.hasDerivAt_cos _).comp x (ua_reg.diff x).hasDerivAt using 1
    all_goals first|rfl|(unfold s;ring)
  have hs (x): HasDerivAt s (c x*deriv angle x) x :=
    (Real.hasDerivAt_sin _).comp x (ua_reg.diff x).hasDerivAt
  have hi (n:Nat): Moderate n c ∧ Moderate n s:= by
    induction n with
    | zero=> exact ⟨⟨PolyBound.of_bound 1 (fun x=>Real.abs_cos_le_one _),continuous_cos.comp ua_reg.cont⟩,
        ⟨PolyBound.of_bound 1 (fun x=>Real.abs_sin_le_one _),continuous_sin.comp ua_reg.cont⟩⟩
    | succ n ih=> exact ⟨Moderate.mk' hc (ih.2.mul (ua_reg.der n)).neg, Moderate.mk' hs (ih.1.mul (ua_reg.der n))⟩
  exact ⟨(TestF.const _).mul (fun n=>(hi n).1),(TestF.const _).mul (fun n=>(hi n).2)⟩

lemma Geven : Function.Even Profile.g := by
  intro x
  unfold Profile.g
  have hh:=Y_ref x; have he : X (-x)=Y x:=by rw [← Y_ref,neg_neg]
  rw [hh,he,j_ref,← j_ref,neg_neg]; ring
lemma Deven : Function.Even Profile.d := by
  intro x; unfold Profile.d Xd Yd
  have he : X (-x)=Y x:=by rw [← Y_ref,neg_neg]
  rw [he,Y_ref,j_ref,← j_ref,neg_neg]; ring
lemma Reven : Function.Even rad:= by intro x; unfold rad; rw [Deven]
lemma Keven : Function.Even Kp:=by intro x; unfold Kp; rw [Geven,Deven]
lemma Ceven : Function.Even Cp:=by
  intro x; unfold Cp; rw [Deven, map_deriv_odd g_test.der (map_deriv_even g_test Geven)]
lemma Qeven : Function.Even qu:=by intro x; unfold qu;rw [Reven]
lemma uc_ref : Function.Even uc:= by intro x; unfold uc angle; rw [neg_div,Real.arsinh_neg,mul_neg]; simp
lemma us_ref : Function.Odd us:= by intro x; unfold us angle; rw [neg_div,Real.arsinh_neg,mul_neg]; simp
lemma N_ref (hf:TestF f) (h:Function.Even f):Function.Even (N2 f):=by
  have hi:=map_deriv_even hf h
  intro x; unfold N2 N; rw [hi,h,map_deriv_odd hf.der hi]; ring
lemma lift_ref (h:Function.Even f) : Function.Even (liftF f) := by
  intro x; unfold liftF xs; rw [Real.sinh_neg,mul_neg,h]
lemma x_neg (x):xs (-x) = -(xs x):=by simp [xs]
lemma a_neg (x):ast (-x)=ast x:=by simp [ast]
lemma t_ref (h:TestF f) (hh:Function.Even f):
    Function.Odd (DotF f) ∧ Function.Even (DDot f)∧ Function.Even (NNf f) := by
  have hi (x:ℝ) := (d_lift h x).deriv
  have hv (x:ℝ) := (dd_lift h x).deriv
  have hj:= map_deriv_even h hh
  have ha : Function.Odd (DotF f):= by
    intro x; unfold DotF; rw [hi,hi,x_neg,a_neg,hj]; ring
  have hb : Function.Even (DDot f):= by
    intro x; unfold DDot; rw [hv,hv,x_neg,a_neg,hj,map_deriv_odd h.der hj]; ring
  exact ⟨ha,hb,fun x=> by unfold NNf thR; rw [ha,hb,x_neg,a_neg]; ring⟩
namespace Tag
def odd : Tag→Bool
  | dK|dC|dQ|RV =>true
  | _=>false
lemma TvEv {i:Tag}(hf:TestF qu) (he:i.odd=false):Function.Even i.act:= by
  cases i <;> simp only [odd,Bool.true_eq_false] at he
  · exact lift_ref Reven
  · exact lift_ref Keven
  · exact lift_ref Ceven
  · exact lift_ref Qeven
  · exact (t_ref testK Keven).2.1
  · exact (t_ref testC Ceven).2.1
  · exact (t_ref hf Qeven).2.1
  · exact (t_ref testK Keven).2.2
  · exact (t_ref testC Ceven).2.2
  · exact (t_ref hf Qeven).2.2
  · exact lift_ref (map_deriv_odd v_test.der (map_deriv_even v_test Veven))
  exact lift_ref (N_ref hf Qeven)
lemma TvOd {i:Tag} (hf:TestF qu) (he:i.odd=true):Function.Odd i.act:=by
  cases i <;> simp only [odd,Bool.false_eq_true] at he
  · exact (t_ref testK Keven).1
  · exact (t_ref testC Ceven).1
  · exact (t_ref hf Qeven).1
  intro x
  change deriv Profile.v (xs (-x))-xs (-x)=-(deriv Profile.v (xs x)-xs x)
  rw [x_neg, map_deriv_even v_test Veven]; ring
end Tag
end GeneralMahler.SCal

end

end OAI
