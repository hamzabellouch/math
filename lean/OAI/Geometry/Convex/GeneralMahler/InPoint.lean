import OAI.Geometry.Convex.GeneralMahler.Angle

namespace OAI
/-! Estimates for one-dimensional layers under changing coordinates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers ProjField
variable {m : ℕ}

lemma exp_est_dir (m : ℕ) [NeZero m] :
    ∃ D ≥ 0, ∀ f : Rn m → ℝ, (∀ x y, ‖f x - f y‖ ≤ 2 * ‖x-y‖) →
    ∀ v : Rn m, ‖v‖ ≤ 2 → ∀ j : ℝ, 1 ≤ j →
    (∫ x, ⟪x,v⟫*f x ∂normal m) ≤
      D*(j*(∫ x, ‖f x‖ ∂normal m) + Real.exp (-(j^2)/4)) := by
  classical
  obtain ⟨C,hC,h₁⟩ := normal_tail m 2
  have hJ := j_nonneg m
  let D := 2+2*J m+4*(1+J m)*C
  use D
  refine ⟨by unfold D; positivity, fun f hf v hv j hj => ?_⟩
  have hk : LipschitzWith 2 f := LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [dist_eq_norm,NNReal.coe_ofNat] using hf x y
  let μ := normal m
  have hi : Integrable f μ := (PolyBound.lipschitz hk).gaussian_integrable
    hk.continuous.aestronglyMeasurable
  let F := ∫ x, ‖f x‖ ∂μ
  have hh : 0 ≤ F := integral_nonneg fun x => norm_nonneg _
  let E := fun x : Rn m => (1+‖x‖)^2
  let S : Set (Rn m) := {x| j ≤ ‖x‖}
  have hm : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  let b := 4*(1+J m)
  let g := fun x : Rn m => (2*j)*‖f x‖ + (2*F)*‖x‖ + b*S.indicator E x
  have hl (x) : ⟪x,v⟫*f x ≤ g x := by
    have h₀ : ⟪x,v⟫*f x ≤ (‖x‖*2)*‖f x‖ := calc
      _ ≤ |⟪x,v⟫*f x| := le_abs_self _
      _ ≤ _ := by
        rw [abs_mul, Real.norm_eq_abs (f x)]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg (f x))
        exact (abs_real_inner_le_norm x v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg x))
    apply h₀.trans
    by_cases hx:x∈S
    · change _ ≤ _+_+b*_
      rw [indicator_of_mem hx]
      have he := norm_le_mean_error hi hf (by norm_num) x
      change ‖f x‖ ≤ F+_ at he
      have hv : ‖x‖+J m ≤ (1+J m)*(1+‖x‖) := by nlinarith [norm_nonneg x]
      have ht : (‖x‖*2)*‖f x‖ ≤ (‖x‖*2)*(F+2*((1+J m)*(1+‖x‖))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      unfold b E
      nlinarith [norm_nonneg x,mul_nonneg hJ (norm_nonneg x),norm_nonneg (f x)]
    change _ ≤ _+_+b*_
    rw [indicator_of_notMem hx]
    change ¬j≤‖x‖ at hx
    nlinarith [norm_nonneg x,norm_nonneg (f x)]
  have hA : Integrable (fun x=> (2*j)*‖f x‖) μ := hi.norm.const_mul _
  have hB : Integrable (fun x:Rn m=> (2*F)*‖x‖) μ := (i_norm _).const_mul _
  have hE : Integrable (fun x:Rn m=> b*S.indicator E x) μ :=
    ((integrable_envelope 2).indicator hm).const_mul _
  have hg : Integrable (fun x:Rn m=>⟪x,v⟫*f x) μ := by
    have he : PolyBound (fun x:Rn m=>⟪x,v⟫) := by
      simp_rw [real_inner_comm v]
      exact PolyBound.clm (f := (show Rn m→L[ℝ] ℝ from innerSL ℝ v))
    exact (he.mul (PolyBound.lipschitz hk)).gaussian_integrable
      (((continuous_id.inner continuous_const).mul hk.continuous).aestronglyMeasurable)
  apply (integral_mono hg ((hA.add hB).add hE) hl).trans
  change ∫ x, _+_+b*S.indicator E x ∂μ ≤ _
  rw [integral_add (show Integrable (fun x=>2*j*‖f x‖+(2*F)*‖x‖) μ from hA.add hB) hE, integral_add hA hB]
  simp_rw [integral_const_mul]; rw [integral_indicator hm]
  change 2*j*F+2*F*J m+b*_ ≤ D*(j*F+_)
  have hx := h₁ j (by linarith)
  change ∫ x in S, E x ∂μ ≤ _ at hx
  have he := mul_le_mul_of_nonneg_left hx (show 0 ≤ b by unfold b; positivity)
  unfold D
  set e := Real.exp (-(j^2)/4)
  have hp : 0 ≤ e := Real.exp_nonneg _
  unfold b at *
  have hu : F ≤ j*F := by nlinarith
  calc
    _ ≤ 2*j*F + 2*(j*F)*J m + 4*(1+J m)*(C*e) := add_le_add (by nlinarith) he
    _ ≤ _ := by
      rw [← sub_nonneg]
      ring_nf
      positivity

namespace Param

variable {R:ℝ} (x:Param m R) (hr:0<R) (q₀:ProjField m) (v:Rn m) (hv:‖v‖=1)
lemma normS : ‖x.S‖ ≤ 2 ∧ ‖(equivPD x.S_pos).symm.toContinuousLinearMap‖ ≤ 2 :=
  inv_norm_box 2 (by norm_num) (A := x.S) (by simpa using x.S_box)
    (equivPD x.S_pos) (equivPD_spec _)
include hv in lemma vp_two : ‖(x.instanceQ hr q₀).vp v‖ ≤ 2 := by
  apply ((equivPD x.S_pos).symm.toContinuousLinearMap.le_opNorm v).trans
  rw [hv,mul_one]; exact x.normS.2

lemma Z_two (w:Rn m) : ‖(x.instanceQ hr q₀).Z w‖ ≤ 2*‖w‖ := by
  rw [(x.instanceQ hr q₀).Z_def]
  apply ((op (x.instanceQ hr q₀).S).le_opNorm w).trans
  rw [op_norm]; apply mul_le_mul_of_nonneg_right x.normS.1 (norm_nonneg _)

include hv in lemma coordLipX (z:ℝ) (a b:Rn m) :
    ‖⟪v,(x.instanceQ hr q₀).XT z a⟫-⟪v,(x.instanceQ hr q₀).XT z b⟫‖ ≤ 2*‖a-b‖ := by
  rw [← inner_sub_right]
  apply (abs_real_inner_le_norm ..).trans
  rw [hv,one_mul]
  apply le_trans _ (x.Z_two hr q₀ (a-b))
  have he : affineN (x.instanceQ hr q₀).root ((x.instanceQ hr q₀).shift z) a-affineN (x.instanceQ hr q₀).root ((x.instanceQ hr q₀).shift z) b=(x.instanceQ hr q₀).Z (a-b) := by
    unfold affineN Z; rw [_root_.map_sub]; abel
  rw [← he]
  simpa only [XT,sample,dist_eq_norm, NNReal.coe_one,one_mul] using (coneProj_lip (x.instanceQ hr q₀).C).dist_le_mul
    (affineN (x.instanceQ hr q₀).root ((x.instanceQ hr q₀).shift z) a) (affineN (x.instanceQ hr q₀).root ((x.instanceQ hr q₀).shift z) b)

include hv in lemma coordLipY (z:ℝ) (a b:Rn m) :
    ‖-⟪v,(x.instanceQ hr q₀).YT z a⟫- -⟪v,(x.instanceQ hr q₀).YT z b⟫‖ ≤ 2*‖a-b‖ := by
  rw [sub_neg_eq_add, ← sub_eq_neg_add, ← inner_sub_right]
  apply (abs_real_inner_le_norm ..).trans
  rw [hv,one_mul, norm_sub_rev ((x.instanceQ hr q₀).YT z b)]
  apply le_trans _ (x.Z_two hr q₀ (a-b))
  let f := fun t => -((x.instanceQ hr q₀).Z t + (x.instanceQ hr q₀).shift z)
  have he : f a-f b= -((x.instanceQ hr q₀).Z (a-b)) := by unfold f Z; rw [_root_.map_sub]; abel
  have h := (coneProj_lip (x.instanceQ hr q₀).D).dist_le_mul (f a) (f b)
  rw [dist_eq_norm,dist_eq_norm,NNReal.coe_one, one_mul,he,norm_neg] at h
  exact h

include hv in lemma small_X {K} (hk:q₀.Bound K) (he : op x.B v=R⁻¹ • v) (z:ℝ) :
    (∫ t, ‖⟪v,(x.instanceQ hr q₀).XT z t⟫‖ ∂normal m) ≤ K*m/R*a z := by
  let e := x.transE hr
  have hb (w : Rn m) (hw : w∈(x.instanceQ hr q₀).C) : ‖⟪v,w⟫‖ ≤ R⁻¹*K*⟪(x.instanceQ hr q₀).V,w⟫ := by
    obtain ⟨w,rfl⟩ := e.surjective w
    change e.toLinearEquiv w ∈ pushCone e.toLinearEquiv q₀.C at hw
    have hi := hk.inD w (by simpa using hw)
    have HH : ⟪(x.instanceQ hr q₀).V,e w⟫=⟪q₀.V,w⟫ := by
      rw [real_inner_comm, real_inner_comm w]; apply pair_contra e.toLinearEquiv
    rw [HH,show e w= _ from x.trans_apply hr w,
      ← op_iff_hermitian.mp x.in_box.1.1,he,real_inner_smul_left,norm_mul,
      Real.norm_eq_abs, abs_of_nonneg (inv_pos.mpr hr).le,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hr).le
    apply (abs_real_inner_le_norm v w).trans
    rwa [hv,one_mul]
  let l : Rn m→L[ℝ]ℝ := innerSL ℝ (x.instanceQ hr q₀).V
  have hi := (x.instanceQ hr q₀).X_int z
  calc
    _ ≤ ∫ t,R⁻¹*K*l ((x.instanceQ hr q₀).XT z t) ∂normal m := integral_mono
      (ContinuousLinearMap.integrable_comp (show Rn m→L[ℝ]ℝ from innerSL ℝ v) hi).norm
      ((l.integrable_comp hi).const_mul _) (fun t=> hb _ (proj_mem ..))
    _ = _ := by
      rw [integral_const_mul,l.integral_comp_comm hi,(x.instanceQ hr q₀).XT_mean]
      change _*⟪(x.instanceQ hr q₀).V,a z • (x.instanceQ hr q₀).U⟫=_
      rw [real_inner_smul_right,real_inner_comm,(x.instanceQ hr q₀).ip]
      ring

include hv in lemma large_Y [NeZero m] {K} (hk:q₀.Bound K) (he : op x.B v=R • v) (z:ℝ) :
    (∫ t, ‖-⟪v,(x.instanceQ hr q₀).YT z t⟫‖ ∂normal m) ≤ K*m/R*(x.instanceQ hr q₀).Bt z := by
  let e := x.transE hr
  let b := contra e.toLinearEquiv
  have hb (w : Rn m) (hw : w∈(x.instanceQ hr q₀).D) : ‖-⟪v,w⟫‖ ≤ R⁻¹*K*⟪(x.instanceQ hr q₀).U,w⟫ := by
    obtain ⟨w,rfl⟩ := b.surjective w
    change b w ∈ posDual (pushCone e.toLinearEquiv q₀.C) at hw
    rw [dual_pushCone] at hw
    have hi := hk.inC w (by simpa only [b,mem_pushCone,LinearEquiv.symm_apply_apply] using hw)
    have HH : ⟪(x.instanceQ hr q₀).U,b w⟫=⟪q₀.U,w⟫ := pair_contra e.toLinearEquiv ..
    have hv' : e v= R • v := (x.trans_apply hr _).trans he
    have HH' : ⟪v,b w⟫= R⁻¹*⟪v,w⟫ := by
      have h := pair_contra e.toLinearEquiv v w
      change ⟪e v,b w⟫=_ at h
      rw [hv',real_inner_smul_left] at h
      rw [← h]; field_simp
    rw [norm_neg,HH,HH',norm_mul,Real.norm_eq_abs,abs_of_nonneg (inv_pos.mpr hr).le,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hr).le
    apply (abs_real_inner_le_norm v w).trans
    rwa [hv,one_mul]
  let l : Rn m→L[ℝ]ℝ := innerSL ℝ (x.instanceQ hr q₀).U
  have hi := (x.instanceQ hr q₀).Y_int z
  calc
    _ ≤ ∫ t,R⁻¹*K*l ((x.instanceQ hr q₀).YT z t) ∂normal m := integral_mono
      (ContinuousLinearMap.integrable_comp (show Rn m→L[ℝ]ℝ from innerSL ℝ v) hi).neg.norm
      ((l.integrable_comp hi).const_mul _) (fun t=> hb _ (proj_mem ..))
    _ = _ := by
      rw [integral_const_mul,l.integral_comp_comm hi]
      dsimp [l,Bt]; have H:= m_pos (m:=m); field_simp
end Param

lemma angle_est [NeZero m] (q₀:ProjField m) :
    ∃ D ≥ 0, ∀ R, ∀ hr:0<R, ∀ x : Param m R, ∀ v:Rn m, ‖v‖=1 →
      let q := x.instanceQ hr q₀
      ∀ (z:ℝ) (j:ℝ), 1 ≤ j →
       (op x.B v= R⁻¹ • v → q.dimH v z ≤ D*(j/R*a z+ Real.exp (-(j^2)/4))) ∧
       (op x.B v= R • v → 1-q.dimH v z ≤ D*(j/R*q.Bt z+ Real.exp (-(j^2)/4))) := by
  obtain ⟨K,hK⟩ := q₀.Field_isBound
  obtain ⟨C,hC,hc⟩ := exp_est_dir m
  have hv := hK.positive
  use C*(1+K*m)
  refine ⟨by positivity, fun R hr x v hv z j hj => ?_⟩
  let q := x.instanceQ hr q₀
  have HH (F g : ℝ) (hf : F ≤ K*m/R*g) (hg : 0 ≤ g) :
      C*(j*F+Real.exp (-(j^2)/4)) ≤ C*(1+K*m)*(j/R*g+Real.exp (-(j^2)/4)) := by
    rw [mul_assoc C]
    apply mul_le_mul_of_nonneg_left _ hC
    apply le_trans (add_le_add (mul_le_mul_of_nonneg_left hf (by linarith)) le_rfl)
    rw [← sub_nonneg]; ring_nf; positivity
  constructor
  · intro he
    change q.dimH _ _ ≤ _
    rw [q.dimH_X]
    exact (hc _ (x.coordLipX hr q₀ v hv z) (q.vp v) (x.vp_two hr q₀ v hv) j hj).trans
      (HH _ _ (x.small_X hr q₀ v hv hK he z) (a_pos z).le)
  intro he
  change 1-q.dimH v z≤_
  rw [q.dimH_Y v hv]
  exact (hc _ (x.coordLipY hr q₀ v hv z) (q.vp v) (x.vp_two hr q₀ v hv) j hj).trans
    (HH _ _ (x.large_Y hr q₀ v hv hK he z) (q.Bt_nonneg z))
end GeneralMahler

end

end OAI
