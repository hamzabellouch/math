import OAI.Geometry.Convex.GeneralMahler.GainIndent

namespace OAI
/-! Lower bound for beta on the band l∈[-z,z] for z≥0, using
integration by parts against 1/W; equivalent to the subprobability
argument in the paper. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]

namespace Edge
variable (e:Edge m) (x:Rn m) (z:ℝ)
def BH (l:ℝ) := e.H x z - e.H x l
lemma BH_both (l:ℝ) (hl:l≤z) :
    0 ≤ e.BH x z l ∧ e.BH x z l ≤ scalar m (MillsC l-MillsC z) := by
  rw [BH,e.H_diff,intervalIntegral.integral_of_le hl]
  let μ := volume.restrict (Ioc l z)
  have hi : Integrable (fun y=> e.WP y x) μ := (e.wp_slice_i x).integrableOn
  constructor
  · exact (psd_integral hi (ae_of_all _ fun y=>(e.wp_psd y x).posSemidef)).nonneg
  let f := fun y:ℝ=> MillsW y • (1:Mat m)
  have hh : IntervalIntegrable MillsW volume l z := c_mw.intervalIntegrable ..
  have he := hh.1
  have hF : Integrable f μ := he.smul_const _
  have hu : scalar m (MillsC l-MillsC z) = ∫ y in Ioc l z,f y := by
    unfold f scalar; rw [integral_smul_const, ← intervalIntegral.integral_of_le hl]
    have h (t:ℝ) : HasDerivAt (-MillsC) (MillsW t) t := by simpa using (d_mc t).neg
    have hx := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> h t) hh
    rw [hx]; simp [sub_eq_add_neg,add_comm]
  rw [hu, ← sub_nonneg]
  change 0 ≤ (∫ y,f y ∂μ)-∫ y,e.WP y x ∂μ
  rw [← integral_sub hF hi]
  exact (psd_integral (hF.sub hi) (ae_of_all _ fun y=> (sub_nonneg.mpr (e.wp_le y x)).posSemidef)).nonneg
lemma BH_beta (l:ℝ) (hl:l≤z) :
    (MillsC l)⁻¹ • e.BH x z l ≤ thresh (e.Sh x z) := by
  let c := MillsC z; let d := MillsC l; let B := e.BH x z l
  have hc : 0 < c := mc_pos z
  have hd : 0 < d := mc_pos l
  let D := c⁻¹ • B
  have hi : 0 ≤ D := smul_nonneg (inv_pos.mpr hc).le (e.BH_both x z l hl).1
  have ht : D≤e.Sh x z := smul_le_smul_of_nonneg_left
    (sub_le_self _ (e.H_nonneg x l)) (inv_pos.mpr hc).le
  apply le_trans _ (thresh_mono hi ht)
  have hh : 1+D ≤ scalar m (c⁻¹*d) :=
    le_trans (show 1+D ≤ 1+c⁻¹ • scalar m (d-c) from add_le_add le_rfl
      (smul_le_smul_of_nonneg_left (e.BH_both x z l hl).2 (inv_pos.mpr hc).le)) (by
        apply le_of_eq
        have hx : 1+c⁻¹*(d-c)=c⁻¹*d := by field_simp; ring
        simp only [scalar,smul_smul]
        conv_rhs => rw [← hx,add_smul,one_smul])
  apply le_trans _ (thresh_low hi (mul_pos (inv_pos.mpr hc) hd) hh)
  apply le_of_eq; change d⁻¹•B=(c⁻¹*d)⁻¹•(c⁻¹•B); rw [smul_smul]
  congr 1
  field_simp

def FF (l:ℝ) := trN (e.BH x z l*(1-e.P z x))
def ntb (l:ℝ) := trN (e.P l x*(1-e.P z x))
lemma ntb_both (l:ℝ) : 0 ≤ e.ntb x z l ∧ e.ntb x z l ≤ 1 :=
  trN_prod_unit (e.psd ..) (e.le_one ..) (sub_nonneg.mpr (e.le_one ..)) (sub_le_self _ (e.psd ..))

lemma FF_upper (l:ℝ) (hl:l≤z) :
    e.FF x z l ≤ e.beta x z/MillsJ z*MillsC l := by
  have hh := trN_mul_mono (e.BH_beta x z l hl) (sub_nonneg.mpr (e.le_one z x))
  rw [smul_mul_assoc,trN_smul] at hh
  have ht := mj_pos z
  unfold beta FF
  rw [mul_div_cancel_left₀ _ ht.ne']
  rwa [inv_mul_eq_div,div_le_iff₀ (mc_pos _)] at hh

def trC : Mat m→L[ℝ]ℝ :=
  trL.comp ((ContinuousLinearMap.mul ℝ (Mat m)).flip (1-e.P z x))
omit [NeZero m] in
lemma trC_eq (A:Mat m) : e.trC x z A=trN (A*(1-e.P z x)) := by simp [trC,mul_sub,trN_sub]

lemma FF_lip : ∃ K,LipschitzWith K (e.FF x z) := by
  rw [show e.FF x z=(e.trC x z) ∘ e.BH x z from funext (fun l=> (e.trC_eq x z _).symm)]
  exact ⟨_, (e.trC x z).lipschitzWith.comp
    ((LipschitzWith.const (e.H x z)).sub (e.H_lip x))⟩
lemma FF_deriv :
    ∀ᵐ l:ℝ, HasDerivAt (e.FF x z) (-(MillsW l * e.ntb x z l)) l := by
  filter_upwards [e.H_deriv x] with l hl
  have hf : HasDerivAt (e.BH x z) (-e.WP l x) l := by
    have h := (hasDerivAt_const l (e.H x z)).sub hl
    rw [zero_sub] at h
    exact h
  have hh := (e.trC x z).hasFDerivAt.comp_hasDerivAt l hf
  rw [_root_.map_neg,WP,_root_.map_smul,e.trC_eq] at hh
  have he : e.FF x z=(e.trC x z) ∘ e.BH x z := by ext; simp [FF,e.trC_eq]
  rw [he]; exact hh

def Wi (t:ℝ) := (MillsW t)⁻¹
lemma d_wi₀ (t:ℝ) : HasDerivAt Wi (-(MillsC t*((1-MillsW t)-MillsJ t^2))/((MillsW t)^2)) t :=
  (d_mw t).inv (mw_pos _).ne'
lemma d_wi (t:ℝ) : HasDerivAt Wi (deriv Wi t) t := (d_wi₀ t).differentiableAt.hasDerivAt
lemma dw_cont : Continuous (deriv Wi) := by
  simp_rw [funext (fun t=>(d_wi₀ t).deriv)]
  exact (((c_mc.mul ((continuous_const.sub c_mw).sub (c_mj.pow 2))).neg).div (c_mw.pow 2)
    (fun t=>pow_ne_zero 2 (mw_pos _).ne'))
lemma wi_cd : ContDiff ℝ 1 Wi :=
  contDiff_one_iff_deriv.mpr ⟨fun t=>(d_wi t).differentiableAt,dw_cont⟩
lemma dwi_nonneg (t:ℝ) : 0 ≤ deriv Wi t :=
  (show Monotone Wi from fun _x _y h=> (inv_le_inv₀ (mw_pos _) (mw_pos _)).mpr (mw_anti h)).deriv_nonneg

lemma ntb_int (a b:ℝ) : IntervalIntegrable (e.ntb x z) volume a b := by
  have he : Measurable (e.ntb x z) :=
    meas_trN.comp (((e.meas.comp (measurable_id.prodMk measurable_const)).mul measurable_const))
  apply intervalIntegrable_iff.mpr
  let μ := volume.restrict (Ι a b)
  have : IsFiniteMeasure μ := by
    apply isFiniteMeasure_restrict.mpr
    exact (lt_of_le_of_lt (measure_mono uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top).ne
  exact (integrable_const (μ:=μ) (1:ℝ)).mono' he.aestronglyMeasurable (ae_of_all _ fun t=> by
    rw [Real.norm_of_nonneg (e.ntb_both x z t).1]; exact (e.ntb_both x z t).2)

lemma band (hz:0≤z) :
    (∫ l in -z..z,e.ntb x z l) ≤ 4*e.beta x z := by
  let f := e.FF x z
  let b := e.beta x z/MillsJ z
  have hb : 0 ≤ b := div_nonneg (e.beta_bound ..).1 (mj_pos _).le
  have he : -z ≤ z := by linarith
  obtain ⟨K,h⟩ := e.FF_lip x z
  have hf : Continuous f := h.continuous
  have ha := (h.lipschitzOnWith (s:=uIcc (-z) z)).absolutelyContinuousOnInterval
  have hc : AbsolutelyContinuousOnInterval Wi (-z) z :=
    wi_cd.contDiffOn.absolutelyContinuousOnInterval
  let G := fun t=>f t*deriv Wi t
  have hg : Continuous G := hf.mul dw_cont
  have hbase := (ha.fun_mul hc).integral_deriv_eq_sub
  have h₀ : f z=0 := by unfold f FF BH; simp [trN]
  have hh : (∫ l in -z..z,e.ntb x z l)=f (-z)*Wi (-z)+(∫ l in -z..z,G l) := by
    have hi : (∫ l in -z..z,deriv (fun t=>f t*Wi t) l) =
        ∫ l in -z..z,(G l-e.ntb x z l) := by
      rw [intervalIntegral.integral_of_le he,intervalIntegral.integral_of_le he]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (e.FF_deriv x z)] with t ht
      have hu : deriv (fun t=>f t*Wi t) t=-(MillsW t*e.ntb x z t)*Wi t+f t*deriv Wi t :=
        (ht.fun_mul (d_wi t)).deriv
      rw [hu]; unfold G Wi; field_simp [ne_of_gt (mw_pos t)]; ring
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable ..) (e.ntb_int ..)] at hi
    change (∫ l in -z..z,deriv (fun t=> f t*Wi t) l)=_ at hbase
    change _= f z*Wi z-f (-z)*Wi (-z) at hbase
    rw [h₀] at hbase; linarith
  let H := fun t=>MillsC t*deriv Wi t
  have ht : Continuous H := c_mc.mul dw_cont
  have hH : MillsC (-z)*Wi (-z)+(∫ t in -z..z,H t)=MillsC z*Wi z+2*z := by
    have hd (t:ℝ) : HasDerivAt (fun t=>MillsC t*Wi t) (H t-1) t := by
      convert (d_mc t).fun_mul (d_wi t) using 1
      all_goals first | rfl | (unfold H Wi; field_simp [ne_of_gt (mw_pos t)]; ring)
    have hu := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> hd t)
      ((ht.sub continuous_const).intervalIntegrable (-z) z)
    rw [intervalIntegral.integral_sub (ht.intervalIntegrable ..)
      (continuous_const.intervalIntegrable ..)] at hu
    simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one] at hu
    linarith
  have hw : Wi (-z) ≥ 0 := (inv_pos.mpr (mw_pos _)).le
  have hu : ∫ l in -z..z,G l ≤ ∫ l in -z..z,b*H l :=
    intervalIntegral.integral_mono_on he (hg.intervalIntegrable ..)
      ((continuous_const.mul ht).intervalIntegrable ..) fun l hl=>
      le_trans (mul_le_mul_of_nonneg_right (e.FF_upper x z l hl.2) (dwi_nonneg l))
        (by unfold b H; rw [mul_assoc])
  rw [intervalIntegral.integral_const_mul] at hu
  calc
    _ = _ := hh
    _ ≤ (b*MillsC (-z))*Wi (-z)+ b* (∫ l in -z..z,H l) :=
      add_le_add (mul_le_mul_of_nonneg_right (e.FF_upper x z (-z) he) hw) hu
    _ = b*(MillsC z*Wi z+2*z) := by rw [← hH]; ring
    _ ≤ b*(4*MillsJ z) := by
      apply mul_le_mul_of_nonneg_left _ hb
      have hp := mj_pos z
      have hc := mc_pos z
      have hx : MillsC z*Wi z = (MillsJ z)⁻¹ := by unfold Wi MillsW; field_simp
      have hz' : z ≤ MillsJ z := by unfold MillsJ; linarith
      rw [hx]
      have hy : 1≤2*MillsJ z^2 := by
        have hh := mj_mono hz
        have he : MillsJ 0^2=2/π := by
          unfold MillsJ MillsC; rw [p_half,phi_apply]
          have he := Real.sq_sqrt (show 0≤2*π by positivity)
          have hi : 0 < √(2*π) := by positivity
          simp only [zero_add,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true, zero_pow,neg_zero,zero_div, Real.exp_zero,mul_one]
          field_simp
          nlinarith
        have h₁ := Real.pi_lt_four
        have h₂ := Real.pi_pos
        have h₃ : 1≤2*MillsJ 0^2 := by rw [he]; apply le_of_sub_nonneg; field_simp; linarith
        nlinarith [mj_pos 0]
      rw [← one_div]
      have hh : 1/MillsJ z ≤ 2*MillsJ z := (div_le_iff₀ hp).mpr (by nlinarith)
      linarith
    _ = _ := by unfold b; field_simp [ne_of_gt (mj_pos z)]
end Edge
end GeneralMahler

end

end OAI
