import OAI.Geometry.Convex.GeneralMahler.LogPath

namespace OAI
/-! Exact linear and nonnegative surplus terms in the log identity. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]
omit [NeZero m] in
lemma meas_trN : Measurable (@trN m) := by simp_rw [← funext trL_apply]; exact trL.continuous.measurable
omit [NeZero m] in
lemma poly_trN : PolyBound (@trN m) := by simp_rw [← funext trL_apply]; exact PolyBound.clm _
omit [NeZero m] in
lemma meas_inv : Measurable (fun A:Mat m=>A⁻¹) := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv]
  exact det_cdiff.continuous.measurable.inv.smul continuous_id.matrix_adjugate.measurable
omit [NeZero m] in
lemma meas_thresh : Measurable (@thresh m) :=
  measurable_const.sub (meas_inv.comp (measurable_const.add measurable_id))

namespace Edge
variable (e:Edge m)
omit [NeZero m] in
lemma path_int_meas : Measurable fun v:ℝ × Rn m=> e.H v.2 v.1 := by
  classical
  let f := fun x:ℝ × (ℝ × Rn m)=> e.WP x.1 x.2.2
  let S : Set (ℝ × (ℝ × Rn m)) := {x|x.1≤x.2.1}
  have hs : MeasurableSet S := (isClosed_le continuous_fst (continuous_fst.comp continuous_snd)).measurableSet
  have hm : StronglyMeasurable (S.indicator f) :=
    (e.wp_meas.comp_measurable (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).indicator hs
  have he (v:ℝ×Rn m) : e.H v.2 v.1=∫ x,S.indicator f (x,v) := by
    unfold H
    rw [← integral_indicator measurableSet_Iic]
    congr 1
  simp_rw [he]
  let g := fun x (v:ℝ×Rn m)=>S.indicator f (x,v)
  exact ((show StronglyMeasurable g.uncurry from hm).integral_prod_left).measurable
omit [NeZero m] in
lemma meas_beta : Measurable fun v:ℝ×Rn m=>e.beta v.2 v.1 :=
  (c_mj.measurable.comp measurable_fst).mul
    (meas_trN.comp ((meas_thresh.comp
      (((c_mc.measurable.comp measurable_fst).inv).smul e.path_int_meas)).mul
      (measurable_const.sub e.meas)))

omit [NeZero m] in
lemma meas_h1 : Measurable fun v:ℝ×Rn m=> e.h1 v.2 v.1 :=
  meas_trN.comp e.meas
lemma beta_mixed : mixed fun z x=> e.beta x z := by
  have he : PolyBound (fun v:ℝ × Rn m=> e.beta v.2 v.1) :=
    (poly_mj.comp PolyBound.fst).mono fun v=>by
      change ‖e.beta _ _‖≤‖MillsJ _‖
      rw [Real.norm_of_nonneg (mj_pos _).le,Real.norm_of_nonneg (e.beta_bound ..).1]
      exact (e.beta_bound ..).2
  apply mixed.of_cutoff he e.r_poly
  intro z x hz
  rw [Real.norm_eq_abs,lt_abs] at hz
  rcases hz with h|h
  · exact (e.path_pos x h).2.1
  exact (e.path_neg x (by linarith)).2.2.1

def LinearT (z:ℝ) (x:Rn m) := MillsJ z*(e.h1 x z-st z)

omit [NeZero m] in
lemma meas_T : StronglyMeasurable e.LinearT.uncurry :=
  ((c_mj.measurable.comp measurable_fst).mul
    (e.meas_h1.sub (measurable_st.comp measurable_fst))).stronglyMeasurable
lemma mixed_T : mixed e.LinearT := by
  have hi : PolyBound (fun v:ℝ × Rn m=> e.h1 v.2 v.1) := poly_trN.comp e.P_poly
  have ht : PolyBound e.LinearT.uncurry := (poly_mj.comp PolyBound.fst).mul
    (hi.sub (st_poly.comp PolyBound.fst))
  apply mixed.of_cutoff ht e.r_poly
  intro z x hz
  rw [Real.norm_eq_abs,lt_abs] at hz
  rcases hz with h|h
  · have hi := e.path_pos x h
    simp only [LinearT, hi.2.2,st,ite_eq_left ((e.r_pos x).trans h).le,sub_self,mul_zero]
  have hi := e.path_neg x (z:=z) (by linarith)
  have hh : ¬0 ≤ z := by have hh := e.r_pos x; linarith
  simp [LinearT,hi.2.2.2,st,hh]

lemma gain_poly : PolyBound fun x=>logD (e.Jedge x) := by
  have h := (poly_lc.comp e.r_poly).norm.add ((poly_trN.comp e.Jedge_poly).norm)
  apply h.mono
  intro x
  obtain ⟨hh,h'⟩ := logD_between (e.Jedge_pd x) (mc_pos _) (e.Jedge_bound x)
  change LC _ ≤ _ at hh
  change ‖logD _‖ ≤ ‖‖LC _‖+‖trN _‖‖
  rw [Real.norm_of_nonneg (show 0≤‖LC (e.radius x)‖+‖trN (e.Jedge x)‖ by positivity)]
  rw [Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,abs_le]
  refine ⟨le_trans ?_ hh,h'.trans ?_⟩ <;> grind
lemma gain_int : Integrable (fun x=>logD (e.Jedge x)) (normal m) :=
  e.gain_poly.gaussian_integrable
    (meas_logD.comp e.Jedge_SM.measurable).aestronglyMeasurable

lemma gain_exact (x) :
    logD (e.Jedge x)=LC 0+(∫ z,e.LinearT z x) + ∫ z,e.beta x z := by
  let F := e.Fedge x
  let f := fun z=>e.LinearT z x + e.beta x z
  let a := e.radius x+1
  have hi : 0<a := by unfold a; have h := e.r_pos x; linarith
  have hf : Integrable (fun z=> e.LinearT z x) := mixed_integrable_left e.mixed_T x
    (e.meas_T.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hg : Integrable (e.beta x) := mixed_integrable_left e.beta_mixed x
    (e.meas_beta.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hh : (∫ z in -a..a,f z)=∫ z,f z := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rcases (show z≤ -a ∨ a<z from by simp only [mem_Ioc] at hz; grind) with h|h
    · have he : z < -e.radius x := by unfold a at h; linarith
      have h' := e.path_neg x he
      have hx : ¬0≤z := by linarith
      simp [f,LinearT,h'.2.2,hx,st]
    have he : e.radius x < z := by unfold a at h; linarith
    have h' := e.path_pos x he
    have hx : 0 ≤ z := by linarith
    simp [f,LinearT,h'.2,hx,st]
  have hJ : IntervalIntegrable f volume (-a) (0:ℝ) :=
    (hf.add hg).intervalIntegrable ..
  have ht := e.Fedge_d x
  have hR : (∫ z in (0:ℝ)..a,f z)= F a - F 0 := by
    rw [← (e.F_AC x 0 a).integral_deriv_eq_sub]
    rw [intervalIntegral.integral_of_le hi.le,intervalIntegral.integral_of_le hi.le]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ht, ae_restrict_mem measurableSet_Ioc] with z hz hy
    have hy' : 0≤z := le_of_lt (mem_Ioc.mp hy).1
    rw [hz.deriv]
    unfold f LinearT st; rw [ite_eq_left hy']; ring
  have hL : (∫ z in -a..(0:ℝ),f z)+(LC 0-LC (-a)) = F 0-F (-a) := by
    have hj (x:ℝ) : deriv LC x= -MillsJ x := (d_lc x).deriv
    have he : (∫ z in -a..(0:ℝ), -MillsJ z) = LC 0-LC (-a) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _=> d_lc z) (c_mj.neg.intervalIntegrable ..)
    rw [← he, ← intervalIntegral.integral_add hJ (show IntervalIntegrable (fun z=> -MillsJ z) volume (-a) 0 from c_mj.neg.intervalIntegrable ..),
      ← (e.F_AC x (-a) 0).integral_deriv_eq_sub]
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    apply integral_congr_ae
    have h₀ : ∀ᵐ z:ℝ, z≠0 := by rw [ae_iff]; simp
    filter_upwards [ae_restrict_of_ae ht,ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae h₀] with z hz hy hh
    have hy' : ¬0≤z := not_le_of_gt (lt_of_le_of_ne (mem_Ioc.mp hy).2 hh)
    rw [hz.deriv]
    unfold f LinearT st; rw [ite_eq_right hy']; ring
  have hl : F (-a)=LC (-a) := (e.path_neg x (by unfold a; linarith)).2.1
  have hr : F a=logD (e.Jedge x) := (e.path_pos x (by unfold a; linarith)).1
  rw [hr] at hR; rw [hl] at hL
  have hu : (∫ z in -a..(0:ℝ),f z)+(∫ z in (0:ℝ)..a,f z)=
      (∫ z,e.LinearT z x)+∫ z,e.beta x z :=
    (intervalIntegral.integral_add_adjacent_intervals hJ ((hf.add hg).intervalIntegrable ..)).trans
      (hh.trans (integral_add hf hg))
  linarith
end Edge
end GeneralMahler

end

end OAI
