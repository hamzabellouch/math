import OAI.Geometry.Convex.GeneralMahler.TraceOrder
import OAI.Geometry.Convex.GeneralMahler.MixedField
import OAI.Geometry.Convex.GeneralMahler.MillsLog

namespace OAI
/-! Deterministic-endcut layer of PSD contractions. Carries the
precise data needed for log-Jacobian estimate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ}
structure Edge (m:ℕ) where
  P : ℝ → Rn m → Mat m
  psd : ∀ z x, 0 ≤ P z x
  le_one : ∀ z x,P z x≤1
  meas : Measurable P.uncurry
  C : ℝ
  hp : 1 ≤ C
  tend_pos : ∀ z x,C*(1+‖x‖)<z → P z x=1
  tend_neg : ∀ z x,C*(1+‖x‖)< -z → P z x=0

variable [NeZero m]
namespace ProjField
variable (q:ProjField m)
lemma Field_tend :
    ∃ c≥(1:ℝ), (∀ z x,c*(1+‖x‖)<z → q.Pmat z x=1) ∧
      (∀ z x,c*(1+‖x‖)< -z → q.Pmat z x=0) := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  obtain ⟨a,ha,h⟩ := positive_cutoff m hk.one_le
  obtain ⟨b,hb,h'⟩ := negative_cutoff m hk.one_le
  refine ⟨max a b,ha.trans (le_max_left ..),?_,?_⟩
  · intro z x hx; apply projJac_id q.C (h _ hk _ x ?_)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)) hx
  intro z x hx
  have hi := h' q hk (-z) x (lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)) hx)
  rw [neg_neg] at hi
  exact projJac_zero q.C hi

def edge : Edge m where
  P := q.Pmat
  psd := q.Pmat_psd
  le_one := q.Pmat_le
  meas :=
    ((strongly_projJac q.C).comp_measurable
      ((q.root.continuous.comp continuous_snd).add (q.shift_cd.continuous.comp continuous_fst)).measurable).measurable
  C := q.Field_tend.choose
  hp := q.Field_tend.choose_spec.1
  tend_pos := q.Field_tend.choose_spec.2.1
  tend_neg := q.Field_tend.choose_spec.2.2
end ProjField
namespace Edge
variable (e:Edge m)
def ref : Edge m where
  P := fun z x=>1-e.P (-z) x
  psd := fun z x=> sub_nonneg.mpr (e.le_one ..)
  le_one := fun z x=> sub_le_self _ (e.psd ..)
  meas := measurable_const.sub (e.meas.comp ((measurable_neg.comp measurable_fst).prodMk measurable_snd))
  C := e.C
  hp := e.hp
  tend_pos := fun z x hx=> by rw [e.tend_neg _ _ (by simpa using hx),sub_zero]
  tend_neg := fun z x hx=> by rw [e.tend_pos _ _ hx,sub_self]

def radius (x:Rn m) := e.C*(1+‖x‖)
omit [NeZero m] in
lemma r_meas : Continuous e.radius := by unfold radius; fun_prop
omit [NeZero m] in
lemma r_poly : PolyBound e.radius := (PolyBound.const _).mul
  ((PolyBound.const _).add PolyBound.id.norm)
omit [NeZero m] in
lemma r_pos (x) : 0 < e.radius x := mul_pos (lt_of_lt_of_le zero_lt_one e.hp) (by positivity)
omit [NeZero m] in
lemma Pcont (x y) : ‖e.P x y‖ ≤ 1 := by
  apply spectrum_norm_box zero_le_one (e.psd ..).posSemidef.1
  · apply le_trans _ (e.psd ..)
    have he := scalar_le' (m:=m) (-1) 0 (by norm_num)
    simpa only [scalar, zero_smul] using he
  simpa [scalar] using e.le_one x y
omit [NeZero m] in
lemma P_poly : PolyBound e.P.uncurry := PolyBound.of_bound 1 fun ⟨x,y⟩=>e.Pcont x y

def EP (z:ℝ) (x:Rn m) := e.P z x-st z • (1:Mat m)
lemma st_poly : PolyBound st := PolyBound.of_bound 1 fun x=>by unfold st; split <;> simp
omit [NeZero m] in
lemma EP_mixed : mixed e.EP := by
  have h : PolyBound (fun x:ℝ × Rn m=> st x.1 • (1:Mat m)) := (st_poly.comp PolyBound.fst).smul
    (PolyBound.const _)
  apply mixed.of_cutoff (e.P_poly.sub h) e.r_poly
  intro x y hx
  unfold EP st; split_ifs with ht
  · rw [e.tend_pos _ _ (by rw [Real.norm_of_nonneg ht] at hx; exact hx),one_smul,sub_self]
  rw [e.tend_neg _ _ (by rw [Real.norm_eq_abs,abs_of_neg (lt_of_not_ge ht)] at hx;exact hx),zero_smul,sub_self]

def WP (z:ℝ) (x:Rn m) := MillsW z • e.P z x
omit [NeZero m] in
lemma wp_meas : StronglyMeasurable e.WP.uncurry :=
  ((c_mw.measurable.comp measurable_fst).smul e.meas).stronglyMeasurable
omit [NeZero m] in
lemma wp_psd (z x) : 0 ≤ e.WP z x :=
  smul_nonneg (mw_pos z).le (e.psd ..)
omit [NeZero m] in
lemma wp_le (z x) : e.WP z x≤MillsW z•1 :=
  smul_le_smul_of_nonneg_left (e.le_one ..) (mw_pos z).le
lemma WP_mixed : mixed e.WP := by
  let f := fun z (x:Rn m)=> (MillsW z*st z) • (1:Mat m)
  let g := fun z x => MillsW z • e.EP z x
  have hh : e.WP = fun z x=> f z x+ g z x := by
    funext z x; simp only [WP,f,g,EP,mul_smul,smul_sub]; abel
  rw [hh]
  have hi : mixed f := (mixed.of_rapid (Y:=Rn m) rapid_mws).mono
    (fun z x=>by unfold f; rw [norm_smul]; simp)
  apply hi.add
  let H := fun z (_:Rn m) => MillsW z
  have h : PolyBound H.uncurry := poly_mw.comp PolyBound.fst
  exact e.EP_mixed.product h (fun z x=>by unfold g H; rw [norm_smul,mul_comm])
omit [NeZero m] in
lemma wp_slice_SM (x) : StronglyMeasurable (fun z=> e.WP z x) :=
  e.wp_meas.comp_measurable (measurable_id.prodMk measurable_const)
lemma wp_slice_i (x) : Integrable (fun z=>e.WP z x) :=
  mixed_integrable_left e.WP_mixed x (e.wp_slice_SM x).aestronglyMeasurable
lemma wp_int : Integrable e.WP.uncurry (volume.prod (normal m)) :=
  mixed_integrable e.WP_mixed e.wp_meas.aestronglyMeasurable

def Jedge (x:Rn m) := ∫ z,e.WP z x
omit [NeZero m] in
lemma Jedge_SM : StronglyMeasurable e.Jedge := e.wp_meas.integral_prod_left
lemma Jedge_poly : PolyBound e.Jedge := poly_integral_left e.WP_mixed fun x=> (e.wp_slice_SM x).aestronglyMeasurable
lemma Jedge_bound (x) : scalar m (MillsC (e.radius x)) ≤ e.Jedge x := by
  let a := e.radius x
  have hf := integral_add_compl measurableSet_Iic (e.wp_slice_i x) (s:=Iic a)
  rw [compl_Iic] at hf
  have hh : (∫ z in Ioi a,e.WP z x) = scalar m (MillsC a) := by
    rw [← (mw_tail a).2,scalar,← integral_smul_const]
    exact setIntegral_congr_fun measurableSet_Ioi fun z hz=>by rw [WP,e.tend_pos _ _ hz]
  have hi : (0:Mat m) ≤ ∫ z in Iic a,e.WP z x :=
    (psd_integral (e.wp_slice_i x).integrableOn (ae_of_all _ fun z=>(e.wp_psd z x).posSemidef)).nonneg
  unfold Jedge
  rw [← hf,hh]; exact le_add_of_nonneg_left hi
lemma Jedge_pd (x) : (e.Jedge x).PosDef := by
  let B := scalar m (MillsC (e.radius x))
  have hi : B.PosDef := form_posDef (mc_pos _)
    (show B∈specBox m (MillsC (e.radius x)) (MillsC (e.radius x)) from ⟨scalar_sym ..,le_rfl,le_rfl⟩)
  have hh := Matrix.le_iff.mp (e.Jedge_bound x)
  have h := hi.add_posSemidef hh
  simpa only [B, add_sub_cancel] using h

end Edge
end GeneralMahler

end

end OAI
