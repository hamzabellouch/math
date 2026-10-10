import OAI.Geometry.Kahler.BaseHorizontalArc

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def HorizontalBound (W : Base → ℝ) (H : ℝ) : Prop :=
  ∀ ξ : Sphere, ∀ v : Base, Horizontal ξ v →
    |fderiv ℝ W ξ v| ≤ H*‖v‖*W ξ

lemma horizontalArc_reaches {r : ℝ} (hr : 0 < r) (q d ξ : Base)
    (hn : r^2+‖d‖^2=1) (he : ξ=r • q+d) : horizontalArc q d (1/r)=ξ := by
  have hh : Real.sqrt (1+(1/r)^2*‖d‖^2)=1/r := by
    apply Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity) |>.mpr
    field_simp
    nlinarith
  unfold horizontalArc
  rw [hh]
  simp only [one_div,inv_inv,smul_add,smul_smul]
  rw [mul_inv_cancel₀ hr.ne',one_smul]
  exact he.symm

lemma horizontal_growth {W : Base → ℝ} (hW : Differentiable ℝ W)
    (hp : ∀ ξ : Sphere, 0 < W ξ) {H : ℝ} (hH : 0 ≤ H) (hd : HorizontalBound W H)
    (q : Sphere) (d : Base) (hq : bracket d (q:Base)=0) (t : ℝ) :
    W (horizontalArc q d t) ≤ Real.exp (H*‖d‖*|t|)*W q ∧
    W q ≤ Real.exp (H*‖d‖*|t|)*W (horizontalArc q d t) := by
  let γ := horizontalArc (q:Base) d
  let f := fun u => W (γ u)
  have hg : ∀ u, HasDerivAt γ (horizontalArcVelocity q d u) u := horizontalArc_derivative _ _
  have hsp : ∀ u, γ u ∈ Sphere := fun u => by
    simpa only [Metric.mem_sphere,dist_zero_right] using horizontalArc_norm q d hq u
  have hfp : ∀ u, 0 < f u := fun u => hp ⟨γ u,hsp u⟩
  have hfd : ∀ u, HasDerivAt f (fderiv ℝ W (γ u) (horizontalArcVelocity q d u)) u :=
    fun u => (hW _).hasFDerivAt.comp_hasDerivAt u (hg u)
  have hfb : ∀ u, |deriv f u| ≤ (H*‖d‖)*f u := by
    intro u
    rw [(hfd u).deriv]
    have hh := hd ⟨γ u,hsp u⟩ (horizontalArcVelocity q d u) (horizontalArc_horizontal q d hq u)
    simpa only [Complex.star_def,Complex.ofReal_pow] using hh.trans (by
      apply mul_le_mul_of_nonneg_right _ (hfp u).le
      exact mul_le_mul_of_nonneg_left (horizontalArc_velocity_norm q d hq u) hH)
  have hf0 : f 0=W q := by simp [f,γ,horizontalArc]
  have hforward := positive_log_growth (fun u => (hfd u).differentiableAt) hfp (mul_nonneg hH (norm_nonneg _)) hfb 0 t
  have hback := positive_log_growth (fun u => (hfd u).differentiableAt) hfp (mul_nonneg hH (norm_nonneg _)) hfb t (-t)
  simp only [zero_add] at hforward
  simp only [add_neg_cancel,abs_neg] at hback
  rw [hf0] at hforward hback
  exact ⟨hforward,hback⟩

lemma central_residual (p ξ : Sphere) (h0 : bracket (ξ:Base) (p:Base) ≠ 0) :
    let q := centralPoint p ξ
    let r := ‖bracket (ξ:Base) (p:Base)‖
    let d := (ξ:Base)-r • q
    bracket d q=0 ∧ r^2+‖d‖^2=1 ∧ ‖d‖=projectiveDistance ξ p := by
  dsimp only
  let c := bracket (ξ:Base) (p:Base)
  have hr : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hc : (‖c‖:ℂ) ≠ 0 := by exact_mod_cast hr
  have hq : bracket (ξ:Base) (centralPoint p ξ)=(‖c‖:ℂ) := by
    simp only [centralPoint,bracket,inner_smul_left]
    change star (c/(‖c‖:ℂ))*c=(‖c‖:ℂ)
    rw [star_div₀,Complex.star_def,Complex.conj_ofReal]
    have hh : star c*c=(‖c‖^2:ℝ) := by
      simpa only [Complex.star_def,Complex.ofReal_pow] using Complex.conj_mul' c
    field_simp
    simpa only [Complex.star_def,Complex.ofReal_pow] using hh
  have hqq : bracket (centralPoint p ξ) (centralPoint p ξ)=1 := by
    simp only [bracket,inner_self_eq_norm_sq_to_K,centralPoint_norm p h0]
    norm_num
  have hd : bracket ((ξ:Base)-‖c‖ • centralPoint p ξ) (centralPoint p ξ)=0 := by
    rw [bracket,inner_sub_right,← Complex.coe_smul,inner_smul_right]
    change bracket (ξ:Base) (centralPoint p ξ)-(‖c‖:ℂ)*bracket (centralPoint p ξ) (centralPoint p ξ)=0
    rw [hq,hqq,mul_one,sub_self]
  have hn : ‖(ξ:Base)-‖c‖ • centralPoint p ξ‖^2=1-‖c‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ),sphere_norm,norm_smul,centralPoint_norm p h0,mul_one,Real.norm_eq_abs,abs_norm]
    have hi : inner ℂ (ξ:Base) (‖c‖ • centralPoint p ξ)=(‖c‖^2:ℝ) := by
      rw [← Complex.coe_smul,inner_smul_right,← inner_conj_symm]
      change (‖c‖:ℂ)*star (bracket (ξ:Base) (centralPoint p ξ))=_
      rw [hq,Complex.star_def,Complex.conj_ofReal]
      push_cast; ring
    rw [hi]
    change 1^2-2*‖c‖^2+‖c‖^2=1-‖c‖^2
    ring
  refine ⟨hd,by linarith,?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (projectiveDistance_nonneg _ _)).mp
  rw [hn,projectiveDistance_sq]

lemma central_comparison {W : Base → ℝ} (hW : Differentiable ℝ W)
    (hp : ∀ ξ : Sphere, 0 < W ξ) {H : ℝ} (hH : 0 ≤ H) (hd : HorizontalBound W H)
    {k : ℕ} {R : ℝ} (hk : 0 < k) (hR : 0 < R) (hkR : 2*R ≤ k)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p) :
    W (centralPoint p ξ) ≤ Real.exp (H*(2*Real.sqrt (2*R)/Real.sqrt (k:ℝ)))*W ξ ∧
    W ξ ≤ Real.exp (H*(2*Real.sqrt (2*R)/Real.sqrt (k:ℝ)))*W (centralPoint p ξ) := by
  have hc : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (peakPatch_norm_pos hξ)
  let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hc⟩
  let r := ‖bracket (ξ:Base) (p:Base)‖
  let d := (ξ:Base)-r • (q:Base)
  obtain ⟨hdq,hn,hdn⟩ := central_residual p ξ hc
  change bracket d (q:Base)=0 at hdq
  change r^2+‖d‖^2=1 at hn
  change ‖d‖=projectiveDistance ξ p at hdn
  have hr : 0 < r := peakPatch_norm_pos hξ
  have he : horizontalArc q d (1/r)=(ξ:Base) := horizontalArc_reaches hr q d ξ hn (by dsimp [d]; abel)
  obtain ⟨h1,h2⟩ := horizontal_growth hW hp hH hd q d hdq (1/r)
  rw [he] at h1 h2
  have hlen : ‖d‖*|1/r| ≤ 2*Real.sqrt (2*R)/Real.sqrt (k:ℝ) := by
    rw [hdn,abs_of_pos (one_div_pos.mpr hr)]
    have hr2 : 1/2 < r := patch_bracket_lower hk hR.le hkR p ξ hξ
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hk0)).mpr
    have hpdist := peakPatch_radius hk hR hξ
    have hrinv : 1/r ≤ 2 := (div_le_iff₀ hr).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_left hrinv (mul_nonneg (projectiveDistance_nonneg ξ p) (Real.sqrt_nonneg (k:ℝ)))
    nlinarith
  have hex : Real.exp (H*‖d‖*|1/r|) ≤ Real.exp (H*(2*Real.sqrt (2*R)/Real.sqrt (k:ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact ⟨h2.trans (mul_le_mul_of_nonneg_right hex (hp ξ).le),h1.trans (mul_le_mul_of_nonneg_right hex (hp q).le)⟩

end PinchedHartogs.BaseConstruction

end

end OAI
