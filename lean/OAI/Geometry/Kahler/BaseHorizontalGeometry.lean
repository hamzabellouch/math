import OAI.Geometry.Kahler.BasePhaseDifferential

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def Horizontal (ξ : Sphere) (v : Base) : Prop := bracket v (ξ:Base)=0

lemma orthogonal_residual_norm (ξ p : Sphere) :
    ‖(p:Base)-bracket (p:Base) (ξ:Base) • (ξ:Base)‖ = projectiveDistance ξ p := by
  apply (sq_eq_sq₀ (norm_nonneg _) (projectiveDistance_nonneg _ _)).mp
  rw [norm_sub_sq (𝕜 := ℂ),norm_smul,sphere_norm,sphere_norm,mul_one,projectiveDistance_sq]
  simp only [bracket,inner_smul_right]
  have hconj : inner ℂ (ξ:Base) (p:Base) = star (inner ℂ (p:Base) (ξ:Base)) := (inner_conj_symm _ _).symm
  have he : (inner ℂ (ξ:Base) (p:Base)*(inner ℂ (p:Base) (ξ:Base))).re = ‖inner ℂ (p:Base) (ξ:Base)‖^2 := by
    rw [hconj]
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
    ring
  have hn : ‖inner ℂ (ξ:Base) (p:Base)‖=‖inner ℂ (p:Base) (ξ:Base)‖ := norm_inner_symm _ _
  change 1^2-2*(inner ℂ (ξ:Base) (p:Base)*inner ℂ (p:Base) (ξ:Base)).re+_=_
  rw [he,hn]
  ring

lemma horizontal_bracket_bound (ξ p : Sphere) (v : Base) (hv : Horizontal ξ v) :
    ‖bracket v (p:Base)‖ ≤ projectiveDistance ξ p*‖v‖ := by
  have he : bracket v ((p:Base)-bracket (p:Base) (ξ:Base) • (ξ:Base)) = bracket v (p:Base) := by
    dsimp [bracket,Horizontal] at hv ⊢
    rw [inner_sub_left,inner_smul_left,hv,mul_zero,sub_zero]
  calc
    ‖bracket v (p:Base)‖ = ‖bracket v ((p:Base)-bracket (p:Base) (ξ:Base) • (ξ:Base))‖ := by rw [he]
    _ ≤ ‖(p:Base)-bracket (p:Base) (ξ:Base) • (ξ:Base)‖*‖v‖ := norm_inner_le_norm _ _
    _ = _ := by rw [orthogonal_residual_norm]

lemma patch_bracket_lower {k : ℕ} {R : ℝ} (hk : 0 < k) (hR : 0 ≤ R) (hkR : 2*R ≤ k)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p) :
    (1:ℝ)/2 < ‖bracket (ξ:Base) (p:Base)‖ := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have radiusBound : |R/k| ≤ (1:ℝ)/2 := by
    rw [abs_of_nonneg (div_nonneg hR hk0.le)]
    exact (div_le_iff₀ hk0).mpr (by nlinarith)
  have hh : -(1:ℝ)/2 ≤ -R/k := by
    simpa only [neg_div] using neg_le_neg ((le_abs_self (R/k)).trans radiusBound)
  have he := Real.add_one_le_exp (-R/k)
  have hc := hξ
  change Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖ at hc
  linarith

lemma horizontal_patch_log_derivative_bound {k : ℕ} {R : ℝ} (hk : 0 < k) (hR : 0 < R)
    (hkR : 2*R ≤ k) (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p)
    (v : Base) (hv : Horizontal ξ v) :
    ‖bracket v (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ 2*Real.sqrt (2*R/(k:ℝ))*‖v‖ := by
  have hn := patch_bracket_lower hk hR.le hkR p ξ hξ
  have hd0 := peakPatch_radius hk hR hξ
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hd : projectiveDistance ξ p < Real.sqrt (2*R/(k:ℝ)) := by
    rw [Real.sqrt_div (by positivity)]
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr hk0)).mpr
    nlinarith
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖bracket (ξ:Base) (p:Base)‖)).mpr
  have hb := horizontal_bracket_bound ξ p v hv
  have hm := mul_le_mul_of_nonneg_right hd.le (norm_nonneg v)
  have hnn : 0 ≤ Real.sqrt (2*R/(k:ℝ))*‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

end PinchedHartogs.BaseConstruction

end

end OAI
