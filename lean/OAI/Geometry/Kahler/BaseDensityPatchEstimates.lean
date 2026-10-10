import OAI.Geometry.Kahler.BaseDensityUpdate

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

lemma density_central_envelope {W : Base → ℝ} (hW : Differentiable ℝ W)
    (hpos : ∀ ξ : Sphere, 0 < W ξ) {H : ℝ} (hH : 0 ≤ H) (hd : HorizontalBound W H)
    {k : ℕ} {R : ℝ} (hk : 0 < k) (hR : 0 < R) (hkR : 2*R ≤ k)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p) :
    Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ) ≤
      Real.exp (H*(2*Real.sqrt (2*R)/Real.sqrt (k:ℝ))+2*R/k)*W ξ := by
  have hh : densityHeight k p ξ < R := ((peakPatch_iff_height hk R p ξ).mp hξ).2
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hw := (central_comparison hW hpos hH hd hk hR hkR p ξ hξ).1
  calc
    _ ≤ Real.exp (2*R/k)*(Real.exp (H*(2*Real.sqrt (2*R)/Real.sqrt (k:ℝ)))*W ξ) := by
      apply mul_le_mul _ hw (le_of_lt (hpos ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p (norm_pos_iff.mp (peakPatch_norm_pos hξ))⟩)) (Real.exp_pos _).le
      exact Real.exp_le_exp.mpr (by gcongr)
    _ = _ := by rw [← mul_assoc,← Real.exp_add]; congr 2; ring

def centralSphere (p ξ : Sphere) (hξ : bracket (ξ:Base) (p:Base) ≠ 0) : Sphere :=
  ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩

lemma densityCorrection_patch_value {k : ℕ} (hk : 0 < k)
    (f b : ℝ → ℝ) (W : Base → ℝ) {R F B r H : ℝ}
    (hF : 0 ≤ F) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hpos : ∀ ξ : Sphere, 0 < W ξ)
    (hT : ∀ ξ : Sphere, |phaseDerivative W ξ| ≤ (k:ℝ)*r*W ξ)
    (hf : ∀ y, 0 ≤ y → |f y| ≤ F) (hb : ∀ y, 0 ≤ y → |b y| ≤ B)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p)
    (henv : Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ) ≤ H*W ξ) :
    |densityCorrection k R f b W p ξ| ≤ H*(F+B*r)*W ξ := by
  have hc : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (peakPatch_norm_pos hξ)
  change Real.exp (-R/k)<‖bracket (ξ:Base) (p:Base)‖ at hξ
  rw [densityCorrection,ite_eq_left hξ]
  have hh := densityCorrectionRaw_value_bound hk f b W p ξ hc hF hB hr
    (hpos (centralSphere p ξ hc)).le (hT (centralSphere p ξ hc)) (hf _ (patchHeight_nonneg k p ξ)) (hb _ (patchHeight_nonneg k p ξ))
  exact hh.trans ((mul_le_mul_of_nonneg_right henv (by positivity)).trans_eq (by ring))

lemma densityCorrection_patch_direction {k : ℕ} (hk : 0 < k)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    {R F B F₁ B₁ H D : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁) (hD : 0 ≤ D)
    (hpos : ∀ ξ : Sphere, 0 < W ξ)
    (hT : ∀ ξ : Sphere, |phaseDerivative W ξ| ≤ (k:ℝ)*W ξ)
    (hTT : ∀ ξ : Sphere, |phaseDerivative (phaseDerivative W) ξ| ≤ (k:ℝ)^2*W ξ)
    (hfv : ∀ y, 0 ≤ y → |f y| ≤ F) (hbv : ∀ y, 0 ≤ y → |b y| ≤ B)
    (hfd : ∀ y, 0 ≤ y → |deriv f y| ≤ F₁) (hbd : ∀ y, 0 ≤ y → |deriv b y| ≤ B₁)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p) (v : Base)
    (hdir : ‖bracket v (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ D/k)
    (henv : Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ) ≤ H*W ξ) :
    |fderiv ℝ (densityCorrection k R f b W p) ξ v| ≤ D*H*(4*(F+B)+F₁+B₁)*W ξ := by
  have hc : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (peakPatch_norm_pos hξ)
  rw [densityCorrection_fderiv_raw f b W p ξ hξ]
  have hh := densityCorrectionRaw_direction_bound hk hD hF hB hF₁ hB₁ hf hb hW p ξ v hc hdir
    (hpos (centralSphere p ξ hc)).le (hT (centralSphere p ξ hc)) (hTT (centralSphere p ξ hc)) (hfv _ (patchHeight_nonneg k p ξ)) (hbv _ (patchHeight_nonneg k p ξ)) (hfd _ (patchHeight_nonneg k p ξ)) (hbd _ (patchHeight_nonneg k p ξ))
  calc
    _ ≤ D*(Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ))*(4*(F+B)+F₁+B₁) := by simpa only [mul_assoc] using hh
    _ ≤ D*(H*W ξ)*(4*(F+B)+F₁+B₁) := by gcongr
    _ = _ := by ring

lemma fderiv_density_update {k : ℕ} (hk : 0 < k) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : Finset Sphere) (ξ v : Base) :
    fderiv ℝ (fun z => W z+∑ p ∈ P, densityCorrection k R f b W p z) ξ v =
      fderiv ℝ W ξ v+∑ p ∈ P, fderiv ℝ (densityCorrection k R f b W p) ξ v := by
  have hw := hW.differentiable (by simp) ξ
  have hp : ∀ p ∈ P, DifferentiableAt ℝ (densityCorrection k R f b W p) ξ :=
    fun p hp => (densityCorrection_smooth hk hER hf hb hW htail p).differentiable (by simp) ξ
  rw [fderiv_fun_add hw (DifferentiableAt.fun_sum hp),fderiv_fun_sum hp]
  simp only [add_apply,sum_apply]

end PinchedHartogs.BaseConstruction

end

end OAI
