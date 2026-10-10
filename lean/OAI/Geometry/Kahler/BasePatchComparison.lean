import OAI.Geometry.Kahler.BaseLogBounds

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityCorrection_one_bound {a : ℝ} (pr : RadialProfiles a) {k : ℕ}
    (hk : 0 < k) (hkR : 2*pr.R ≤ k) {p ξ : Sphere} (hξ : ξ ∈ peakPatch k pr.R p) :
    |densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ| ≤ Real.exp 1 := by
  have hn := peakPatch_norm_pos hξ
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hy : 0 ≤ densityHeight k p ξ := patchHeight_nonneg k p ξ
  have hyR : densityHeight k p ξ < pr.R := ((peakPatch_iff_height hk pr.R p ξ).mp hξ).2
  obtain ⟨w,hw⟩ := exists_circle_norm_factor (bracket (ξ:Base) (p:Base))
  have hw' : bracket (ξ:Base) (p:Base)=(‖bracket (ξ:Base) (p:Base)‖:ℂ)*(w:ℂ) := by rw [mul_comm]; exact hw.symm
  have he := densityCorrection_constant_phase (f := pr.f) (b := pr.b) hξ w hw' (1:Circle)
  simp only [phaseAction_coe, Circle.coe_one, one_smul, one_mul] at he
  rw [he,densityHeight_inv_sq hk p hn,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hwre : |((w:ℂ)^k).re| ≤ 1 := by
    exact (Complex.abs_re_le_norm _).trans_eq (by simp [w.norm_coe])
  have hex : Real.exp (2*densityHeight k p ξ/k) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_one hk0).mpr
    linarith
  calc
    _ ≤ Real.exp 1 * 1 * 1 := mul_le_mul (mul_le_mul hex (le_trans (pr.small _ hy) pr.F_lt.le) (abs_nonneg _) (Real.exp_pos _).le) hwre (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma peak_log_difference_bound {a ε ρ C D : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hC : 0 ≤ C)
    (hlip : ∀ v w : ℂ, ‖v‖ ≤ max gaussianConstant 1 → ‖w‖ ≤ max gaussianConstant 1 →
      |regularizedLog a ε v-regularizedLog a ε w| ≤ C*‖v-w‖)
    {k : ℕ} (hk : 0 < k) (pr : RadialProfiles a) (hD : 1 ≤ D) (hDR : Real.sqrt (2*pr.R) ≤ D)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    {p ξ : Sphere} (hp : p ∈ P) (hξ : ξ ∈ peakPatch k pr.R p) :
    |regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)-regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)| ≤
      C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4) := by
  have hnρ : ‖(ρ:ℂ)‖ = ρ := by simp [abs_of_nonneg hρ]
  have hg0 : 0 ≤ gaussianConstant := gaussianConstant_pos.le
  have hp1 : ‖peakPolynomial P k (ξ:Base)‖ ≤ gaussianConstant := peak_sphere_bound hD (by omega) hP ξ
  have hs1 : ‖bracket (ξ:Base) (p:Base)^k‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (bracket_norm_le_one ξ p)
  have harg : ‖(ρ:ℂ)*peakPolynomial P k ξ‖ ≤ max gaussianConstant 1 := by
    rw [norm_mul,hnρ]
    exact (mul_le_mul hρ1 hp1 (norm_nonneg _) (by norm_num)).trans (by simp)
  have harg' : ‖(ρ:ℂ)*bracket (ξ:Base) (p:Base)^k‖ ≤ max gaussianConstant 1 := by
    rw [norm_mul,hnρ]
    exact (mul_le_mul hρ1 hs1 (norm_nonneg _) (by norm_num)).trans (by simp)
  have herr := peakPatch_single (by omega : 1 ≤ k) pr.R_pos hD hDR hP hp hξ
  apply (hlip _ _ harg harg').trans
  rw [← mul_sub,norm_mul,hnρ]
  calc
    _ ≤ C*(1*(gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))) := by gcongr
    _ = _ := by ring

lemma weighted_patch_error {a ε ρ C D : ℝ} (hε : ε ≠ 0) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hC : 0 ≤ C)
    (hlip : ∀ v w : ℂ, ‖v‖ ≤ max gaussianConstant 1 → ‖w‖ ≤ max gaussianConstant 1 →
      |regularizedLog a ε v-regularizedLog a ε w| ≤ C*‖v-w‖)
    {k : ℕ} (hk : 0 < k) (pr : RadialProfiles a) (hkR : 2*pr.R ≤ k)
    (hD : 1 ≤ D) (hDR : Real.sqrt (2*pr.R) ≤ D)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) {p : Sphere} (hp : p ∈ P) :
    |(∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma)-
     (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma)| ≤
      (2*pr.R/k)*(C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1) := by
  have hg0 : 0 ≤ gaussianConstant := gaussianConstant_pos.le
  have hco : Continuous (fun ξ : Sphere => densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) := (densityCorrection_smooth hk pr.cutoff_lt pr.smooth_f pr.smooth_b
    (show ContDiff ℝ ∞ (fun _ : Base => (1:ℝ)) from contDiff_const) pr.tail p).continuous.comp continuous_subtype_val
  have hu := (regularizedLog_contDiff a hε).continuous
  have h1 : Continuous (fun ξ : Sphere => regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ)) :=
    (hu.comp (continuous_const.mul ((peakPolynomial_analytic P k).continuous.comp continuous_subtype_val))).mul (continuous_const.add hco)
  have h2 : Continuous (fun ξ : Sphere => regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ)) :=
    (hu.comp (continuous_const.mul (((bracket_analytic (p:Base)).continuous.comp continuous_subtype_val).pow k))).mul (continuous_const.add hco)
  rw [← integral_sub (compact_continuous_integrable h1) (compact_continuous_integrable h2)]
  have hh : |(∫ ξ in peakPatch k pr.R p,
      regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*(1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ)-
      regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*(1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma)| ≤
      sigma.real (peakPatch k pr.R p)*((C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1)) := by
    rw [mul_comm (sigma.real _), ← Real.norm_eq_abs]
    apply norm_setIntegral_le_of_norm_le_const (measure_lt_top sigma (peakPatch k pr.R p))
    intro ξ hξ
    rw [Real.norm_eq_abs,← sub_mul,abs_mul]
    apply mul_le_mul (peak_log_difference_bound hρ hρ1 hC hlip hk pr hD hDR hP hp hξ)
    · exact (abs_add_le _ _).trans (by simpa using add_le_add_left (densityCorrection_one_bound pr hk hkR hξ) 1)
    · positivity
    · positivity
  apply hh.trans
  have hm := peakPatch_measure_le hk pr.R_pos p
  calc
    _ ≤ (2*pr.R/k)*((C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1)) := by gcongr
    _ = _ := by ring

end PinchedHartogs.BaseConstruction

end

end OAI
