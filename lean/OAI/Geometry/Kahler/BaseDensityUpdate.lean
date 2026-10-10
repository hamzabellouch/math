import OAI.Geometry.Kahler.BaseCorrectionDifferential

namespace OAI

universe uKahler14283_1

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

lemma disjoint_sum_abs_bound {α : Type uKahler14283_1} (s : Finset α) (active : α → Prop)
    (hu : ∀ p ∈ s, ∀ q ∈ s, active p → active q → p=q)
    (A : α → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ p ∈ s, ¬ active p → A p=0)
    (hbound : ∀ p ∈ s, active p → |A p| ≤ B) :
    |∑ p ∈ s, A p| ≤ B := by
  classical
  by_cases ha : ∃ p ∈ s, active p
  · obtain ⟨p,hp,hap⟩ := ha
    rw [Finset.sum_eq_single p]
    · exact hbound p hp hap
    · intro q hq hqp
      exact hzero q hq (fun haq => hqp (hu q hq p hp haq hap))
    · exact fun h => (h hp).elim
  · have hz : ∑ p ∈ s, A p=0 := Finset.sum_eq_zero (fun p hp => hzero p hp (fun h => ha ⟨p,hp,h⟩))
    rw [hz,abs_zero]
    exact hB

lemma densityCorrectionRaw_value_bound {k : ℕ} (hk : 0 < k)
    (f b : ℝ → ℝ) (W : Base → ℝ) (p : Sphere) (ξ : Base) (hξ : bracket ξ (p:Base) ≠ 0)
    {F B r : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hS : 0 ≤ W (centralPoint p ξ))
    (hT : |phaseDerivative W (centralPoint p ξ)| ≤ (k:ℝ)*r*W (centralPoint p ξ))
    (hf : |f (densityHeight k p ξ)| ≤ F) (hb : |b (densityHeight k p ξ)| ≤ B) :
    |densityCorrectionRaw k f b W p ξ| ≤
      Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ)*(F+B*r) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  let z := (bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k
  have hn : ‖z‖=1 := by
    dsimp [z]
    rw [norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm,div_self (norm_ne_zero_iff.mpr hξ),one_pow]
  have hzre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans_eq hn
  have hzim : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans_eq hn
  rw [densityCorrectionRaw_model hk f b W p hξ]
  unfold correctionModel
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (2*densityHeight k p ξ/k)*
      (|f (densityHeight k p ξ)| * |W (centralPoint p ξ)| * |z.re| +
       |b (densityHeight k p ξ)/k| * |phaseDerivative W (centralPoint p ξ)| * |z.im|) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [abs_mul] using abs_sub_triangle
        (f (densityHeight k p ξ)*W (centralPoint p ξ)*z.re)
        (b (densityHeight k p ξ)/k*phaseDerivative W (centralPoint p ξ)*z.im)
    _ ≤ Real.exp (2*densityHeight k p ξ/k)*(F*W (centralPoint p ξ)*1+
      (B/k)*((k:ℝ)*r*W (centralPoint p ξ))*1) := by
      rw [abs_of_nonneg hS,abs_div,abs_of_pos hk0]
      gcongr
    _ = _ := by field_simp

lemma horizontal_direction_ratio {k : ℕ} {R D : ℝ} (hk : 0 < k) (hR : 0 < R)
    (hkR : 2*R ≤ k) (hD : 2*Real.sqrt (2*R) ≤ D)
    (p ξ : Sphere) (hξ : ξ ∈ peakPatch k R p) (v : Base) (hv : Horizontal ξ v) :
    ‖bracket v (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ D*Real.sqrt (k:ℝ)*‖v‖/k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hb := horizontal_patch_log_derivative_bound hk hR hkR p ξ hξ v hv
  rw [Real.sqrt_div (by positivity)] at hb
  apply hb.trans
  have hroot := Real.sq_sqrt hk0.le
  have hroot0 : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr hk0
  apply (le_div_iff₀ hk0).mpr
  have he : 2*(Real.sqrt (2*R)/Real.sqrt (k:ℝ))*‖v‖*(k:ℝ)=
      (2*Real.sqrt (2*R))*Real.sqrt (k:ℝ)*‖v‖ := by
    rw [← hroot]
    rw [Real.sqrt_sq (Real.sqrt_nonneg _)]
    field_simp
  rw [he]
  gcongr

lemma phase_direction_ratio (p ξ : Sphere) (hξ : bracket (ξ:Base) (p:Base) ≠ 0) :
    ‖bracket (Complex.I • (ξ:Base)) (p:Base)/bracket (ξ:Base) (p:Base)‖=1 := by
  rw [bracket_smul,mul_div_cancel_right₀ Complex.I hξ,Complex.norm_I]

end PinchedHartogs.BaseConstruction

end

end OAI
