import Mathlib
import OAI.Geometry.SmoothYau.Estimates.CosUnitQuadraticGap
import OAI.Geometry.SmoothYau.Estimates.GeneratedCutoffWaveEndpointRatio

namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace YauCounterexamples

section Correlations
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def unitCorrelation (a b : E) : ℝ := ⟪‖a‖⁻¹ • a, ‖b‖⁻¹ • b⟫

lemma unitCorrelation_error (a b c : E) (ha : a ≠ 0) (hb : b ≠ 0)
    {δ : ℝ} (hδ : δ < 1) (hbc : ‖b-c‖ ≤ δ*‖b‖) :
    c ≠ 0 ∧ |unitCorrelation a b-unitCorrelation a c| ≤ 2*δ := by
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hc : c ≠ 0 := by
    intro hc
    simp only [hc,sub_zero] at hbc
    nlinarith
  refine ⟨hc,?_⟩
  calc
    _ = |⟪‖a‖⁻¹ • a, ‖b‖⁻¹ • b-‖c‖⁻¹ • c⟫| := by
      rw [inner_sub_right]; rfl
    _ ≤ ‖‖a‖⁻¹ • a‖*‖‖b‖⁻¹ • b-‖c‖⁻¹ • c‖ := abs_real_inner_le_norm _ _
    _ = ‖‖b‖⁻¹ • b-‖c‖⁻¹ • c‖ := by rw [norm_normalize_vector a ha,one_mul]
    _ ≤ 2*‖b-c‖/‖b‖ := normalize_vector_error b c hb hc
    _ ≤ 2*δ := by apply (div_le_iff₀ hbn).mpr; nlinarith

lemma unitCorrelation_pos_smul (a b : E) {r : ℝ} (hr : 0 < r) :
    unitCorrelation a (r • b) = unitCorrelation a b := by
  unfold unitCorrelation
  congr 1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_inv_rev,smul_smul]
  congr 1
  field_simp

end Correlations

variable {I : Type*} [Fintype I]

lemma common_complex_weights {z : I → ℂ} (hz : complexValueVector z ≠ 0) :
    (∀ i, 0 ≤ ‖z i‖^2/‖complexValueVector z‖^2) ∧
      (∑ i, ‖z i‖^2/‖complexValueVector z‖^2) = 1 := by
  refine ⟨fun i => div_nonneg (sq_nonneg _) (sq_nonneg _),?_⟩
  rw [←Finset.sum_div,←complexValueVector_norm_sq]
  exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))

lemma rotated_complex_unitCorrelation (z : I → ℂ) (θ : I → ℝ) :
    unitCorrelation (complexValueVector z) (complexValueVector (rotatedWaveValues z θ)) =
      ∑ i, (‖z i‖^2/‖complexValueVector z‖^2)*Real.cos (θ i) := by
  unfold unitCorrelation
  rw [real_inner_smul_left,real_inner_smul_right,complexValueVector_rotated_norm,
    complexValueVector_rotated_inner]
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div]
  ring

theorem three_axis_correlation_gap {z : I → ℂ} (hz : complexValueVector z ≠ 0)
    (w : Fin 3 → I → ℂ) (α : Fin 3 → ℝ) (hα : ∀ j, 0 < α j)
    (θ : I → Fin 3 → ℝ) {κ δ : ℝ} (_hκ : 0 < κ)
    (hδsmall : δ ≤ 1/8) (hδgap : δ ≤ κ/48)
    (hθ : ∀ i j, |θ i j| ≤ 1) (henergy : ∀ i, κ ≤ ∑ j, (θ i j)^2)
    (herror : ∀ j, ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)
        -complexValueVector (w j)‖ ≤
      δ*‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)‖) :
    (∀ j, complexValueVector (w j) ≠ 0) ∧
      ∃ j, 1/4 ≤ unitCorrelation (complexValueVector z) (complexValueVector (w j)) ∧
        unitCorrelation (complexValueVector z) (complexValueVector (w j)) ≤ 1-κ/24 := by
  let ρ : Fin 3 → ℝ := fun j => unitCorrelation (complexValueVector z) (complexValueVector (w j))
  let c : Fin 3 → ℝ := fun j => ∑ i, (‖z i‖^2/‖complexValueVector z‖^2)*Real.cos (θ i j)
  have herr (j) : complexValueVector (w j) ≠ 0 ∧ |c j-ρ j| ≤ 2*δ := by
    have hb : complexValueVector (rotatedWaveValues z (fun i => θ i j)) ≠ 0 := by
      rw [←norm_ne_zero_iff,complexValueVector_rotated_norm]
      exact norm_ne_zero_iff.mpr hz
    have hbb : complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i) ≠ 0 := by
      rw [complexValueVector_real_smul]
      exact smul_ne_zero (ne_of_gt (hα j)) hb
    have hh := unitCorrelation_error (complexValueVector z) _ (complexValueVector (w j))
      hz hbb (show δ < 1 by linarith) (herror j)
    rw [complexValueVector_real_smul,unitCorrelation_pos_smul _ _ (hα j),
      rotated_complex_unitCorrelation] at hh
    exact hh
  obtain ⟨hlow,hsum⟩ := common_weight_cosine_gap _ (common_complex_weights hz).1
    (common_complex_weights hz).2 θ hθ henergy
  have hl (j) : 1/4 ≤ ρ j := by
    have hh := (abs_le.mp (herr j).2).2
    have hc := hlow j
    change 1/2 ≤ c j at hc
    linarith
  have hg : κ/8 ≤ ∑ j, (1-ρ j) := by
    have hh : (∑ j, (1-c j)) ≤ (∑ j, (1-ρ j))+6*δ := by
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (f := fun j => 1-c j) (g := fun j => 1-ρ j+2*δ)
        (fun j _ => by have hj := (abs_le.mp (herr j).2).1; linarith)
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
      norm_num at hh ⊢
      linarith
    change κ/4 ≤ ∑ j, (1-c j) at hsum
    linarith
  have haxis : ∃ j, κ/24 ≤ 1-ρ j := by
    by_contra! h
    simp only [Fin.sum_univ_three] at hg
    linarith [h 0,h 1,h 2]
  obtain ⟨j,hj⟩ := haxis
  exact ⟨fun j => (herr j).1,j,hl j,by dsimp [ρ] at hj ⊢; linarith⟩

end YauCounterexamples
end

end OAI
