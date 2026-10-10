import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ComplexGaussianRealValue

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace YauCounterexamples

lemma unitCorrelation_symm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) : unitCorrelation a b = unitCorrelation b a := real_inner_comm _ _

lemma unitCorrelation_two_errors {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a₀ b₀ a b : E) (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0) {δ : ℝ} (hδ : δ < 1)
    (ha : ‖a₀-a‖ ≤ δ*‖a₀‖) (hb : ‖b₀-b‖ ≤ δ*‖b₀‖) :
    a ≠ 0 ∧ b ≠ 0 ∧ |unitCorrelation a₀ b₀-unitCorrelation a b| ≤ 4*δ := by
  obtain ⟨hb',hhb⟩ := unitCorrelation_error a₀ b₀ b ha₀ hb₀ hδ hb
  obtain ⟨ha',hha⟩ := unitCorrelation_error b a₀ a hb' ha₀ hδ ha
  rw [unitCorrelation_symm b a₀,unitCorrelation_symm b a] at hha
  refine ⟨ha',hb',?_⟩
  calc
    _ ≤ |unitCorrelation a₀ b₀-unitCorrelation a₀ b|+
        |unitCorrelation a₀ b-unitCorrelation a b| := abs_sub_le _ _ _
    _ ≤ 2*δ+2*δ := add_le_add hhb hha
    _ = 4*δ := by ring

section NearFar
variable {I : Type*} [Fintype I]

theorem perturbed_three_axis_correlation_gap {z : I → ℂ} (hz : complexValueVector z ≠ 0)
    (v : I → ℂ) (w : Fin 3 → I → ℂ) (α : Fin 3 → ℝ) (hα : ∀ j, 0 < α j)
    (θ : I → Fin 3 → ℝ) {κ δ : ℝ} (hκ : 0 < κ)
    (hδsmall : δ ≤ 1/16) (hδgap : δ ≤ κ/96)
    (hθ : ∀ i j, |θ i j| ≤ 1) (henergy : ∀ i, κ ≤ ∑ j, (θ i j)^2)
    (hbase : ‖complexValueVector z-complexValueVector v‖ ≤ δ*‖complexValueVector z‖)
    (herror : ∀ j, ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)
        -complexValueVector (w j)‖ ≤
      δ*‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)‖) :
    complexValueVector v ≠ 0 ∧ (∀ j, complexValueVector (w j) ≠ 0) ∧
      ∃ j, 1/4 ≤ unitCorrelation (complexValueVector v) (complexValueVector (w j)) ∧
        unitCorrelation (complexValueVector v) (complexValueVector (w j)) ≤ 1-κ/24 := by
  let ρ : Fin 3 → ℝ := fun j => unitCorrelation (complexValueVector v) (complexValueVector (w j))
  let c : Fin 3 → ℝ := fun j => ∑ i, (‖z i‖^2/‖complexValueVector z‖^2)*Real.cos (θ i j)
  have herr (j) : complexValueVector v ≠ 0 ∧
      complexValueVector (w j) ≠ 0 ∧ |c j-ρ j| ≤ 4*δ := by
    have hb : complexValueVector (rotatedWaveValues z (fun i => θ i j)) ≠ 0 := by
      rw [←norm_ne_zero_iff,complexValueVector_rotated_norm]
      exact norm_ne_zero_iff.mpr hz
    have hbb : complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i) ≠ 0 := by
      rw [complexValueVector_real_smul]
      exact smul_ne_zero (ne_of_gt (hα j)) hb
    have hh := unitCorrelation_two_errors (complexValueVector z) _
      (complexValueVector v) (complexValueVector (w j)) hz hbb
      (show δ < 1 by linarith) hbase (herror j)
    rw [complexValueVector_real_smul,unitCorrelation_pos_smul _ _ (hα j),
      rotated_complex_unitCorrelation] at hh
    exact hh
  obtain ⟨hlow,hsum⟩ := common_weight_cosine_gap _ (common_complex_weights hz).1
    (common_complex_weights hz).2 θ hθ henergy
  have hl (j) : 1/4 ≤ ρ j := by
    have hh := (abs_le.mp (herr j).2.2).2
    have hc := hlow j
    change 1/2 ≤ c j at hc
    linarith
  have hg : 1/8 ≤ (∑ j, (1-ρ j))/κ := by
    have hh : (∑ j, (1-c j)) ≤ (∑ j, (1-ρ j))+12*δ := by
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (f := fun j => 1-c j) (g := fun j => 1-ρ j+4*δ)
        (fun j _ => by have hj := (abs_le.mp (herr j).2.2).1; linarith)
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
      norm_num at hh ⊢
      linarith
    change κ/4 ≤ ∑ j, (1-c j) at hsum
    apply (le_div_iff₀ hκ).mpr
    linarith
  have haxis : ∃ j, κ/24 ≤ 1-ρ j := by
    by_contra! h
    have hsumρ := (le_div_iff₀ hκ).mp hg
    simp only [Fin.sum_univ_three] at hsumρ
    linarith [h 0,h 1,h 2]
  obtain ⟨j,hj⟩ := haxis
  exact ⟨(herr 0).1,fun j => (herr j).2.1,j,hl j,by dsimp [ρ] at hj ⊢; linarith⟩

end NearFar

theorem common_near_wave_sign_probability {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ q > 0, ∀ (I : Type) [Fintype I] (z v : I → ℂ) (w : Fin 3 → I → ℂ)
      (α : Fin 3 → ℝ) (θ : I → Fin 3 → ℝ) (m : ℝ) (m' : Fin 3 → ℝ) (δ : ℝ),
      complexValueVector z ≠ 0 → (∀ j, 0 < α j) → δ ≤ 1/16 → δ ≤ κ/96 →
      (∀ i j, |θ i j| ≤ 1) → (∀ i, κ ≤ ∑ j, (θ i j)^2) →
      ‖complexValueVector z-complexValueVector v‖ ≤ δ*‖complexValueVector z‖ →
      (∀ j, ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)
        -complexValueVector (w j)‖ ≤
        δ*‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)‖) →
      |m/‖complexValueVector v‖| ≤ 1 → (∀ j, |m' j/‖complexValueVector (w j)‖| ≤ 1) →
      ∃ j, ENNReal.ofReal q ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (m+complexGaussianRealValue v γ)*(m' j+complexGaussianRealValue (w j) γ) < 0} := by
  obtain ⟨q,hq,hprob⟩ := complex_gaussian_sign_uniform (1/4) (1-κ/24) 1
    (by norm_num) (by linarith) (by linarith) zero_le_one
  refine ⟨q,hq,?_⟩
  intro I _ z v w α θ m m' δ hz hα hδsmall hδgap hθ henergy hbase herror hm hm'
  obtain ⟨hv,hw,j,hlo,hhi⟩ := perturbed_three_axis_correlation_gap hz v w α hα θ hκ
    hδsmall hδgap hθ henergy hbase herror
  exact ⟨j,hprob I v (w j) m (m' j) hv (hw j) hlo hhi hm (hm' j)⟩

end YauCounterexamples
end

end OAI
