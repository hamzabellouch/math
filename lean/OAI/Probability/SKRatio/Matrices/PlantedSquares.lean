import Mathlib
import OAI.Probability.SKRatio.Gaussian.GaussianEvents
import OAI.Probability.SKRatio.Gaussian.Planted
import OAI.Probability.SKRatio.Matrices.GaussianSquareMatrix

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable

def affineDisorder {n : ℕ} (β : ℝ) (z : Disorder n) : Disorder n :=
  fun e => (β / sqrt n)*z e+β^2/n

lemma affineDisorder_hasLaw {n : ℕ} (hn : 0<n) (β : ℝ) :
    HasLaw (affineDisorder (n := n) β) (law β n) (standardArrayLaw (Edge n)) := by
  have hi := (coordinates_independent (ι := Edge n)).comp (fun _ (x : ℝ) => (β/sqrt n)*x+β^2/n)
    (fun _ => by fun_prop)
  apply iIndepFun.hasLaw_pi (μ := fun _ => gaussianReal (β^2/n) (Real.toNNReal (β^2/n))) _ hi
  intro e
  have h := gaussianReal_add_const (gaussianReal_const_mul (coordinate_hasLaw e) (β/sqrt n)) (β^2/n)
  have hv : (NNReal.mk ((β/sqrt n)^2) (sq_nonneg _) : ℝ≥0)*1 = Real.toNNReal (β^2/n) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk,mul_one,
      Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))]
    rw [div_pow,sq_sqrt (Nat.cast_pos.mpr hn).le]
  simpa only [mul_zero,zero_add,hv,Function.comp_def] using h

lemma coupling_scaled_norm {n : ℕ} (c : ℝ) (g : Disorder n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => c*g e))‖ =
      |c| *‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling g)‖ := by
  rw [coupling_const_mul]
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (c • Matrix.of (coupling g))‖ = _
  rw [map_smul,norm_smul,Real.norm_eq_abs]
  rfl

lemma normalized_absolute_row_le {n : ℕ} (hn : 0<n) (z : Disorder n) (i : Fin n) :
    (∑ e ∈ incidentEdges i, |z e|)/(n:ℝ) ≤
      (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ)+1 := by
  have hsum : ∑ e ∈ incidentEdges i, |z e| ≤ (∑ e ∈ incidentEdges i, z e^2)+(n:ℝ) := by
    calc
      _ ≤ ∑ e ∈ incidentEdges i, (z e^2+1) := Finset.sum_le_sum (fun e _ => by
        nlinarith [sq_nonneg (|z e|-1),sq_abs (z e)])
      _ = (∑ e ∈ incidentEdges i, z e^2)+((incidentEdges i).card:ℝ) := by simp [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add_right (by exact_mod_cast incidentEdges_card_le i) _
  have hd := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n : (0:ℝ)≤n)
  simpa only [add_div,div_self (show (n:ℝ)≠0 from Nat.cast_ne_zero.mpr hn.ne')] using hd

lemma normalized_matrix_norm_le_row_square {n : ℕ} (hn : 0<n) (z : Disorder n)
    {C : ℝ} (hC : 0≤C) (hrow : ∀ i, (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ) ≤ C) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => z e/n))‖ ≤ C+1 := by
  have hr (i : Fin n) : ∑ j, |coupling (fun e => z e/n) i j| ≤ C+1 := by
    simp_rw [abs_coupling]
    rw [sum_coupling_row]
    simp only [abs_div,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n),←Finset.sum_div]
    exact (normalized_absolute_row_le hn z i).trans (add_le_add_left (hrow i) _)
  exact matrix_opNorm_le_schur _ (C+1) (by linarith) hr
    (fun j => by simpa only [coupling_symm] using hr j)

lemma gaussian_rows_square_bounded :
    ∃ C : ℝ, 0<C ∧ ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | ∃ i : Fin n, C < (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ)}) := by
  obtain ⟨R,c,hR,hc,_,ht⟩ := gaussian_squareTail_row_bound (a := 1) zero_lt_one
  refine ⟨R^2+1,by positivity,?_⟩
  have hr : ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => ⋃ i : Fin n, {z | 1 ≤ (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ)}) := by
    apply exponentiallyRare_iUnion_polynomial _ _ hc (hC := zero_lt_one) (hD := zero_lt_one) 1
    · exact Eventually.of_forall (fun n => by simp)
    · filter_upwards [eventually_gt_atTop 0] with n hn
      intro i
      simpa only [one_mul] using ht (incidentEdges i) hn (incidentEdges_card_le i)
  apply hr.mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  rintro z ⟨i,hi⟩
  apply mem_iUnion.mpr
  refine ⟨i,?_⟩
  have hb : (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ) ≤ R^2+
      (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ) := by
    have hs : ∑ e ∈ incidentEdges i, z e^2 ≤
        (n:ℝ)*R^2+∑ e ∈ incidentEdges i, squareTail R (z e) := by
      calc
        _ ≤ ∑ e ∈ incidentEdges i, (R^2+squareTail R (z e)) :=
          Finset.sum_le_sum (fun e _ => by
            linarith [clippedSquare_le R (z e),square_sub_clip_le hR.le (z e)])
        _ = ((incidentEdges i).card:ℝ)*R^2+∑ e ∈ incidentEdges i, squareTail R (z e) := by simp [Finset.sum_add_distrib]
        _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right
          (by exact_mod_cast incidentEdges_card_le i) (sq_nonneg R)) _
    have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n : (0:ℝ)≤n)
    simpa only [add_div,mul_div_cancel_left₀ _ (show (n:ℝ)≠0 from Nat.cast_ne_zero.mpr hn.ne')] using hd
  change (1:ℝ) ≤ (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ)
  linarith only [hb,hi]

lemma affine_square_decomposition {n : ℕ} (hn : 0<n) (β : ℝ) (z : Disorder n) :
    (fun e => affineDisorder β z e^2-β^2/n) =
      (fun e => β^2*((z e^2-1)/n)) +
      (fun e => (2*β^3/sqrt n)*(z e/n)) + (fun _ => β^4/(n:ℝ)^2) := by
  have hnR : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have hs : sqrt (n:ℝ)≠0 := (sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  funext e
  dsimp only [affineDisorder,Pi.add_apply]
  rw [add_sq,mul_pow,div_pow,sq_sqrt (Nat.cast_nonneg n)]
  field_simp
  ring

lemma affine_square_norm_le {n : ℕ} (hn : 0<n) (β : ℝ) (z : Disorder n)
    {C : ℝ} (hC : 0≤C) (hrow : ∀ i, (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ) ≤ C) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => affineDisorder β z e^2-β^2/n))‖ ≤
      β^2*‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => (z e^2-1)/n))‖ +
        |2*β^3/sqrt n| *(C+1)+β^4/n := by
  rw [affine_square_decomposition hn]
  apply (coupling_norm_add_three _ _ _).trans
  rw [coupling_scaled_norm,coupling_scaled_norm,abs_of_nonneg (sq_nonneg β)]
  apply add_le_add
  · apply add_le_add_right
    exact mul_le_mul_of_nonneg_left (normalized_matrix_norm_le_row_square hn z hC hrow) (abs_nonneg _)
  · have hh := coupling_const_norm_le (n := n) (β^4/(n:ℝ)^2)
    have hm : (n:ℝ)*|β^4/(n:ℝ)^2| = β^4/n := by
      rw [abs_of_nonneg (by positivity)]
      field_simp
    simpa only [hm] using hh

lemma affine_square_matrix_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (coupling (fun e => affineDisorder β z e^2-β^2/n))‖}) := by
  obtain ⟨C,hC,hrows⟩ := gaussian_rows_square_bounded
  have hsq := centered_gaussian_square_matrix_rare (u := u/(2*(β^2+1))) (by positivity)
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  have hl : Tendsto (fun n : ℕ => |2*β^3/sqrt n| *(C+1)+β^4/n) atTop (𝓝 0) := by
    have h1 := ((tendsto_const_nhds (x := 2*β^3)).div_atTop (tendsto_sqrt_atTop.comp hn)).abs.mul_const (C+1)
    have h2 := (tendsto_const_nhds (x := β^4)).div_atTop hn
    simpa only [abs_zero,zero_mul,zero_add,Function.comp_def] using h1.add h2
  apply (hsq.union hrows).mono
  filter_upwards [eventually_gt_atTop 0,hl.eventually (gt_mem_nhds (by positivity : (0:ℝ)<u/2))] with n hn hb
  intro z hz
  by_contra hnot
  have hgood : ∀ i, (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ) ≤ C := by
    intro i
    exact le_of_not_gt (fun hi => hnot (Or.inr ⟨i,hi⟩))
  have hsmall : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => (z e^2-1)/n))‖ ≤ u/(2*(β^2+1)) :=
    le_of_not_gt (fun hi => hnot (Or.inl hi))
  have ha := affine_square_norm_le hn β z hC.le hgood
  have hh := mul_le_mul_of_nonneg_left hsmall (sq_nonneg β)
  have ht : β^2*(u/(2*(β^2+1))) ≤ u/2 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (by positivity : (0:ℝ)<2*(β^2+1))).mpr (by nlinarith)
  change u < _ at hz
  linarith only [ha,hh,ht,hb,hz]

theorem square_matrix_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (law β)
      (fun n => {g | u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (coupling (fun e => g e^2-β^2/n))‖}) := by
  obtain ⟨C,c,hC,hc,hb⟩ := affine_square_matrix_rare β hu
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [hb,eventually_gt_atTop 0] with n hn hdim
  have hm : MeasurableSet {g : Disorder n | u <
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => g e^2-β^2/n))‖} := by
    apply measurableSet_lt measurable_const
    exact ((Gaussian.continuous_operator_norm (n := n)).comp (continuous_pi (fun e =>
      ((continuous_apply e).pow 2).sub continuous_const))).measurable
  rw [←(affineDisorder_hasLaw hdim β).measure_eq hm]
  exact hn

end SKRatio.Planted

end
end

end OAI
