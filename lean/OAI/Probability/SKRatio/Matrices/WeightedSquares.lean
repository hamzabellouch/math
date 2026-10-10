import Mathlib
import OAI.Probability.SKRatio.Matrices.PlantedSquares

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable

def squareError {n : ℕ} (β : ℝ) (g : Disorder n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => coupling g i j^2-β^2/n

lemma squareError_decomposition {n : ℕ} (β : ℝ) (g : Disorder n) :
    squareError β g = Matrix.of (coupling (fun e => g e^2-β^2/n)) -
      Matrix.diagonal (fun _ => β^2/(n:ℝ)) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [squareError,coupling]
  · rcases lt_or_gt_of_ne h with hij | hij
    · simp [squareError,coupling,hij,h]
    · simp [squareError,coupling,hij,not_lt_of_gt hij,h]

lemma squareError_symmetric {n : ℕ} (β : ℝ) (g : Disorder n) (i j : Fin n) :
    squareError β g i j = squareError β g j i := by
  simp only [squareError,coupling_symm g i j]

theorem squareError_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (law β) (fun n => {g | u <
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (squareError β g)‖}) := by
  have h := square_matrix_rare β (half_pos hu)
  have ht : Tendsto (fun n : ℕ => β^2/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply h.mono
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hu))] with n hn
  intro g hg
  change u/2 < _
  apply lt_of_not_ge
  intro hsmall
  have hd := matrix_diagonal_opNorm_le (n := n) (fun _ => β^2/(n:ℝ))
    (β^2/(n:ℝ)) (by positivity) (fun _ => le_of_eq (abs_of_nonneg (by positivity)))
  have hh : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (squareError β g)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => g e^2-β^2/n))‖+
      β^2/(n:ℝ) := by
    rw [squareError_decomposition,map_sub]
    exact (norm_sub_le _ _).trans (add_le_add_right hd _)
  change u < _ at hg
  change _ ≤ u/2 at hsmall
  linarith only [hh,hg,hsmall,hn]

lemma coupling_sq {n : ℕ} (g : Disorder n) (i j : Fin n) :
    coupling g i j^2 = coupling (fun e => g e^2) i j := by
  unfold coupling
  split_ifs <;> simp

lemma affine_square_row_bound {n : ℕ} (hn : 0<n) (β : ℝ) (z : Disorder n)
    {C : ℝ} (hrow : ∀ i, (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ) ≤ C) (i : Fin n) :
    ∑ j, coupling (affineDisorder β z) i j^2 ≤ 2*β^2*C+2*β^4 := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hc : ((incidentEdges i).card:ℝ) ≤ n := by exact_mod_cast incidentEdges_card_le i
  have hne : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have ht : ∑ e ∈ incidentEdges i, affineDisorder β z e^2 ≤
      (2*β^2)*((∑ e ∈ incidentEdges i, z e^2)/(n:ℝ))+
        ((incidentEdges i).card:ℝ)*(2*β^4/(n:ℝ)^2) := by
    calc
      _ ≤ ∑ e ∈ incidentEdges i, (2*(β/sqrt n)^2*z e^2+2*(β^2/(n:ℝ))^2) := by
        apply Finset.sum_le_sum
        intro e _
        dsimp only [affineDisorder]
        nlinarith only [sq_nonneg ((β/sqrt n)*z e-β^2/n)]
      _ = _ := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum]
        simp only [Finset.sum_const,nsmul_eq_mul,div_pow,sq_sqrt (Nat.cast_nonneg n)]
        ring
  have hb : ((incidentEdges i).card:ℝ)*(2*β^4/(n:ℝ)^2) ≤ 2*β^4 := by
    calc
      _ ≤ (n:ℝ)*(2*β^4/(n:ℝ)^2) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (2*β^4)/(n:ℝ) := by field_simp
      _ ≤ _ := div_le_self (by positivity) hn1
  simp_rw [coupling_sq]
  rw [sum_coupling_row]
  exact ht.trans (add_le_add (mul_le_mul_of_nonneg_left (hrow i) (by positivity)) hb)

theorem square_rows_bounded (β : ℝ) :
    ∃ C : ℝ, 0<C ∧ ExponentiallyRare (law β)
      (fun n => {g | ∃ i : Fin n, C < ∑ j, coupling g i j^2}) := by
  obtain ⟨C,hC,hrows⟩ := gaussian_rows_square_bounded
  let D := 2*β^2*C+2*β^4+1
  have hD : 0<D := by dsimp [D]; positivity
  have ht : ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | ∃ i : Fin n, D < ∑ j, coupling (affineDisorder β z) i j^2}) := by
    apply hrows.mono
    filter_upwards [eventually_gt_atTop 0] with n hn
    rintro z ⟨i,hi⟩
    by_contra hnot
    have hrow : ∀ j, (∑ e ∈ incidentEdges j, z e^2)/(n:ℝ) ≤ C := by
      intro j
      exact le_of_not_gt (fun hj => hnot ⟨j,hj⟩)
    have hs := affine_square_row_bound hn β z hrow i
    dsimp [D] at hi
    linarith only [hs,hi]
  obtain ⟨A,c,hA,hc,hb⟩ := ht
  refine ⟨D,hD,A,c,hA,hc,?_⟩
  filter_upwards [hb,eventually_gt_atTop 0] with n hn hn0
  have hm : MeasurableSet {g : Disorder n | ∃ i : Fin n, D < ∑ j, coupling g i j^2} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    exact (continuous_finsetSum _ (fun j _ => (continuous_coupling i j).pow 2)).measurable
  rw [←(affineDisorder_hasLaw hn0 β).measure_eq hm]
  exact hn

lemma squareError_absolute_row {n : ℕ} (β : ℝ) (g : Disorder n) (i : Fin n) :
    ∑ j, |squareError β g i j| ≤ (∑ j, coupling g i j^2)+β^2 := by
  calc
    _ ≤ ∑ j, (coupling g i j^2+β^2/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (by positivity)])
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := i.isLt; omega)
      rw [mul_div_cancel₀ _ hn]

end SKRatio.Planted

end
end

end OAI
