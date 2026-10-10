import OAI.Analysis.IrrationalRotation.Operators.TowerBlockAlgebras
import OAI.Analysis.IrrationalRotation.Analysis.TowerApproximationBounds

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233.TowerTraceBounds
open TowerMatrixUnits

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {ξ : H}
  {β : Type*} [Fintype β] {ι : β → Type*} [∀ b, Fintype (ι b)]
  [∀ b, DecidableEq (ι b)]
  (e : (b : β) → ι b → ι b → H →L[ℂ] H)
  (he : IsBlockMatrixUnitFamily e)

include he

omit [Fintype β] [∀ b, Fintype (ι b)] in

theorem diagonal_isStarProjection (b : β) (i : ι b) :
    IsStarProjection (e b i i) := by
  constructor
  · change e b i i * e b i i = e b i i
    simpa using (he.block b).mul i i i i
  · exact (he.block b).star i i

omit [∀ b, Fintype (ι b)] in

theorem selectedFloor_isStarProjection (top : ∀ b, ι b) :
    IsStarProjection (∑ b, e b (top b) (top b)) := by
  classical
  constructor
  · change (∑ b, e b (top b) (top b)) * (∑ b, e b (top b) (top b)) = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum, Finset.sum_eq_single b]
    · simpa using (he.block b).mul (top b) (top b) (top b) (top b)
    · intro c hc hcb
      exact he.cross b c (Ne.symm hcb) _ _ _ _
    · simp
  · change star (∑ b, e b (top b) (top b)) = _
    rw [star_sum]
    exact Finset.sum_congr rfl (fun b _ => (he.block b).star _ _)

omit [Fintype β] [∀ b, Fintype (ι b)] in

theorem diagonal_trace_eq (htrace : IsFaithfulTracialVector M ξ)
    (hmem : ∀ b i j, e b i j ∈ M) (b : β) (i j : ι b) :
    vectorTrace ξ (e b i i) = vectorTrace ξ (e b j j) := by
  have h := htrace.2.1 (e b i j) (e b j i) (hmem b i j) (hmem b j i)
  simpa only [(he.block b).mul, ite_true] using h

omit he [CompleteSpace H] in

theorem vectorTrace_sum_re {κ : Type*} [Fintype κ] (f : κ → H →L[ℂ] H) :
    (vectorTrace ξ (∑ k, f k)).re = ∑ k, (vectorTrace ξ (f k)).re := by
  simp only [vectorTrace, sum_apply, inner_sum]
  exact map_sum Complex.reAddGroupHom _ _

theorem height_weighted_trace_eq_one (htrace : IsFaithfulTracialVector M ξ)
    (hmem : ∀ b i j, e b i j ∈ M) (top : ∀ b, ι b)
    (hcomplete : ∑ b, ∑ i, e b i i = 1) :
    (∑ b, (Fintype.card (ι b) : ℝ) * (vectorTrace ξ (e b (top b) (top b))).re) = 1 := by
  have heq := congrArg (fun T : H →L[ℂ] H => (vectorTrace ξ T).re) hcomplete
  rw [vectorTrace_sum_re] at heq
  simp_rw [vectorTrace_sum_re, diagonal_trace_eq e he htrace hmem _ _ (top _)] at heq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at heq
  have hone : (vectorTrace ξ (1 : H →L[ℂ] H)).re = 1 := by
    change (inner ℂ ξ ξ).re = 1
    calc
      (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) ξ
      _ = 1 := by rw [htrace.1]; norm_num
  exact heq.trans hone

theorem selectedFloor_trace_le_inv_height (htrace : IsFaithfulTracialVector M ξ)
    (hmem : ∀ b i j, e b i j ∈ M) (top : ∀ b, ι b)
    (hcomplete : ∑ b, ∑ i, e b i i = 1)
    (N : ℕ) (hN : 0 < N) (hheight : ∀ b, N ≤ Fintype.card (ι b)) :
    (vectorTrace ξ (∑ b, e b (top b) (top b))).re ≤ 1 / (N : ℝ) := by
  have hnonneg (b : β) : 0 ≤ (vectorTrace ξ (e b (top b) (top b))).re := by
    rw [TowerApproximation.vectorTrace_projection_re _
      (diagonal_isStarProjection e he b (top b)) ξ]
    positivity
  have hcount := height_weighted_trace_eq_one e he htrace hmem top hcomplete
  rw [vectorTrace_sum_re]
  apply (le_div_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN)).mpr
  calc
    (∑ b, (vectorTrace ξ (e b (top b) (top b))).re) * (N : ℝ) =
        ∑ b, (N : ℝ) * (vectorTrace ξ (e b (top b) (top b))).re := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
    _ ≤ ∑ b, (Fintype.card (ι b) : ℝ) *
        (vectorTrace ξ (e b (top b) (top b))).re := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hheight b) (hnonneg b)
    _ = 1 := hcount

theorem norm_sub_apply_sq_le_four_div_height
    (htrace : IsFaithfulTracialVector M ξ)
    (hmem : ∀ b i j, e b i j ∈ M) (top : ∀ b, ι b)
    (hcomplete : ∑ b, ∑ i, e b i i = 1)
    (N : ℕ) (hN : 0 < N) (hheight : ∀ b, N ≤ Fintype.card (ι b))
    {A B : H →L[ℂ] H} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hagree : A * (1 - ∑ b, e b (top b) (top b)) =
      B * (1 - ∑ b, e b (top b) (top b))) :
    ‖A ξ - B ξ‖ ^ 2 ≤ 4 / (N : ℝ) := by
  have hp := selectedFloor_isStarProjection e he top
  have hb := TowerApproximation.norm_sub_apply_sq_le_four_trace_compl hA hB hp.one_sub hagree ξ
  simp only [sub_sub_cancel] at hb
  have ht := selectedFloor_trace_le_inv_height e he htrace hmem top hcomplete N hN hheight
  calc
    ‖A ξ - B ξ‖ ^ 2 ≤ 4 * (vectorTrace ξ (∑ b, e b (top b) (top b))).re := hb
    _ ≤ 4 * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left ht (by norm_num)
    _ = 4 / (N : ℝ) := by ring

end Invariant233.TowerTraceBounds

end

end OAI
