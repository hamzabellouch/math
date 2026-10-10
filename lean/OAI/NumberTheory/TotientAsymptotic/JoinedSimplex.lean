import OAI.NumberTheory.TotientAsymptotic.TailArray
import OAI.NumberTheory.TotientAsymptotic.TailBoxCoordinates
import OAI.NumberTheory.TotientAsymptotic.UnbandedLower
import OAI.NumberTheory.TotientAsymptotic.SimplexCube

namespace OAI

/-! Exact full-dimensional completion of a continuous prefix by its discrete tail. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma joined_prefix_row {R T : ℕ} (u : Fin R → ℝ) (v : Fin T → ℝ) (i : Fin R) :
    (∑ j : Fin (R+T), if Fin.castAdd T i < j then
      a (j.val-i.val)*joinCoordinates R T (u,v) j else 0) =
    (∑ j : Fin R, if i < j then a (j.val-i.val)*u j else 0) +
      ∑ j : Fin T, a (R+j.val-i.val)*v j := by
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.lt_def, Fin.val_castAdd, joinCoordinates_left]
  · apply Finset.sum_congr rfl
    intro j _
    rw [ite_eq_left (by simp [Fin.lt_def]; omega), joinCoordinates_right]
    rfl

lemma joined_tail_row {R T : ℕ} (u : Fin R → ℝ) (v : Fin T → ℝ) (i : Fin T) :
    (∑ j : Fin (R+T), if Fin.natAdd R i < j then
      a (j.val-(R+i.val))*joinCoordinates R T (u,v) j else 0) =
    ∑ j : Fin T, if i < j then a (j.val-i.val)*v j else 0 := by
  rw [Fin.sum_univ_add]
  have hz : (∑ j : Fin R, if Fin.natAdd R i < Fin.castAdd T j then
      a ((Fin.castAdd T j).val-(R+i.val))*joinCoordinates R T (u,v) (Fin.castAdd T j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by simp [Fin.lt_def]; omega)]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.natAdd_lt_natAdd_iff, Fin.val_natAdd, Nat.add_sub_add_left,
    joinCoordinates_right]

lemma joined_budget {R T : ℕ} (u : Fin R → ℝ) (v : Fin T → ℝ) :
    (∑ j : Fin (R+T), a (j.val+1)*joinCoordinates R T (u,v) j) =
      (∑ j : Fin R, a (j.val+1)*u j) + ∑ j : Fin T, a (R+j.val+1)*v j := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, joinCoordinates_left, joinCoordinates_right]

lemma prefix_D_tailVector {x : ℝ} {H : ℕ} (η : TailDatum H)
    (hPH : P H ≤ H) (hHm : H ≤ m x) (i : Fin (R x H)) :
    D (m x-(i.val+1)) η =
      ∑ j : Fin (H-P H), a (R x H+j.val-i.val)*tailVector η j := by
  rw [D_eq_tailVector_sum η hPH]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  have hi := i.isLt
  have hj := j.isLt
  unfold R at *
  omega

lemma top_D_tailVector {x : ℝ} {H : ℕ} (η : TailDatum H)
    (hPH : P H ≤ H) (hHm : H ≤ m x) :
    D (m x) η = ∑ j : Fin (H-P H), a (R x H+j.val+1)*tailVector η j := by
  rw [D_eq_tailVector_sum η hPH]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  have hj := j.isLt
  unfold R
  omega

/-- No prefix prime bands are required for exact completion to the full
simplex: the unperturbed prefix constraints and the witness tail suffice. -/
theorem join_witness_enlarged {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hη : IsWitness H (theta x) η) (hPH : P H < H) (hHm : H ≤ m x) (hB : 0 ≤ B x)
    {u : Fin (R x H) → ℝ} (hu : u ∈ tailPrefixRegion x H η) :
    joinCoordinates (R x H) (H-P H) (u,tailVector η) ∈
      enlargedSimplex (R x H+(H-P H)) (B x) (xi x 0) (fun i => xi x (i.val+1)) := by
  have hun (i : Fin (R x H)) : 0 ≤ u i :=
    (mul_nonneg (g_pos _).le (tailLog_nonneg hη (Finset.mem_Ico.mpr (by omega)))).trans
      (tailPrefixRegion_terminal_lower hη hPH hHm hu i)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [joinCoordinates_left] using hun j
    · simpa only [joinCoordinates_right] using tailVector_nonneg hη j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.val_castAdd]
      rw [joined_prefix_row, joinCoordinates_left]
      have hd := prefix_D_tailVector η hPH.le hHm j
      have hh := hu.1 j
      rw [prefixLinear_apply] at hh
      change D (m x-(j.val+1)) η ≤ u j-_ at hh
      rw [← hd]
      have hmul := le_mul_of_one_le_left (hun j) (xi_bounds x (j.val+1)).1
      simpa only [Fin.val_castAdd] using (show _ ≤ xi x (j.val+1)*u j by linarith)
    · simp only [Fin.val_natAdd]
      rw [joined_tail_row, joinCoordinates_right]
      have hj := j.isLt
      have he : m x-(R x H+j.val+1) = H-1-j.val := by
        unfold R
        omega
      have hh := tailVector_simplex hη j
      simpa only [xi, he] using hh
  · rw [joined_budget, ← top_D_tailVector η hPH.le hHm]
    have hh := hu.2
    have hb := le_mul_of_one_le_left hB (xi_bounds x 0).1
    change (∑ j, a (j.val+1)*u j) ≤ B x-D (m x) η at hh
    linarith

end TotientAsymptotic

end

end OAI
