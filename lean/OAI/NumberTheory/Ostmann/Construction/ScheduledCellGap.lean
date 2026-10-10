import OAI.NumberTheory.Ostmann.Construction.ScheduledCellSteps
import OAI.NumberTheory.Ostmann.Construction.SelectedCellGap

namespace OAI

/-! # The geometric gap on the actual compensation schedule -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def scheduledSmallLower (top : ℕ) (cs : List ℕ) (n : ℕ)
    (i : TreeLeafIndex n × Fin (scheduledSmallLength cs)) : ℝ :=
  (scheduledSmallCell top cs i.2 : ℝ) - 1

theorem scheduledSmallCell_lower_sum (top : ℕ) (cs : List ℕ) :
    (∑ i : Fin (scheduledSmallLength cs), ((scheduledSmallCell top cs i : ℝ) - 1)) =
      6 * ((top : ℝ) - 1) + 4 * (cs.map (fun c : ℕ => (c : ℝ) - 1)).sum := by
  induction cs with
  | nil =>
    change (∑ _ : Fin 6, ((top : ℝ) - 1)) = _
    norm_num [Fin.sum_univ_succ]
    ring
  | cons c cs ih =>
    change (∑ i : Fin (4 + scheduledSmallLength cs),
      (((Fin.append (fun _ : Fin 4 => c) (scheduledSmallCell top cs) i : ℕ) : ℝ) - 1)) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ih, List.map_cons, List.sum_cons]
    push_cast
    ring

theorem scheduledSmallLower_sum (top : ℕ) (cs : List ℕ) (n : ℕ) :
    (∑ i, scheduledSmallLower top cs n i) =
      (2 ^ n : ℕ) * (6 * ((top : ℝ) - 1) +
        4 * (cs.map (fun c : ℕ => (c : ℝ) - 1)).sum) := by
  simp only [scheduledSmallLower, Fintype.sum_prod_type]
  rw [scheduledSmallCell_lower_sum]
  simp only [Finset.sum_const, Finset.card_univ, card_treeLeafIndex, nsmul_eq_mul]

theorem list_sum_sub_one (cs : List ℝ) :
    (cs.map (fun c => c - 1)).sum = cs.sum - cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one, ih]; ring

theorem sum_le_four_of_forall₂ {cs ts : List ℝ}
    (h : List.Forall₂ (fun c t => t ≤ 4 * c) cs ts) : ts.sum ≤ 4 * cs.sum := by
  induction h with
  | nil => simp
  | cons h hrest ih => simp only [List.sum_cons]; linarith

theorem scheduledSmallLower_sum_eq (top : ℕ) (cs : List ℕ) (n : ℕ) :
    (∑ i, scheduledSmallLower top cs n i) =
      ∑ i, movingCellLower n
        (movingSmallCellCenters (List.replicate 6 (top : ℝ))
          (cs.map (fun c : ℕ => (c : ℝ)))) i := by
  rw [scheduledSmallLower_sum, movingCellLower_sum, list_sum_sub_one,
    movingSmallCellCenters_sum, movingSmallCellCenters_length, List.sum_replicate,
    List.length_replicate, List.length_map]
  have hs : (cs.map (fun c : ℕ => (c : ℝ) - 1)).sum =
      (cs.map (fun c : ℕ => (c : ℝ))).sum - cs.length := by
    simpa only [List.map_map, Function.comp_def, List.length_map] using
      list_sum_sub_one (cs.map (fun c : ℕ => (c : ℝ)))
  rw [hs]
  push_cast
  ring

theorem selected_scheduled_cell_diagonal_gap
    {A B : Set ℕ} {N hi top pivot : ℕ} {a C L X J cb w cg BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ} (k n : ℕ)
    (hL : 1 ≤ L) (hX : 0 < X) (hXupper : X ≤ Real.exp L)
    (hk : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (7 + 4 * centers.length : ℕ) ≤ L)
    (hcg : cg ≤ (91 / 100 : ℝ) * L)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - cb) / 6) top)
    (hpivot : SelectedSmallTailCell A B N a C L X hi D (w / 4) pivot)
    (hcenters : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j) centers targets)
    (hbalance : (2 ^ n : ℕ) * w = (2 ^ n : ℕ) * (J + targets.sum) -
      spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L)) :
    2 * cg + 1 + ((2 ^ n : ℕ) * 4) * ((pivot : ℝ) + 1) -
        ((∑ i, scheduledSmallLower top centers n i) + (2 ^ n : ℕ) * (cb - 1)) ≤
      -spectatorStepGap (BD - 1) Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
        (spectatorBulkCount k L) := by
  rw [scheduledSmallLower_sum_eq]
  exact selected_cell_diagonal_gap k n hL hX hXupper hk hcount hcg htop hpivot
    hcenters hbalance

theorem selected_scheduled_initial_diagonal_gap
    {A B : Set ℕ} {N hi top pivot : ℕ} {a C L X J cb w cg BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ} (k n : ℕ)
    (hL : 1 ≤ L) (hX : 0 < X) (hXupper : X ≤ Real.exp L)
    (hk : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * centers.length : ℕ) ≤ L)
    (hcg : cg ≤ (91 / 100 : ℝ) * L)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hpivot : SelectedSmallTailCell A B N a C L X hi D (w / 4) pivot)
    (hcenters : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j) centers targets)
    (hbalance : (2 ^ n : ℕ) * w = (2 ^ n : ℕ) * (J + targets.sum) -
      spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L)) :
    2 * cg + 1 + ((2 ^ n : ℕ) * 4) * ((pivot : ℝ) + 1) -
        ((∑ i, scheduledSmallLower top centers n i) + (2 ^ n : ℕ) * (2 * cb - 2)) ≤
      -spectatorStepGap (BD - 1) Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
        (spectatorBulkCount k L) := by
  have hr : (0 : ℝ) ≤ (2 ^ n : ℕ) := Nat.cast_nonneg _
  have ht : J ≤ 6 * (top : ℝ) + 2 * cb := by linarith [htop.1]
  have hc : targets.sum ≤ 4 * (centers.map (fun j : ℕ => (j : ℝ))).sum := by
    exact sum_le_four_of_forall₂ (selected_centers_lower hcenters)
  have hlower : (2 ^ n : ℕ) * (J + targets.sum) -
      (8 + 4 * centers.length : ℕ) * (2 ^ n : ℕ) ≤
      (∑ i, scheduledSmallLower top centers n i) + (2 ^ n : ℕ) * (2 * cb - 2) := by
    rw [scheduledSmallLower_sum]
    have hs := list_sum_sub_one (centers.map (fun j : ℕ => (j : ℝ)))
    simp only [List.map_map, Function.comp_def, List.length_map] at hs
    rw [hs]
    have htr := mul_le_mul_of_nonneg_left ht hr
    have hcr := mul_le_mul_of_nonneg_left hc hr
    push_cast at htr hcr ⊢
    nlinarith only [htr, hcr]
  have hcost : 2 * cg + 1 +
      (256 * tailDefectBudget a C X + 8 + (8 + 4 * centers.length : ℕ)) * (2 ^ n : ℕ) ≤
      (2 ^ n : ℕ) * (spectatorBulkCount k L : ℝ) := by
    apply moving_linear_cell_error_budget k n (256 * tailCellLinearRate a C + 9) L cg
      (256 * tailDefectBudget a C X + 8) (8 + 4 * centers.length : ℕ)
      (by linarith [tailCellLinearRate_nonneg a C]) (by linarith) hL hcg
    have he := tailDefectBudget_linear a C L X hL hX hXupper
    nlinarith only [he, hcount, hL]
  have he := moving_cell_diagonal_gap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
    (spectatorBulkCount k L) J targets.sum w ((pivot : ℝ) + 1) (2 * cb - 1)
    (∑ i, scheduledSmallLower top centers n i) cg
    (256 * tailDefectBudget a C X + 8) (8 + 4 * centers.length : ℕ)
    hr hbalance (by simpa only [add_assoc] using hpivot.compensation_upper)
    (by convert hlower using 1; ring) hcost
  convert he using 1; ring

end Ostmann

end OAI
