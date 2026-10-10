import OAI.NumberTheory.TwoPoint.Bounds.LitBlockGeometry

namespace OAI

/-! Force the trace midpoint boundary by charging one extra imperfect position. -/

namespace TwoPointCorrelations

open Finset

theorem imperfectColumnCount_eq_card_compl {n : ℕ} (perfect : Finset (Fin n)) :
    imperfectColumnCount perfect = perfectᶜ.card := by
  classical
  let entries := (List.finRange n).filter (fun i => !decide (i ∈ perfect))
  have he : columnPositionEntries perfect =
      (List.finRange n).map (fun i => (i, decide (i ∈ perfect))) := by
    simp [columnPositionEntries, List.finRange, List.map_ofFn, Function.comp_def]
  have hn : entries.Nodup := (List.nodup_finRange n).filter _
  have hs : entries.toFinset = perfectᶜ := by
    ext i
    simp [entries]
  rw [imperfectColumnCount, he, List.filter_map, List.length_map]
  change entries.length = perfectᶜ.card
  rw [← List.toFinset_card_of_nodup hn, hs]

theorem imperfectColumnCount_erase_le {n : ℕ} (perfect : Finset (Fin n)) (cut : Fin n) :
    imperfectColumnCount (perfect.erase cut) ≤ imperfectColumnCount perfect + 1 := by
  classical
  rw [imperfectColumnCount_eq_card_compl, imperfectColumnCount_eq_card_compl]
  have hs : (perfect.erase cut)ᶜ ⊆ insert cut perfectᶜ := by
    intro i hi
    by_cases he : i = cut
    · simp [he]
    · have hp : i ∉ perfect := by
        intro hip
        exact (mem_compl.mp hi) (mem_erase.mpr ⟨he, hip⟩)
      exact mem_insert_of_mem (mem_compl.mpr hp)
  exact (card_le_card hs).trans (card_insert_le _ _)

/-- A block containing only retained perfect positions cannot cross the
erased midpoint. The erased step is still encoded by its ordinary
imperfect-position reference. -/
theorem perfect_block_avoids_cut {n : ℕ} (perfect : Finset (Fin n)) (cut : Fin n)
    (start len : ℕ) (_hend : start + len ≤ n)
    (hperfect : ∀ t ∈ intervalPositions (start, len),
      columnNatPerfect (perfect.erase cut) t = true) :
    start + len ≤ cut.val ∨ cut.val < start := by
  by_contra h
  have hlo : start ≤ cut.val := by omega
  have hhi : cut.val < start + len := by omega
  have hm : cut.val ∈ intervalPositions (start, len) := by
    simp only [intervalPositions, List.mem_map, List.mem_range]
    exact ⟨cut.val - start, by omega, by omega⟩
  have hp := hperfect cut.val hm
  simp [columnNatPerfect_fin] at hp

theorem isChain_slice_of_two_halves {α : Type*} {R : α → α → Prop}
    (w : List α) (cut start len : ℕ)
    (hleft : (w.take cut).IsChain R) (hright : (w.drop cut).IsChain R)
    (hside : start + len ≤ cut ∨ cut ≤ start) :
    ((w.drop start).take len).IsChain R := by
  rcases hside with hl | hr
  · have hs := (hleft.drop start).take len
    simpa only [List.drop_take, List.take_take, Nat.min_eq_left (by omega : len ≤ cut - start)] using hs
  · have hs := (hright.drop (start - cut)).take len
    simpa only [List.drop_drop, Nat.add_sub_cancel' hr] using hs

/-- The two actual nonbacktracking halves suffice for every retained
perfect block; no relation between the two midpoint tuples is needed. -/
theorem trace_perfect_block_chain {n : ℕ} (perfect : Finset (Fin n)) (cut : Fin n)
    (w : List SignedStep)
    (hleft : (w.take cut.val).IsChain (fun a b => a.tuple ≠ b.tuple))
    (hright : (w.drop cut.val).IsChain (fun a b => a.tuple ≠ b.tuple))
    (start len : ℕ) (hend : start + len ≤ n)
    (hperfect : ∀ t ∈ intervalPositions (start, len),
      columnNatPerfect (perfect.erase cut) t = true) :
    (wordSlice w start (start + len)).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  have hs := perfect_block_avoids_cut perfect cut start len hend hperfect
  have hc := isChain_slice_of_two_halves w cut.val start len hleft hright
    (hs.imp_right Nat.le_of_lt)
  simpa only [wordSlice, Nat.add_sub_cancel_left] using hc

/-- The one additional midpoint reference fits inside the same imperfect
budget once the singleton and unlit exceptional classes have been removed. -/
theorem eventually_imperfect_with_cut_bound :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ singletons unlit imperfect : ℕ,
      imperfect ≤ singletons + unlit + 1 →
      (singletons : ℝ) ≤ L ^ (1 / 4 : ℝ) →
      (unlit : ℝ) ≤ L ^ (1 / 50 : ℝ) →
      (imperfect : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ) := by
  have hp := (tendsto_rpow_atTop (show 0 < (23 / 100 : ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop 2)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hp] with L hL hp
  intro S U I hI hS hU
  have hone : 1 ≤ L ^ (1 / 50 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have he : L ^ (1 / 50 : ℝ) * L ^ (23 / 100 : ℝ) = L ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add (by linarith : 0 < L)]
    norm_num
  have hprod := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by linarith) (1 / 50 : ℝ))
  have hi : (I : ℝ) ≤ (S : ℝ) + U + 1 := by exact_mod_cast hI
  nlinarith

end TwoPointCorrelations

end OAI
