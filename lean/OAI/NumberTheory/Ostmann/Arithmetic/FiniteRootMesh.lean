import OAI.NumberTheory.Ostmann.Characters.PolynomialRootCells

namespace OAI

/-! # A finite interval partition at every arithmetic root -/

namespace Ostmann
open scoped Classical

/-- Partition a bounded interval at all roots in it, retaining the roots as
endpoints. The number of intervals is at most the number of cuts plus one. -/
theorem finite_root_mesh (S : Finset ℝ) (u v : ℝ) (huv : u ≤ v) :
    ∃ (s : ℕ → ℝ) (N : ℕ), Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ S.card + 1 ∧
      ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (s j) (s (j + 1)) := by
  let R := insert u (insert v (S.filter (fun r => r ∈ Set.Icc u v)))
  have hu : u ∈ R := by simp [R]
  have hv : v ∈ R := by simp [R]
  have hpos : 0 < R.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hmem (r : ℝ) (hr : r ∈ R) : r ∈ Set.Icc u v := by
    simp only [R, Finset.mem_insert, Finset.mem_filter] at hr
    rcases hr with rfl | rfl | ⟨_, hr⟩
    · exact ⟨le_rfl, huv⟩
    · exact ⟨huv, le_rfl⟩
    · exact hr
  let f := R.orderEmbOfFin rfl
  have hf0 : f ⟨0, hpos⟩ = u := by
    rw [Finset.orderEmbOfFin_zero rfl hpos]
    exact le_antisymm (Finset.min'_le R u hu)
      (hmem _ (Finset.min'_mem R _)).1
  have hflast : f ⟨R.card - 1, Nat.sub_lt hpos (by decide)⟩ = v := by
    rw [Finset.orderEmbOfFin_last rfl hpos]
    exact le_antisymm (hmem _ (Finset.max'_mem R _)).2 (Finset.le_max' R v hv)
  let N := R.card - 1
  let s := fun j : ℕ => f ⟨min j N, lt_of_le_of_lt (min_le_right _ _) (by omega)⟩
  have hs : Monotone s := by
    intro i j hij
    exact f.monotone (show min i N ≤ min j N from min_le_min hij le_rfl)
  have hs0 : s 0 = u := by simpa only [s, Nat.zero_min] using hf0
  have hsN : s N = v := by simpa only [s, min_self, N] using hflast
  refine ⟨s, N, hs, hs0, hsN, ?_, ?_⟩
  · have hcard : R.card ≤ S.card + 2 := by
      calc
        R.card ≤ (insert v (S.filter (fun r => r ∈ Set.Icc u v))).card + 1 := Finset.card_insert_le _ _
        _ ≤ (S.filter (fun r => r ∈ Set.Icc u v)).card + 1 + 1 := by
          gcongr
          exact Finset.card_insert_le _ _
        _ ≤ S.card + 2 := by have := Finset.card_filter_le S (fun r => r ∈ Set.Icc u v); omega
    omega
  · intro j hj r hr hin
    have hjc : j < R.card := by omega
    have hj1c : j + 1 < R.card := by omega
    have he0 : s j = f ⟨j, hjc⟩ := by simp only [s, min_eq_left (by omega : j ≤ N)]
    have he1 : s (j + 1) = f ⟨j + 1, hj1c⟩ := by
      simp only [s, min_eq_left (by omega : j + 1 ≤ N)]
    have hrange : r ∈ Set.Icc u v :=
      ⟨(hs0 ▸ hs (Nat.zero_le j)).trans hin.1.le,
        hin.2.le.trans (hsN ▸ hs (by omega : j + 1 ≤ N))⟩
    have hrR : r ∈ R := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hr, hrange⟩))
    let k := (R.orderIsoOfFin rfl).symm ⟨r, hrR⟩
    have hk : f k = r := congrArg Subtype.val ((R.orderIsoOfFin rfl).apply_symm_apply ⟨r, hrR⟩)
    have hleft : (⟨j, hjc⟩ : Fin R.card) < k := f.lt_iff_lt.mp (by rw [← he0, hk]; exact hin.1)
    have hright : k < (⟨j + 1, hj1c⟩ : Fin R.card) := f.lt_iff_lt.mp (by rw [← he1, hk]; exact hin.2)
    have hl : j < k.val := hleft
    have hr' : k.val < j + 1 := hright
    omega

/-- The side of every root is constant in the open part of one partition cell. -/
theorem rootCellCode_eq_of_root_free (S : Finset ℝ) (a b x y : ℝ)
    (hfree : ∀ r ∈ S, r ∉ Set.Ioo a b)
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    rootCellCode S x = rootCellCode S y := by
  funext r
  change compare x r.val = compare y r.val
  by_cases hr : r.val ≤ a
  · rw [compare_gt_iff_gt.mpr (hr.trans_lt hx.1), compare_gt_iff_gt.mpr (hr.trans_lt hy.1)]
  · have hb : b ≤ r.val := by
      by_contra hb
      exact hfree r.val r.property ⟨lt_of_not_ge hr, lt_of_not_ge hb⟩
    rw [compare_lt_iff_lt.mpr (hx.2.trans_le hb), compare_lt_iff_lt.mpr (hy.2.trans_le hb)]

/-- A partition in logarithmic coordinates still includes every positive
root of the original giant-variable polynomials. -/
theorem finite_log_root_mesh (S : Finset ℝ) (u v : ℝ) (huv : u ≤ v) :
    ∃ (s : ℕ → ℝ) (N : ℕ), Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ S.card + 1 ∧
      ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))) := by
  obtain ⟨x, N, hx, hx0, hxN, hN, hfree⟩ :=
    finite_root_mesh S (Real.exp u) (Real.exp v) (Real.exp_le_exp.mpr huv)
  have hpos (j : ℕ) : 0 < x j := by
    have hh := hx (Nat.zero_le j)
    rw [hx0] at hh
    exact (Real.exp_pos u).trans_le hh
  let s := fun j => Real.log (x j)
  refine ⟨s, N, ?_, ?_, ?_, hN, ?_⟩
  · intro i j hij
    exact Real.log_le_log (hpos i) (hx hij)
  · simp only [s, hx0, Real.log_exp]
  · simp only [s, hxN, Real.log_exp]
  · intro j hj r hr
    simpa only [s, Real.exp_log (hpos _)] using hfree j hj r hr

end Ostmann

end OAI
