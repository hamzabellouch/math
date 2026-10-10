import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import OAI.NumberTheory.Catalan.Analysis.ZetaIntegral

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace InternalCatalan

theorem zetaTerm_adjacent (i u : ℕ) :
    zetaTerm i (i + 1) u =
      1 / ((i + u + 1 : ℕ) : ℝ) - 1 / ((i + u + 2 : ℕ) : ℝ) := by
  unfold zetaTerm
  rw [show i + 1 + u + 1 = i + u + 2 by omega]
  push_cast
  have ha : (i : ℝ) + (u : ℝ) + 1 ≠ 0 := by positivity
  have hb : (i : ℝ) + (u : ℝ) + 2 ≠ 0 := by positivity
  field_simp [ha, hb]
  ring

theorem sum_zetaTerm_adjacent (i m : ℕ) :
    (∑ u ∈ Finset.range m, zetaTerm i (i + 1) u) =
      1 / ((i + 1 : ℕ) : ℝ) - 1 / ((i + m + 1 : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, zetaTerm_adjacent]
    rw [show i + (m + 1) + 1 = i + m + 2 by omega]
    ring

theorem zetaSeries_adjacent (i : ℕ) :
    zetaSeries i (i + 1) = 1 / ((i + 1 : ℕ) : ℝ) := by
  have ht : Tendsto (fun m : ℕ => 1 / ((i + m + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat (i + 1)).2
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  apply tendsto_nhds_unique (tendsto_partial_sums_zetaSeries i (i + 1))
  simp_rw [sum_zetaTerm_adjacent]
  simpa only [sub_zero] using
    (tendsto_const_nhds (x := 1 / ((i + 1 : ℕ) : ℝ))).sub ht

theorem zetaTerm_gap_step (i d u : ℕ) :
    ((d + 1 : ℕ) : ℝ) * zetaTerm i (i + d + 1) u =
      (d : ℝ) * zetaTerm i (i + d) u + zetaTerm (i + d) (i + d + 1) u := by
  unfold zetaTerm
  push_cast
  have ha : (i : ℝ) + (u : ℝ) + 1 ≠ 0 := by positivity
  have hb : (i : ℝ) + (d : ℝ) + (u : ℝ) + 1 ≠ 0 := by positivity
  have hc : (i : ℝ) + (d : ℝ) + 1 + (u : ℝ) + 1 ≠ 0 := by positivity
  field_simp [ha, hb, hc]
  ring

theorem zetaSeries_gap_step (i d : ℕ) :
    ((d + 1 : ℕ) : ℝ) * zetaSeries i (i + d + 1) =
      (d : ℝ) * zetaSeries i (i + d) + 1 / ((i + d + 1 : ℕ) : ℝ) := by
  have hs := ((hasSum_zetaSeries i (i + d)).mul_left (d : ℝ)).add
    (hasSum_zetaSeries (i + d) (i + d + 1))
  calc
    ((d + 1 : ℕ) : ℝ) * zetaSeries i (i + d + 1) =
        ∑' u : ℕ, ((d + 1 : ℕ) : ℝ) * zetaTerm i (i + d + 1) u := by
      exact tsum_mul_left.symm
    _ = ∑' u : ℕ, ((d : ℝ) * zetaTerm i (i + d) u +
        zetaTerm (i + d) (i + d + 1) u) :=
      tsum_congr (zetaTerm_gap_step i d)
    _ = (d : ℝ) * zetaSeries i (i + d) + zetaSeries (i + d) (i + d + 1) :=
      hs.tsum_eq
    _ = _ := by rw [zetaSeries_adjacent]

theorem zetaSeries_mul_gap (i d : ℕ) :
    ((d + 1 : ℕ) : ℝ) * zetaSeries i (i + (d + 1)) =
      (harmonicRat 1 (i + (d + 1)) : ℝ) - (harmonicRat 1 i : ℝ) := by
  induction d with
  | zero =>
    simp only [Nat.zero_add, Nat.cast_one, one_mul]
    rw [zetaSeries_adjacent, harmonicRat_succ]
    push_cast
    simp only [pow_one]
    ring
  | succ d ih =>
    have hH := congrArg (fun q : ℚ => (q : ℝ)) (harmonicRat_succ 1 (i + (d + 1)))
    push_cast at hH
    simp only [pow_one] at hH
    calc
      ((d + 1 + 1 : ℕ) : ℝ) * zetaSeries i (i + (d + 1 + 1)) =
          ((d + 1 : ℕ) : ℝ) * zetaSeries i (i + (d + 1)) +
            1 / ((i + (d + 1) + 1 : ℕ) : ℝ) := by
        simpa only [Nat.add_assoc] using zetaSeries_gap_step i (d + 1)
      _ = (harmonicRat 1 (i + (d + 1 + 1)) : ℝ) - (harmonicRat 1 i : ℝ) := by
        rw [ih, show i + (d + 1 + 1) = i + (d + 1) + 1 by omega, hH]
        push_cast
        ring

theorem zetaSeries_eq_harmonic_div {i j : ℕ} (hij : i < j) :
    zetaSeries i j =
      ((harmonicRat 1 j : ℝ) - (harmonicRat 1 i : ℝ)) / ((j : ℝ) - (i : ℝ)) := by
  let d := j - i - 1
  have he : j = i + (d + 1) := by dsimp [d]; omega
  have hd : (j : ℝ) - (i : ℝ) = ((d + 1 : ℕ) : ℝ) := by
    rw [he]
    push_cast
    ring
  have hd0 : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [hd]
  apply (eq_div_iff hd0).2
  have h := zetaSeries_mul_gap i d
  rw [← he] at h
  simpa only [mul_comm] using h

theorem zetaSeries_eq_zetaRat_of_lt {i j : ℕ} (hij : i < j) :
    zetaSeries i j = (zetaRat i j : ℝ) := by
  rw [zetaSeries_eq_harmonic_div hij, zetaRat_of_ne (ne_of_lt hij)]
  push_cast
  have hlt : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  apply (div_eq_div_iff (sub_ne_zero.mpr (ne_of_gt hlt))
    (sub_ne_zero.mpr (ne_of_lt hlt))).2
  ring

theorem zetaSeries_offDiagonal {i j : ℕ} (hij : i ≠ j) :
    zetaSeries i j = (zetaRat i j : ℝ) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact zetaSeries_eq_zetaRat_of_lt hlt
  · rw [zetaSeries_symm i j, zetaRat_symm i j]
    exact zetaSeries_eq_zetaRat_of_lt hgt

theorem zetaSeries_eq_zetaRat_add (i j : ℕ) :
    zetaSeries i j = (zetaRat i j : ℝ) +
      if i = j then zetaSeries 0 0 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using zetaSeries_diagonal i
  · rw [ite_eq_right hij, add_zero]
    exact zetaSeries_offDiagonal hij

end InternalCatalan

end

end OAI
