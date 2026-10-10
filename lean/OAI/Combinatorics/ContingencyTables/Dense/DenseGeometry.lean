import OAI.Combinatorics.ContingencyTables.Dense.DenseRegularity
import OAI.Combinatorics.ContingencyTables.Transport.RealCompletion

namespace OAI

/-!
# Feasible region and interior point of the dense block

These statements use the actual integer margins and quotient widths. Every
feasible real completion lies in the declared scaled cube, and one scaled
completion has normalized slack at least `1/(2d)` in every cell.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def Feasible (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (u : I × J → ℝ) : Prop :=
  ∀ i j, 0 ≤ table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (denseWidth R P d) u i j

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem denseWidth_pos (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j) (i : I) (j : J) :
    0 < denseWidth R P d i j := by
  unfold denseWidth
  exact_mod_cast dense_width_positive d (min (R (some i)) (P (some j))) hd
    (le_min (hR _) (hP _))

omit [DecidableEq I] [DecidableEq J] in
private theorem table_entry_upper (R : Option I → ℝ) (P : Option J → ℝ)
    (w : I → J → ℝ) (u : I × J → ℝ) (htotal : ∑ i, R i = ∑ j, P j)
    (hfeas : ∀ i j, 0 ≤ table R P w u i j) (i : Option I) (j : Option J) :
    table R P w u i j ≤ min (R i) (P j) := by
  apply le_min
  · have h := Finset.single_le_sum (fun k _ => hfeas i k) (Finset.mem_univ j)
    rwa [table_rows] at h
  · have h := Finset.single_le_sum (fun k _ => hfeas k j) (Finset.mem_univ i)
    rwa [table_columns _ _ _ _ htotal] at h

omit [DecidableEq I] [DecidableEq J] in
theorem feasible_in_cube (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (htotal : ∑ i, R i = ∑ j, P j) (u : I × J → ℝ) (hu : Feasible R P d u) :
    ∀ p, 0 ≤ u p ∧ u p ≤ 2 * (d : ℝ) ^ 8 := by
  intro p
  have hw := denseWidth_pos R P d hd hR hP p.1 p.2
  have hlo := hu (some p.1) (some p.2)
  have ht : (∑ i, (R i : ℝ)) = ∑ j, (P j : ℝ) := by exact_mod_cast htotal
  have hhi := table_entry_upper (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
    (denseWidth R P d) u ht hu (some p.1) (some p.2)
  change denseWidth R P d p.1 p.2 * u p ≤ min (R (some p.1) : ℝ) (P (some p.2) : ℝ) at hhi
  change 0 ≤ denseWidth R P d p.1 p.2 * u p at hlo
  have hwidth := (dense_width_bounds d (min (R (some p.1)) (P (some p.2))) hd
    (le_min (hR _) (hP _))).1
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hs : min (R (some p.1) : ℝ) (P (some p.2) : ℝ) ≤
      denseWidth R P d p.1 p.2 * (2 * (d : ℝ) ^ 8) := by
    apply (div_le_iff₀ (show (0 : ℝ) < 2 * (d : ℝ) ^ 8 by positivity)).mp
    simpa only [Nat.cast_min, denseWidth] using hwidth
  exact ⟨nonneg_of_mul_nonneg_right hlo hw, le_of_mul_le_mul_left (hhi.trans hs) hw⟩

omit [DecidableEq I] [DecidableEq J] in
/-- Real residual completion constructs the strict interior point. -/
theorem dense_interior_exists (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (htotal : ∑ i, R i = ∑ j, P j) :
    ∃ u : I × J → ℝ, Feasible R P d u ∧
      (∀ p, 0 ≤ u p ∧ u p ≤ 2 * (d : ℝ) ^ 8) ∧
      ∀ g : Option I × Option J,
        1 / (2 * (d : ℝ)) ≤
          table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (denseWidth R P d) u g.1 g.2 /
            cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hscale (g : Option I × Option J) :
      0 < cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g := by
    change 0 < min (R g.1 : ℝ) (P g.2 : ℝ)
    apply lt_min
    · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hR _))
    · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hP _))
  obtain ⟨X, hX, hXR, hXP⟩ := strict_real_completion
    (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (d : ℝ) hd₀
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    (by exact_mod_cast hdimR) (by exact_mod_cast hdimP) (by exact_mod_cast htotal)
  let u : I × J → ℝ := fun p => X (some p.1) (some p.2) / denseWidth R P d p.1 p.2
  have heq : table (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (denseWidth R P d) u = X :=
    table_recover _ _ _ (fun i j => ne_of_gt (denseWidth_pos R P d hd hR hP i j)) X hXR hXP
  have hfeas : Feasible R P d u := by
    intro i j
    rw [heq]
    exact (div_nonneg (hscale (i, j)).le (by positivity)).trans (hX i j)
  refine ⟨u, hfeas, feasible_in_cube R P d hd hR hP htotal u hfeas, ?_⟩
  intro g
  rw [heq]
  apply (le_div_iff₀ (hscale g)).mpr
  simpa only [cellScale, div_mul_eq_mul_div, one_mul] using hX g.1 g.2

theorem densePenalty_eq_zero_of_feasible (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (u : I × J → ℝ) (hu : Feasible R P d u) : densePenalty R P d u = 0 := by
  apply le_antisymm
  · unfold densePenalty AffinePenalty.penalty
    apply Finset.sup'_le
    intro g _
    cases g with
    | none => exact le_rfl
    | some g =>
      change -AffinePenalty.affineValue _ _ u - (d : ℝ) / (d : ℝ) ^ 8 ≤ 0
      rw [← normalized_table_affine]
      have hnorm : 0 ≤ table (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
          (denseWidth R P d) u g.1 g.2 /
            cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g :=
        div_nonneg (hu g.1 g.2) (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      linarith [show (0 : ℝ) ≤ (d : ℝ) / (d : ℝ) ^ 8 by positivity]
  · exact AffinePenalty.penalty_nonnegative _ _ _ _

end ContingencyTables.DenseAffine

end OAI
