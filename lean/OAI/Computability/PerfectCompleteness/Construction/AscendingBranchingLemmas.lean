import Mathlib.Data.Set.Finite.Basic
import OAI.Computability.PerfectCompleteness.Algebra.MatrixInverseConstantsLemmas
import OAI.Computability.PerfectCompleteness.Decoding.TwoResponseCollisionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.CoordinateReplacementLemmas

namespace OAI


namespace PerfectCompleteness.AscendingBranching

open scoped BigOperators Classical

noncomputable section

theorem exists_prior_sequence {P : (n : Nat) → (Fin n → Nat) → Nat → Prop}
    (h : ∀ n prior, ∃ x, P n prior x) :
    ∃ values : Nat → Nat, ∀ n, P n (fun i => values i.val) (values n) := by
  let pick := fun n prior => Classical.choose (h n prior)
  let step := fun n (previous : ∀ m, m < n → Nat) =>
    pick n (fun i => previous i.val i.isLt)
  let values : Nat → Nat := fun n => Nat.strongRecOn n step
  refine ⟨values, fun n => ?_⟩
  have hrec : values n = pick n (fun i => values i.val) :=
    Nat.strongRecOn_eq step n
  rw [hrec]
  exact Classical.choose_spec (h n (fun i => values i.val))

def CubeErrors (L c ε : ℝ) (m : Nat) : Prop :=
  2 ≤ m ∧
    Real.sqrt (L ^ 2 / (m : ℝ) ^ 3) / 2 < ε ∧
    Real.sqrt ((1 + L ^ 2 / (m : ℝ) ^ 4) ^ (m ^ 3) - 1) / 2 < ε ∧
    2 * ((1 / (m : ℝ) ^ 2) * L / (1 - 1 / (m : ℝ) ^ 2)) < ε ∧
    (1 - c / (m : ℝ) ^ 2) ^ (m ^ 3) < ε

theorem exists_ascending_cubes
    (L c : (n : Nat) → (Fin n → Nat) → ℝ)
    (hL : ∀ n prior, 0 ≤ L n prior)
    (hc : ∀ n prior, 0 < c n prior)
    (hc' : ∀ n prior, c n prior ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ size : Nat → Nat, ∀ n,
      CubeErrors (L n (fun i => size i.val ^ 3))
        (c n (fun i => size i.val ^ 3)) ε (size n) := by
  apply exists_prior_sequence (P := fun n prior size =>
    CubeErrors (L n (fun i => prior i ^ 3)) (c n (fun i => prior i ^ 3)) ε size)
  intro n prior
  exact CubicErrorSchedule.exists_cube_errors_lt
    (hL n (fun i => prior i ^ 3))
    (hc n (fun i => prior i ^ 3))
    (hc' n (fun i => prior i ^ 3)) hε

theorem exists_common_accuracy {I : Type*} [Fintype I]
    (tolerance : I → ℝ) (positive : ∀ i, 0 < tolerance i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε < tolerance i := by
  have hfinite : ∀ S : Finset I, ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε < tolerance i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a S ha ih =>
      obtain ⟨ε, hε, hsmall⟩ := ih
      refine ⟨min ε (tolerance a) / 2, div_pos (lt_min hε (positive a)) (by norm_num), ?_⟩
      intro i hi
      have hhalf : min ε (tolerance a) / 2 < min ε (tolerance a) := by
        have := lt_min hε (positive a)
        linarith
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hhalf.trans_le (min_le_right _ _)
      · exact (hhalf.trans_le (min_le_left _ _)).trans (hsmall i hi)
  obtain ⟨ε, hε, hsmall⟩ := hfinite Finset.univ
  exact ⟨ε, hε, fun i => hsmall i (Finset.mem_univ i)⟩

end
end PerfectCompleteness.AscendingBranching



namespace PerfectCompleteness.DescendingRows

open scoped BigOperators Classical
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier
open UpperParameterScalars

noncomputable section

structure Exclusion (threshold : ℝ) where
  order : Nat
  crossSize : Nat
  cutoff : Nat
  minimumRows : Nat
  density : ℝ
  order_pos : 1 ≤ order
  cross_pos : 0 < crossSize
  cutoff_pos : 1 ≤ cutoff
  density_pos : 0 < density
  density_lt_one : density < 1
  spectral : MatrixLevelBridge.levelCutoffConstant order density +
    RankLevelFilter.node (order + 1) < threshold
  row_bound : ∀ ℓ, minimumRows ≤ ℓ → 2 * crossSize + order ≤ ℓ
  error_bound : ∀ s, cutoff ≤ s →
    (2 : ℝ) ^ crossSize / (2 : ℝ) ^ (s - 2 * order) +
      (2 : ℝ) ^ (2 * crossSize) / (2 : ℝ) ^ (crossSize * crossSize) < density

theorem exclusion_exists {threshold : ℝ} (h : 0 < threshold) :
    Nonempty (Exclusion threshold) := by
  obtain ⟨r, m, s, rowMin, hr, hm, hs, ρ, hρ, hρ', hcut, hrows, herror⟩ :=
    LowerRankParameters.exists_lower_parameters h
  exact ⟨⟨r, m, s, rowMin, ρ, hr, hm, hs, hρ, hρ', hcut, hrows, herror⟩⟩

variable {κ α η : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hη : 0 < η)

def lowerChoice (r ℓ : Nat) : Exclusion (gamma κ α η r ℓ ^ 2 / 8) :=
  Classical.choice (exclusion_exists (by
    have := gamma_pos hκ hα hη r ℓ
    positivity))

theorem exists_rows (r minimum : Nat) :
    ∃ rows : Nat → Nat, ∀ n,
      minimum ≤ rows n ∧ r ≤ rows n ∧ 1 ≤ rows n ∧
        1 / (2 : ℝ) ^ (rows n - r) < rhoPred κ α / 8 ∧
        ∀ i : Fin n, (lowerChoice hκ hα hη r (rows i.val)).minimumRows ≤ rows n := by
  apply AscendingBranching.exists_prior_sequence (P := fun n prior ℓ =>
    minimum ≤ ℓ ∧ r ≤ ℓ ∧ 1 ≤ ℓ ∧
      1 / (2 : ℝ) ^ (ℓ - r) < rhoPred κ α / 8 ∧
      ∀ i : Fin n, (lowerChoice hκ hα hη r (prior i)).minimumRows ≤ ℓ)
  intro n prior
  let required := fun i : Fin n => (lowerChoice hκ hα hη r (prior i)).minimumRows
  obtain ⟨ℓ, hmin, hr, hpos, hsmall⟩ :=
    exists_rows_rhoPred (minimum + ∑ i, required i) r hκ hα
  refine ⟨ℓ, (Nat.le_add_right _ _).trans hmin, hr, hpos, hsmall, ?_⟩
  intro i
  have hi : required i ≤ ∑ j, required j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (required j)) (Finset.mem_univ i)
  exact hi.trans ((Nat.le_add_left _ _).trans hmin)

def commonCutoff (r depth : Nat) (rows : Nat → Nat) : Nat :=
  1 + ∑ i : Fin depth, (lowerChoice hκ hα hη r (rows i.val)).cutoff

theorem commonCutoff_pos (r depth : Nat) (rows : Nat → Nat) :
    1 ≤ commonCutoff hκ hα hη r depth rows := Nat.le_add_right _ _

theorem cutoff_le_common (r depth : Nat) (rows : Nat → Nat) (i : Fin depth) :
    (lowerChoice hκ hα hη r (rows i.val)).cutoff ≤
      commonCutoff hκ hα hη r depth rows := by
  have hi : (lowerChoice hκ hα hη r (rows i.val)).cutoff ≤
      ∑ j : Fin depth, (lowerChoice hκ hα hη r (rows j.val)).cutoff :=
    Finset.single_le_sum
      (fun j _ => Nat.zero_le (lowerChoice hκ hα hη r (rows j.val)).cutoff)
      (Finset.mem_univ i)
  exact hi.trans (Nat.le_add_left _ _)

theorem error_at_common (r depth : Nat) (rows : Nat → Nat) (i : Fin depth) :
    let lower := lowerChoice hκ hα hη r (rows i.val)
    (2 : ℝ) ^ lower.crossSize /
        (2 : ℝ) ^ (commonCutoff hκ hα hη r depth rows - 2 * lower.order) +
      (2 : ℝ) ^ (2 * lower.crossSize) /
        (2 : ℝ) ^ (lower.crossSize * lower.crossSize) < lower.density :=
  (lowerChoice hκ hα hη r (rows i.val)).error_bound _
    (cutoff_le_common hκ hα hη r depth rows i)

def treeRows (depth : Nat) (rows : Nat → Nat) : Nat → Nat :=
  fun height => rows (depth - height)

theorem tree_pair_requirement (r depth : Nat) (rows : Nat → Nat)
    (ordered : ∀ n, ∀ i : Fin n,
      (lowerChoice hκ hα hη r (rows i.val)).minimumRows ≤ rows n)
    {i j : Nat} (hij : i < j) (hj : j ≤ depth) :
    (lowerChoice hκ hα hη r (treeRows depth rows j)).minimumRows ≤
      treeRows depth rows i := by
  exact ordered (depth - i) ⟨depth - j, by omega⟩

theorem tree_cutoff_le_common (r depth : Nat) (rows : Nat → Nat)
    {j : Nat} (hj : 0 < j) (hjd : j ≤ depth) :
    (lowerChoice hκ hα hη r (treeRows depth rows j)).cutoff ≤
      commonCutoff hκ hα hη r depth rows :=
  cutoff_le_common hκ hα hη r depth rows ⟨depth - j, by omega⟩

end
end PerfectCompleteness.DescendingRows

end OAI
