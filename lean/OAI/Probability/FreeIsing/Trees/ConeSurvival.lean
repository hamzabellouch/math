import OAI.Probability.FreeIsing.Trees.BranchingSurvivalLaw
import OAI.Probability.FreeIsing.Trees.ConePercolation

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeConeCoding

theorem rootedPathOpen_cons {b : ℕ} (p : ℝ) (U : List (Fin b) → ℝ)
    (i : Fin b) (w : List (Fin b)) :
    rootedPathOpen p U (i :: w) ↔
      U [i] ≤ p ∧ rootedPathOpen p (BranchingSurvival.branches U i) w := by
  constructor
  · intro h
    constructor
    · simpa only [List.take_succ_cons, List.take_zero] using h 1 (by omega) (by simp)
    · intro k hk hkw
      have hc := h (k + 1) (by omega) (by simp; omega)
      simpa only [List.take_succ_cons, BranchingSurvival.branches] using hc
  · rintro ⟨hi, hw⟩ k hk hkw
    cases k with
    | zero => omega
    | succ k =>
        cases k with
        | zero => simpa only [List.take_succ_cons, List.take_zero] using hi
        | succ k =>
            have hc := hw (k + 1) (by omega) (by simp at hkw; omega)
            simpa only [List.take_succ_cons, BranchingSurvival.branches] using hc

theorem survives_iff_rootedPathOpen {b : ℕ} (p : ℝ) (n : ℕ)
    (U : List (Fin b) → ℝ) :
    U ∈ BranchingSurvival.survives p n ↔
      ∃ w : List (Fin b), w.length = n ∧ rootedPathOpen p U w := by
  induction n generalizing U with
  | zero =>
      constructor
      · intro _
        exact ⟨[], rfl, fun k hk hkn => by simp only [List.length_nil] at hkn; omega⟩
      · intro _
        trivial
  | succ n ih =>
      constructor
      · rintro ⟨i, hi, hU⟩
        obtain ⟨w, hwlen, hw⟩ := (ih _).mp hU
        exact ⟨i :: w, by simp [hwlen], (rootedPathOpen_cons p U i w).mpr ⟨hi, hw⟩⟩
      · rintro ⟨w, hwlen, hw⟩
        cases w with
        | nil => simp at hwlen
        | cons i w =>
            obtain ⟨hi, hw'⟩ := (rootedPathOpen_cons p U i w).mp hw
            exact ⟨i, hi, (ih _).mpr ⟨w, by simpa using hwlen, hw'⟩⟩

theorem survival_probability_eq_branching {b : ℕ} (p : ℝ)
    (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) (n : ℕ) :
    labelMeasure (b + 1) {U | ∃ v : TreeVertex (b + 1),
      v.1.length = r.1.length + n ∧ SubcriticalClusters.DownwardOpen p U r v} =
      BranchingSurvival.wordMeasure b (BranchingSurvival.survives p n) := by
  rw [survival_probability p r hr n]
  congr 1
  ext U
  exact (survives_iff_rootedPathOpen p n U).symm

theorem survival_probability_real {b : ℕ} (p : ℝ)
    (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) (n : ℕ) :
    (labelMeasure (b + 1)).real {U | ∃ v : TreeVertex (b + 1),
      v.1.length = r.1.length + n ∧ SubcriticalClusters.DownwardOpen p U r v} =
      BranchingSurvival.probability b p n := by
  exact congrArg ENNReal.toReal (survival_probability_eq_branching p r hr n)

end Problem367.TreeConeCoding

end

end OAI
