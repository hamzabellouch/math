import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Cut faces of a unit grid

The geometric step in the dense sampler's conductance proof: two points
in differently labelled open bins at sup distance less than `r ≤ 1` are
within `r` of a common closed face of oppositely labelled axis neighbours.
A coordinate path avoids any general-position assumption at simultaneous
grid crossings.
-/

namespace ContingencyTables.GridBoundary

variable {I : Type*} [DecidableEq I]

def mixed (a b : I → ℤ) (S : Finset I) : I → ℤ :=
  fun i => if i ∈ S then b i else a i

private theorem cut_edge_aux (P : (I → ℤ) → Prop) (a b : I → ℤ)
    (ha : P a) (K : Finset I) (hb : ¬ P (mixed a b K)) :
    ∃ S i, S ⊆ K ∧ i ∈ K ∧ i ∉ S ∧ P (mixed a b S) ∧
      ¬ P (mixed a b (insert i S)) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    have heq : mixed a b ∅ = a := by ext i; simp [mixed]
    exact False.elim (hb (heq.symm ▸ ha))
  | @insert i K hi ih =>
    by_cases hK : P (mixed a b K)
    · exact ⟨K, i, Finset.subset_insert _ _, Finset.mem_insert_self _ _, hi, hK, hb⟩
    · obtain ⟨S, j, hS, hj, hjS, hPS, hPj⟩ := ih hK
      exact ⟨S, j, hS.trans (Finset.subset_insert _ _), Finset.mem_insert_of_mem hj,
        hjS, hPS, hPj⟩

/-- A change of labels along a coordinate path occurs on an axis edge. -/
theorem cut_edge [Fintype I] (P : (I → ℤ) → Prop) (a b : I → ℤ)
    (ha : P a) (hb : ¬ P b) :
    ∃ S i, i ∉ S ∧ P (mixed a b S) ∧ ¬ P (mixed a b (insert i S)) := by
  have heq : mixed a b Finset.univ = b := by ext i; simp [mixed]
  have hb' : ¬ P (mixed a b Finset.univ) := by rw [heq]; exact hb
  obtain ⟨S, i, _, _, hi, hS, hSi⟩ := cut_edge_aux P a b ha Finset.univ hb'
  exact ⟨S, i, hi, hS, hSi⟩

def OpenBin (a : I → ℤ) (x : I → ℝ) : Prop :=
  ∀ i, (a i : ℝ) < x i ∧ x i < (a i : ℝ) + 1

def ClosedBin (a : I → ℤ) (x : I → ℝ) : Prop :=
  ∀ i, (a i : ℝ) ≤ x i ∧ x i ≤ (a i : ℝ) + 1

private theorem short_bin_indices (a b : ℤ) (x z r : ℝ)
    (hx : (a : ℝ) < x ∧ x < (a : ℝ) + 1)
    (hz : (b : ℝ) < z ∧ z < (b : ℝ) + 1)
    (hd : |z - x| < r) (hr : r ≤ 1) (hab : a ≠ b) :
    b = a + 1 ∨ a = b + 1 := by
  have hd' := abs_lt.mp hd
  have hba : b < a + 2 := by
    exact_mod_cast (show (b : ℝ) < (a : ℝ) + 2 by linarith)
  have hab' : a < b + 2 := by
    exact_mod_cast (show (a : ℝ) < (b : ℝ) + 2 by linarith)
  omega

private theorem clamp_near (a x z r : ℝ)
    (hx : a < x ∧ x < a + 1) (hd : |z - x| < r) :
    ∃ w, a ≤ w ∧ w ≤ a + 1 ∧ |z - w| < r := by
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) hd
  have hd' := abs_lt.mp hd
  by_cases hza : z < a
  · refine ⟨a, le_rfl, by linarith, ?_⟩
    rw [abs_of_neg (by linarith : z - a < 0)]
    linarith
  · by_cases haz : a + 1 < z
    · refine ⟨a + 1, by linarith, le_rfl, ?_⟩
      rw [abs_of_pos (by linarith : 0 < z - (a + 1))]
      linarith
    · exact ⟨z, le_of_not_gt hza, le_of_not_gt haz, by simpa using hr⟩

private theorem adjacent_boundary (a b : ℤ) (x z r : ℝ)
    (hx : (a : ℝ) < x ∧ x < (a : ℝ) + 1)
    (hz : (b : ℝ) < z ∧ z < (b : ℝ) + 1)
    (hd : |z - x| < r) (hab : b = a + 1 ∨ a = b + 1) :
    (a : ℝ) ≤ max (a : ℝ) b ∧ max (a : ℝ) b ≤ (a : ℝ) + 1 ∧
    (b : ℝ) ≤ max (a : ℝ) b ∧ max (a : ℝ) b ≤ (b : ℝ) + 1 ∧
    |z - max (a : ℝ) b| < r := by
  have hd' := abs_lt.mp hd
  rcases hab with hab | hab
  · have heq : (b : ℝ) = (a : ℝ) + 1 := by exact_mod_cast hab
    rw [max_eq_right (by linarith : (a : ℝ) ≤ b)]
    refine ⟨by linarith, by linarith, le_rfl, by linarith, ?_⟩
    rw [abs_of_pos (by linarith : 0 < z - (b : ℝ))]
    linarith
  · have heq : (a : ℝ) = (b : ℝ) + 1 := by exact_mod_cast hab
    rw [max_eq_left (by linarith : (b : ℝ) ≤ a)]
    refine ⟨le_rfl, by linarith, by linarith, by linarith, ?_⟩
    rw [abs_of_neg (by linarith : z - (a : ℝ) < 0)]
    linarith

/-- The terminal point of a short displacement lies near an actual cut
face. The intermediate bins use only the two endpoint indices in each
coordinate, so they stay inside any rectangular grid containing them. -/
theorem near_cut_face [Fintype I] (P : (I → ℤ) → Prop)
    (a b : I → ℤ) (x z : I → ℝ) (r : ℝ)
    (ha : OpenBin a x) (hb : OpenBin b z)
    (hd : ∀ i, |z i - x i| < r) (hr : r ≤ 1)
    (hPa : P a) (hPb : ¬ P b) :
    ∃ S i w, i ∉ S ∧ P (mixed a b S) ∧ ¬ P (mixed a b (insert i S)) ∧
      (b i = a i + 1 ∨ a i = b i + 1) ∧
      ClosedBin (mixed a b S) w ∧ ClosedBin (mixed a b (insert i S)) w ∧
      (∀ j, |z j - w j| < r) := by
  classical
  obtain ⟨S, i, hi, hS, hSi⟩ := cut_edge P a b hPa hPb
  have hneq : a i ≠ b i := by
    intro heq
    apply hSi
    have hmix : mixed a b (insert i S) = mixed a b S := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [mixed, hi, heq]
      · simp [mixed, hj]
    rwa [hmix]
  have hadj := short_bin_indices (a i) (b i) (x i) (z i) r (ha i) (hb i) (hd i) hr hneq
  have hface := adjacent_boundary (a i) (b i) (x i) (z i) r (ha i) (hb i) (hd i) hadj
  have hnear (j : I) : ∃ w, ((mixed a b S j : ℤ) : ℝ) ≤ w ∧
      w ≤ (mixed a b S j : ℝ) + 1 ∧ |z j - w| < r := by
    by_cases hj : j ∈ S
    · refine ⟨z j, ?_, ?_, ?_⟩
      · simpa [mixed, hj] using (hb j).1.le
      · simpa [mixed, hj] using (hb j).2.le
      · simpa using lt_of_le_of_lt (abs_nonneg _) (hd j)
    · simpa [mixed, hj] using clamp_near (a j) (x j) (z j) r (ha j) (hd j)
  choose v hv using hnear
  let w : I → ℝ := Function.update v i (max (a i : ℝ) (b i))
  refine ⟨S, i, w, hi, hS, hSi, hadj, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst j
      have hp := And.intro hface.1 hface.2.1
      simpa [w, mixed, hi] using hp
    · have hp := And.intro (hv j).1 (hv j).2.1
      simpa [w, hj] using hp
  · intro j
    by_cases hj : j = i
    · subst j
      have hp := And.intro hface.2.2.1 hface.2.2.2.1
      simpa [w, mixed] using hp
    · have hp := And.intro (hv j).1 (hv j).2.1
      simpa [w, mixed, hj] using hp
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [w] using hface.2.2.2.2
    · simpa [w, hj] using (hv j).2.2

end ContingencyTables.GridBoundary

end OAI
