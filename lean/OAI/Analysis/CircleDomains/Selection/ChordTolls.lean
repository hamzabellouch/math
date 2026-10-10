import OAI.Analysis.CircleDomains.Selection.CrossingChords

namespace OAI

/-!
# Accounting for chord tolls

The temporary chord enumeration carries the costs of its actual disks.
Summing over that enumeration charges exactly the disks meeting the
segment, and hence at most all disks meeting the whole parallel line.
-/

open Set Function

namespace CircleDomainRigidity

noncomputable def chordToll {I : Type*} [Fintype I]
    (c : I → ℂ) (r A : I → ℝ) (y a b : ℝ) (z : ℝ × ℝ) : ℝ := by
  classical
  exact ∑ i ∈ crossingDisks c r y a b,
    if horizontalChord (c i) (r i) y = z then A i else 0

theorem le_chordToll {I : Type*} [Fintype I]
    (c : I → ℂ) (r A : I → ℝ) (y a b : ℝ) (hA : ∀ i, 0 ≤ A i)
    {i : I} (hi : i ∈ crossingDisks c r y a b) :
    A i ≤ chordToll c r A y a b (horizontalChord (c i) (r i) y) := by
  classical
  have h := Finset.single_le_sum
    (s := crossingDisks c r y a b)
    (f := fun j => if horizontalChord (c j) (r j) y = horizontalChord (c i) (r i) y
      then A j else 0) (fun j _ => by split <;> simp_all) hi
  simpa [chordToll] using h

theorem sum_chordToll {I : Type*} [Fintype I]
    (c : I → ℂ) (r A : I → ℝ) (y a b : ℝ) :
    (∑ z ∈ crossingChords c r y a b, chordToll c r A y a b z) =
      ∑ i ∈ crossingDisks c r y a b, A i := by
  classical
  unfold chordToll
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hmem : horizontalChord (c i) (r i) y ∈ crossingChords c r y a b :=
    Finset.mem_image.mpr ⟨i, hi, rfl⟩
  simp [eq_comm, hmem]

theorem sum_chordToll_le_line_hits {I : Type*} [Fintype I]
    (c : I → ℂ) (r A : I → ℝ) (y a b : ℝ) (hA : ∀ i, 0 ≤ A i) :
    (∑ z ∈ crossingChords c r y a b, chordToll c r A y a b z) ≤
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  classical
  rw [sum_chordToll]
  calc
    _ = ∑ i, if i ∈ crossingDisks c r y a b then A i else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ crossingDisks c r y a b
      · simp only [hi, ↓reduceIte, indicator_of_mem (crossingDisk_line_hit hi), le_refl]
      · simp only [hi, ↓reduceIte]
        exact indicator_nonneg (fun _ _ => hA i) y

end CircleDomainRigidity

end OAI
