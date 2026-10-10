import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.HistoryFrequencyLabels
open HistoryReconstruction

def labels : (k : ℕ) → List Bool → ℤ → HistoryReconstruction.Tree k → List (List Bool × ℤ)
  | 0, p, s, _ => [(p,s)]
  | k+1, p, s, t => (p,s) ::
      (labels k (false::p) t.1.1 t.2.1 ++ labels k (true::p) t.1.2 t.2.2)

theorem root_mem_labels (k : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree k) :
    (p,s) ∈ labels k p s t := by
  cases k <;> exact List.mem_cons_self

theorem mem_labels_range (S : List Bool → Finset ℤ) {k : ℕ} {p : List Bool}
    {s : ℤ} {t : HistoryReconstruction.Tree k} (h : RangeSupported S k p s t)
    {q : List Bool} {z : ℤ} (hz : (q,z) ∈ labels k p s t) : z ∈ S q := by
  induction k generalizing p s with
  | zero =>
    have he : (q,z) = (p,s) := List.mem_singleton.mp hz
    cases he
    exact h
  | succ k ih =>
    rcases List.mem_cons.mp hz with he | hz
    · cases he
      exact h.1
    · rcases List.mem_append.mp hz with hl | hr
      · exact ih h.2.1 hl
      · exact ih h.2.2 hr

theorem rangeSupported_iff_labels (S : List Bool → Finset ℤ) (k : ℕ)
    (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree k) :
    RangeSupported S k p s t ↔ ∀ q z, (q,z) ∈ labels k p s t → z ∈ S q := by
  refine ⟨fun h _ _ hz => mem_labels_range S h hz, ?_⟩
  intro h
  induction k generalizing p s with
  | zero => exact h p s (root_mem_labels _ _ _ _)
  | succ k ih =>
    refine ⟨h p s (root_mem_labels _ _ _ _), ?_, ?_⟩
    · apply ih
      intro q z hz
      exact h q z (List.mem_cons_of_mem _ (List.mem_append_left _ hz))
    · apply ih
      intro q z hz
      exact h q z (List.mem_cons_of_mem _ (List.mem_append_right _ hz))

def modulus (k : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree k) : ℕ :=
  ((labels k p s t).map (fun a => a.2.natAbs)).prod

@[simp] theorem modulus_zero (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree 0) :
    modulus 0 p s t = s.natAbs := by simp [modulus, labels]

@[simp] theorem modulus_succ (k : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree (k+1)) :
    modulus (k+1) p s t = s.natAbs *
      (modulus k (false::p) t.1.1 t.2.1 * modulus k (true::p) t.1.2 t.2.2) := by
  simp only [modulus, labels, List.map_cons, List.map_append, List.prod_cons, List.prod_append]

theorem frequency_dvd_modulus {k : ℕ} {p : List Bool} {s : ℤ} {t : HistoryReconstruction.Tree k}
    {q : List Bool} {z : ℤ} (hz : (q,z) ∈ labels k p s t) :
    z.natAbs ∣ modulus k p s t :=
  List.dvd_prod (List.mem_map.mpr ⟨(q,z), hz, rfl⟩)

theorem root_dvd_modulus (k : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree k) :
    s.natAbs ∣ modulus k p s t := frequency_dvd_modulus (root_mem_labels k p s t)

theorem left_dvd_modulus (k : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree (k+1)) :
    t.1.1.natAbs ∣ modulus (k+1) p s t :=
  frequency_dvd_modulus (List.mem_cons_of_mem _
    (List.mem_append_left _ (root_mem_labels k (false::p) t.1.1 t.2.1)))

theorem right_dvd_modulus (k : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree (k+1)) :
    t.1.2.natAbs ∣ modulus (k+1) p s t :=
  frequency_dvd_modulus (List.mem_cons_of_mem _
    (List.mem_append_right _ (root_mem_labels k (true::p) t.1.2 t.2.2)))

theorem modulus_pos (S : List Bool → Finset ℤ)
    (hS : ∀ p z, z ∈ S p → z ≠ 0) {k : ℕ} {p : List Bool}
    {s : ℤ} {t : HistoryReconstruction.Tree k} (h : RangeSupported S k p s t) :
    0 < modulus k p s t := by
  apply List.prod_pos
  intro a ha
  obtain ⟨⟨q,z⟩, hz, rfl⟩ := List.mem_map.mp ha
  exact Int.natAbs_pos.mpr (hS q z (mem_labels_range S h hz))

theorem modulusNeZero (S : List Bool → Finset ℤ)
    (hS : ∀ p z, z ∈ S p → z ≠ 0) {k : ℕ} {p : List Bool}
    (h : SupportedHistory S k p) : NeZero (modulus k p h.val.1 h.val.2) :=
  ⟨(modulus_pos S hS h.property).ne'⟩

end Ostmann.Characters.HistoryFrequencyLabels

end

end OAI
