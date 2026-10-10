import Mathlib
import OAI.Computability.VertexCover.Reduction.HonestSelectionCompatible
import OAI.Computability.VertexCover.Reduction.NormAttainedSupport

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
namespace Query

noncomputable abbrev localLabelLinearOrder {Φ : LabelCover} {d : ℕ}
    (i : Φ.Query d) : LinearOrder i.LocalLabel :=
  LinearOrder.lift'
    (fun a : i.LocalLabel => toLex (toLex a.1.1, toLex a.1.2))
    (fun _ _ h => Subtype.ext h)

noncomputable def labels {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) : List i.LocalLabel := by
  letI : LinearOrder i.LocalLabel := localLabelLinearOrder i
  exact (Finset.univ : Finset i.LocalLabel).sort (localLabelLinearOrder i).le

@[simp] theorem mem_labels {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) (a : i.LocalLabel) :
    a ∈ i.labels := by
  simp [labels]

@[simp] theorem labels_length {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :
    i.labels.length = Fintype.card i.LocalLabel := by
  simp [labels]

noncomputable def slot {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) (a : i.LocalLabel) :
    Fin ((max Φ.qU Φ.qV)^(d - 1)) :=
  ⟨i.labels.idxOf a, lt_of_lt_of_le
    (by simpa only [labels_length] using List.idxOf_lt_length_iff.mpr (i.mem_labels a))
    i.localLabel_card_le⟩

theorem slot_injective {Φ : LabelCover} {d : ℕ} (i : Φ.Query d) :
    Function.Injective i.slot := by
  intro a b h
  exact (List.idxOf_inj (i.mem_labels a)).mp (congrArg Fin.val h)

end Query

abbrev WeightDimension (Φ : LabelCover) (d : ℕ) := (max Φ.qU Φ.qV)^(d - 1)

noncomputable def increment (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s : Fin (Φ.WeightDimension d) → ℝ) : Φ.Coordinate d → ℝ :=
  fun p => (Pi.single (M := fun j : Φ.Query d => j.LocalLabel → ℝ)
    i (fun a => s (i.slot a)) p.1) p.2

@[simp] theorem increment_same (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s : Fin (Φ.WeightDimension d) → ℝ) (a : i.LocalLabel) :
    Φ.increment i s ⟨i, a⟩ = s (i.slot a) := by
  simp [increment]

theorem increment_other (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s : Fin (Φ.WeightDimension d) → ℝ) (p : Φ.Coordinate d) (h : p.1 ≠ i) :
    Φ.increment i s p = 0 := by
  simp [increment, Pi.single_eq_of_ne h]

theorem increment_add (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s t : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.increment i (s + t) = Φ.increment i s + Φ.increment i t := by
  funext p
  rcases p with ⟨j, a⟩
  by_cases h : j = i
  · subst j
    simp
  · simp [Φ.increment_other i _ ⟨j, a⟩ h]

theorem increment_mul (Φ : LabelCover) {d : ℕ} (i : Φ.Query d) (a : ℝ)
    (s : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.increment i (fun k => a * s k) = fun p => a * Φ.increment i s p := by
  funext p
  rcases p with ⟨j, b⟩
  by_cases h : j = i
  · subst j
    simp
  · simp [Φ.increment_other i _ ⟨j, b⟩ h]

theorem increment_norm_le (Φ : LabelCover) {d : ℕ} (i : Φ.Query d)
    (s : Fin (Φ.WeightDimension d) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ k, |s k| ≤ B) : Φ.compatibilityNorm (Φ.increment i s) ≤ B := by
  classical
  apply (Φ.norm_le_iff _ _).mpr
  intro I hI
  by_cases hex : ∃ p ∈ I, p.1 = i
  · obtain ⟨p, hp, hip⟩ := hex
    have heq : (∑ q ∈ I, Φ.increment i s q) = Φ.increment i s p := by
      apply Finset.sum_eq_single p
      · intro q hq hqp
        apply Φ.increment_other
        intro hqi
        exact hqp (hI.1 q hq p hp (hqi.trans hip.symm))
      · intro hn
        exact (hn hp).elim
    rw [heq]
    rcases p with ⟨j, a⟩
    change j = i at hip
    subst j
    simpa using hs (i.slot a)
  · have hz : ∀ p ∈ I, Φ.increment i s p = 0 := by
      intro p hp
      exact Φ.increment_other i s p (fun h => hex ⟨p, hp, h⟩)
    simpa [Finset.sum_eq_zero hz] using hB

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
