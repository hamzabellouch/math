import OAI.Combinatorics.Ryser.Selection.Chunk
import Mathlib.Data.Finset.Prod

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem card_entries_with_direction_le (D : ℕ) (data : Data F n)
    (hdata : Bounded D data) (E : Finset (Position n K)) (d : Direction F) :
    (E.filter (fun e => d ∈ data.dirs e.1)).card ≤ K * D := by
  have hsub : E.filter (fun e => d ∈ data.dirs e.1) ⊆
      (Finset.univ.filter (fun i => d ∈ data.dirs i)) ×ˢ
        (Finset.univ : Finset (Fin K)) := by
    intro e he
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ((Finset.univ.filter (fun i => d ∈ data.dirs i)) ×ˢ
        (Finset.univ : Finset (Fin K))).card := Finset.card_le_card hsub
    _ = (Finset.univ.filter (fun i => d ∈ data.dirs i)).card * K := by simp
    _ ≤ D * K := Nat.mul_le_mul_right K (hdata.2.2.2 d)
    _ = K * D := Nat.mul_comm _ _

theorem sum_sourceEnergy_eq (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K)) :
    (∑ e ∈ E, sourceEnergy data I U e.1) =
      ∑ i ∈ I, ∑ d : Direction F,
        ((E.filter (fun e => d ∈ data.dirs e.1)).card : ℝ) * sliceEnergy (U i) d := by
  classical
  unfold sourceEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ e ∈ E, ∑ d : Direction F,
        if d ∈ data.dirs e.1 then sliceEnergy (U i) d else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      simp
    _ = ∑ d : Direction F, ∑ e ∈ E,
        if d ∈ data.dirs e.1 then sliceEnergy (U i) d else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp

theorem sum_sourceEnergy_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F))
    (E : Finset (Position n K)) :
    (∑ e ∈ E, sourceEnergy data I U e.1) ≤
      (K : ℝ) * D * I.card * (Fintype.card F : ℝ) ^ 2 := by
  rw [sum_sourceEnergy_eq]
  calc
    _ ≤ ∑ i ∈ I, ∑ d : Direction F, ((K : ℝ) * D) * sliceEnergy (U i) d := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_entries_with_direction_le D data hdata E d)
        (sliceEnergy_nonneg (U i) d)
    _ = ∑ i ∈ I, ((K : ℝ) * D) * ∑ d : Direction F, sliceEnergy (U i) d := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ _i ∈ I, ((K : ℝ) * D) * (Fintype.card F : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (sum_sliceEnergy_le_sq_card (U i)) (by positivity)
    _ = _ := by simp; ring

end RyserCoveringCounterexample.Selection

end

end OAI
