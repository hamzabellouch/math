import OAI.Analysis.MarkovType.FiniteStoppingTime
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Nat.Find

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity
namespace FinitePartitionFiltration

variable {Ω E : Type*} [SeminormedAddCommGroup E]

attribute [local instance] Classical.propDecidable

def firstCrossing (M : ℕ → Ω → E) (N : ℕ) (t : ℝ) (ω : Ω) : ℕ :=
  if h : ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖ then Nat.find h else N

theorem firstCrossing_le (M : ℕ → Ω → E) (N : ℕ) (t : ℝ) (ω : Ω) :
    firstCrossing M N t ω ≤ N := by
  unfold firstCrossing
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact le_rfl

theorem firstCrossing_spec (M : ℕ → Ω → E) (N : ℕ) (t : ℝ) (ω : Ω)
    (h : ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) :
    t < ‖M (firstCrossing M N t ω) ω‖ := by
  rw [firstCrossing, dite_eq_left h]
  exact (Nat.find_spec h).2

theorem firstCrossing_eq_terminal_of_no_crossing
    (M : ℕ → Ω → E) (N : ℕ) (t : ℝ) (ω : Ω)
    (h : ¬ ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) :
    firstCrossing M N t ω = N := by
  simp only [firstCrossing, dite_eq_right h]

theorem exists_crossing_iff_firstCrossing
    (M : ℕ → Ω → E) (N : ℕ) (t : ℝ) (ω : Ω) :
    (∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) ↔
      t < ‖M (firstCrossing M N t ω) ω‖ :=
  ⟨firstCrossing_spec M N t ω,
    fun h => ⟨firstCrossing M N t ω, firstCrossing_le M N t ω, h⟩⟩

theorem firstCrossing_min (M : ℕ → Ω → E) (N : ℕ) (t : ℝ) (ω : Ω)
    {j : ℕ} (hj : j < firstCrossing M N t ω) : ¬ t < ‖M j ω‖ := by
  intro hc
  have hjN : j ≤ N := (Nat.le_of_lt hj).trans (firstCrossing_le M N t ω)
  have hex : ∃ k : ℕ, k ≤ N ∧ t < ‖M k ω‖ := ⟨j, hjN, hc⟩
  rw [firstCrossing, dite_eq_left hex] at hj
  exact Nat.find_min hex hj ⟨hjN, hc⟩

theorem firstCrossing_le_iff_of_lt (M : ℕ → Ω → E) (t : ℝ)
    {n N : ℕ} (hn : n < N) (ω : Ω) :
    firstCrossing M N t ω ≤ n ↔ ∃ j : ℕ, j ≤ n ∧ t < ‖M j ω‖ := by
  constructor
  · intro hle
    by_cases hex : ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖
    · exact ⟨firstCrossing M N t ω, hle, firstCrossing_spec M N t ω hex⟩
    · rw [firstCrossing_eq_terminal_of_no_crossing M N t ω hex] at hle
      exact False.elim ((Nat.not_le_of_gt hn) hle)
  · rintro ⟨j, hj, hc⟩
    have hjN : j ≤ N := hj.trans hn.le
    have hex : ∃ k : ℕ, k ≤ N ∧ t < ‖M k ω‖ := ⟨j, hjN, hc⟩
    rw [firstCrossing, dite_eq_left hex]
    exact (Nat.find_min' hex ⟨hjN, hc⟩).trans hj

theorem isStoppingTime_firstCrossing (F : FinitePartitionFiltration Ω)
    (M : ℕ → Ω → E) (N : ℕ) (t : ℝ)
    (hM : ∀ j : ℕ, j ≤ N → F.AdaptedAt j (M j)) :
    F.IsStoppingTime (firstCrossing M N t) := by
  intro n ω η hωη
  by_cases hN : N ≤ n
  · exact ⟨fun _ => (firstCrossing_le M N t η).trans hN,
      fun _ => (firstCrossing_le M N t ω).trans hN⟩
  · have hn : n < N := Nat.lt_of_not_ge hN
    rw [firstCrossing_le_iff_of_lt M t hn ω,
      firstCrossing_le_iff_of_lt M t hn η]
    have heq (j : ℕ) (hj : j ≤ n) : M j ω = M j η :=
      hM j (hj.trans hn.le) (F.refines hj hωη)
    constructor
    · rintro ⟨j, hj, hc⟩
      exact ⟨j, hj, by simpa only [heq j hj] using hc⟩
    · rintro ⟨j, hj, hc⟩
      exact ⟨j, hj, by simpa only [heq j hj] using hc⟩

theorem firstCrossing_value_eq_of_stopped_rel (F : FinitePartitionFiltration Ω)
    (M : ℕ → Ω → E) (N : ℕ) (t : ℝ)
    (hM : ∀ j : ℕ, j ≤ N → F.AdaptedAt j (M j))
    {ω η : Ω} (hωη : (F.stoppedSetoid (firstCrossing M N t)).r ω η) :
    M (firstCrossing M N t ω) ω = M (firstCrossing M N t η) η := by
  rw [← hωη.1]
  exact hM _ (firstCrossing_le M N t ω) hωη.2

theorem firstCrossing_event_stopped (F : FinitePartitionFiltration Ω)
    (M : ℕ → Ω → E) (N : ℕ) (t : ℝ)
    (hM : ∀ j : ℕ, j ≤ N → F.AdaptedAt j (M j))
    {ω η : Ω} (hωη : (F.stoppedSetoid (firstCrossing M N t)).r ω η) :
    (∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) ↔
      (∃ j : ℕ, j ≤ N ∧ t < ‖M j η‖) := by
  rw [exists_crossing_iff_firstCrossing M N t ω,
    exists_crossing_iff_firstCrossing M N t η,
    firstCrossing_value_eq_of_stopped_rel F M N t hM hωη]

end FinitePartitionFiltration
end MarkovSuperreflexivity

end

end OAI
