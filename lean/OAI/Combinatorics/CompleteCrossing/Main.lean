import OAI.Combinatorics.CompleteCrossing.Counting
import OAI.Combinatorics.CompleteCrossing.CycleIdentity
import OAI.Combinatorics.CompleteCrossing.Deletion
import OAI.Combinatorics.CompleteCrossing.LowerBound
import OAI.Combinatorics.CompleteCrossing.Normalization
import OAI.Combinatorics.CompleteCrossing.TwoPage

namespace OAI

/-! Odd and even lower bounds, explicit attainment, and the ordinary complete-graph crossing formula. -/

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

theorem complete_graph_odd_lower_bound (s : ℕ) (hs : 2 ≤ s)
    (N : NormalizedDrawing (completeGraph (2 * s + 1))) :
    (s.choose 2) ^ 2 ≤ crossingCount N.toAdmissibleDrawing := by
  obtain ⟨O⟩ := spoke_orders_exist _ N
  obtain ⟨orders, hlocal⟩ := complete_local_orders N O
  obtain ⟨hleft, hright, hrevleft, hrevright, hskew⟩ := raw_cycle_symmetries N O
  let node : Fin (2 * s + 1) → ℝ := fun i => i.val
  have hn : Function.Injective node := by
    intro i j h
    exact Fin.ext (Nat.cast_injective h)
  have ht (H : Poly4) (hH : H ∈ box4 (2 * s - 1)) :
      polynomialTest node (rawCycleIntersection O) H = 0 := by
    apply polynomial_cycle_tests (by omega) node hn (rawCycleIntersection O)
      (raw_cycle_pairing N O) H
    convert hH using 1
    congr 1
  have hl := support_cardinality_lower_bound hs node hn (rawCycleIntersection O) orders
    hleft hright hrevleft hrevright hskew hlocal ht
  have hu := signed_support_bound N O
  omega

lemma complete_graph_odd_lower_arbitrary (s : ℕ) (hs : 2 ≤ s)
    (D : AdmissibleDrawing (completeGraph (2 * s + 1))) : hill (2 * s + 1) ≤ crossingCount D := by
  obtain ⟨N, hN⟩ := polygonal_no_adjacent_normalization _ D
  rw [hill_odd]
  exact (complete_graph_odd_lower_bound s hs N).trans hN

lemma complete_graph_even_lower_normalized (s : ℕ) (hs : 2 ≤ s)
    (N : NormalizedDrawing (completeGraph (2 * s + 2))) :
    hill (2 * s + 2) ≤ crossingCount N.toAdmissibleDrawing := by
  obtain ⟨A, _, hA⟩ := vertex_deletion_count (2 * s + 1) (by omega) N
  have hl : ∀ v, hill (2 * s + 1) ≤ crossingCount (A v) :=
    fun v => complete_graph_odd_lower_arbitrary s hs (A v)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hl v)
  rw [hA] at hh
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hh
  have he : 2 * (s + 1) = 2 * s + 2 := by omega
  have ho : 2 * s + 2 - 1 = 2 * s + 1 := by omega
  conv_lhs => rw [← he]
  apply even_lower_bound_of_deletion (s + 1) _ (by omega)
  simpa only [he, ho, Nat.add_assoc] using hh

theorem complete_graph_lower_bound (n : ℕ) (hn : 3 ≤ n)
    (D : AdmissibleDrawing (completeGraph n)) : hill n ≤ crossingCount D := by
  by_cases hsmall : n < 5
  · interval_cases n <;> norm_num [hill]
  by_cases hodd : n % 2 = 1
  · obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s + 1 := ⟨n / 2, by omega⟩
    exact complete_graph_odd_lower_arbitrary s (by omega) D
  · obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s + 2 := ⟨n / 2 - 1, by omega⟩
    obtain ⟨N, hN⟩ := polygonal_no_adjacent_normalization _ D
    exact (complete_graph_even_lower_normalized s (by omega) N).trans hN

theorem complete_graph_upper_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ D : AdmissibleDrawing (completeGraph n), crossingCount D = hill n := by
  obtain ⟨D, hD⟩ := complete_graph_upper_drawing n
  exact ⟨D, hD.trans (crossingTuples_card hn)⟩

theorem complete_graph_crossing_number (n : ℕ) (hn : 3 ≤ n) :
    ordinaryCrossingNumber (completeGraph n) = hill n := by
  obtain ⟨D, hD⟩ := complete_graph_upper_bound n hn
  apply Nat.le_antisymm
  · rw [← hD]
    exact Paper170Geometry.ordinaryCrossingNumber_le_count D
  · obtain ⟨A,hA,_⟩ := minimum_drawing_exists (completeGraph n)
    rw [← hA]
    exact complete_graph_lower_bound n hn A

end Paper170

end
end

end OAI
