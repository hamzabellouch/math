import OAI.Combinatorics.SnakyCertificate.TableValidity
import OAI.Combinatorics.SnakyCertificate.Invariants
import OAI.Combinatorics.SnakyCertificate.Reconstruction
import OAI.Combinatorics.SnakyCertificate.Heights
import OAI.Combinatorics.SnakyCertificate.Summaries

namespace OAI

namespace SnakyCertificate.Check

theorem rowAt_eq_cached (i : ℕ) (hi : i < 616) : rowAt i = denote (cached i) :=
  rowAt_unique (fun j => denote (cached j)) 616
    (fun _ hlo hhi _ ht => entryAt_backward hlo hhi ht)
    cache_equations i hi

theorem output557 : Output 557 (-1, 0) 118 19 {p | p.1 ≤ -3 ∧ p.2 ≤ -2} := by
  apply output_of_row_eq 557 cache_557 (-1, 0) 118 19 _
  · exact rowAt_eq_cached 557 (by decide)
  · exact cache_summary_557
  · exact cache_omits_557

theorem output595 : Output 595 (-1, 0) 222 27 {p | p.1 = -2 ∧ p.2 ≤ -2} := by
  apply output_of_row_eq 595 cache_595 (-1, 0) 222 27 _
  · exact rowAt_eq_cached 595 (by decide)
  · exact cache_summary_595
  · exact cache_omits_595

theorem output603 : Output 603 (-1, 0) 275 27 {p | p.1 ≤ -3 ∧ p.2 = 0} := by
  apply output_of_row_eq 603 cache_603 (-1, 0) 275 27 _
  · exact rowAt_eq_cached 603 (by decide)
  · exact cache_summary_603
  · exact cache_omits_603

theorem output615 : Output 615 (1, 0) 686 34 {(1, -1)} := by
  apply output_of_row_eq 615 cache_615 (1, 0) 686 34 _
  · exact rowAt_eq_cached 615 (by decide)
  · exact cache_summary_615
  · exact cache_omits_615

theorem all_rows : AllRows := by
  intro i hi
  refine ⟨rowAt_subset i, (rowAt_origin i).1, (rowAt_origin i).2, ?_⟩
  rw [rowAt_eq_cached i hi]
  exact cache_heights i hi

end SnakyCertificate.Check

namespace SnakyCertificate

theorem certificate_correct :
    TableValid ∧ placementCount = 1837 ∧
    Output 557 (-1, 0) 118 19 {p | p.1 ≤ -3 ∧ p.2 ≤ -2} ∧
    Output 595 (-1, 0) 222 27 {p | p.1 = -2 ∧ p.2 ≤ -2} ∧
    Output 603 (-1, 0) 275 27 {p | p.1 ≤ -3 ∧ p.2 = 0} ∧
    Output 615 (1, 0) 686 34 {(1, -1)} ∧
    AllRows := by
  exact ⟨table_valid, placement_count, Check.output557, Check.output595,
    Check.output603, Check.output615, Check.all_rows⟩

end SnakyCertificate

end OAI
