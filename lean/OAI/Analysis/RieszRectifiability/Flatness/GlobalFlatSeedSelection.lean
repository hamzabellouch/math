import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellChainComposition
import OAI.Analysis.RieszRectifiability.Flatness.FlatCellSeeds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_global_flat_seed {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (i : SupportCellDescendant μ R hR k z) (I : ℕ) (A α : ℝ)
    (hflat : HasFlatDescendant n μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I A α) :
    ∃ S : SupportCellDescendant μ R hR k z,
      i.depth < S.depth ∧ S.depth ≤ i.depth + I ∧ S.cell ⊆ i.cell ∧
        A * S.radius ≤ i.radius / 8 ∧
        HasFlatCell n μ R hR (k + S.depth) ⟨S.center, S.mem_net⟩ A α := by
  obtain ⟨j, hjpos, hjI, hsize, hfit⟩ := hflat
  refine ⟨i.compose j, ?_, ?_, ?_, ?_, ?_⟩
  · rw [i.compose_depth]
    omega
  · rw [i.compose_depth]
    omega
  · rw [i.compose_cell]
    exact j.cell_subset_top
  · rw [i.compose_radius]
    exact hsize
  · simpa only [HasFlatCell, SupportCellDescendant.compose, Nat.add_assoc] using! hfit

theorem flat_seed_enlargement_admissible {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (i S : SupportCellDescendant μ R hR k z) (A H : ℝ) (hH : 0 < H) (hHA : H ≤ A)
    (hsize : A * S.radius ≤ i.radius / 8) : AdmissibleRadius μ (H * S.radius) := by
  have hi : AdmissibleRadius μ (i.radius / 8) := by
    simpa only [one_div_mul_eq_div] using! i.core_admissible hcore
  have hle := (mul_le_mul_of_nonneg_right hHA S.radius_pos.le).trans hsize
  exact ⟨mul_pos hH S.radius_pos, (ENNReal.ofReal_le_ofReal hle).trans hi.2⟩

end

end RieszRectifiability

end OAI
