import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.AnnularCellPairSelection

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem CellHaarPair.outer_real_pos {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k I : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (P : CellHaarPair μ R hR k z I) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) : 0 < μ.real P.outerCell := by
  have ha := lattice_core_admissible_at_later_level μ R hR k (k + P.outerOffset) (by omega) hcore
  have hp := cleanSupportCell_measure_pos_finite μ C G hC hG hg hlower R hR
    (k + P.outerOffset) ha P.outerCenter
  exact ENNReal.toReal_pos hp.1.ne' hp.2.ne

theorem exists_annular_cell_pair_with_masses {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R₀ k / 8))
    (a : Ambient d) (ha : a ∈ μ.support) (hnear : dist a (z : Ambient d) ≤ latticeRadius R₀ k / 8)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hRtop : R ≤ latticeRadius R₀ k / 8)
    (I : ℕ) (hdepth : annularLatticeDepth R₀ k r hr ≤ I) :
    ∃ P : CellHaarPair μ R₀ hR₀ k z I,
      (∀ x ∈ P.innerCell, 2 * dist x a ≤ r) ∧
      (∀ x ∈ P.outerCell, 2 * dist x a ≤ R) ∧
      r ^ n ≤ annularCellMassConstant n C * μ.real P.innerCell ∧
      R ^ n ≤ annularCellMassConstant n C * μ.real P.outerCell := by
  obtain ⟨P, hPi, hPo, hri, hRo⟩ := exists_annular_cell_pair μ R₀ hR₀ k z a ha hnear r R hr hrR hRtop I hdepth
  refine ⟨P, hPi, hPo, ?_, ?_⟩
  · exact clean_cell_annular_mass_bound μ C G hC hG hg hlower R₀ hR₀
      (k + P.outerOffset + P.innerOffset) P.innerCenter
      (lattice_core_admissible_at_later_level μ R₀ hR₀ k _ (by omega) hcore) r hr.le hri
  · exact clean_cell_annular_mass_bound μ C G hC hG hg hlower R₀ hR₀
      (k + P.outerOffset) P.outerCenter
      (lattice_core_admissible_at_later_level μ R₀ hR₀ k _ (by omega) hcore) R (hr.trans_le hrR).le hRo

end

end RieszRectifiability

end OAI
