import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellChainComposition
import OAI.Analysis.RieszRectifiability.Flatness.FlatDescendantMass

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem SupportCellDescendant.relative_real_mass_bound {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (i S : SupportCellDescendant μ R hR k z) (I : ℕ)
    (hlo : i.depth ≤ S.depth) (hhi : S.depth ≤ i.depth + I) (hsub : S.cell ⊆ i.cell) :
    μ.real i.cell ≤ flatDescendantMassConstant n C G I * μ.real S.cell := by
  obtain ⟨j, hj, _, hcell, _⟩ := i.exists_relative_descendant S hlo hsub
  have hicore : AdmissibleRadius μ (latticeRadius R (k + i.depth) / 8) := by
    simpa only [one_div_mul_eq_div, SupportCellDescendant.radius] using! i.core_admissible hcore
  have hb := SupportCellDescendant.parent_mass_bound μ C G hC hG hg hlower R hR
    (k + i.depth) ⟨i.center, i.mem_net⟩ hicore j I (by omega)
  change μ.real i.cell ≤ flatDescendantMassConstant n C G I * μ.real j.cell at hb
  rwa [hcell] at hb

theorem SupportCellDescendant.relative_mass_bound {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (i S : SupportCellDescendant μ R hR k z) (I : ℕ)
    (hlo : i.depth ≤ S.depth) (hhi : S.depth ≤ i.depth + I) (hsub : S.cell ⊆ i.cell) :
    μ i.cell ≤ ENNReal.ofReal (flatDescendantMassConstant n C G I) * μ S.cell := by
  have hb := SupportCellDescendant.relative_real_mass_bound μ C G hC hG hg hlower
    R hR k z hcore i S I hlo hhi hsub
  have hi : μ i.cell ≠ ∞ := ((i.measure_upper G hg).trans_lt ENNReal.ofReal_lt_top).ne
  have hS : μ S.cell ≠ ∞ := ((S.measure_upper G hg).trans_lt ENNReal.ofReal_lt_top).ne
  have hM := flatDescendantMassConstant_pos n C G I hC hG
  have he := ENNReal.ofReal_le_ofReal hb
  change ENNReal.ofReal ((μ i.cell).toReal) ≤
    ENNReal.ofReal (flatDescendantMassConstant n C G I * (μ S.cell).toReal) at he
  rwa [ENNReal.ofReal_mul hM.le, ENNReal.ofReal_toReal hi, ENNReal.ofReal_toReal hS] at he

end

end RieszRectifiability

end OAI
