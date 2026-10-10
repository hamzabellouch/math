import OAI.Analysis.MarkovType.FiniteMartingaleDuality
import OAI.Analysis.MarkovType.FiniteMartingaleExtrapolation
import OAI.Analysis.MarkovType.DyadicCotypeDuality
import Mathlib.Tactic.Linarith

namespace OAI

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteLowerL2_extrapolate_dyadic {s χ : ℝ}
    (hs : 2 ≤ s) (hχ : 1 ≤ χ) (hLower : FiniteLowerL2 E s χ) :
    ∃ q : ℝ, 2 ≤ q ∧ ∃ A : ℝ, 1 ≤ A ∧ FiniteDyadicCotype E q A := by
  let r : ℝ := s / (s - 1)
  have hrange : 1 < r ∧ r ≤ 2 := lowerL2_dual_exponent_range hs
  have hDual : FiniteUpperL2 (E →L[ℝ] ℝ) r χ := finiteLowerL2_dual_upper hs hχ hLower
  let p : ℝ := (1 + r) / 2
  have hp : 1 < p := by dsimp [p]; linarith only [hrange.1]
  have hpr : p < r := by dsimp [p]; linarith only [hrange.1]
  have hp2 : p ≤ 2 := by dsimp [p]; linarith only [hrange.2]
  obtain ⟨T, hT, hStrong⟩ := finiteUpperL2_extrapolate_synthesis
    hrange.1 hrange.2 hχ hDual hp hpr
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hq : 2 ≤ q := by
    apply (le_div_iff₀ (sub_pos.mpr hp)).mpr
    linarith only [hp2]
  exact ⟨q, hq, T ^ q, Real.one_le_rpow hT hpq.symm.pos.le,
    finiteDyadicCotype_of_dual_synthesis hpq hT hStrong⟩

theorem hasEquivalentUCNorm_of_finiteLowerL2 {s χ : ℝ}
    (hs : 2 ≤ s) (hχ : 1 ≤ χ) (hLower : FiniteLowerL2 E s χ) :
    HasEquivalentUCNorm E := by
  obtain ⟨q, hq, A, hA, hCotype⟩ := finiteLowerL2_extrapolate_dyadic hs hχ hLower
  exact hasEquivalentUCNorm_of_finiteDyadicCotype hq hA hCotype

end MarkovSuperreflexivity

end OAI
