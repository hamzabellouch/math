import OAI.Analysis.MarkovType.StructuralL2Estimates
import OAI.Analysis.MarkovType.FiniteMartingaleExtrapolation
import OAI.Analysis.MarkovType.PowerRenormingFromDyadic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem exists_power_smooth_equivalentNorm [CompleteSpace X] (hUC : HasEquivalentUCNorm X) :
    ∃ N : EquivalentNorm X, ∃ q : ℝ, 1 < q ∧ q ≤ 2 ∧
      ∃ C : ℝ, 0 < C ∧ SymmetricPowerSmooth N.p q C ∧ PowerSmooth N.p q C ∧
        (∀ t : ℝ, 0 ≤ t → smoothnessModulus N.p t ≤ C * t ^ q) ∧
        UniformSmooth N.p := by
  obtain ⟨r, hr, hr₂, χ, hχ, hUpper⟩ := finiteUpperL2_of_hasEquivalentUCNorm hUC
  have hUpper' : FiniteUpperL2 X r (max 1 χ) := by
    intro m μ F M N B hB hM hdiff
    refine (hUpper m μ F M N B hB hM hdiff).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 χ)
        (Real.rpow_nonneg (by positivity) _)) hB
  let q : ℝ := (1 + r) / 2
  have hq : 1 < q := by dsimp [q]; linarith only [hr]
  have hqr : q < r := by dsimp [q]; linarith only [hr]
  have hq₂ : q ≤ 2 := by dsimp [q]; linarith only [hr₂]
  obtain ⟨T, hT, hDyadic⟩ := finiteUpperL2_extrapolate_dyadic
    hr hr₂ (le_max_left 1 χ) hUpper' hq hqr
  obtain ⟨N, _, _, hC, hSym, hPower, hModulus, hUniform⟩ :=
    exists_powerSmooth_equivalentNorm_of_finiteDyadicType hq hT hDyadic
  exact ⟨N, q, hq, hq₂, T ^ q, hC, hSym, hPower, hModulus, hUniform⟩

end MarkovSuperreflexivity

end OAI
