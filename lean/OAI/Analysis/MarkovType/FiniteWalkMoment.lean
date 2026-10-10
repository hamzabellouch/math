import OAI.Analysis.MarkovType.FiniteWalkWitness
import OAI.Analysis.MarkovType.MarkedPaths
import OAI.Analysis.MarkovType.TailMoment

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

theorem FiniteWalkWitness.moment_lower {N : OrderedNorm} {n : ℕ}
    (W : FiniteWalkWitness N n) {p : ℝ} (hp : 0 ≤ p) :
    (3 / 20 : ℝ) * ((n : ℝ) / 24) ^ p ≤
      @markedExpect W.State W.Edge W.stateFintype W.edgeFintype W.chain n
        (fun ω => N (edgeSum W.label ω) ^ p) := by
  let : Fintype W.State := W.stateFintype
  let : Fintype W.Edge := W.edgeFintype
  have hc : (0 : ℝ) ≤ (n : ℝ) / 24 :=
    div_nonneg (Nat.cast_nonneg n) (by norm_num)
  exact (markedLaw W.chain n).tail_mass_power_le_expect
    (fun ω => N (edgeSum W.label ω)) (fun ω => N.nonneg _) hc hp W.escape

end MarkovSuperreflexivity

end

end OAI
