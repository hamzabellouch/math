import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileVariation

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def admissibleQuantiles (k : ℕ) : Set (Fin (k+1) → ℝ) :=
  {Q | Monotone Q ∧ ∀ j, Q j ∈ Set.Icc 0 1}

theorem admissibleQuantiles_compact (k : ℕ) : IsCompact (admissibleQuantiles k) := by
  have he : admissibleQuantiles k = Set.Icc (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) ∩ {Q | Monotone Q} := by
    ext Q
    simp only [admissibleQuantiles,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_Icc,Pi.le_def]
    aesop
  rw [he]
  exact isCompact_Icc.inter_right isClosed_monotone

theorem admissibleQuantiles_nonempty (k : ℕ) : (admissibleQuantiles k).Nonempty :=
  ⟨fun _ => 0,monotone_const,fun _ => ⟨le_rfl,zero_le_one⟩⟩

theorem exists_finite_quantile_minimizer (k : ℕ) (β : ℝ) :
    ∃ Q ∈ admissibleQuantiles k,
      ∀ R ∈ admissibleQuantiles k, extendedQuantileParisi k β Q ≤ extendedQuantileParisi k β R := by
  exact (admissibleQuantiles_compact k).exists_isMinOn (admissibleQuantiles_nonempty k)
    (extendedQuantileParisi_continuous k β).continuousOn
end SK.Analytic

end
end

end

end OAI
