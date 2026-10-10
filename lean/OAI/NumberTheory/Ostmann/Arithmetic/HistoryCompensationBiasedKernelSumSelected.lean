import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum
open Construction CompensationEqualityPatterns HistoryPairSourceLaws HistoryCompensationPatternBudget
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

theorem selected_biasedKernelSum_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ)
    (K : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) → Block p → ℝ)
    (mask : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) → ℝ)
    (hK : ∀p b q,0 ≤ K p b q ∧ K p b q ≤ 2/((b q).val:ℝ))
    (hm : ∀p b,0 ≤ mask p b ∧ mask p b ≤ 1) :
    biasedKernelSum C.sources origin τ K mask  ≤ 
      ∑p:Pattern τ,(2:ℝ)^Fintype.card (Block p)*
        ∏q:Block p,blockCap p (fun i => C.sourceNormalization (origin i)) q :=
  biasedKernelSum_le_caps C.sources origin τ (fun i => C.sourceNormalization (origin i))
    (HistoryCompensationMoment.selected_sourceWeight_mass_mul_le C origin) K mask hK hm

end Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum

end

end OAI
