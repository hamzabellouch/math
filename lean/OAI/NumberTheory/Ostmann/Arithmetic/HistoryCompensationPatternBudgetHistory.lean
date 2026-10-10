import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPatternBudgetSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationPatternBudget
open Construction Construction.CanonicalOccurrenceTransport CompensationEqualityPatterns
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

def pairTest (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (l : ℕ)
    (f g : FrequencyChoices V l)
    (F : HistoryChoices sources seed V l→HistoryChoices sources seed V l→ℂ)
    (z : PairedInternalSourceDraws sources seed l) : ℂ :=
  F (assembleHistoryChoices sources seed V l f (fun i => z (.inl i)))
    (assembleHistoryChoices sources seed V l g (fun i => z (.inr i)))

theorem selected_pair_history_cmean_norm_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (seed : List SourceSlot) (V : ℕ→ℕ) (l : ℕ) (f g : FrequencyChoices V l)
    (F : HistoryChoices C.sources seed V l→HistoryChoices C.sources seed V l→ℂ)
    (hF : ∀(p:Pattern (pairedHistoryType seed l))
      (b:BlockDraw p (CommonSample C.sources (pairedInternalOrigin seed l))),
      ‖extendSourceTest C.sources (pairedInternalOrigin seed l)
          (pairTest C.sources seed V l f g F) (expand p b)‖ ≤
        (∏i:Internal seed l⊕Internal seed l,((expand p b i).val:ℝ))*
          ∏q:Block p,(2/((b.val q).val:ℝ))) :
    ‖(pairedInternalSourcePrior C.sources seed l).cmean (pairTest C.sources seed V l f g F)‖ ≤
      ∑p:Pattern (pairedHistoryType seed l),(2:ℝ)^Fintype.card (Block p)*
        ∏q:Block p,blockCap p (fun i => C.sourceNormalization (pairedInternalOrigin seed l i)) q :=
  selected_source_cmean_norm_le C (pairedInternalOrigin seed l) (pairedHistoryType seed l)
    (pairTest C.sources seed V l f g F) hF

theorem selected_pair_history_cmean_norm_le_pow (C : InitialSourceChoice d Bs BD Bz k L E)
    (seed : List SourceSlot) (V : ℕ→ℕ) (l : ℕ) (f g : FrequencyChoices V l)
    {R : ℝ} (hR : 1 ≤ R)
    (hcap : ∀i:Internal seed l⊕Internal seed l,
      C.sourceNormalization (pairedInternalOrigin seed l i) ≤ R)
    (F : HistoryChoices C.sources seed V l→HistoryChoices C.sources seed V l→ℂ)
    (hF : ∀(p:Pattern (pairedHistoryType seed l))
      (b:BlockDraw p (CommonSample C.sources (pairedInternalOrigin seed l))),
      ‖extendSourceTest C.sources (pairedInternalOrigin seed l)
          (pairTest C.sources seed V l f g F) (expand p b)‖ ≤
        (∏i:Internal seed l⊕Internal seed l,((expand p b i).val:ℝ))*
          ∏q:Block p,(2/((b.val q).val:ℝ))) :
    let N := Fintype.card (Internal seed l⊕Internal seed l)
    ‖(pairedInternalSourcePrior C.sources seed l).cmean (pairTest C.sources seed V l f g F)‖ ≤
      (2:ℝ)^(N*N)*(2:ℝ)^N*R^N :=
  selected_source_cmean_norm_le_pow C (pairedInternalOrigin seed l) (pairedHistoryType seed l)
    hR hcap (pairTest C.sources seed V l f g F) hF

end Ostmann.Arithmetic.HistoryCompensationPatternBudget

end

end OAI
