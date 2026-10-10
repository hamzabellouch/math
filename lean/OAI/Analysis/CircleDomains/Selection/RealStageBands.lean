import OAI.Analysis.CircleDomains.Transfer.RealTransferStage

namespace OAI

/-! Changing only the presentation of equal terminal widths preserves
all geometric and analytic data of a real stage. -/

open Set Filter
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def RealTransferStage.withBands
    {S : Type*} {n : ℕ} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {r : Fin n → (ℝ × ℝ) → ℝ} {a b : Fin n → S → ℝ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε : ℝ}
    (T : RealTransferStage G π σ r a b Flag O K₀ ε)
    (a' b' : Fin n → S → ℝ) (heq : ∀ l s, b l s - a l s = b' l s - a' l s) :
    RealTransferStage G π σ r a' b' Flag O K₀ ε :=
  { T with
    excess := fun l => by simpa only [heq] using T.excess l
    oscillation := fun l => by simpa only [heq] using T.oscillation l }

end CircleDomainRigidity.FiniteTransfer

end

end OAI
