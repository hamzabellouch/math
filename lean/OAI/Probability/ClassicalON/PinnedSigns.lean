import OAI.Probability.ClassicalON.BondPin

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V]

def positiveCompatibleSigns (left right : E → V) (B : Set V) (η : E → Bool) : Set (V → Bool) :=
  {s | s∈compatibleSigns left right η ∧ ∀ v∈B,s v=true}

def positiveCompatibleSignsEquiv (left right : E → V) (B : Set V) (η : E → Bool) :
    positiveCompatibleSigns left right B η ≃ pinnedBondSubspace left right B η :=
  (Equiv.piCongrRight (fun _ : V => signFieldEquiv)).subtypeEquiv (by
    intro s
    change ((∀ e,η e=true → s (left e)=s (right e)) ∧ ∀ v∈B,s v=true) ↔
      ((∀ e,η e=true → signFieldEquiv (s (left e))=signFieldEquiv (s (right e))) ∧
        (fun v : B => signFieldEquiv (s v))=0)
    simp only [Equiv.apply_eq_iff_eq,funext_iff,Pi.zero_apply,Subtype.forall,
      ← signFieldEquiv_true,Equiv.apply_eq_iff_eq])

theorem positiveCompatibleSigns_card (left right : E → V) (B : Set V) (η : E → Bool) :
    (Fintype.card (positiveCompatibleSigns left right B η):ℝ)=
      clusterWeight left right η*bondPinFactor left right B η := by
  rw [Fintype.card_congr (positiveCompatibleSignsEquiv left right B η)]
  exact pinnedBond_card left right B η

theorem positiveCompatibleSigns_sum (left right : E → V) (B : Set V) (η : E → Bool) :
    (∑ s : V → Bool,if s∈positiveCompatibleSigns left right B η then (1:ℝ) else 0)=
      clusterWeight left right η*bondPinFactor left right B η := by
  rw [Finset.sum_boole,← Fintype.card_subtype]
  exact positiveCompatibleSigns_card left right B η

end ClassicalON

end

end OAI
