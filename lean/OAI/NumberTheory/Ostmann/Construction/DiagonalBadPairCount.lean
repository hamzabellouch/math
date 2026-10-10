import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairExpansionBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

theorem badCounterpartPair_first_square_le (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (B : Equiv.Perm (RemainingIndex T)→Prop)
    (w c : ℝ) (F : RemainingSample sources T giant→ℝ)
    (hc : 0≤c) (hF : ∀x,0≤F x)
    (hpoint : ∀(x : RemainingSample sources T giant)(e : Equiv.Perm (RemainingIndex T))
      (he : CounterpartCompatible sources T giant x e),B e →
      w*(remainingPrior sources T giant).mass (reconstructCounterpart sources T giant x e he)*F x≤c*F x) :
    (∑z : BadCounterpartPair sources T giant B,
      w*(remainingPrior sources T giant).mass
        (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)*F z.val.1)≤
      (Nat.card {e // B e}:ℝ)*c*(∑x,F x) := by
  rw [badCounterpartPair_sum_eq sources T giant B
    (fun x e he _ => w*(remainingPrior sources T giant).mass
      (reconstructCounterpart sources T giant x e he)*F x)]
  calc
    _ ≤ ∑e,if B e then ∑x,c*F x else 0 := by
      apply Finset.sum_le_sum
      intro e he
      by_cases hb : B e
      · simp only [dite_eq_left hb,ite_eq_left hb]
        apply Finset.sum_le_sum
        intro x hx
        by_cases hcompat : CounterpartCompatible sources T giant x e
        · rw [dite_eq_left hcompat]
          exact hpoint x e hcompat hb
        · rw [dite_eq_right hcompat]
          exact mul_nonneg hc (hF x)
      · simp only [dite_eq_right hb,ite_eq_right hb]
        exact le_rfl
    _ = _ := by
      simp only [←Finset.mul_sum]
      rw [←Finset.sum_filter]
      simp [Nat.card_eq_fintype_card,Fintype.card_subtype,mul_assoc]

end Ostmann.Construction

end

end OAI
