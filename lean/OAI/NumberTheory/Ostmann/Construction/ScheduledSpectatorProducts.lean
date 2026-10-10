import Mathlib.Algebra.Field.ZMod
import OAI.NumberTheory.Ostmann.Construction.ScheduledGiantFactorization
import OAI.NumberTheory.Ostmann.Construction.ScheduleAtomSystem

namespace OAI

/-! # The spectator products are reductions of the actual integer child products -/

namespace Ostmann
open scoped Classical BigOperators

theorem scheduled_child_spectator_product {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (giant : ScheduledNonbulkH role n)
    {q : ℕ} [Fact q.Prime] (b : Bool)
    (x : CopyScheduleAtoms role (n + 1) → ℕ)
    (units : CopyScheduleAtoms role (n + 1) → (ZMod q)ˣ)
    (hunits : ∀ i, (x i : ZMod q) = units i) :
    ((∏ h : CopyScheduleH role n, x ⟨.inl (b, h.val), h.property⟩ : ℕ) : ZMod q) =
      ((units ⟨.inl (b, giant.val.val), giant.val.property⟩ *
        scheduledRegularCoefficient role n giant
          (fun h => units ⟨.inl (b, h.val), h.property⟩) *
        treeLeafProduct n ((treeLeafTupleEquiv (ZMod q)ˣ n).symm
          (fun t => ∏ i : Fin m,
            units (wordLeafSlot role (word i).val (word i).property (n + 1)
              (if b then .inl t else .inr t)))) : (ZMod q)ˣ) : ZMod q) := by
  have h := congrArg (fun v : (ZMod q)ˣ => (v : ZMod q))
    (scheduled_child_giant_regular_bulk role n m word giant b units)
  have hc : ((∏ h : CopyScheduleH role n,
      x ⟨.inl (b, h.val), h.property⟩ : ℕ) : ZMod q) =
      ((∏ h : CopyScheduleH role n,
        units ⟨.inl (b, h.val), h.property⟩ : (ZMod q)ˣ) : ZMod q) := by
    simp only [Nat.cast_prod, Units.coe_prod]
    exact Finset.prod_congr rfl (fun i _ => hunits _)
  exact hc.trans h

end Ostmann

end OAI
