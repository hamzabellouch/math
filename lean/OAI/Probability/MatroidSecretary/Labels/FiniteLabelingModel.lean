import OAI.Probability.MatroidProphet.Main
import Mathlib.Combinatorics.Matroid.Map

namespace OAI

namespace MatroidProphet.Labeling

open Finset

/-- The same offline maximum as `MatroidProphet.optimum`, on an arbitrary
finite ground type.  The empty independent set is among the competitors. -/
noncomputable def finiteOptimum {E : Type*} [Fintype E]
    (M : Matroid E) (w : E → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun I : Finset E => if M.Indep (I : Set E) then ∑ e ∈ I, w e else 0)

/-- Relabel all elements, without restricting the matroid or dropping loops. -/
noncomputable def finMatroid {E : Type*} [Fintype E] (M : Matroid E) :
    Matroid (Fin (Fintype.card E)) := M.mapEquiv (Fintype.equivFin E)

/-- Transport each weight along the inverse of the chosen enumeration. -/
noncomputable def finWeights {E : Type*} [Fintype E] (w : E → ℝ) :
    Weights (Fintype.card E) := fun i => w ((Fintype.equivFin E).symm i)

/-- A labeled arrival order uses arrival times `Fin |E|` and actual labels `E`.
It is a bijection, so every label arrives exactly once. -/
abbrev LabeledOrder (E : Type*) [Fintype E] := Fin (Fintype.card E) ≃ E

/-- Arrival orders form a finite discrete measurable space, just as in the
`Fin n` information model. -/
instance labeledOrderMeasurableSpace (E : Type*) [Fintype E] :
    MeasurableSpace (LabeledOrder E) := ⊤

instance labeledOrderMeasurableSingletonClass (E : Type*) [Fintype E] :
    MeasurableSingletonClass (LabeledOrder E) := ⟨fun _ => trivial⟩

/-- Only the label coordinates of a history are relabeled. -/
def encodeHistory {E : Type*} {n : ℕ} (e : E ≃ Fin n) (k : Fin n)
    (h : Fin (k.val + 1) → E × ℝ) : History n k :=
  fun j => (e (h j).1, (h j).2)

/-- A rule on arbitrary finite labels has exactly the same information
restriction as `OnlineRule`: seed, initial samples, and the observed prefix. -/
structure LabeledOnlineRule (E : Type*) [Fintype E] [MeasurableSpace E]
    (bits : ℕ) where
  decide : (k : Fin (Fintype.card E)) → Seed bits → (E → ℝ) →
    (Fin (k.val + 1) → E × ℝ) → Bool
  measurable_decide : ∀ k, Measurable
    (fun x : Seed bits × ((E → ℝ) × (Fin (k.val + 1) → E × ℝ)) =>
      decide k x.1 x.2.1 x.2.2)

/-- The actual observed history for an arbitrary labeled arrival order. -/
def labeledHistory {E : Type*} [Fintype E] (v : E → ℝ)
    (π : LabeledOrder E) (k : Fin (Fintype.card E)) :
    Fin (k.val + 1) → E × ℝ :=
  fun j => let e := π (prefixIndex k j); (e, v e)

/-- Accepted labels after `t` arrivals in the arbitrary-label model. -/
noncomputable def labeledAcceptedThrough {E : Type*} [Fintype E] [MeasurableSpace E]
    {bits : ℕ} (A : LabeledOnlineRule E bits) (r : Seed bits)
    (s v : E → ℝ) (π : LabeledOrder E) (t : ℕ) : Finset E := by
  classical
  exact Finset.univ.filter fun e => (π.symm e).val < t ∧
    A.decide (π.symm e) r s (labeledHistory v π (π.symm e)) = true

end MatroidProphet.Labeling

end OAI
