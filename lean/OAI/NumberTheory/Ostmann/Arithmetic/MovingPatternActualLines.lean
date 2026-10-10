import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternFinite
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampledIndexedProbability

namespace OAI

/-! # The actual field average in fixed pattern coordinates -/

namespace Ostmann
open scoped Classical BigOperators

def movingPatternValueData {A B C : Type*} {N : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → A)
    (side : Bool) : MovingSlotData A n :=
  buildMovingSlotData n (t side)
    (treeLeafMap (List.map (fun b => x (e.symm (.inl b)))) n (small side))
    (treeLeafMap (List.map (fun b => x (e.symm (.inl b)))) n (bulk side))
    (movingPatternSamples A n (fun i => x (e.symm (.inr (pattern i)))) side)

/-- The field average over both original giant residues is precisely the
simultaneous line probability appearing in the fixed-coordinate comparison.
This identification needs no assumptions forbidding sample coincidences. -/
theorem movingPatternActualBaseAverage {A B C : Type*} {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → A) (c : C) :
    let p := prime (x (e.symm (.inr c)))
    let _ : Fact p.Prime := ⟨hprime _⟩
    (Fintype.card (ZMod p × (ZMod p)ˣ) : ℂ)⁻¹ *
      (∑ z : ZMod p × (ZMod p)ˣ,
        movingInternalBaseFactor prime (movingPatternValueData e n t small bulk pattern x) p z.1 z.2) =
      (movingSampledInternalProbability prime hprime
        (movingPatternFinData e n t small bulk pattern) x (e.symm (.inr c)) : ℂ) := by
  let p := prime (x (e.symm (.inr c)))
  let _ : Fact p.Prime := ⟨hprime _⟩
  let T := fun side => movingPatternSlotData n (t side) (small side) (bulk side) pattern side
  let eval : B ⊕ C → A :=
    Sum.elim (fun b => x (e.symm (.inl b))) (fun c => x (e.symm (.inr c)))
  have he : (fun side => (T side).map eval) = movingPatternValueData e n t small bulk pattern x := by
    funext side
    exact movingPatternSlotData_evaluate _ _ n (t side) (small side) (bulk side) pattern side
  have hv : prime ∘ eval = (fun i => prime (x i)) ∘ e.symm := by
    funext i
    cases i <;> rfl
  dsimp only
  rw [movingInternalBaseFactor_average]
  have ha := movingInternalBaseProbability_map eval prime T p
  have hf := movingInternalBaseProbability_map e.symm (fun i => prime (x i)) T p
  rw [hv, he] at ha
  exact congrArg (fun y : ℝ => (y : ℂ)) (ha.trans hf.symm)

end Ostmann

end OAI
