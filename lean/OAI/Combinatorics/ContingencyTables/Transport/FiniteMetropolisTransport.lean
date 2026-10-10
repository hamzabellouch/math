import OAI.Combinatorics.ContingencyTables.Transport.FiniteAdaptiveObservable

namespace OAI

/-! # Exact observable transport of optional proposals and acceptance -/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical
noncomputable section

variable {X P Q U V : Type*} [Fintype P] [Fintype Q] [Fintype U] [Fintype V]

def proposedMove (start : X) (pick : Option X) (accept : X → U → Bool) (bits : U) : X :=
  match pick with
  | none => start
  | some next => if accept next bits then next else start

/-- The proposed state and fresh acceptance experiment can both be
replaced by experiments with the same observable law. -/
theorem proposedMove_sameLaw (start : X) (pick : P → Option X) (pick' : Q → Option X)
    (accept : X → U → Bool) (accept' : X → V → Bool)
    (hp : SameLaw pick pick') (ha : ∀ next,SameLaw (accept next) (accept' next)) :
    SameLaw (fun z : P × U => proposedMove start (pick z.1) accept z.2)
      (fun z : Q × V => proposedMove start (pick' z.1) accept' z.2) := by
  apply hp.bind (fun o u => proposedMove start o accept u)
    (fun o v => proposedMove start o accept' v)
  intro o
  cases o with
  | none => exact (ha start).map (fun _ : Bool => start)
  | some next => exact (ha next).map (fun flag : Bool => if flag then next else start)

/-- An independent holding flag is preserved by the replacement. -/
theorem holding_sameLaw {A B : Type*} [Fintype A] [Fintype B]
    (start : X) (f : A → X) (g : B → X) (h : SameLaw f g) :
    SameLaw (fun z : (Fin 1 → Bool) × A => if z.1 0 then start else f z.2)
      (fun z : (Fin 1 → Bool) × B => if z.1 0 then start else g z.2) := by
  have hid : SameLaw (fun b : Fin 1 → Bool => b 0) (fun b : Fin 1 → Bool => b 0) := fun _ => rfl
  exact (hid.prod h).map (fun z : Bool × X => if z.1 then start else z.2)

end
end ContingencyTables.FiniteObservableTransport

end OAI
