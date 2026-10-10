import OAI.Combinatorics.ContingencyTables.Transport.CompletionStepApproximation
import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordDependent

namespace OAI

/-! # Independent finite words for a proposal and its completion test -/

namespace ContingencyTables.CompletionTranslation
open FirstSuccess FairBits
open scoped Classical
noncomputable section
variable {X I J : Type*} [Fintype X] [DecidableEq X] [Fintype I] [Fintype J]
variable {s f : ℕ} (R : X → Option I → ℕ) (P : X → Option J → ℕ)
variable (proposal : X → (Fin s → Bool) → Option X)
variable (draw : (x : X) → (Fin f → Bool) → Table (R x) (P x))

def wordCompletionStep (x : X) (bits : Fin (s+f) → Bool) : X :=
  let parts := splitWordEquiv s f bits
  completionDecision R P x (proposal x parts.1) (draw x parts.2)

theorem wordCompletionStep_law (x : X) :
    mapLaw (uniformLaw (α := Fin (s+f) → Bool)) (wordCompletionStep R P proposal draw x)=
      completionStepLaw R P
        (fun x => mapLaw (uniformLaw (α := Fin s → Bool)) (proposal x))
        (fun x => mapLaw (uniformLaw (α := Fin f → Bool)) (draw x)) x := by
  let finish := fun y word => completionDecision R P x y (draw x word)
  let F := fun ab : (Fin s → Bool)×(Fin f → Bool) => finish (proposal x ab.1) ab.2
  have he := map_equiv (splitWordEquiv s f) (uniformLaw (α := Fin (s+f) → Bool)) F
  rw [uniform_equiv,←uniform_product] at he
  calc
    _ = mapLaw (productLaw (uniformLaw (α := Fin s → Bool))
        (uniformLaw (α := Fin f → Bool))) F := he.symm
    _ = _ := by
      rw [mapLaw_product_finish]
      unfold completionStepLaw
      congr 1
      funext y
      exact (mapLaw_comp (uniformLaw (α := Fin f → Bool)) (draw x)
        (completionDecision R P x y)).symm

end
end ContingencyTables.CompletionTranslation

end OAI
