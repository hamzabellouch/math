import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperImplementedLaw
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBooleanProposal
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordDependent

namespace OAI

/-! # The actual small transition driven by one fixed Boolean word -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
variable {q : ℕ}
variable (e : ({i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀} ×
  {j : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20) // j≠j₀}) ≃ Fin q)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
variable (a : GridBoundary.Grid (I := Fin q) (4*(dimensionAllowance (I := I) (J := J))^8))
variable (fallback : (z : PaperStates r c) → PaperFibre r c z)

local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀

local notation "s" => smallProposalBits (I := I) (J := J)
local notation "f" => 25*(d+b+h+1)^62

def smallBitStep (x : PaperStates r c) (bits : Fin (s+f) → Bool) : PaperStates r c :=
  let draws := splitWordEquiv s f bits
  completionDecision R P x (smallBitProposal r c x draws.1)
    (finiteBlockDraw r c i₀ j₀ e b h hb a fallback x draws.2)

/-- The proposal and the completion consume disjoint fixed segments. -/
theorem smallBitStep_law (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin (s+f) → Bool))
      (smallBitStep r c i₀ j₀ e b h hb a fallback x)=
      implementedSmallKernel r c i₀ j₀ e b h hb a fallback x := by
  let E := splitWordEquiv s f
  let finish := fun (y : Option (PaperStates r c)) (word : Fin f → Bool) =>
    completionDecision R P x y (finiteBlockDraw r c i₀ j₀ e b h hb a fallback x word)
  let F := fun ab : (Fin s → Bool) × (Fin f → Bool) =>
    finish (smallBitProposal r c x ab.1) ab.2
  have he := map_equiv E (uniformLaw (α := Fin (s+f) → Bool)) F
  rw [uniform_equiv,←uniform_product] at he
  calc
    _ = mapLaw (productLaw (uniformLaw (α := Fin s → Bool))
        (uniformLaw (α := Fin f → Bool))) F := he.symm
    _ = bindLaw (smallProposalLaw r c x)
        (fun y => mapLaw (uniformLaw (α := Fin f → Bool)) (finish y)) := by
      rw [mapLaw_product_finish,smallBitProposal_law]
    _ = _ := by
      have hfinish (y : Option (PaperStates r c)) :
          mapLaw (uniformLaw (α := Fin f → Bool)) (finish y)=
            mapLaw (finiteBlockLaw r c i₀ j₀ e b h hb a fallback x)
              (completionDecision R P x y) := by
        dsimp only [finish]
        rw [←mapLaw_comp,finiteBlockDraw_law]
      exact congrArg (fun K => bindLaw (smallProposalLaw r c x) K) (funext hfinish)

end
end ContingencyTables.SmallGraphProfiles

end OAI
