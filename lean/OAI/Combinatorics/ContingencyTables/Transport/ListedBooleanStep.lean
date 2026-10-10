import OAI.Combinatorics.ContingencyTables.Transport.WordCompletionStep
import OAI.Combinatorics.ContingencyTables.Transport.ListedKernelAccuracy
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTransitionSemantics
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordWalk

namespace OAI

/-! # The computed binary outer step has the proved mixing kernel -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open ResidualMixture FirstSuccess FairBits CompletionTranslation SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "i₀" => largeOptionEquiv r (d^20) hr none
local notation "j₀" => largeOptionEquiv c (d^20) hc none
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

def listedBlockDraw (x : PaperStates r c) (word : Fin f → Bool) : Table (R x) (P x) :=
  paperReferenceEquiv r c i₀ j₀ x (listedPaddedDraw r c hr hc b h hb x word)

lemma listedBlockDraw_law (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin f → Bool)) (listedBlockDraw r c hr hc b h hb x)=
      listedReferenceLaw r c hr hc b h hb x := by
  exact mapLaw_equiv_output (paperReferenceEquiv r c i₀ j₀ x) _ _

def listedBitStep (x : PaperStates r c) (bits : Fin (s+f) → Bool) : PaperStates r c :=
  wordCompletionStep R P (decodedCodeProposal r c e) (listedBlockDraw r c hr hc b h hb) x bits

attribute [local irreducible] FirstSuccess.mapLaw completionStepLaw

theorem listedBitStep_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin (s+f) → Bool)) (listedBitStep r c e hr hc b h hb x)=
      listedSmallKernel r c hr hc b h hb x := by
  have he := wordCompletionStep_law R P (decodedCodeProposal r c e)
    (listedBlockDraw r c hr hc b h hb) x
  have hp := funext (decodedCodeProposal_law r c e htotal)
  have hd := funext (listedBlockDraw_law r c hr hc b h hb)
  have hP := congrArg (fun prop : PaperStates r c → RationalLaw (Option (PaperStates r c)) =>
    completionStepLaw R P prop
      (fun x => mapLaw (uniformLaw (α := Fin f → Bool)) (listedBlockDraw r c hr hc b h hb x)) x) hp
  have hD := congrArg (fun draw : (x : PaperStates r c) → RationalLaw (Table (R x) (P x)) =>
    completionStepLaw R P (smallProposalLaw r c) draw x) hd
  have hq := funext (fun y : PaperStates r c =>
    mapLaw_decidableEq_irrel (@Option.instDecidableEq (PaperStates r c) inferInstance)
      (inferInstance : DecidableEq (Option (PaperStates r c)))
      (uniformLaw (α := Fin s → Bool)) (decodedCodeProposal r c e y))
  have hQ := congrArg (fun prop : PaperStates r c → RationalLaw (Option (PaperStates r c)) =>
    completionStepLaw R P prop
      (fun x => mapLaw (uniformLaw (α := Fin f → Bool)) (listedBlockDraw r c hr hc b h hb x)) x) hq
  exact he.trans (hQ.trans (hP.trans hD))

theorem profileStep_listedBitStep (htotal : (∑ i,r i)=∑ j,c j)
    (x : PaperStates r c) (bits : Fin (s+f) → Bool) :
    profileStep (encodedStepInput r c e b h x (splitWordEquiv s f bits).1 (splitWordEquiv s f bits).2)=
      stateCode r c e (listedBitStep r c e hr hc b h hb x bits) := by
  rw [profileStep_encoded r c e hr hc b h hb htotal]
  rw [listed_completionDecision r c hr hc]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
