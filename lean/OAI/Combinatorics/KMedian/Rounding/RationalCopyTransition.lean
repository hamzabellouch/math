import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyRound
import OAI.Combinatorics.KMedian.Rounding.RationalBatchData

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {F : Type} [DecidableEq F] [Fintype F] {Δ : ℕ}

def sources {I : Type} [DecidableEq I] [Fintype I]
    (G : I → Finset I) (H : Finset I) (Z : Finset (HeavyAction (graph G) H)) : Finset I :=
  H ∪ (Z ∩ (heavy (graph G) H).ordinary).image (heavy (graph G) H).source

def erased (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) : Finset (CopyState.Copy (F := F) Δ) :=
  (Z.biUnion (heavy (graph G) H).erase).image Subtype.val

def opened (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) : Finset F :=
  (sources G H Z).image (fun i => i.val.1)

def transition (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) : Finset (CopyState.Copy (F := F) Δ) :=
  CopyState.next Δ A (erased A G H Z) (opened A G H Z)

omit [Fintype F] in
theorem erased_eq (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) :
    erased A G H Z=CopyState.roundErased A G H Z := rfl

omit [Fintype F] in
theorem opened_eq (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) :
    opened A G H Z=CopyState.roundOpened A G H Z := rfl

omit [Fintype F] in

theorem transition_eq (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) :
    transition A G H Z=CopyState.next Δ A (CopyState.roundErased A G H Z)
      (CopyState.roundOpened A G H Z) := rfl

end MetricKMedian.RationalBatchData
end
end

end OAI
