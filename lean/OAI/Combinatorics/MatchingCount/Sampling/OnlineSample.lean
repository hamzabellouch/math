import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreePreparedMarked
import OAI.Combinatorics.MatchingCount.Machines.OnlineTraverse
import OAI.Combinatorics.MatchingCount.Tapes.OnlineWord

namespace OAI

namespace MatchingFPRAS.OnlineSample
open PhysicalStream TreeTyped

abbrev word (k : ℕ) : Experiment (List Bool) := OnlineWord.prepend k []

variable {A : Type} [Codec A]
def repeatInputRealizer : TreeTyped.Realizer (fun x : ℕ×A=>List.replicate x.1 x.2) :=
  (TreeTyped.composition (TreeTyped.pair TreeTyped.second (TreeTyped.composition TreeTyped.first TreeTyped.range))
    (TreeTyped.mapWith TreeTyped.first)).congr (by intro x; simp)

def words (x : ℕ×ℕ) : Experiment (List (List Bool)) :=
  OnlineTree.traverseM word (List.replicate x.2 x.1)
noncomputable def wordsRealizer : OnlineTree.Realizer words :=
  (OnlineTree.composition (OnlineTree.deterministic (TreeTyped.composition
    (TreeTyped.pair TreeTyped.second TreeTyped.first) repeatInputRealizer))
    (OnlineTree.traverse OnlineWord.naturalRealizer)).congr (by intro x h; rfl)

def localWords (x : ℕ×ℕ) : Experiment NumericLadder.Bits :=
  (word x.1).bind (fun w=>(words x).map (Prod.mk w))
noncomputable def localRealizer : OnlineTree.Realizer localWords :=
  OnlineTree.pair (OnlineTree.composition (OnlineTree.deterministic TreeTyped.first) OnlineWord.naturalRealizer)
    wordsRealizer

def scan (x : ℕ×ℕ) : Experiment (List Bool×NumericLadder.Bits) :=
  (word x.1).bind (fun w=>(localWords x).map (Prod.mk w))
noncomputable def scanRealizer : OnlineTree.Realizer scan :=
  OnlineTree.pair (OnlineTree.composition (OnlineTree.deterministic TreeTyped.first) OnlineWord.naturalRealizer)
    localRealizer

def scans (x : (ℕ×ℕ)×ℕ) : Experiment (List (List Bool×NumericLadder.Bits)) :=
  OnlineTree.traverseM scan (List.replicate x.2 x.1)
noncomputable def scansRealizer : OnlineTree.Realizer scans :=
  (OnlineTree.composition (OnlineTree.deterministic (TreeTyped.composition
    (TreeTyped.pair TreeTyped.second TreeTyped.first) repeatInputRealizer))
    (OnlineTree.traverse scanRealizer)).congr (by intro x h; rfl)

def markWord (x : ℕ×ℕ) : Experiment (ℕ×List Bool) := (word x.2).map (Prod.mk x.1)
noncomputable def markWordRealizer : OnlineTree.Realizer markWord :=
  OnlineTree.mapSecond OnlineWord.naturalRealizer

def markRequests (x : ℕ×List ℕ) : List (ℕ×ℕ) := x.2.map (fun i=>(i,x.1))
def markRequestsRealizer : TreeTyped.Realizer markRequests :=
  (TreeTyped.mapWith (TreeTyped.pair TreeTyped.second TreeTyped.first)).congr (fun _=>rfl)
def marks (x : ℕ×List ℕ) : Experiment (List (ℕ×List Bool)) :=
  OnlineTree.traverseM markWord (markRequests x)
noncomputable def marksRealizer : OnlineTree.Realizer marks :=
  OnlineTree.composition (OnlineTree.deterministic markRequestsRealizer) (OnlineTree.traverse markWordRealizer)

abbrev Request := ((ℕ×ℕ)×ℕ)×(ℕ×List ℕ)
def sample (x : Request) : Experiment NumericMarking.SampleBits :=
  (scans x.1).bind (fun s=>(marks x.2).map (Prod.mk s))
noncomputable def sampleRealizer : OnlineTree.Realizer sample :=
  OnlineTree.pair (OnlineTree.composition (OnlineTree.deterministic TreeTyped.first) scansRealizer)
    (OnlineTree.composition (OnlineTree.deterministic TreeTyped.second) marksRealizer)
def many (x : ℕ×Request) : Experiment (List NumericMarking.SampleBits) :=
  OnlineTree.traverseM sample (List.replicate x.1 x.2)
noncomputable def manyRealizer : OnlineTree.Realizer many :=
  OnlineTree.composition (OnlineTree.deterministic repeatInputRealizer) (OnlineTree.traverse sampleRealizer)
end MatchingFPRAS.OnlineSample

end OAI
