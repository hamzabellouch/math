import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.LabelOrder

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Enlargement Subdivision RealGeometry Switching

variable {n : ℕ}
def pairIndex (he : Even n) (i : Fin n) : Fin n :=
  if hi : i.val%2=0 then ⟨i.val+1,by obtain ⟨k,hk⟩:=he; have h:=i.isLt; omega⟩
  else ⟨i.val-1,by have h:=i.isLt; omega⟩
lemma pairIndex_involutive (he : Even n) : Function.Involutive (pairIndex he) := by
  intro i
  apply Fin.ext
  by_cases hi : i.val % 2 = 0
  · have hp : (i.val+1) % 2 ≠ 0 := by omega
    simp only [pairIndex, dite_eq_left hi, dite_eq_right hp]
    omega
  · have hp : (i.val-1) % 2 = 0 := by omega
    simp only [pairIndex, dite_eq_right hi, dite_eq_left hp]
    omega
lemma pairIndex_ne (he : Even n) (i : Fin n) : pairIndex he i≠i := by
  intro h
  have hh:=congrArg Fin.val h
  unfold pairIndex at hh
  split_ifs at hh <;> simp only at hh <;> omega

def orderedMate (he : Even n) : Mate (Fin n) := ⟨pairIndex he,pairIndex_involutive he⟩
lemma orderedMate_holes (he : Even n) : HasHoles (orderedMate he) ∅ := by
  intro i
  simp only [Finset.notMem_empty,iff_false]
  exact pairIndex_ne he i

def selectMate (m : Mate (Fin n)) (e : LogicalEdge (Fin n)) : Bool :=
  decide (m.val (source e)=target e)
lemma selectMate_eq (m : Mate (Fin n)) : selectMate m=Representation.select m := by
  funext e
  exact rfl

def startSet (K : ℕ) (he : Even n) : Finset (SourceRealEdge (Fin n) K) :=
  univ.filter fun q=>alternating (selectMate (orderedMate he) q.1) q.2.val=true
variable [Nontrivial (Fin n)]
lemma startSet_matching (K : ℕ) (he : Even n) :
    MatchingOn (fun (q : SourceRealEdge (Fin n) K) x=>x∈edge source target (4*(2*K+2)) q.1 q.2)
      (startSet K he) univ := by
  have h:= (family_iff_matching source target (4*(2*K+2)) source_ne_target ∅ (fun _=>∅)
    (fun e i=>alternating (Representation.select (orderedMate he) e) i.val)).mp
      (intact_family (2*K+2) (orderedMate he) (orderedMate_holes he))
  rw [survivors_empty] at h
  convert h using 1
  unfold startSet selectedSet
  rw [selectMate_eq]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

def startMatching (w : Fin n → Fin n → ℚ) (K : ℕ) (he : Even n) : BagPM (bags w K) :=
  ⟨(startSet K he).map ⟨coloredReal w K,coloredReal_injective w K⟩,by
    exact (matching_map_iff
      (fun (q : SourceRealEdge (Fin n) K) x=>x∈edge source target (4*(2*K+2)) q.1 q.2)
      BagEdge.Incident ⟨coloredReal w K,coloredReal_injective w K⟩
      (fun _ _=>Iff.rfl) (startSet K he) univ).mpr (startSet_matching K he)⟩
end MatchingFPRAS.RationalSource

end OAI
