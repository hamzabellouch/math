import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16000step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16000 raw16000Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw16000 raw16000Labels = mixedMoment B raw16000step0 raw16000step0Labels := by
      have ha : raw16000step0 = (fun i j => raw16000 (permutation678 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16000step0 raw16000; decide +kernel
      have hl : raw16000step0Labels = raw16000Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16000 raw16000Labels permutation678 permutation5
    mixedMoment B raw16000step0 raw16000step0Labels = mixedMoment B raw16000step1 raw16000step1Labels := by
      have ha : raw16000step1 = raw16000step0 := by apply Matrix.ext; unfold raw16000step1 raw16000step0; decide +kernel
      have hl : raw16000step0Labels = labelEmbedding1 ∘ raw16000step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16000step0 raw16000step0Labels raw16000step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw16001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16001step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16001 raw16001Labels = mixedMoment B node3431 node3431Labels := by
  calc
    mixedMoment B raw16001 raw16001Labels = mixedMoment B raw16001step0 raw16001step0Labels := by
      have ha : raw16001step0 = (fun i j => raw16001 (permutation677 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16001step0 raw16001; decide +kernel
      have hl : raw16001step0Labels = raw16001Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16001 raw16001Labels permutation677 permutation5
    mixedMoment B raw16001step0 raw16001step0Labels = mixedMoment B raw16001step1 raw16001step1Labels := by
      have ha : raw16001step1 = raw16001step0 := by apply Matrix.ext; unfold raw16001step1 raw16001step0; decide +kernel
      have hl : raw16001step0Labels = labelEmbedding1 ∘ raw16001step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16001step0 raw16001step0Labels raw16001step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3431 node3431Labels := by rfl

def raw16002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw16002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16002 raw16002Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw16002 raw16002Labels = mixedMoment B raw16002step0 raw16002step0Labels := by
      have hz : ∀ j, raw16002 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16002step0 = (fun i j => raw16002 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16002step0 raw16002; decide +kernel
      have hl : raw16002step0Labels = raw16002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16002 raw16002Labels permutation520 hz
    mixedMoment B raw16002step0 raw16002step0Labels = mixedMoment B raw16002step1 raw16002step1Labels := by
      have ha : raw16002step1 = (fun i j => raw16002step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16002step1 raw16002step0; decide +kernel
      have hl : raw16002step1Labels = raw16002step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16002step0 raw16002step0Labels permutation141 permutation5
    mixedMoment B raw16002step1 raw16002step1Labels = mixedMoment B raw16002step2 raw16002step2Labels := by
      have ha : raw16002step2 = raw16002step1 := by apply Matrix.ext; unfold raw16002step2 raw16002step1; decide +kernel
      have hl : raw16002step1Labels = labelEmbedding1 ∘ raw16002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16002step1 raw16002step1Labels raw16002step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw16003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16003 raw16003Labels = mixedMoment B node3871 node3871Labels := by
  calc
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw16004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16004 raw16004Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw16004 raw16004Labels = mixedMoment B raw16004step0 raw16004step0Labels := by
      have ha : raw16004step0 = (fun i j => raw16004 (permutation321 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16004step0 raw16004; decide +kernel
      have hl : raw16004step0Labels = raw16004Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16004 raw16004Labels permutation321 permutation4
    mixedMoment B raw16004step0 raw16004step0Labels = mixedMoment B raw16004step1 raw16004step1Labels := by
      have ha : raw16004step1 = -raw16004step0 := by apply Matrix.ext; change ∀ i j, raw16004step1 i j = -(raw16004step0 i j); unfold raw16004step1 raw16004step0; decide +kernel
      have hl : raw16004step1Labels = raw16004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw16005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16005 raw16005Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw16005 raw16005Labels = mixedMoment B raw16005step0 raw16005step0Labels := by
      have ha : raw16005step0 = (fun i j => raw16005 (permutation312 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16005step0 raw16005; decide +kernel
      have hl : raw16005step0Labels = raw16005Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16005 raw16005Labels permutation312 permutation4
    mixedMoment B raw16005step0 raw16005step0Labels = mixedMoment B raw16005step1 raw16005step1Labels := by
      have ha : raw16005step1 = -raw16005step0 := by apply Matrix.ext; change ∀ i j, raw16005step1 i j = -(raw16005step0 i j); unfold raw16005step1 raw16005step0; decide +kernel
      have hl : raw16005step1Labels = raw16005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw16006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16006 raw16006Labels = mixedMoment B node3927 node3927Labels := by
  calc
    mixedMoment B raw16006 raw16006Labels = mixedMoment B raw16006step0 raw16006step0Labels := by
      have ha : raw16006step0 = (fun i j => raw16006 (permutation321 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16006step0 raw16006; decide +kernel
      have hl : raw16006step0Labels = raw16006Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16006 raw16006Labels permutation321 permutation4
    mixedMoment B raw16006step0 raw16006step0Labels = mixedMoment B raw16006step1 raw16006step1Labels := by
      have ha : raw16006step1 = -raw16006step0 := by apply Matrix.ext; change ∀ i j, raw16006step1 i j = -(raw16006step0 i j); unfold raw16006step1 raw16006step0; decide +kernel
      have hl : raw16006step1Labels = raw16006step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3927 node3927Labels := by rfl

def raw16007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16007 raw16007Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw16007 raw16007Labels = mixedMoment B raw16007step0 raw16007step0Labels := by
      have hz : ∀ j, raw16007 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16007step0 = (fun i j => raw16007 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16007step0 raw16007; decide +kernel
      have hl : raw16007step0Labels = raw16007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16007 raw16007Labels permutation520 hz
    mixedMoment B raw16007step0 raw16007step0Labels = mixedMoment B raw16007step1 raw16007step1Labels := by
      have ha : raw16007step1 = (fun i j => raw16007step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16007step1 raw16007step0; decide +kernel
      have hl : raw16007step1Labels = raw16007step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16007step0 raw16007step0Labels permutation73 permutation4
    mixedMoment B raw16007step1 raw16007step1Labels = mixedMoment B raw16007step2 raw16007step2Labels := by
      have ha : raw16007step2 = -raw16007step1 := by apply Matrix.ext; change ∀ i j, raw16007step2 i j = -(raw16007step1 i j); unfold raw16007step2 raw16007step1; decide +kernel
      have hl : raw16007step2Labels = raw16007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw16008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16008 raw16008Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw16008 raw16008Labels = mixedMoment B raw16008step0 raw16008step0Labels := by
      have ha : raw16008step0 = (fun i j => raw16008 (permutation321 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16008step0 raw16008; decide +kernel
      have hl : raw16008step0Labels = raw16008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16008 raw16008Labels permutation321 permutation4
    mixedMoment B raw16008step0 raw16008step0Labels = mixedMoment B raw16008step1 raw16008step1Labels := by
      have ha : raw16008step1 = -raw16008step0 := by apply Matrix.ext; change ∀ i j, raw16008step1 i j = -(raw16008step0 i j); unfold raw16008step1 raw16008step0; decide +kernel
      have hl : raw16008step1Labels = raw16008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw16009 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]
def raw16009Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16009step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw16009step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16009step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw16009step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical16009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16009 raw16009Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw16009 raw16009Labels = mixedMoment B raw16009step0 raw16009step0Labels := by
      have hz : ∀ j, raw16009 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16009step0 = (fun i j => raw16009 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16009step0 raw16009; decide +kernel
      have hl : raw16009step0Labels = raw16009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16009 raw16009Labels permutation520 hz
    mixedMoment B raw16009step0 raw16009step0Labels = mixedMoment B raw16009step1 raw16009step1Labels := by
      have ha : raw16009step1 = (fun i j => raw16009step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16009step1 raw16009step0; decide +kernel
      have hl : raw16009step1Labels = raw16009step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16009step0 raw16009step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw16010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw16010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16010 raw16010Labels = mixedMoment B node2944 node2944Labels := by
  calc
    mixedMoment B raw16010 raw16010Labels = mixedMoment B raw16010step0 raw16010step0Labels := by
      have ha : raw16010step0 = (fun i j => raw16010 (permutation310 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16010step0 raw16010; decide +kernel
      have hl : raw16010step0Labels = raw16010Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16010 raw16010Labels permutation310 permutation4
    mixedMoment B raw16010step0 raw16010step0Labels = mixedMoment B raw16010step1 raw16010step1Labels := by
      have ha : raw16010step1 = -raw16010step0 := by apply Matrix.ext; change ∀ i j, raw16010step1 i j = -(raw16010step0 i j); unfold raw16010step1 raw16010step0; decide +kernel
      have hl : raw16010step1Labels = raw16010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2944 node2944Labels := by rfl

def raw16011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16011 raw16011Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw16011 raw16011Labels = mixedMoment B raw16011step0 raw16011step0Labels := by
      have ha : raw16011step0 = (fun i j => raw16011 (permutation310 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16011step0 raw16011; decide +kernel
      have hl : raw16011step0Labels = raw16011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16011 raw16011Labels permutation310 permutation4
    mixedMoment B raw16011step0 raw16011step0Labels = mixedMoment B raw16011step1 raw16011step1Labels := by
      have ha : raw16011step1 = -raw16011step0 := by apply Matrix.ext; change ∀ i j, raw16011step1 i j = -(raw16011step0 i j); unfold raw16011step1 raw16011step0; decide +kernel
      have hl : raw16011step1Labels = raw16011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3091 node3091Labels := by rfl

def raw16012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16012 raw16012Labels = mixedMoment B node2945 node2945Labels := by
  calc
    mixedMoment B raw16012 raw16012Labels = mixedMoment B raw16012step0 raw16012step0Labels := by
      have ha : raw16012step0 = (fun i j => raw16012 (permutation309 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16012step0 raw16012; decide +kernel
      have hl : raw16012step0Labels = raw16012Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16012 raw16012Labels permutation309 permutation4
    mixedMoment B raw16012step0 raw16012step0Labels = mixedMoment B raw16012step1 raw16012step1Labels := by
      have ha : raw16012step1 = -raw16012step0 := by apply Matrix.ext; change ∀ i j, raw16012step1 i j = -(raw16012step0 i j); unfold raw16012step1 raw16012step0; decide +kernel
      have hl : raw16012step1Labels = raw16012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2945 node2945Labels := by rfl

def raw16013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 3, -1]]
def raw16013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw16013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16013 raw16013Labels = mixedMoment B node2947 node2947Labels := by
  calc
    mixedMoment B raw16013 raw16013Labels = mixedMoment B raw16013step0 raw16013step0Labels := by
      have ha : raw16013step0 = (fun i j => raw16013 (permutation307 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16013step0 raw16013; decide +kernel
      have hl : raw16013step0Labels = raw16013Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16013 raw16013Labels permutation307 permutation4
    mixedMoment B raw16013step0 raw16013step0Labels = mixedMoment B raw16013step1 raw16013step1Labels := by
      have ha : raw16013step1 = -raw16013step0 := by apply Matrix.ext; change ∀ i j, raw16013step1 i j = -(raw16013step0 i j); unfold raw16013step1 raw16013step0; decide +kernel
      have hl : raw16013step1Labels = raw16013step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2947 node2947Labels := by rfl

def raw16014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw16014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16014 raw16014Labels = mixedMoment B node2622 node2622Labels := by
  calc
    mixedMoment B raw16014 raw16014Labels = mixedMoment B raw16014step0 raw16014step0Labels := by
      have ha : raw16014step0 = (fun i j => raw16014 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16014step0 raw16014; decide +kernel
      have hl : raw16014step0Labels = raw16014Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16014 raw16014Labels permutation158 permutation2
    _ = mixedMoment B node2622 node2622Labels := by rfl

def raw16015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw16015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16015 raw16015Labels = mixedMoment B node3864 node3864Labels := by
  calc
    mixedMoment B raw16015 raw16015Labels = mixedMoment B raw16015step0 raw16015step0Labels := by
      have ha : raw16015step0 = (fun i j => raw16015 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16015step0 raw16015; decide +kernel
      have hl : raw16015step0Labels = raw16015Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16015 raw16015Labels permutation158 permutation2
    _ = mixedMoment B node3864 node3864Labels := by rfl

def raw16016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16016 raw16016Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw16016 raw16016Labels = mixedMoment B raw16016step0 raw16016step0Labels := by
      have hz : ∀ j, raw16016 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16016step0 = (fun i j => raw16016 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16016step0 raw16016; decide +kernel
      have hl : raw16016step0Labels = raw16016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16016 raw16016Labels permutation520 hz
    mixedMoment B raw16016step0 raw16016step0Labels = mixedMoment B raw16016step1 raw16016step1Labels := by
      have ha : raw16016step1 = (fun i j => raw16016step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16016step1 raw16016step0; decide +kernel
      have hl : raw16016step1Labels = raw16016step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16016step0 raw16016step0Labels permutation34 permutation2
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw16017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16017 raw16017Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw16017 raw16017Labels = mixedMoment B raw16017step0 raw16017step0Labels := by
      have ha : raw16017step0 = (fun i j => raw16017 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16017step0 raw16017; decide +kernel
      have hl : raw16017step0Labels = raw16017Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16017 raw16017Labels permutation158 permutation2
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw16018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16018 raw16018Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw16018 raw16018Labels = mixedMoment B raw16018step0 raw16018step0Labels := by
      have ha : raw16018step0 = (fun i j => raw16018 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16018step0 raw16018; decide +kernel
      have hl : raw16018step0Labels = raw16018Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16018 raw16018Labels permutation176 permutation2
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw16019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16019 raw16019Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw16019 raw16019Labels = mixedMoment B raw16019step0 raw16019step0Labels := by
      have ha : raw16019step0 = (fun i j => raw16019 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16019step0 raw16019; decide +kernel
      have hl : raw16019step0Labels = raw16019Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16019 raw16019Labels permutation178 permutation2
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw16020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16020 raw16020Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw16020 raw16020Labels = mixedMoment B raw16020step0 raw16020step0Labels := by
      have ha : raw16020step0 = (fun i j => raw16020 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16020step0 raw16020; decide +kernel
      have hl : raw16020step0Labels = raw16020Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16020 raw16020Labels permutation176 permutation2
    _ = mixedMoment B node3783 node3783Labels := by rfl

def raw16021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16021 raw16021Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw16021 raw16021Labels = mixedMoment B raw16021step0 raw16021step0Labels := by
      have ha : raw16021step0 = (fun i j => raw16021 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16021step0 raw16021; decide +kernel
      have hl : raw16021step0Labels = raw16021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16021 raw16021Labels permutation686 permutation2
    mixedMoment B raw16021step0 raw16021step0Labels = mixedMoment B raw16021step1 raw16021step1Labels := by
      have ha : raw16021step1 = -raw16021step0 := by apply Matrix.ext; change ∀ i j, raw16021step1 i j = -(raw16021step0 i j); unfold raw16021step1 raw16021step0; decide +kernel
      have hl : raw16021step1Labels = raw16021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw16022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16022 raw16022Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw16022 raw16022Labels = mixedMoment B raw16022step0 raw16022step0Labels := by
      have ha : raw16022step0 = (fun i j => raw16022 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16022step0 raw16022; decide +kernel
      have hl : raw16022step0Labels = raw16022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16022 raw16022Labels permutation154 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw16023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16023 raw16023Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16023 raw16023Labels = mixedMoment B raw16023step0 raw16023step0Labels := by
      have hz : ∀ j, raw16023 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16023step0 = (fun i j => raw16023 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16023step0 raw16023; decide +kernel
      have hl : raw16023step0Labels = raw16023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16023 raw16023Labels permutation520 hz
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw16024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16024 raw16024Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw16024 raw16024Labels = mixedMoment B raw16024step0 raw16024step0Labels := by
      have ha : raw16024step0 = (fun i j => raw16024 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16024step0 raw16024; decide +kernel
      have hl : raw16024step0Labels = raw16024Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16024 raw16024Labels permutation154 permutation2
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw16025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16025 raw16025Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw16025 raw16025Labels = mixedMoment B raw16025step0 raw16025step0Labels := by
      have ha : raw16025step0 = (fun i j => raw16025 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16025step0 raw16025; decide +kernel
      have hl : raw16025step0Labels = raw16025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16025 raw16025Labels permutation271 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw16026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16026 raw16026Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw16026 raw16026Labels = mixedMoment B raw16026step0 raw16026step0Labels := by
      have ha : raw16026step0 = (fun i j => raw16026 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16026step0 raw16026; decide +kernel
      have hl : raw16026step0Labels = raw16026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16026 raw16026Labels permutation687 permutation2
    mixedMoment B raw16026step0 raw16026step0Labels = mixedMoment B raw16026step1 raw16026step1Labels := by
      have ha : raw16026step1 = -raw16026step0 := by apply Matrix.ext; change ∀ i j, raw16026step1 i j = -(raw16026step0 i j); unfold raw16026step1 raw16026step0; decide +kernel
      have hl : raw16026step1Labels = raw16026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw16027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16027 raw16027Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw16027 raw16027Labels = mixedMoment B raw16027step0 raw16027step0Labels := by
      have ha : raw16027step0 = (fun i j => raw16027 (permutation678 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16027step0 raw16027; decide +kernel
      have hl : raw16027step0Labels = raw16027Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16027 raw16027Labels permutation678 permutation2
    mixedMoment B raw16027step0 raw16027step0Labels = mixedMoment B raw16027step1 raw16027step1Labels := by
      have ha : raw16027step1 = -raw16027step0 := by apply Matrix.ext; change ∀ i j, raw16027step1 i j = -(raw16027step0 i j); unfold raw16027step1 raw16027step0; decide +kernel
      have hl : raw16027step1Labels = raw16027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw16028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16028step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16028step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16028step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16028 raw16028Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw16028 raw16028Labels = mixedMoment B raw16028step0 raw16028step0Labels := by
      have ha : raw16028step0 = (fun i j => raw16028 (permutation309 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16028step0 raw16028; decide +kernel
      have hl : raw16028step0Labels = raw16028Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16028 raw16028Labels permutation309 permutation6
    mixedMoment B raw16028step0 raw16028step0Labels = mixedMoment B raw16028step1 raw16028step1Labels := by
      have ha : raw16028step1 = -raw16028step0 := by apply Matrix.ext; change ∀ i j, raw16028step1 i j = -(raw16028step0 i j); unfold raw16028step1 raw16028step0; decide +kernel
      have hl : raw16028step1Labels = raw16028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16028step1 raw16028step1Labels = mixedMoment B raw16028step2 raw16028step2Labels := by
      have ha : raw16028step2 = raw16028step1 := by apply Matrix.ext; unfold raw16028step2 raw16028step1; decide +kernel
      have hl : raw16028step1Labels = labelEmbedding9 ∘ raw16028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16028step1 raw16028step1Labels raw16028step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw16029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16029step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16029step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16029step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16029 raw16029Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw16029 raw16029Labels = mixedMoment B raw16029step0 raw16029step0Labels := by
      have ha : raw16029step0 = (fun i j => raw16029 (permutation308 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16029step0 raw16029; decide +kernel
      have hl : raw16029step0Labels = raw16029Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16029 raw16029Labels permutation308 permutation6
    mixedMoment B raw16029step0 raw16029step0Labels = mixedMoment B raw16029step1 raw16029step1Labels := by
      have ha : raw16029step1 = -raw16029step0 := by apply Matrix.ext; change ∀ i j, raw16029step1 i j = -(raw16029step0 i j); unfold raw16029step1 raw16029step0; decide +kernel
      have hl : raw16029step1Labels = raw16029step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16029step1 raw16029step1Labels = mixedMoment B raw16029step2 raw16029step2Labels := by
      have ha : raw16029step2 = raw16029step1 := by apply Matrix.ext; unfold raw16029step2 raw16029step1; decide +kernel
      have hl : raw16029step1Labels = labelEmbedding9 ∘ raw16029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16029step1 raw16029step1Labels raw16029step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw16030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16030step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16030step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16030step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16030step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16030 raw16030Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw16030 raw16030Labels = mixedMoment B raw16030step0 raw16030step0Labels := by
      have ha : raw16030step0 = (fun i j => raw16030 (permutation191 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16030step0 raw16030; decide +kernel
      have hl : raw16030step0Labels = raw16030Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16030 raw16030Labels permutation191 permutation5
    mixedMoment B raw16030step0 raw16030step0Labels = mixedMoment B raw16030step1 raw16030step1Labels := by
      have ha : raw16030step1 = -raw16030step0 := by apply Matrix.ext; change ∀ i j, raw16030step1 i j = -(raw16030step0 i j); unfold raw16030step1 raw16030step0; decide +kernel
      have hl : raw16030step1Labels = raw16030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16030step1 raw16030step1Labels = mixedMoment B raw16030step2 raw16030step2Labels := by
      have ha : raw16030step2 = raw16030step1 := by apply Matrix.ext; unfold raw16030step2 raw16030step1; decide +kernel
      have hl : raw16030step1Labels = labelEmbedding8 ∘ raw16030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16030step1 raw16030step1Labels raw16030step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw16031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16031step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16031step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16031step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16031 raw16031Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw16031 raw16031Labels = mixedMoment B raw16031step0 raw16031step0Labels := by
      have ha : raw16031step0 = (fun i j => raw16031 (permutation191 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16031step0 raw16031; decide +kernel
      have hl : raw16031step0Labels = raw16031Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16031 raw16031Labels permutation191 permutation5
    mixedMoment B raw16031step0 raw16031step0Labels = mixedMoment B raw16031step1 raw16031step1Labels := by
      have ha : raw16031step1 = -raw16031step0 := by apply Matrix.ext; change ∀ i j, raw16031step1 i j = -(raw16031step0 i j); unfold raw16031step1 raw16031step0; decide +kernel
      have hl : raw16031step1Labels = raw16031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16031step1 raw16031step1Labels = mixedMoment B raw16031step2 raw16031step2Labels := by
      have ha : raw16031step2 = raw16031step1 := by apply Matrix.ext; unfold raw16031step2 raw16031step1; decide +kernel
      have hl : raw16031step1Labels = labelEmbedding8 ∘ raw16031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16031step1 raw16031step1Labels raw16031step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw16032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16032step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16032step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16032step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16032 raw16032Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw16032 raw16032Labels = mixedMoment B raw16032step0 raw16032step0Labels := by
      have ha : raw16032step0 = (fun i j => raw16032 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16032step0 raw16032; decide +kernel
      have hl : raw16032step0Labels = raw16032Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16032 raw16032Labels permutation185 permutation5
    mixedMoment B raw16032step0 raw16032step0Labels = mixedMoment B raw16032step1 raw16032step1Labels := by
      have ha : raw16032step1 = -raw16032step0 := by apply Matrix.ext; change ∀ i j, raw16032step1 i j = -(raw16032step0 i j); unfold raw16032step1 raw16032step0; decide +kernel
      have hl : raw16032step1Labels = raw16032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16032step1 raw16032step1Labels = mixedMoment B raw16032step2 raw16032step2Labels := by
      have ha : raw16032step2 = raw16032step1 := by apply Matrix.ext; unfold raw16032step2 raw16032step1; decide +kernel
      have hl : raw16032step1Labels = labelEmbedding8 ∘ raw16032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16032step1 raw16032step1Labels raw16032step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw16033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16033step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16033 raw16033Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw16033 raw16033Labels = mixedMoment B raw16033step0 raw16033step0Labels := by
      have ha : raw16033step0 = (fun i j => raw16033 (permutation319 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16033step0 raw16033; decide +kernel
      have hl : raw16033step0Labels = raw16033Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16033 raw16033Labels permutation319 permutation4
    mixedMoment B raw16033step0 raw16033step0Labels = mixedMoment B raw16033step1 raw16033step1Labels := by
      have ha : raw16033step1 = raw16033step0 := by apply Matrix.ext; unfold raw16033step1 raw16033step0; decide +kernel
      have hl : raw16033step0Labels = labelEmbedding7 ∘ raw16033step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16033step0 raw16033step0Labels raw16033step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw16034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16034step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16034 raw16034Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw16034 raw16034Labels = mixedMoment B raw16034step0 raw16034step0Labels := by
      have ha : raw16034step0 = (fun i j => raw16034 (permutation317 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16034step0 raw16034; decide +kernel
      have hl : raw16034step0Labels = raw16034Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16034 raw16034Labels permutation317 permutation4
    mixedMoment B raw16034step0 raw16034step0Labels = mixedMoment B raw16034step1 raw16034step1Labels := by
      have ha : raw16034step1 = raw16034step0 := by apply Matrix.ext; unfold raw16034step1 raw16034step0; decide +kernel
      have hl : raw16034step0Labels = labelEmbedding7 ∘ raw16034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16034step0 raw16034step0Labels raw16034step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw16035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16035step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16035 raw16035Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw16035 raw16035Labels = mixedMoment B raw16035step0 raw16035step0Labels := by
      have ha : raw16035step0 = (fun i j => raw16035 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16035step0 raw16035; decide +kernel
      have hl : raw16035step0Labels = raw16035Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16035 raw16035Labels permutation158 permutation3
    mixedMoment B raw16035step0 raw16035step0Labels = mixedMoment B raw16035step1 raw16035step1Labels := by
      have ha : raw16035step1 = raw16035step0 := by apply Matrix.ext; unfold raw16035step1 raw16035step0; decide +kernel
      have hl : raw16035step0Labels = labelEmbedding6 ∘ raw16035step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16035step0 raw16035step0Labels raw16035step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw16036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16036 raw16036Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw16036 raw16036Labels = mixedMoment B raw16036step0 raw16036step0Labels := by
      have ha : raw16036step0 = (fun i j => raw16036 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16036step0 raw16036; decide +kernel
      have hl : raw16036step0Labels = raw16036Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16036 raw16036Labels permutation271 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw16037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16037step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16037 raw16037Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw16037 raw16037Labels = mixedMoment B raw16037step0 raw16037step0Labels := by
      have ha : raw16037step0 = (fun i j => raw16037 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16037step0 raw16037; decide +kernel
      have hl : raw16037step0Labels = raw16037Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16037 raw16037Labels permutation200 permutation3
    mixedMoment B raw16037step0 raw16037step0Labels = mixedMoment B raw16037step1 raw16037step1Labels := by
      have ha : raw16037step1 = raw16037step0 := by apply Matrix.ext; unfold raw16037step1 raw16037step0; decide +kernel
      have hl : raw16037step0Labels = labelEmbedding6 ∘ raw16037step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16037step0 raw16037step0Labels raw16037step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw16038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16038step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16038step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16038step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16038step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16038 raw16038Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw16038 raw16038Labels = mixedMoment B raw16038step0 raw16038step0Labels := by
      have ha : raw16038step0 = (fun i j => raw16038 (permutation230 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16038step0 raw16038; decide +kernel
      have hl : raw16038step0Labels = raw16038Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16038 raw16038Labels permutation230 permutation5
    mixedMoment B raw16038step0 raw16038step0Labels = mixedMoment B raw16038step1 raw16038step1Labels := by
      have ha : raw16038step1 = -raw16038step0 := by apply Matrix.ext; change ∀ i j, raw16038step1 i j = -(raw16038step0 i j); unfold raw16038step1 raw16038step0; decide +kernel
      have hl : raw16038step1Labels = raw16038step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16038step1 raw16038step1Labels = mixedMoment B raw16038step2 raw16038step2Labels := by
      have ha : raw16038step2 = raw16038step1 := by apply Matrix.ext; unfold raw16038step2 raw16038step1; decide +kernel
      have hl : raw16038step1Labels = labelEmbedding8 ∘ raw16038step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16038step1 raw16038step1Labels raw16038step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw16039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16039step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16039 raw16039Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw16039 raw16039Labels = mixedMoment B raw16039step0 raw16039step0Labels := by
      have ha : raw16039step0 = (fun i j => raw16039 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16039step0 raw16039; decide +kernel
      have hl : raw16039step0Labels = raw16039Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16039 raw16039Labels permutation158 permutation3
    mixedMoment B raw16039step0 raw16039step0Labels = mixedMoment B raw16039step1 raw16039step1Labels := by
      have ha : raw16039step1 = raw16039step0 := by apply Matrix.ext; unfold raw16039step1 raw16039step0; decide +kernel
      have hl : raw16039step0Labels = labelEmbedding6 ∘ raw16039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16039step0 raw16039step0Labels raw16039step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw16040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16040step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16040step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16040step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16040 raw16040Labels = mixedMoment B node4799 node4799Labels := by
  calc
    mixedMoment B raw16040 raw16040Labels = mixedMoment B raw16040step0 raw16040step0Labels := by
      have ha : raw16040step0 = (fun i j => raw16040 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16040step0 raw16040; decide +kernel
      have hl : raw16040step0Labels = raw16040Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16040 raw16040Labels permutation189 permutation5
    mixedMoment B raw16040step0 raw16040step0Labels = mixedMoment B raw16040step1 raw16040step1Labels := by
      have ha : raw16040step1 = -raw16040step0 := by apply Matrix.ext; change ∀ i j, raw16040step1 i j = -(raw16040step0 i j); unfold raw16040step1 raw16040step0; decide +kernel
      have hl : raw16040step1Labels = raw16040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16040step1 raw16040step1Labels = mixedMoment B raw16040step2 raw16040step2Labels := by
      have ha : raw16040step2 = raw16040step1 := by apply Matrix.ext; unfold raw16040step2 raw16040step1; decide +kernel
      have hl : raw16040step1Labels = labelEmbedding8 ∘ raw16040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16040step1 raw16040step1Labels raw16040step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4799 node4799Labels := by rfl

def raw16041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16041step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16041 raw16041Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw16041 raw16041Labels = mixedMoment B raw16041step0 raw16041step0Labels := by
      have ha : raw16041step0 = (fun i j => raw16041 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16041step0 raw16041; decide +kernel
      have hl : raw16041step0Labels = raw16041Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16041 raw16041Labels permutation154 permutation3
    mixedMoment B raw16041step0 raw16041step0Labels = mixedMoment B raw16041step1 raw16041step1Labels := by
      have ha : raw16041step1 = raw16041step0 := by apply Matrix.ext; unfold raw16041step1 raw16041step0; decide +kernel
      have hl : raw16041step0Labels = labelEmbedding6 ∘ raw16041step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16041step0 raw16041step0Labels raw16041step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw16042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16042step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16042step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16042step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16042step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16042 raw16042Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw16042 raw16042Labels = mixedMoment B raw16042step0 raw16042step0Labels := by
      have ha : raw16042step0 = (fun i j => raw16042 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16042step0 raw16042; decide +kernel
      have hl : raw16042step0Labels = raw16042Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16042 raw16042Labels permutation189 permutation5
    mixedMoment B raw16042step0 raw16042step0Labels = mixedMoment B raw16042step1 raw16042step1Labels := by
      have ha : raw16042step1 = -raw16042step0 := by apply Matrix.ext; change ∀ i j, raw16042step1 i j = -(raw16042step0 i j); unfold raw16042step1 raw16042step0; decide +kernel
      have hl : raw16042step1Labels = raw16042step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16042step1 raw16042step1Labels = mixedMoment B raw16042step2 raw16042step2Labels := by
      have ha : raw16042step2 = raw16042step1 := by apply Matrix.ext; unfold raw16042step2 raw16042step1; decide +kernel
      have hl : raw16042step1Labels = labelEmbedding8 ∘ raw16042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16042step1 raw16042step1Labels raw16042step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

def raw16043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16043step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16043step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16043step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16043 raw16043Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw16043 raw16043Labels = mixedMoment B raw16043step0 raw16043step0Labels := by
      have ha : raw16043step0 = (fun i j => raw16043 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16043step0 raw16043; decide +kernel
      have hl : raw16043step0Labels = raw16043Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16043 raw16043Labels permutation189 permutation5
    mixedMoment B raw16043step0 raw16043step0Labels = mixedMoment B raw16043step1 raw16043step1Labels := by
      have ha : raw16043step1 = -raw16043step0 := by apply Matrix.ext; change ∀ i j, raw16043step1 i j = -(raw16043step0 i j); unfold raw16043step1 raw16043step0; decide +kernel
      have hl : raw16043step1Labels = raw16043step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16043step1 raw16043step1Labels = mixedMoment B raw16043step2 raw16043step2Labels := by
      have ha : raw16043step2 = raw16043step1 := by apply Matrix.ext; unfold raw16043step2 raw16043step1; decide +kernel
      have hl : raw16043step1Labels = labelEmbedding8 ∘ raw16043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16043step1 raw16043step1Labels raw16043step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw16044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16044step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16044step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16044 raw16044Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw16044 raw16044Labels = mixedMoment B raw16044step0 raw16044step0Labels := by
      have ha : raw16044step0 = (fun i j => raw16044 (permutation192 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16044step0 raw16044; decide +kernel
      have hl : raw16044step0Labels = raw16044Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16044 raw16044Labels permutation192 permutation5
    mixedMoment B raw16044step0 raw16044step0Labels = mixedMoment B raw16044step1 raw16044step1Labels := by
      have ha : raw16044step1 = -raw16044step0 := by apply Matrix.ext; change ∀ i j, raw16044step1 i j = -(raw16044step0 i j); unfold raw16044step1 raw16044step0; decide +kernel
      have hl : raw16044step1Labels = raw16044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16044step1 raw16044step1Labels = mixedMoment B raw16044step2 raw16044step2Labels := by
      have ha : raw16044step2 = raw16044step1 := by apply Matrix.ext; unfold raw16044step2 raw16044step1; decide +kernel
      have hl : raw16044step1Labels = labelEmbedding8 ∘ raw16044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16044step1 raw16044step1Labels raw16044step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw16045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw16045step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16045step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16045step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16045step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16045 raw16045Labels = mixedMoment B node4825 node4825Labels := by
  calc
    mixedMoment B raw16045 raw16045Labels = mixedMoment B raw16045step0 raw16045step0Labels := by
      have ha : raw16045step0 = (fun i j => raw16045 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16045step0 raw16045; decide +kernel
      have hl : raw16045step0Labels = raw16045Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16045 raw16045Labels permutation176 permutation5
    mixedMoment B raw16045step0 raw16045step0Labels = mixedMoment B raw16045step1 raw16045step1Labels := by
      have ha : raw16045step1 = -raw16045step0 := by apply Matrix.ext; change ∀ i j, raw16045step1 i j = -(raw16045step0 i j); unfold raw16045step1 raw16045step0; decide +kernel
      have hl : raw16045step1Labels = raw16045step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16045step1 raw16045step1Labels = mixedMoment B raw16045step2 raw16045step2Labels := by
      have ha : raw16045step2 = raw16045step1 := by apply Matrix.ext; unfold raw16045step2 raw16045step1; decide +kernel
      have hl : raw16045step1Labels = labelEmbedding8 ∘ raw16045step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16045step1 raw16045step1Labels raw16045step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4825 node4825Labels := by rfl

def raw16046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16046 raw16046Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw16046 raw16046Labels = mixedMoment B raw16046step0 raw16046step0Labels := by
      have ha : raw16046step0 = (fun i j => raw16046 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16046step0 raw16046; decide +kernel
      have hl : raw16046step0Labels = raw16046Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16046 raw16046Labels permutation271 permutation2
    _ = mixedMoment B node5377 node5377Labels := by rfl

def raw16047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw16047step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16047step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16047step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16047 raw16047Labels = mixedMoment B node5362 node5362Labels := by
  calc
    mixedMoment B raw16047 raw16047Labels = mixedMoment B raw16047step0 raw16047step0Labels := by
      have ha : raw16047step0 = (fun i j => raw16047 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16047step0 raw16047; decide +kernel
      have hl : raw16047step0Labels = raw16047Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16047 raw16047Labels permutation176 permutation5
    mixedMoment B raw16047step0 raw16047step0Labels = mixedMoment B raw16047step1 raw16047step1Labels := by
      have ha : raw16047step1 = -raw16047step0 := by apply Matrix.ext; change ∀ i j, raw16047step1 i j = -(raw16047step0 i j); unfold raw16047step1 raw16047step0; decide +kernel
      have hl : raw16047step1Labels = raw16047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16047step1 raw16047step1Labels = mixedMoment B raw16047step2 raw16047step2Labels := by
      have ha : raw16047step2 = raw16047step1 := by apply Matrix.ext; unfold raw16047step2 raw16047step1; decide +kernel
      have hl : raw16047step1Labels = labelEmbedding8 ∘ raw16047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16047step1 raw16047step1Labels raw16047step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5362 node5362Labels := by rfl

def raw16048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16048 raw16048Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw16048 raw16048Labels = mixedMoment B raw16048step0 raw16048step0Labels := by
      have ha : raw16048step0 = (fun i j => raw16048 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16048step0 raw16048; decide +kernel
      have hl : raw16048step0Labels = raw16048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16048 raw16048Labels permutation200 permutation3
    mixedMoment B raw16048step0 raw16048step0Labels = mixedMoment B raw16048step1 raw16048step1Labels := by
      have ha : raw16048step1 = raw16048step0 := by apply Matrix.ext; unfold raw16048step1 raw16048step0; decide +kernel
      have hl : raw16048step0Labels = labelEmbedding6 ∘ raw16048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16048step0 raw16048step0Labels raw16048step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw16049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw16049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16049step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16049step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16049step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16049step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16049 raw16049Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw16049 raw16049Labels = mixedMoment B raw16049step0 raw16049step0Labels := by
      have ha : raw16049step0 = (fun i j => raw16049 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16049step0 raw16049; decide +kernel
      have hl : raw16049step0Labels = raw16049Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16049 raw16049Labels permutation194 permutation5
    mixedMoment B raw16049step0 raw16049step0Labels = mixedMoment B raw16049step1 raw16049step1Labels := by
      have ha : raw16049step1 = -raw16049step0 := by apply Matrix.ext; change ∀ i j, raw16049step1 i j = -(raw16049step0 i j); unfold raw16049step1 raw16049step0; decide +kernel
      have hl : raw16049step1Labels = raw16049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16049step1 raw16049step1Labels = mixedMoment B raw16049step2 raw16049step2Labels := by
      have ha : raw16049step2 = raw16049step1 := by apply Matrix.ext; unfold raw16049step2 raw16049step1; decide +kernel
      have hl : raw16049step1Labels = labelEmbedding8 ∘ raw16049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16049step1 raw16049step1Labels raw16049step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw16050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw16050step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16050step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16050step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16050step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16050 raw16050Labels = mixedMoment B node4797 node4797Labels := by
  calc
    mixedMoment B raw16050 raw16050Labels = mixedMoment B raw16050step0 raw16050step0Labels := by
      have ha : raw16050step0 = (fun i j => raw16050 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16050step0 raw16050; decide +kernel
      have hl : raw16050step0Labels = raw16050Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16050 raw16050Labels permutation188 permutation5
    mixedMoment B raw16050step0 raw16050step0Labels = mixedMoment B raw16050step1 raw16050step1Labels := by
      have ha : raw16050step1 = -raw16050step0 := by apply Matrix.ext; change ∀ i j, raw16050step1 i j = -(raw16050step0 i j); unfold raw16050step1 raw16050step0; decide +kernel
      have hl : raw16050step1Labels = raw16050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16050step1 raw16050step1Labels = mixedMoment B raw16050step2 raw16050step2Labels := by
      have ha : raw16050step2 = raw16050step1 := by apply Matrix.ext; unfold raw16050step2 raw16050step1; decide +kernel
      have hl : raw16050step1Labels = labelEmbedding8 ∘ raw16050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16050step1 raw16050step1Labels raw16050step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4797 node4797Labels := by rfl

def raw16051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16051step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16051step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16051step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16051 raw16051Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw16051 raw16051Labels = mixedMoment B raw16051step0 raw16051step0Labels := by
      have ha : raw16051step0 = (fun i j => raw16051 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16051step0 raw16051; decide +kernel
      have hl : raw16051step0Labels = raw16051Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16051 raw16051Labels permutation688 permutation3
    mixedMoment B raw16051step0 raw16051step0Labels = mixedMoment B raw16051step1 raw16051step1Labels := by
      have ha : raw16051step1 = -raw16051step0 := by apply Matrix.ext; change ∀ i j, raw16051step1 i j = -(raw16051step0 i j); unfold raw16051step1 raw16051step0; decide +kernel
      have hl : raw16051step1Labels = raw16051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16051step1 raw16051step1Labels = mixedMoment B raw16051step2 raw16051step2Labels := by
      have ha : raw16051step2 = raw16051step1 := by apply Matrix.ext; unfold raw16051step2 raw16051step1; decide +kernel
      have hl : raw16051step1Labels = labelEmbedding6 ∘ raw16051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16051step1 raw16051step1Labels raw16051step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw16052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16052step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16052step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16052 raw16052Labels = mixedMoment B node5132 node5132Labels := by
  calc
    mixedMoment B raw16052 raw16052Labels = mixedMoment B raw16052step0 raw16052step0Labels := by
      have ha : raw16052step0 = (fun i j => raw16052 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16052step0 raw16052; decide +kernel
      have hl : raw16052step0Labels = raw16052Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16052 raw16052Labels permutation686 permutation3
    mixedMoment B raw16052step0 raw16052step0Labels = mixedMoment B raw16052step1 raw16052step1Labels := by
      have ha : raw16052step1 = -raw16052step0 := by apply Matrix.ext; change ∀ i j, raw16052step1 i j = -(raw16052step0 i j); unfold raw16052step1 raw16052step0; decide +kernel
      have hl : raw16052step1Labels = raw16052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16052step1 raw16052step1Labels = mixedMoment B raw16052step2 raw16052step2Labels := by
      have ha : raw16052step2 = raw16052step1 := by apply Matrix.ext; unfold raw16052step2 raw16052step1; decide +kernel
      have hl : raw16052step1Labels = labelEmbedding6 ∘ raw16052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16052step1 raw16052step1Labels raw16052step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5132 node5132Labels := by rfl

def raw16053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16053step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16053step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16053step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16053step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16053 raw16053Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw16053 raw16053Labels = mixedMoment B raw16053step0 raw16053step0Labels := by
      have ha : raw16053step0 = (fun i j => raw16053 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16053step0 raw16053; decide +kernel
      have hl : raw16053step0Labels = raw16053Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16053 raw16053Labels permutation680 permutation3
    mixedMoment B raw16053step0 raw16053step0Labels = mixedMoment B raw16053step1 raw16053step1Labels := by
      have ha : raw16053step1 = -raw16053step0 := by apply Matrix.ext; change ∀ i j, raw16053step1 i j = -(raw16053step0 i j); unfold raw16053step1 raw16053step0; decide +kernel
      have hl : raw16053step1Labels = raw16053step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16053step1 raw16053step1Labels = mixedMoment B raw16053step2 raw16053step2Labels := by
      have ha : raw16053step2 = raw16053step1 := by apply Matrix.ext; unfold raw16053step2 raw16053step1; decide +kernel
      have hl : raw16053step1Labels = labelEmbedding6 ∘ raw16053step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16053step1 raw16053step1Labels raw16053step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw16054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw16054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16054step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16054step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16054step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16054step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16054 raw16054Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw16054 raw16054Labels = mixedMoment B raw16054step0 raw16054step0Labels := by
      have ha : raw16054step0 = (fun i j => raw16054 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16054step0 raw16054; decide +kernel
      have hl : raw16054step0Labels = raw16054Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16054 raw16054Labels permutation658 permutation3
    mixedMoment B raw16054step0 raw16054step0Labels = mixedMoment B raw16054step1 raw16054step1Labels := by
      have ha : raw16054step1 = -raw16054step0 := by apply Matrix.ext; change ∀ i j, raw16054step1 i j = -(raw16054step0 i j); unfold raw16054step1 raw16054step0; decide +kernel
      have hl : raw16054step1Labels = raw16054step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16054step1 raw16054step1Labels = mixedMoment B raw16054step2 raw16054step2Labels := by
      have ha : raw16054step2 = raw16054step1 := by apply Matrix.ext; unfold raw16054step2 raw16054step1; decide +kernel
      have hl : raw16054step1Labels = labelEmbedding6 ∘ raw16054step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16054step1 raw16054step1Labels raw16054step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw16055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16055 raw16055Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw16055 raw16055Labels = mixedMoment B raw16055step0 raw16055step0Labels := by
      have ha : raw16055step0 = (fun i j => raw16055 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16055step0 raw16055; decide +kernel
      have hl : raw16055step0Labels = raw16055Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16055 raw16055Labels permutation687 permutation3
    mixedMoment B raw16055step0 raw16055step0Labels = mixedMoment B raw16055step1 raw16055step1Labels := by
      have ha : raw16055step1 = -raw16055step0 := by apply Matrix.ext; change ∀ i j, raw16055step1 i j = -(raw16055step0 i j); unfold raw16055step1 raw16055step0; decide +kernel
      have hl : raw16055step1Labels = raw16055step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw16056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16056 raw16056Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw16056 raw16056Labels = mixedMoment B raw16056step0 raw16056step0Labels := by
      have ha : raw16056step0 = (fun i j => raw16056 (permutation310 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16056step0 raw16056; decide +kernel
      have hl : raw16056step0Labels = raw16056Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16056 raw16056Labels permutation310 permutation6
    mixedMoment B raw16056step0 raw16056step0Labels = mixedMoment B raw16056step1 raw16056step1Labels := by
      have ha : raw16056step1 = -raw16056step0 := by apply Matrix.ext; change ∀ i j, raw16056step1 i j = -(raw16056step0 i j); unfold raw16056step1 raw16056step0; decide +kernel
      have hl : raw16056step1Labels = raw16056step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw16057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16057 raw16057Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw16057 raw16057Labels = mixedMoment B raw16057step0 raw16057step0Labels := by
      have ha : raw16057step0 = (fun i j => raw16057 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16057step0 raw16057; decide +kernel
      have hl : raw16057step0Labels = raw16057Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16057 raw16057Labels permutation680 permutation3
    mixedMoment B raw16057step0 raw16057step0Labels = mixedMoment B raw16057step1 raw16057step1Labels := by
      have ha : raw16057step1 = -raw16057step0 := by apply Matrix.ext; change ∀ i j, raw16057step1 i j = -(raw16057step0 i j); unfold raw16057step1 raw16057step0; decide +kernel
      have hl : raw16057step1Labels = raw16057step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw16058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16058 raw16058Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw16058 raw16058Labels = mixedMoment B raw16058step0 raw16058step0Labels := by
      have ha : raw16058step0 = (fun i j => raw16058 (permutation309 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16058step0 raw16058; decide +kernel
      have hl : raw16058step0Labels = raw16058Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16058 raw16058Labels permutation309 permutation6
    mixedMoment B raw16058step0 raw16058step0Labels = mixedMoment B raw16058step1 raw16058step1Labels := by
      have ha : raw16058step1 = -raw16058step0 := by apply Matrix.ext; change ∀ i j, raw16058step1 i j = -(raw16058step0 i j); unfold raw16058step1 raw16058step0; decide +kernel
      have hl : raw16058step1Labels = raw16058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw16059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16059 raw16059Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw16059 raw16059Labels = mixedMoment B raw16059step0 raw16059step0Labels := by
      have ha : raw16059step0 = (fun i j => raw16059 (permutation308 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16059step0 raw16059; decide +kernel
      have hl : raw16059step0Labels = raw16059Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16059 raw16059Labels permutation308 permutation6
    mixedMoment B raw16059step0 raw16059step0Labels = mixedMoment B raw16059step1 raw16059step1Labels := by
      have ha : raw16059step1 = -raw16059step0 := by apply Matrix.ext; change ∀ i j, raw16059step1 i j = -(raw16059step0 i j); unfold raw16059step1 raw16059step0; decide +kernel
      have hl : raw16059step1Labels = raw16059step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw16060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16060 raw16060Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw16060 raw16060Labels = mixedMoment B raw16060step0 raw16060step0Labels := by
      have ha : raw16060step0 = (fun i j => raw16060 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16060step0 raw16060; decide +kernel
      have hl : raw16060step0Labels = raw16060Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16060 raw16060Labels permutation182 permutation3
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw16061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16061 raw16061Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw16061 raw16061Labels = mixedMoment B raw16061step0 raw16061step0Labels := by
      have ha : raw16061step0 = (fun i j => raw16061 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16061step0 raw16061; decide +kernel
      have hl : raw16061step0Labels = raw16061Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16061 raw16061Labels permutation182 permutation3
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw16062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16062 raw16062Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw16062 raw16062Labels = mixedMoment B raw16062step0 raw16062step0Labels := by
      have ha : raw16062step0 = (fun i j => raw16062 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16062step0 raw16062; decide +kernel
      have hl : raw16062step0Labels = raw16062Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16062 raw16062Labels permutation206 permutation3
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw16063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16063 raw16063Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw16063 raw16063Labels = mixedMoment B raw16063step0 raw16063step0Labels := by
      have ha : raw16063step0 = (fun i j => raw16063 (permutation309 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16063step0 raw16063; decide +kernel
      have hl : raw16063step0Labels = raw16063Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16063 raw16063Labels permutation309 permutation6
    mixedMoment B raw16063step0 raw16063step0Labels = mixedMoment B raw16063step1 raw16063step1Labels := by
      have ha : raw16063step1 = -raw16063step0 := by apply Matrix.ext; change ∀ i j, raw16063step1 i j = -(raw16063step0 i j); unfold raw16063step1 raw16063step0; decide +kernel
      have hl : raw16063step1Labels = raw16063step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3810 node3810Labels := by rfl

def raw16064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16064 raw16064Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw16064 raw16064Labels = mixedMoment B raw16064step0 raw16064step0Labels := by
      have ha : raw16064step0 = (fun i j => raw16064 (permutation308 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16064step0 raw16064; decide +kernel
      have hl : raw16064step0Labels = raw16064Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16064 raw16064Labels permutation308 permutation6
    mixedMoment B raw16064step0 raw16064step0Labels = mixedMoment B raw16064step1 raw16064step1Labels := by
      have ha : raw16064step1 = -raw16064step0 := by apply Matrix.ext; change ∀ i j, raw16064step1 i j = -(raw16064step0 i j); unfold raw16064step1 raw16064step0; decide +kernel
      have hl : raw16064step1Labels = raw16064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw16065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16065 raw16065Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw16065 raw16065Labels = mixedMoment B raw16065step0 raw16065step0Labels := by
      have ha : raw16065step0 = (fun i j => raw16065 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16065step0 raw16065; decide +kernel
      have hl : raw16065step0Labels = raw16065Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16065 raw16065Labels permutation158 permutation3
    _ = mixedMoment B node2088 node2088Labels := by rfl

def raw16066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16066 raw16066Labels = mixedMoment B node3726 node3726Labels := by
  calc
    mixedMoment B raw16066 raw16066Labels = mixedMoment B raw16066step0 raw16066step0Labels := by
      have ha : raw16066step0 = (fun i j => raw16066 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16066step0 raw16066; decide +kernel
      have hl : raw16066step0Labels = raw16066Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16066 raw16066Labels permutation158 permutation3
    _ = mixedMoment B node3726 node3726Labels := by rfl

def raw16067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16067 raw16067Labels = mixedMoment B node3829 node3829Labels := by
  calc
    mixedMoment B raw16067 raw16067Labels = mixedMoment B raw16067step0 raw16067step0Labels := by
      have ha : raw16067step0 = (fun i j => raw16067 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16067step0 raw16067; decide +kernel
      have hl : raw16067step0Labels = raw16067Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16067 raw16067Labels permutation200 permutation3
    _ = mixedMoment B node3829 node3829Labels := by rfl

def raw16068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16068 raw16068Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw16068 raw16068Labels = mixedMoment B raw16068step0 raw16068step0Labels := by
      have ha : raw16068step0 = (fun i j => raw16068 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16068step0 raw16068; decide +kernel
      have hl : raw16068step0Labels = raw16068Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16068 raw16068Labels permutation166 permutation3
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw16069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw16069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16069 raw16069Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw16069 raw16069Labels = mixedMoment B raw16069step0 raw16069step0Labels := by
      have ha : raw16069step0 = (fun i j => raw16069 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16069step0 raw16069; decide +kernel
      have hl : raw16069step0Labels = raw16069Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16069 raw16069Labels permutation158 permutation3
    _ = mixedMoment B node3882 node3882Labels := by rfl

def raw16070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16070 raw16070Labels = mixedMoment B node2076 node2076Labels := by
  calc
    mixedMoment B raw16070 raw16070Labels = mixedMoment B raw16070step0 raw16070step0Labels := by
      have ha : raw16070step0 = (fun i j => raw16070 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16070step0 raw16070; decide +kernel
      have hl : raw16070step0Labels = raw16070Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16070 raw16070Labels permutation154 permutation3
    _ = mixedMoment B node2076 node2076Labels := by rfl

def raw16071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16071 raw16071Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw16071 raw16071Labels = mixedMoment B raw16071step0 raw16071step0Labels := by
      have ha : raw16071step0 = (fun i j => raw16071 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16071step0 raw16071; decide +kernel
      have hl : raw16071step0Labels = raw16071Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16071 raw16071Labels permutation154 permutation3
    _ = mixedMoment B node3720 node3720Labels := by rfl

def raw16072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16072 raw16072Labels = mixedMoment B node3750 node3750Labels := by
  calc
    mixedMoment B raw16072 raw16072Labels = mixedMoment B raw16072step0 raw16072step0Labels := by
      have ha : raw16072step0 = (fun i j => raw16072 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16072step0 raw16072; decide +kernel
      have hl : raw16072step0Labels = raw16072Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16072 raw16072Labels permutation178 permutation3
    _ = mixedMoment B node3750 node3750Labels := by rfl

def raw16073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16073 raw16073Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw16073 raw16073Labels = mixedMoment B raw16073step0 raw16073step0Labels := by
      have ha : raw16073step0 = (fun i j => raw16073 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16073step0 raw16073; decide +kernel
      have hl : raw16073step0Labels = raw16073Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16073 raw16073Labels permutation154 permutation3
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw16074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16074 raw16074Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw16074 raw16074Labels = mixedMoment B raw16074step0 raw16074step0Labels := by
      have ha : raw16074step0 = (fun i j => raw16074 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16074step0 raw16074; decide +kernel
      have hl : raw16074step0Labels = raw16074Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16074 raw16074Labels permutation155 permutation3
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw16075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16075 raw16075Labels = mixedMoment B node2073 node2073Labels := by
  calc
    mixedMoment B raw16075 raw16075Labels = mixedMoment B raw16075step0 raw16075step0Labels := by
      have ha : raw16075step0 = (fun i j => raw16075 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16075step0 raw16075; decide +kernel
      have hl : raw16075step0Labels = raw16075Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16075 raw16075Labels permutation152 permutation3
    _ = mixedMoment B node2073 node2073Labels := by rfl

def raw16076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16076 raw16076Labels = mixedMoment B node3716 node3716Labels := by
  calc
    mixedMoment B raw16076 raw16076Labels = mixedMoment B raw16076step0 raw16076step0Labels := by
      have ha : raw16076step0 = (fun i j => raw16076 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16076step0 raw16076; decide +kernel
      have hl : raw16076step0Labels = raw16076Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16076 raw16076Labels permutation152 permutation3
    _ = mixedMoment B node3716 node3716Labels := by rfl

def raw16077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16077 raw16077Labels = mixedMoment B node3748 node3748Labels := by
  calc
    mixedMoment B raw16077 raw16077Labels = mixedMoment B raw16077step0 raw16077step0Labels := by
      have ha : raw16077step0 = (fun i j => raw16077 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16077step0 raw16077; decide +kernel
      have hl : raw16077step0Labels = raw16077Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16077 raw16077Labels permutation176 permutation3
    _ = mixedMoment B node3748 node3748Labels := by rfl

def raw16078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16078 raw16078Labels = mixedMoment B node3825 node3825Labels := by
  calc
    mixedMoment B raw16078 raw16078Labels = mixedMoment B raw16078step0 raw16078step0Labels := by
      have ha : raw16078step0 = (fun i j => raw16078 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16078step0 raw16078; decide +kernel
      have hl : raw16078step0Labels = raw16078Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16078 raw16078Labels permutation200 permutation3
    _ = mixedMoment B node3825 node3825Labels := by rfl

def raw16079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw16079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16079 raw16079Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw16079 raw16079Labels = mixedMoment B raw16079step0 raw16079step0Labels := by
      have ha : raw16079step0 = (fun i j => raw16079 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16079step0 raw16079; decide +kernel
      have hl : raw16079step0Labels = raw16079Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16079 raw16079Labels permutation153 permutation3
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw16080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw16080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16080 raw16080Labels = mixedMoment B node2070 node2070Labels := by
  calc
    mixedMoment B raw16080 raw16080Labels = mixedMoment B raw16080step0 raw16080step0Labels := by
      have ha : raw16080step0 = (fun i j => raw16080 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16080step0 raw16080; decide +kernel
      have hl : raw16080step0Labels = raw16080Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16080 raw16080Labels permutation152 permutation3
    _ = mixedMoment B node2070 node2070Labels := by rfl

def raw16081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16081 raw16081Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw16081 raw16081Labels = mixedMoment B raw16081step0 raw16081step0Labels := by
      have ha : raw16081step0 = (fun i j => raw16081 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16081step0 raw16081; decide +kernel
      have hl : raw16081step0Labels = raw16081Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16081 raw16081Labels permutation688 permutation3
    mixedMoment B raw16081step0 raw16081step0Labels = mixedMoment B raw16081step1 raw16081step1Labels := by
      have ha : raw16081step1 = -raw16081step0 := by apply Matrix.ext; change ∀ i j, raw16081step1 i j = -(raw16081step0 i j); unfold raw16081step1 raw16081step0; decide +kernel
      have hl : raw16081step1Labels = raw16081step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw16082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16082 raw16082Labels = mixedMoment B node2551 node2551Labels := by
  calc
    mixedMoment B raw16082 raw16082Labels = mixedMoment B raw16082step0 raw16082step0Labels := by
      have ha : raw16082step0 = (fun i j => raw16082 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16082step0 raw16082; decide +kernel
      have hl : raw16082step0Labels = raw16082Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16082 raw16082Labels permutation686 permutation3
    mixedMoment B raw16082step0 raw16082step0Labels = mixedMoment B raw16082step1 raw16082step1Labels := by
      have ha : raw16082step1 = -raw16082step0 := by apply Matrix.ext; change ∀ i j, raw16082step1 i j = -(raw16082step0 i j); unfold raw16082step1 raw16082step0; decide +kernel
      have hl : raw16082step1Labels = raw16082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2551 node2551Labels := by rfl

def raw16083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16083 raw16083Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw16083 raw16083Labels = mixedMoment B raw16083step0 raw16083step0Labels := by
      have ha : raw16083step0 = (fun i j => raw16083 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16083step0 raw16083; decide +kernel
      have hl : raw16083step0Labels = raw16083Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16083 raw16083Labels permutation680 permutation3
    mixedMoment B raw16083step0 raw16083step0Labels = mixedMoment B raw16083step1 raw16083step1Labels := by
      have ha : raw16083step1 = -raw16083step0 := by apply Matrix.ext; change ∀ i j, raw16083step1 i j = -(raw16083step0 i j); unfold raw16083step1 raw16083step0; decide +kernel
      have hl : raw16083step1Labels = raw16083step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2566 node2566Labels := by rfl

def raw16084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw16084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16084 raw16084Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw16084 raw16084Labels = mixedMoment B raw16084step0 raw16084step0Labels := by
      have ha : raw16084step0 = (fun i j => raw16084 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16084step0 raw16084; decide +kernel
      have hl : raw16084step0Labels = raw16084Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16084 raw16084Labels permutation658 permutation3
    mixedMoment B raw16084step0 raw16084step0Labels = mixedMoment B raw16084step1 raw16084step1Labels := by
      have ha : raw16084step1 = -raw16084step0 := by apply Matrix.ext; change ∀ i j, raw16084step1 i j = -(raw16084step0 i j); unfold raw16084step1 raw16084step0; decide +kernel
      have hl : raw16084step1Labels = raw16084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw16085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16085step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16085 raw16085Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw16085 raw16085Labels = mixedMoment B raw16085step0 raw16085step0Labels := by
      have ha : raw16085step0 = (fun i j => raw16085 (permutation305 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16085step0 raw16085; decide +kernel
      have hl : raw16085step0Labels = raw16085Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16085 raw16085Labels permutation305 permutation7
    mixedMoment B raw16085step0 raw16085step0Labels = mixedMoment B raw16085step1 raw16085step1Labels := by
      have ha : raw16085step1 = -raw16085step0 := by apply Matrix.ext; change ∀ i j, raw16085step1 i j = -(raw16085step0 i j); unfold raw16085step1 raw16085step0; decide +kernel
      have hl : raw16085step1Labels = raw16085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16085step1 raw16085step1Labels = mixedMoment B raw16085step2 raw16085step2Labels := by
      have ha : raw16085step2 = raw16085step1 := by apply Matrix.ext; unfold raw16085step2 raw16085step1; decide +kernel
      have hl : raw16085step1Labels = labelEmbedding1 ∘ raw16085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16085step1 raw16085step1Labels raw16085step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw16086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16086 raw16086Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw16086 raw16086Labels = mixedMoment B raw16086step0 raw16086step0Labels := by
      have ha : raw16086step0 = (fun i j => raw16086 (permutation356 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16086step0 raw16086; decide +kernel
      have hl : raw16086step0Labels = raw16086Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16086 raw16086Labels permutation356 permutation5
    mixedMoment B raw16086step0 raw16086step0Labels = mixedMoment B raw16086step1 raw16086step1Labels := by
      have ha : raw16086step1 = -raw16086step0 := by apply Matrix.ext; change ∀ i j, raw16086step1 i j = -(raw16086step0 i j); unfold raw16086step1 raw16086step0; decide +kernel
      have hl : raw16086step1Labels = raw16086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16086step1 raw16086step1Labels = mixedMoment B raw16086step2 raw16086step2Labels := by
      have ha : raw16086step2 = raw16086step1 := by apply Matrix.ext; unfold raw16086step2 raw16086step1; decide +kernel
      have hl : raw16086step1Labels = labelEmbedding1 ∘ raw16086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16086step1 raw16086step1Labels raw16086step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw16087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16087 raw16087Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw16087 raw16087Labels = mixedMoment B raw16087step0 raw16087step0Labels := by
      have ha : raw16087step0 = (fun i j => raw16087 (permutation305 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16087step0 raw16087; decide +kernel
      have hl : raw16087step0Labels = raw16087Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16087 raw16087Labels permutation305 permutation7
    mixedMoment B raw16087step0 raw16087step0Labels = mixedMoment B raw16087step1 raw16087step1Labels := by
      have ha : raw16087step1 = -raw16087step0 := by apply Matrix.ext; change ∀ i j, raw16087step1 i j = -(raw16087step0 i j); unfold raw16087step1 raw16087step0; decide +kernel
      have hl : raw16087step1Labels = raw16087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16087step1 raw16087step1Labels = mixedMoment B raw16087step2 raw16087step2Labels := by
      have ha : raw16087step2 = raw16087step1 := by apply Matrix.ext; unfold raw16087step2 raw16087step1; decide +kernel
      have hl : raw16087step1Labels = labelEmbedding1 ∘ raw16087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16087step1 raw16087step1Labels raw16087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw16088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16088step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16088 raw16088Labels = mixedMoment B node3991 node3991Labels := by
  calc
    mixedMoment B raw16088 raw16088Labels = mixedMoment B raw16088step0 raw16088step0Labels := by
      have ha : raw16088step0 = (fun i j => raw16088 (permutation305 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16088step0 raw16088; decide +kernel
      have hl : raw16088step0Labels = raw16088Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16088 raw16088Labels permutation305 permutation7
    mixedMoment B raw16088step0 raw16088step0Labels = mixedMoment B raw16088step1 raw16088step1Labels := by
      have ha : raw16088step1 = -raw16088step0 := by apply Matrix.ext; change ∀ i j, raw16088step1 i j = -(raw16088step0 i j); unfold raw16088step1 raw16088step0; decide +kernel
      have hl : raw16088step1Labels = raw16088step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16088step1 raw16088step1Labels = mixedMoment B raw16088step2 raw16088step2Labels := by
      have ha : raw16088step2 = raw16088step1 := by apply Matrix.ext; unfold raw16088step2 raw16088step1; decide +kernel
      have hl : raw16088step1Labels = labelEmbedding1 ∘ raw16088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16088step1 raw16088step1Labels raw16088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3991 node3991Labels := by rfl

def raw16089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16089step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16089step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16089 raw16089Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw16089 raw16089Labels = mixedMoment B raw16089step0 raw16089step0Labels := by
      have ha : raw16089step0 = (fun i j => raw16089 (permutation305 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16089step0 raw16089; decide +kernel
      have hl : raw16089step0Labels = raw16089Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16089 raw16089Labels permutation305 permutation7
    mixedMoment B raw16089step0 raw16089step0Labels = mixedMoment B raw16089step1 raw16089step1Labels := by
      have ha : raw16089step1 = -raw16089step0 := by apply Matrix.ext; change ∀ i j, raw16089step1 i j = -(raw16089step0 i j); unfold raw16089step1 raw16089step0; decide +kernel
      have hl : raw16089step1Labels = raw16089step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16089step1 raw16089step1Labels = mixedMoment B raw16089step2 raw16089step2Labels := by
      have ha : raw16089step2 = raw16089step1 := by apply Matrix.ext; unfold raw16089step2 raw16089step1; decide +kernel
      have hl : raw16089step1Labels = labelEmbedding1 ∘ raw16089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16089step1 raw16089step1Labels raw16089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw16090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16090 raw16090Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw16090 raw16090Labels = mixedMoment B raw16090step0 raw16090step0Labels := by
      have ha : raw16090step0 = (fun i j => raw16090 (permutation191 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16090step0 raw16090; decide +kernel
      have hl : raw16090step0Labels = raw16090Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16090 raw16090Labels permutation191 permutation5
    mixedMoment B raw16090step0 raw16090step0Labels = mixedMoment B raw16090step1 raw16090step1Labels := by
      have ha : raw16090step1 = -raw16090step0 := by apply Matrix.ext; change ∀ i j, raw16090step1 i j = -(raw16090step0 i j); unfold raw16090step1 raw16090step0; decide +kernel
      have hl : raw16090step1Labels = raw16090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16090step1 raw16090step1Labels = mixedMoment B raw16090step2 raw16090step2Labels := by
      have ha : raw16090step2 = raw16090step1 := by apply Matrix.ext; unfold raw16090step2 raw16090step1; decide +kernel
      have hl : raw16090step1Labels = labelEmbedding1 ∘ raw16090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16090step1 raw16090step1Labels raw16090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw16091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16091step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16091step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16091 raw16091Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw16091 raw16091Labels = mixedMoment B raw16091step0 raw16091step0Labels := by
      have ha : raw16091step0 = (fun i j => raw16091 (permutation191 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16091step0 raw16091; decide +kernel
      have hl : raw16091step0Labels = raw16091Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16091 raw16091Labels permutation191 permutation5
    mixedMoment B raw16091step0 raw16091step0Labels = mixedMoment B raw16091step1 raw16091step1Labels := by
      have ha : raw16091step1 = -raw16091step0 := by apply Matrix.ext; change ∀ i j, raw16091step1 i j = -(raw16091step0 i j); unfold raw16091step1 raw16091step0; decide +kernel
      have hl : raw16091step1Labels = raw16091step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16091step1 raw16091step1Labels = mixedMoment B raw16091step2 raw16091step2Labels := by
      have ha : raw16091step2 = raw16091step1 := by apply Matrix.ext; unfold raw16091step2 raw16091step1; decide +kernel
      have hl : raw16091step1Labels = labelEmbedding1 ∘ raw16091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16091step1 raw16091step1Labels raw16091step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw16092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16092step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16092step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16092 raw16092Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw16092 raw16092Labels = mixedMoment B raw16092step0 raw16092step0Labels := by
      have ha : raw16092step0 = (fun i j => raw16092 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16092step0 raw16092; decide +kernel
      have hl : raw16092step0Labels = raw16092Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16092 raw16092Labels permutation185 permutation5
    mixedMoment B raw16092step0 raw16092step0Labels = mixedMoment B raw16092step1 raw16092step1Labels := by
      have ha : raw16092step1 = -raw16092step0 := by apply Matrix.ext; change ∀ i j, raw16092step1 i j = -(raw16092step0 i j); unfold raw16092step1 raw16092step0; decide +kernel
      have hl : raw16092step1Labels = raw16092step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16092step1 raw16092step1Labels = mixedMoment B raw16092step2 raw16092step2Labels := by
      have ha : raw16092step2 = raw16092step1 := by apply Matrix.ext; unfold raw16092step2 raw16092step1; decide +kernel
      have hl : raw16092step1Labels = labelEmbedding1 ∘ raw16092step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16092step1 raw16092step1Labels raw16092step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw16093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16093step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16093step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16093 raw16093Labels = mixedMoment B node3822 node3822Labels := by
  calc
    mixedMoment B raw16093 raw16093Labels = mixedMoment B raw16093step0 raw16093step0Labels := by
      have ha : raw16093step0 = (fun i j => raw16093 (permutation191 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16093step0 raw16093; decide +kernel
      have hl : raw16093step0Labels = raw16093Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16093 raw16093Labels permutation191 permutation5
    mixedMoment B raw16093step0 raw16093step0Labels = mixedMoment B raw16093step1 raw16093step1Labels := by
      have ha : raw16093step1 = -raw16093step0 := by apply Matrix.ext; change ∀ i j, raw16093step1 i j = -(raw16093step0 i j); unfold raw16093step1 raw16093step0; decide +kernel
      have hl : raw16093step1Labels = raw16093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16093step1 raw16093step1Labels = mixedMoment B raw16093step2 raw16093step2Labels := by
      have ha : raw16093step2 = raw16093step1 := by apply Matrix.ext; unfold raw16093step2 raw16093step1; decide +kernel
      have hl : raw16093step1Labels = labelEmbedding1 ∘ raw16093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16093step1 raw16093step1Labels raw16093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3822 node3822Labels := by rfl

def raw16094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16094step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16094 raw16094Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw16094 raw16094Labels = mixedMoment B raw16094step0 raw16094step0Labels := by
      have ha : raw16094step0 = (fun i j => raw16094 (permutation193 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16094step0 raw16094; decide +kernel
      have hl : raw16094step0Labels = raw16094Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16094 raw16094Labels permutation193 permutation5
    mixedMoment B raw16094step0 raw16094step0Labels = mixedMoment B raw16094step1 raw16094step1Labels := by
      have ha : raw16094step1 = -raw16094step0 := by apply Matrix.ext; change ∀ i j, raw16094step1 i j = -(raw16094step0 i j); unfold raw16094step1 raw16094step0; decide +kernel
      have hl : raw16094step1Labels = raw16094step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16094step1 raw16094step1Labels = mixedMoment B raw16094step2 raw16094step2Labels := by
      have ha : raw16094step2 = raw16094step1 := by apply Matrix.ext; unfold raw16094step2 raw16094step1; decide +kernel
      have hl : raw16094step1Labels = labelEmbedding1 ∘ raw16094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16094step1 raw16094step1Labels raw16094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw16095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16095step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16095step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16095 raw16095Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw16095 raw16095Labels = mixedMoment B raw16095step0 raw16095step0Labels := by
      have ha : raw16095step0 = (fun i j => raw16095 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16095step0 raw16095; decide +kernel
      have hl : raw16095step0Labels = raw16095Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16095 raw16095Labels permutation188 permutation5
    mixedMoment B raw16095step0 raw16095step0Labels = mixedMoment B raw16095step1 raw16095step1Labels := by
      have ha : raw16095step1 = -raw16095step0 := by apply Matrix.ext; change ∀ i j, raw16095step1 i j = -(raw16095step0 i j); unfold raw16095step1 raw16095step0; decide +kernel
      have hl : raw16095step1Labels = raw16095step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16095step1 raw16095step1Labels = mixedMoment B raw16095step2 raw16095step2Labels := by
      have ha : raw16095step2 = raw16095step1 := by apply Matrix.ext; unfold raw16095step2 raw16095step1; decide +kernel
      have hl : raw16095step1Labels = labelEmbedding1 ∘ raw16095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16095step1 raw16095step1Labels raw16095step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw16096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16096step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16096 raw16096Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw16096 raw16096Labels = mixedMoment B raw16096step0 raw16096step0Labels := by
      have ha : raw16096step0 = (fun i j => raw16096 (permutation305 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16096step0 raw16096; decide +kernel
      have hl : raw16096step0Labels = raw16096Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16096 raw16096Labels permutation305 permutation7
    mixedMoment B raw16096step0 raw16096step0Labels = mixedMoment B raw16096step1 raw16096step1Labels := by
      have ha : raw16096step1 = -raw16096step0 := by apply Matrix.ext; change ∀ i j, raw16096step1 i j = -(raw16096step0 i j); unfold raw16096step1 raw16096step0; decide +kernel
      have hl : raw16096step1Labels = raw16096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16096step1 raw16096step1Labels = mixedMoment B raw16096step2 raw16096step2Labels := by
      have ha : raw16096step2 = raw16096step1 := by apply Matrix.ext; unfold raw16096step2 raw16096step1; decide +kernel
      have hl : raw16096step1Labels = labelEmbedding1 ∘ raw16096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16096step1 raw16096step1Labels raw16096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

def raw16097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw16097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16097step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw16097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16097 raw16097Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw16097 raw16097Labels = mixedMoment B raw16097step0 raw16097step0Labels := by
      have ha : raw16097step0 = (fun i j => raw16097 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16097step0 raw16097; decide +kernel
      have hl : raw16097step0Labels = raw16097Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16097 raw16097Labels permutation208 permutation5
    mixedMoment B raw16097step0 raw16097step0Labels = mixedMoment B raw16097step1 raw16097step1Labels := by
      have ha : raw16097step1 = -raw16097step0 := by apply Matrix.ext; change ∀ i j, raw16097step1 i j = -(raw16097step0 i j); unfold raw16097step1 raw16097step0; decide +kernel
      have hl : raw16097step1Labels = raw16097step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16097step1 raw16097step1Labels = mixedMoment B raw16097step2 raw16097step2Labels := by
      have ha : raw16097step2 = raw16097step1 := by apply Matrix.ext; unfold raw16097step2 raw16097step1; decide +kernel
      have hl : raw16097step1Labels = labelEmbedding1 ∘ raw16097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16097step1 raw16097step1Labels raw16097step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3900 node3900Labels := by rfl

def raw16098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16098step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16098step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16098 raw16098Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw16098 raw16098Labels = mixedMoment B raw16098step0 raw16098step0Labels := by
      have ha : raw16098step0 = (fun i j => raw16098 (permutation230 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16098step0 raw16098; decide +kernel
      have hl : raw16098step0Labels = raw16098Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16098 raw16098Labels permutation230 permutation5
    mixedMoment B raw16098step0 raw16098step0Labels = mixedMoment B raw16098step1 raw16098step1Labels := by
      have ha : raw16098step1 = -raw16098step0 := by apply Matrix.ext; change ∀ i j, raw16098step1 i j = -(raw16098step0 i j); unfold raw16098step1 raw16098step0; decide +kernel
      have hl : raw16098step1Labels = raw16098step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16098step1 raw16098step1Labels = mixedMoment B raw16098step2 raw16098step2Labels := by
      have ha : raw16098step2 = raw16098step1 := by apply Matrix.ext; unfold raw16098step2 raw16098step1; decide +kernel
      have hl : raw16098step1Labels = labelEmbedding1 ∘ raw16098step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16098step1 raw16098step1Labels raw16098step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw16099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw16099step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw16099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16099step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw16099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16099 raw16099Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw16099 raw16099Labels = mixedMoment B raw16099step0 raw16099step0Labels := by
      have ha : raw16099step0 = (fun i j => raw16099 (permutation192 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16099step0 raw16099; decide +kernel
      have hl : raw16099step0Labels = raw16099Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16099 raw16099Labels permutation192 permutation5
    mixedMoment B raw16099step0 raw16099step0Labels = mixedMoment B raw16099step1 raw16099step1Labels := by
      have ha : raw16099step1 = -raw16099step0 := by apply Matrix.ext; change ∀ i j, raw16099step1 i j = -(raw16099step0 i j); unfold raw16099step1 raw16099step0; decide +kernel
      have hl : raw16099step1Labels = raw16099step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16099step1 raw16099step1Labels = mixedMoment B raw16099step2 raw16099step2Labels := by
      have ha : raw16099step2 = raw16099step1 := by apply Matrix.ext; unfold raw16099step2 raw16099step1; decide +kernel
      have hl : raw16099step1Labels = labelEmbedding1 ∘ raw16099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16099step1 raw16099step1Labels raw16099step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw16100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16100step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16100step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16100 raw16100Labels = mixedMoment B node2017 node2017Labels := by
  calc
    mixedMoment B raw16100 raw16100Labels = mixedMoment B raw16100step0 raw16100step0Labels := by
      have ha : raw16100step0 = (fun i j => raw16100 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16100step0 raw16100; decide +kernel
      have hl : raw16100step0Labels = raw16100Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16100 raw16100Labels permutation189 permutation5
    mixedMoment B raw16100step0 raw16100step0Labels = mixedMoment B raw16100step1 raw16100step1Labels := by
      have ha : raw16100step1 = -raw16100step0 := by apply Matrix.ext; change ∀ i j, raw16100step1 i j = -(raw16100step0 i j); unfold raw16100step1 raw16100step0; decide +kernel
      have hl : raw16100step1Labels = raw16100step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16100step1 raw16100step1Labels = mixedMoment B raw16100step2 raw16100step2Labels := by
      have ha : raw16100step2 = raw16100step1 := by apply Matrix.ext; unfold raw16100step2 raw16100step1; decide +kernel
      have hl : raw16100step1Labels = labelEmbedding1 ∘ raw16100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16100step1 raw16100step1Labels raw16100step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2017 node2017Labels := by rfl

def raw16101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16101step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16101step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16101step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16101 raw16101Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw16101 raw16101Labels = mixedMoment B raw16101step0 raw16101step0Labels := by
      have ha : raw16101step0 = (fun i j => raw16101 (permutation179 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16101step0 raw16101; decide +kernel
      have hl : raw16101step0Labels = raw16101Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16101 raw16101Labels permutation179 permutation5
    mixedMoment B raw16101step0 raw16101step0Labels = mixedMoment B raw16101step1 raw16101step1Labels := by
      have ha : raw16101step1 = -raw16101step0 := by apply Matrix.ext; change ∀ i j, raw16101step1 i j = -(raw16101step0 i j); unfold raw16101step1 raw16101step0; decide +kernel
      have hl : raw16101step1Labels = raw16101step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16101step1 raw16101step1Labels = mixedMoment B raw16101step2 raw16101step2Labels := by
      have ha : raw16101step2 = raw16101step1 := by apply Matrix.ext; unfold raw16101step2 raw16101step1; decide +kernel
      have hl : raw16101step1Labels = labelEmbedding1 ∘ raw16101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16101step1 raw16101step1Labels raw16101step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw16102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16102 raw16102Labels = mixedMoment B node3688 node3688Labels := by
  calc
    mixedMoment B raw16102 raw16102Labels = mixedMoment B raw16102step0 raw16102step0Labels := by
      have ha : raw16102step0 = (fun i j => raw16102 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16102step0 raw16102; decide +kernel
      have hl : raw16102step0Labels = raw16102Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16102 raw16102Labels permutation189 permutation5
    mixedMoment B raw16102step0 raw16102step0Labels = mixedMoment B raw16102step1 raw16102step1Labels := by
      have ha : raw16102step1 = -raw16102step0 := by apply Matrix.ext; change ∀ i j, raw16102step1 i j = -(raw16102step0 i j); unfold raw16102step1 raw16102step0; decide +kernel
      have hl : raw16102step1Labels = raw16102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16102step1 raw16102step1Labels = mixedMoment B raw16102step2 raw16102step2Labels := by
      have ha : raw16102step2 = raw16102step1 := by apply Matrix.ext; unfold raw16102step2 raw16102step1; decide +kernel
      have hl : raw16102step1Labels = labelEmbedding1 ∘ raw16102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16102step1 raw16102step1Labels raw16102step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3688 node3688Labels := by rfl

def raw16103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16103step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16103step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16103 raw16103Labels = mixedMoment B node3819 node3819Labels := by
  calc
    mixedMoment B raw16103 raw16103Labels = mixedMoment B raw16103step0 raw16103step0Labels := by
      have ha : raw16103step0 = (fun i j => raw16103 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16103step0 raw16103; decide +kernel
      have hl : raw16103step0Labels = raw16103Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16103 raw16103Labels permutation189 permutation5
    mixedMoment B raw16103step0 raw16103step0Labels = mixedMoment B raw16103step1 raw16103step1Labels := by
      have ha : raw16103step1 = -raw16103step0 := by apply Matrix.ext; change ∀ i j, raw16103step1 i j = -(raw16103step0 i j); unfold raw16103step1 raw16103step0; decide +kernel
      have hl : raw16103step1Labels = raw16103step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16103step1 raw16103step1Labels = mixedMoment B raw16103step2 raw16103step2Labels := by
      have ha : raw16103step2 = raw16103step1 := by apply Matrix.ext; unfold raw16103step2 raw16103step1; decide +kernel
      have hl : raw16103step1Labels = labelEmbedding1 ∘ raw16103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16103step1 raw16103step1Labels raw16103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3819 node3819Labels := by rfl

def raw16104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16104step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16104step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16104 raw16104Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw16104 raw16104Labels = mixedMoment B raw16104step0 raw16104step0Labels := by
      have ha : raw16104step0 = (fun i j => raw16104 (permutation192 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16104step0 raw16104; decide +kernel
      have hl : raw16104step0Labels = raw16104Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16104 raw16104Labels permutation192 permutation5
    mixedMoment B raw16104step0 raw16104step0Labels = mixedMoment B raw16104step1 raw16104step1Labels := by
      have ha : raw16104step1 = -raw16104step0 := by apply Matrix.ext; change ∀ i j, raw16104step1 i j = -(raw16104step0 i j); unfold raw16104step1 raw16104step0; decide +kernel
      have hl : raw16104step1Labels = raw16104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16104step1 raw16104step1Labels = mixedMoment B raw16104step2 raw16104step2Labels := by
      have ha : raw16104step2 = raw16104step1 := by apply Matrix.ext; unfold raw16104step2 raw16104step1; decide +kernel
      have hl : raw16104step1Labels = labelEmbedding1 ∘ raw16104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16104step1 raw16104step1Labels raw16104step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw16105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw16105step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16105step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16105step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16105 raw16105Labels = mixedMoment B node2044 node2044Labels := by
  calc
    mixedMoment B raw16105 raw16105Labels = mixedMoment B raw16105step0 raw16105step0Labels := by
      have ha : raw16105step0 = (fun i j => raw16105 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16105step0 raw16105; decide +kernel
      have hl : raw16105step0Labels = raw16105Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16105 raw16105Labels permutation176 permutation5
    mixedMoment B raw16105step0 raw16105step0Labels = mixedMoment B raw16105step1 raw16105step1Labels := by
      have ha : raw16105step1 = -raw16105step0 := by apply Matrix.ext; change ∀ i j, raw16105step1 i j = -(raw16105step0 i j); unfold raw16105step1 raw16105step0; decide +kernel
      have hl : raw16105step1Labels = raw16105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16105step1 raw16105step1Labels = mixedMoment B raw16105step2 raw16105step2Labels := by
      have ha : raw16105step2 = raw16105step1 := by apply Matrix.ext; unfold raw16105step2 raw16105step1; decide +kernel
      have hl : raw16105step1Labels = labelEmbedding1 ∘ raw16105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16105step1 raw16105step1Labels raw16105step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2044 node2044Labels := by rfl

def raw16106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw16106step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16106step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16106 raw16106Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw16106 raw16106Labels = mixedMoment B raw16106step0 raw16106step0Labels := by
      have ha : raw16106step0 = (fun i j => raw16106 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16106step0 raw16106; decide +kernel
      have hl : raw16106step0Labels = raw16106Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16106 raw16106Labels permutation176 permutation5
    mixedMoment B raw16106step0 raw16106step0Labels = mixedMoment B raw16106step1 raw16106step1Labels := by
      have ha : raw16106step1 = -raw16106step0 := by apply Matrix.ext; change ∀ i j, raw16106step1 i j = -(raw16106step0 i j); unfold raw16106step1 raw16106step0; decide +kernel
      have hl : raw16106step1Labels = raw16106step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16106step1 raw16106step1Labels = mixedMoment B raw16106step2 raw16106step2Labels := by
      have ha : raw16106step2 = raw16106step1 := by apply Matrix.ext; unfold raw16106step2 raw16106step1; decide +kernel
      have hl : raw16106step1Labels = labelEmbedding1 ∘ raw16106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16106step1 raw16106step1Labels raw16106step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

def raw16107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw16107step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16107step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw16107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16107 raw16107Labels = mixedMoment B node3700 node3700Labels := by
  calc
    mixedMoment B raw16107 raw16107Labels = mixedMoment B raw16107step0 raw16107step0Labels := by
      have ha : raw16107step0 = (fun i j => raw16107 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16107step0 raw16107; decide +kernel
      have hl : raw16107step0Labels = raw16107Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16107 raw16107Labels permutation176 permutation5
    mixedMoment B raw16107step0 raw16107step0Labels = mixedMoment B raw16107step1 raw16107step1Labels := by
      have ha : raw16107step1 = -raw16107step0 := by apply Matrix.ext; change ∀ i j, raw16107step1 i j = -(raw16107step0 i j); unfold raw16107step1 raw16107step0; decide +kernel
      have hl : raw16107step1Labels = raw16107step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16107step1 raw16107step1Labels = mixedMoment B raw16107step2 raw16107step2Labels := by
      have ha : raw16107step2 = raw16107step1 := by apply Matrix.ext; unfold raw16107step2 raw16107step1; decide +kernel
      have hl : raw16107step1Labels = labelEmbedding1 ∘ raw16107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16107step1 raw16107step1Labels raw16107step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3700 node3700Labels := by rfl

def raw16108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw16108step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw16108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16108step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw16108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16108 raw16108Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw16108 raw16108Labels = mixedMoment B raw16108step0 raw16108step0Labels := by
      have ha : raw16108step0 = (fun i j => raw16108 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16108step0 raw16108; decide +kernel
      have hl : raw16108step0Labels = raw16108Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16108 raw16108Labels permutation182 permutation5
    mixedMoment B raw16108step0 raw16108step0Labels = mixedMoment B raw16108step1 raw16108step1Labels := by
      have ha : raw16108step1 = -raw16108step0 := by apply Matrix.ext; change ∀ i j, raw16108step1 i j = -(raw16108step0 i j); unfold raw16108step1 raw16108step0; decide +kernel
      have hl : raw16108step1Labels = raw16108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16108step1 raw16108step1Labels = mixedMoment B raw16108step2 raw16108step2Labels := by
      have ha : raw16108step2 = raw16108step1 := by apply Matrix.ext; unfold raw16108step2 raw16108step1; decide +kernel
      have hl : raw16108step1Labels = labelEmbedding1 ∘ raw16108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16108step1 raw16108step1Labels raw16108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

def raw16109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw16109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16109step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16109step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16109step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16109 raw16109Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw16109 raw16109Labels = mixedMoment B raw16109step0 raw16109step0Labels := by
      have ha : raw16109step0 = (fun i j => raw16109 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16109step0 raw16109; decide +kernel
      have hl : raw16109step0Labels = raw16109Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16109 raw16109Labels permutation194 permutation5
    mixedMoment B raw16109step0 raw16109step0Labels = mixedMoment B raw16109step1 raw16109step1Labels := by
      have ha : raw16109step1 = -raw16109step0 := by apply Matrix.ext; change ∀ i j, raw16109step1 i j = -(raw16109step0 i j); unfold raw16109step1 raw16109step0; decide +kernel
      have hl : raw16109step1Labels = raw16109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16109step1 raw16109step1Labels = mixedMoment B raw16109step2 raw16109step2Labels := by
      have ha : raw16109step2 = raw16109step1 := by apply Matrix.ext; unfold raw16109step2 raw16109step1; decide +kernel
      have hl : raw16109step1Labels = labelEmbedding1 ∘ raw16109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16109step1 raw16109step1Labels raw16109step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw16110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw16110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16110step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw16110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16110 raw16110Labels = mixedMoment B node2015 node2015Labels := by
  calc
    mixedMoment B raw16110 raw16110Labels = mixedMoment B raw16110step0 raw16110step0Labels := by
      have ha : raw16110step0 = (fun i j => raw16110 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16110step0 raw16110; decide +kernel
      have hl : raw16110step0Labels = raw16110Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16110 raw16110Labels permutation188 permutation5
    mixedMoment B raw16110step0 raw16110step0Labels = mixedMoment B raw16110step1 raw16110step1Labels := by
      have ha : raw16110step1 = -raw16110step0 := by apply Matrix.ext; change ∀ i j, raw16110step1 i j = -(raw16110step0 i j); unfold raw16110step1 raw16110step0; decide +kernel
      have hl : raw16110step1Labels = raw16110step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16110step1 raw16110step1Labels = mixedMoment B raw16110step2 raw16110step2Labels := by
      have ha : raw16110step2 = raw16110step1 := by apply Matrix.ext; unfold raw16110step2 raw16110step1; decide +kernel
      have hl : raw16110step1Labels = labelEmbedding1 ∘ raw16110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16110step1 raw16110step1Labels raw16110step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2015 node2015Labels := by rfl

def raw16111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16111 raw16111Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw16111 raw16111Labels = mixedMoment B raw16111step0 raw16111step0Labels := by
      have ha : raw16111step0 = (fun i j => raw16111 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16111step0 raw16111; decide +kernel
      have hl : raw16111step0Labels = raw16111Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16111 raw16111Labels permutation662 permutation5
    mixedMoment B raw16111step0 raw16111step0Labels = mixedMoment B raw16111step1 raw16111step1Labels := by
      have ha : raw16111step1 = raw16111step0 := by apply Matrix.ext; unfold raw16111step1 raw16111step0; decide +kernel
      have hl : raw16111step0Labels = labelEmbedding1 ∘ raw16111step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16111step0 raw16111step0Labels raw16111step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw16112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16112 raw16112Labels = mixedMoment B node3499 node3499Labels := by
  calc
    mixedMoment B raw16112 raw16112Labels = mixedMoment B raw16112step0 raw16112step0Labels := by
      have ha : raw16112step0 = (fun i j => raw16112 (permutation654 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16112step0 raw16112; decide +kernel
      have hl : raw16112step0Labels = raw16112Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16112 raw16112Labels permutation654 permutation5
    mixedMoment B raw16112step0 raw16112step0Labels = mixedMoment B raw16112step1 raw16112step1Labels := by
      have ha : raw16112step1 = raw16112step0 := by apply Matrix.ext; unfold raw16112step1 raw16112step0; decide +kernel
      have hl : raw16112step0Labels = labelEmbedding1 ∘ raw16112step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16112step0 raw16112step0Labels raw16112step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3499 node3499Labels := by rfl

def raw16113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16113step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16113step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16113 raw16113Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw16113 raw16113Labels = mixedMoment B raw16113step0 raw16113step0Labels := by
      have ha : raw16113step0 = (fun i j => raw16113 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16113step0 raw16113; decide +kernel
      have hl : raw16113step0Labels = raw16113Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16113 raw16113Labels permutation622 permutation5
    mixedMoment B raw16113step0 raw16113step0Labels = mixedMoment B raw16113step1 raw16113step1Labels := by
      have ha : raw16113step1 = raw16113step0 := by apply Matrix.ext; unfold raw16113step1 raw16113step0; decide +kernel
      have hl : raw16113step0Labels = labelEmbedding1 ∘ raw16113step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16113step0 raw16113step0Labels raw16113step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw16114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw16114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16114 raw16114Labels = mixedMoment B node3502 node3502Labels := by
  calc
    mixedMoment B raw16114 raw16114Labels = mixedMoment B raw16114step0 raw16114step0Labels := by
      have ha : raw16114step0 = (fun i j => raw16114 (permutation653 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16114step0 raw16114; decide +kernel
      have hl : raw16114step0Labels = raw16114Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16114 raw16114Labels permutation653 permutation5
    mixedMoment B raw16114step0 raw16114step0Labels = mixedMoment B raw16114step1 raw16114step1Labels := by
      have ha : raw16114step1 = raw16114step0 := by apply Matrix.ext; unfold raw16114step1 raw16114step0; decide +kernel
      have hl : raw16114step0Labels = labelEmbedding1 ∘ raw16114step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16114step0 raw16114step0Labels raw16114step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3502 node3502Labels := by rfl

def raw16115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16115 raw16115Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw16115 raw16115Labels = mixedMoment B raw16115step0 raw16115step0Labels := by
      have ha : raw16115step0 = (fun i j => raw16115 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16115step0 raw16115; decide +kernel
      have hl : raw16115step0Labels = raw16115Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16115 raw16115Labels permutation682 permutation2
    mixedMoment B raw16115step0 raw16115step0Labels = mixedMoment B raw16115step1 raw16115step1Labels := by
      have ha : raw16115step1 = -raw16115step0 := by apply Matrix.ext; change ∀ i j, raw16115step1 i j = -(raw16115step0 i j); unfold raw16115step1 raw16115step0; decide +kernel
      have hl : raw16115step1Labels = raw16115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw16116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16116 raw16116Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw16116 raw16116Labels = mixedMoment B raw16116step0 raw16116step0Labels := by
      have ha : raw16116step0 = (fun i j => raw16116 (permutation193 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16116step0 raw16116; decide +kernel
      have hl : raw16116step0Labels = raw16116Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16116 raw16116Labels permutation193 permutation4
    mixedMoment B raw16116step0 raw16116step0Labels = mixedMoment B raw16116step1 raw16116step1Labels := by
      have ha : raw16116step1 = -raw16116step0 := by apply Matrix.ext; change ∀ i j, raw16116step1 i j = -(raw16116step0 i j); unfold raw16116step1 raw16116step0; decide +kernel
      have hl : raw16116step1Labels = raw16116step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw16117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16117 raw16117Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw16117 raw16117Labels = mixedMoment B raw16117step0 raw16117step0Labels := by
      have ha : raw16117step0 = (fun i j => raw16117 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16117step0 raw16117; decide +kernel
      have hl : raw16117step0Labels = raw16117Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16117 raw16117Labels permutation158 permutation2
    _ = mixedMoment B node3172 node3172Labels := by rfl

def raw16118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16118 raw16118Labels = mixedMoment B node3176 node3176Labels := by
  calc
    _ = mixedMoment B node3176 node3176Labels := by rfl

def raw16119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16119 raw16119Labels = mixedMoment B node3169 node3169Labels := by
  calc
    mixedMoment B raw16119 raw16119Labels = mixedMoment B raw16119step0 raw16119step0Labels := by
      have ha : raw16119step0 = (fun i j => raw16119 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16119step0 raw16119; decide +kernel
      have hl : raw16119step0Labels = raw16119Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16119 raw16119Labels permutation158 permutation2
    _ = mixedMoment B node3169 node3169Labels := by rfl

def raw16120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw16120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw16120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16120 raw16120Labels = mixedMoment B node2915 node2915Labels := by
  calc
    mixedMoment B raw16120 raw16120Labels = mixedMoment B raw16120step0 raw16120step0Labels := by
      have ha : raw16120step0 = (fun i j => raw16120 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16120step0 raw16120; decide +kernel
      have hl : raw16120step0Labels = raw16120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16120 raw16120Labels permutation682 permutation2
    mixedMoment B raw16120step0 raw16120step0Labels = mixedMoment B raw16120step1 raw16120step1Labels := by
      have ha : raw16120step1 = -raw16120step0 := by apply Matrix.ext; change ∀ i j, raw16120step1 i j = -(raw16120step0 i j); unfold raw16120step1 raw16120step0; decide +kernel
      have hl : raw16120step1Labels = raw16120step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2915 node2915Labels := by rfl

def raw16121 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw16121Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16121step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw16121step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16121step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw16121step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical16121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16121 raw16121Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw16121 raw16121Labels = mixedMoment B raw16121step0 raw16121step0Labels := by
      have hz : ∀ j, raw16121 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw16121step0 = (fun i j => raw16121 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw16121step0 raw16121; decide +kernel
      have hl : raw16121step0Labels = raw16121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16121 raw16121Labels permutation152 hz
    mixedMoment B raw16121step0 raw16121step0Labels = mixedMoment B raw16121step1 raw16121step1Labels := by
      have ha : raw16121step1 = (fun i j => raw16121step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16121step1 raw16121step0; decide +kernel
      have hl : raw16121step1Labels = raw16121step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16121step0 raw16121step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw16122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16122 raw16122Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw16122 raw16122Labels = mixedMoment B raw16122step0 raw16122step0Labels := by
      have ha : raw16122step0 = (fun i j => raw16122 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16122step0 raw16122; decide +kernel
      have hl : raw16122step0Labels = raw16122Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16122 raw16122Labels permutation271 permutation2
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw16123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16123 raw16123Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw16123 raw16123Labels = mixedMoment B raw16123step0 raw16123step0Labels := by
      have ha : raw16123step0 = (fun i j => raw16123 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16123step0 raw16123; decide +kernel
      have hl : raw16123step0Labels = raw16123Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16123 raw16123Labels permutation271 permutation2
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw16124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16124 raw16124Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw16124 raw16124Labels = mixedMoment B raw16124step0 raw16124step0Labels := by
      have ha : raw16124step0 = (fun i j => raw16124 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16124step0 raw16124; decide +kernel
      have hl : raw16124step0Labels = raw16124Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16124 raw16124Labels permutation265 permutation2
    _ = mixedMoment B node3724 node3724Labels := by rfl

def raw16125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16125 raw16125Labels = mixedMoment B node3716 node3716Labels := by
  calc
    mixedMoment B raw16125 raw16125Labels = mixedMoment B raw16125step0 raw16125step0Labels := by
      have ha : raw16125step0 = (fun i j => raw16125 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16125step0 raw16125; decide +kernel
      have hl : raw16125step0Labels = raw16125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16125 raw16125Labels permutation271 permutation2
    _ = mixedMoment B node3716 node3716Labels := by rfl

def raw16126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16126 raw16126Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw16126 raw16126Labels = mixedMoment B raw16126step0 raw16126step0Labels := by
      have ha : raw16126step0 = (fun i j => raw16126 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16126step0 raw16126; decide +kernel
      have hl : raw16126step0Labels = raw16126Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16126 raw16126Labels permutation681 permutation2
    mixedMoment B raw16126step0 raw16126step0Labels = mixedMoment B raw16126step1 raw16126step1Labels := by
      have ha : raw16126step1 = -raw16126step0 := by apply Matrix.ext; change ∀ i j, raw16126step1 i j = -(raw16126step0 i j); unfold raw16126step1 raw16126step0; decide +kernel
      have hl : raw16126step1Labels = raw16126step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw16127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16127 raw16127Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw16127 raw16127Labels = mixedMoment B raw16127step0 raw16127step0Labels := by
      have ha : raw16127step0 = (fun i j => raw16127 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16127step0 raw16127; decide +kernel
      have hl : raw16127step0Labels = raw16127Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16127 raw16127Labels permutation646 permutation2
    mixedMoment B raw16127step0 raw16127step0Labels = mixedMoment B raw16127step1 raw16127step1Labels := by
      have ha : raw16127step1 = -raw16127step0 := by apply Matrix.ext; change ∀ i j, raw16127step1 i j = -(raw16127step0 i j); unfold raw16127step1 raw16127step0; decide +kernel
      have hl : raw16127step1Labels = raw16127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
