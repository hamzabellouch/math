import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5632 raw5632Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw5632 raw5632Labels = mixedMoment B raw5632step0 raw5632step0Labels := by
      have ha : raw5632step0 = (fun i j => raw5632 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5632step0 raw5632; decide +kernel
      have hl : raw5632step0Labels = raw5632Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5632 raw5632Labels permutation676 permutation2
    mixedMoment B raw5632step0 raw5632step0Labels = mixedMoment B raw5632step1 raw5632step1Labels := by
      have ha : raw5632step1 = -raw5632step0 := by apply Matrix.ext; change ∀ i j, raw5632step1 i j = -(raw5632step0 i j); unfold raw5632step1 raw5632step0; decide +kernel
      have hl : raw5632step1Labels = raw5632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw5633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5633 raw5633Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw5633 raw5633Labels = mixedMoment B raw5633step0 raw5633step0Labels := by
      have ha : raw5633step0 = (fun i j => raw5633 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5633step0 raw5633; decide +kernel
      have hl : raw5633step0Labels = raw5633Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5633 raw5633Labels permutation674 permutation2
    mixedMoment B raw5633step0 raw5633step0Labels = mixedMoment B raw5633step1 raw5633step1Labels := by
      have ha : raw5633step1 = -raw5633step0 := by apply Matrix.ext; change ∀ i j, raw5633step1 i j = -(raw5633step0 i j); unfold raw5633step1 raw5633step0; decide +kernel
      have hl : raw5633step1Labels = raw5633step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw5634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw5634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5634 raw5634Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw5634 raw5634Labels = mixedMoment B raw5634step0 raw5634step0Labels := by
      have ha : raw5634step0 = (fun i j => raw5634 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5634step0 raw5634; decide +kernel
      have hl : raw5634step0Labels = raw5634Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5634 raw5634Labels permutation674 permutation2
    mixedMoment B raw5634step0 raw5634step0Labels = mixedMoment B raw5634step1 raw5634step1Labels := by
      have ha : raw5634step1 = -raw5634step0 := by apply Matrix.ext; change ∀ i j, raw5634step1 i j = -(raw5634step0 i j); unfold raw5634step1 raw5634step0; decide +kernel
      have hl : raw5634step1Labels = raw5634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw5635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5635 raw5635Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw5635 raw5635Labels = mixedMoment B raw5635step0 raw5635step0Labels := by
      have ha : raw5635step0 = (fun i j => raw5635 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5635step0 raw5635; decide +kernel
      have hl : raw5635step0Labels = raw5635Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5635 raw5635Labels permutation260 permutation4
    mixedMoment B raw5635step0 raw5635step0Labels = mixedMoment B raw5635step1 raw5635step1Labels := by
      have ha : raw5635step1 = -raw5635step0 := by apply Matrix.ext; change ∀ i j, raw5635step1 i j = -(raw5635step0 i j); unfold raw5635step1 raw5635step0; decide +kernel
      have hl : raw5635step1Labels = raw5635step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw5636 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw5636Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5636step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw5636step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5636step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw5636step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5636step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw5636step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5636 raw5636Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw5636 raw5636Labels = mixedMoment B raw5636step0 raw5636step0Labels := by
      have hz : ∀ j, raw5636 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw5636step0 = (fun i j => raw5636 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw5636step0 raw5636; decide +kernel
      have hl : raw5636step0Labels = raw5636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5636 raw5636Labels permutation152 hz
    mixedMoment B raw5636step0 raw5636step0Labels = mixedMoment B raw5636step1 raw5636step1Labels := by
      have ha : raw5636step1 = (fun i j => raw5636step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5636step1 raw5636step0; decide +kernel
      have hl : raw5636step1Labels = raw5636step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5636step0 raw5636step0Labels permutation146 permutation0
    mixedMoment B raw5636step1 raw5636step1Labels = mixedMoment B raw5636step2 raw5636step2Labels := by
      have ha : raw5636step2 = -raw5636step1 := by apply Matrix.ext; change ∀ i j, raw5636step2 i j = -(raw5636step1 i j); unfold raw5636step2 raw5636step1; decide +kernel
      have hl : raw5636step2Labels = raw5636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw5637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5637 raw5637Labels = mixedMoment B node1464 node1464Labels := by
  calc
    mixedMoment B raw5637 raw5637Labels = mixedMoment B raw5637step0 raw5637step0Labels := by
      have ha : raw5637step0 = (fun i j => raw5637 (permutation263 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5637step0 raw5637; decide +kernel
      have hl : raw5637step0Labels = raw5637Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5637 raw5637Labels permutation263 permutation4
    mixedMoment B raw5637step0 raw5637step0Labels = mixedMoment B raw5637step1 raw5637step1Labels := by
      have ha : raw5637step1 = -raw5637step0 := by apply Matrix.ext; change ∀ i j, raw5637step1 i j = -(raw5637step0 i j); unfold raw5637step1 raw5637step0; decide +kernel
      have hl : raw5637step1Labels = raw5637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1464 node1464Labels := by rfl

def raw5638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5638 raw5638Labels = mixedMoment B node1464 node1464Labels := by
  calc
    mixedMoment B raw5638 raw5638Labels = mixedMoment B raw5638step0 raw5638step0Labels := by
      have ha : raw5638step0 = (fun i j => raw5638 (permutation261 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5638step0 raw5638; decide +kernel
      have hl : raw5638step0Labels = raw5638Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5638 raw5638Labels permutation261 permutation4
    mixedMoment B raw5638step0 raw5638step0Labels = mixedMoment B raw5638step1 raw5638step1Labels := by
      have ha : raw5638step1 = -raw5638step0 := by apply Matrix.ext; change ∀ i j, raw5638step1 i j = -(raw5638step0 i j); unfold raw5638step1 raw5638step0; decide +kernel
      have hl : raw5638step1Labels = raw5638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1464 node1464Labels := by rfl

def raw5639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5639 raw5639Labels = mixedMoment B node1464 node1464Labels := by
  calc
    mixedMoment B raw5639 raw5639Labels = mixedMoment B raw5639step0 raw5639step0Labels := by
      have ha : raw5639step0 = (fun i j => raw5639 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5639step0 raw5639; decide +kernel
      have hl : raw5639step0Labels = raw5639Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5639 raw5639Labels permutation260 permutation4
    mixedMoment B raw5639step0 raw5639step0Labels = mixedMoment B raw5639step1 raw5639step1Labels := by
      have ha : raw5639step1 = -raw5639step0 := by apply Matrix.ext; change ∀ i j, raw5639step1 i j = -(raw5639step0 i j); unfold raw5639step1 raw5639step0; decide +kernel
      have hl : raw5639step1Labels = raw5639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1464 node1464Labels := by rfl

def raw5640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5640 raw5640Labels = mixedMoment B node1467 node1467Labels := by
  calc
    mixedMoment B raw5640 raw5640Labels = mixedMoment B raw5640step0 raw5640step0Labels := by
      have ha : raw5640step0 = (fun i j => raw5640 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5640step0 raw5640; decide +kernel
      have hl : raw5640step0Labels = raw5640Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5640 raw5640Labels permutation260 permutation4
    mixedMoment B raw5640step0 raw5640step0Labels = mixedMoment B raw5640step1 raw5640step1Labels := by
      have ha : raw5640step1 = -raw5640step0 := by apply Matrix.ext; change ∀ i j, raw5640step1 i j = -(raw5640step0 i j); unfold raw5640step1 raw5640step0; decide +kernel
      have hl : raw5640step1Labels = raw5640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1467 node1467Labels := by rfl

def raw5641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5641 raw5641Labels = mixedMoment B node1474 node1474Labels := by
  calc
    _ = mixedMoment B node1474 node1474Labels := by rfl

def raw5642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5642 raw5642Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw5642 raw5642Labels = mixedMoment B raw5642step0 raw5642step0Labels := by
      have ha : raw5642step0 = (fun i j => raw5642 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5642step0 raw5642; decide +kernel
      have hl : raw5642step0Labels = raw5642Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5642 raw5642Labels permutation182 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw5643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5643 raw5643Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw5643 raw5643Labels = mixedMoment B raw5643step0 raw5643step0Labels := by
      have ha : raw5643step0 = (fun i j => raw5643 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5643step0 raw5643; decide +kernel
      have hl : raw5643step0Labels = raw5643Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5643 raw5643Labels permutation206 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw5644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5644 raw5644Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw5644 raw5644Labels = mixedMoment B raw5644step0 raw5644step0Labels := by
      have ha : raw5644step0 = (fun i j => raw5644 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5644step0 raw5644; decide +kernel
      have hl : raw5644step0Labels = raw5644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5644 raw5644Labels permutation243 permutation4
    mixedMoment B raw5644step0 raw5644step0Labels = mixedMoment B raw5644step1 raw5644step1Labels := by
      have ha : raw5644step1 = -raw5644step0 := by apply Matrix.ext; change ∀ i j, raw5644step1 i j = -(raw5644step0 i j); unfold raw5644step1 raw5644step0; decide +kernel
      have hl : raw5644step1Labels = raw5644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3197 node3197Labels := by rfl

def raw5645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5645 raw5645Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw5645 raw5645Labels = mixedMoment B raw5645step0 raw5645step0Labels := by
      have ha : raw5645step0 = (fun i j => raw5645 (permutation263 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5645step0 raw5645; decide +kernel
      have hl : raw5645step0Labels = raw5645Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5645 raw5645Labels permutation263 permutation4
    mixedMoment B raw5645step0 raw5645step0Labels = mixedMoment B raw5645step1 raw5645step1Labels := by
      have ha : raw5645step1 = -raw5645step0 := by apply Matrix.ext; change ∀ i j, raw5645step1 i j = -(raw5645step0 i j); unfold raw5645step1 raw5645step0; decide +kernel
      have hl : raw5645step1Labels = raw5645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3172 node3172Labels := by rfl

def raw5646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5646 raw5646Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw5646 raw5646Labels = mixedMoment B raw5646step0 raw5646step0Labels := by
      have ha : raw5646step0 = (fun i j => raw5646 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5646step0 raw5646; decide +kernel
      have hl : raw5646step0Labels = raw5646Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5646 raw5646Labels permutation158 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw5647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5647 raw5647Labels = mixedMoment B node3202 node3202Labels := by
  calc
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw5648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5648 raw5648Labels = mixedMoment B node3199 node3199Labels := by
  calc
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw5649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw5649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw5649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5649 raw5649Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw5649 raw5649Labels = mixedMoment B raw5649step0 raw5649step0Labels := by
      have ha : raw5649step0 = (fun i j => raw5649 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5649step0 raw5649; decide +kernel
      have hl : raw5649step0Labels = raw5649Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5649 raw5649Labels permutation682 permutation2
    mixedMoment B raw5649step0 raw5649step0Labels = mixedMoment B raw5649step1 raw5649step1Labels := by
      have ha : raw5649step1 = -raw5649step0 := by apply Matrix.ext; change ∀ i j, raw5649step1 i j = -(raw5649step0 i j); unfold raw5649step1 raw5649step0; decide +kernel
      have hl : raw5649step1Labels = raw5649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw5650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5650 raw5650Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw5650 raw5650Labels = mixedMoment B raw5650step0 raw5650step0Labels := by
      have ha : raw5650step0 = (fun i j => raw5650 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5650step0 raw5650; decide +kernel
      have hl : raw5650step0Labels = raw5650Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5650 raw5650Labels permutation176 permutation2
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw5651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5651 raw5651Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw5651 raw5651Labels = mixedMoment B raw5651step0 raw5651step0Labels := by
      have ha : raw5651step0 = (fun i j => raw5651 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5651step0 raw5651; decide +kernel
      have hl : raw5651step0Labels = raw5651Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5651 raw5651Labels permutation200 permutation2
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw5652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw5652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5652 raw5652Labels = mixedMoment B node3179 node3179Labels := by
  calc
    mixedMoment B raw5652 raw5652Labels = mixedMoment B raw5652step0 raw5652step0Labels := by
      have ha : raw5652step0 = (fun i j => raw5652 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5652step0 raw5652; decide +kernel
      have hl : raw5652step0Labels = raw5652Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5652 raw5652Labels permutation260 permutation4
    mixedMoment B raw5652step0 raw5652step0Labels = mixedMoment B raw5652step1 raw5652step1Labels := by
      have ha : raw5652step1 = -raw5652step0 := by apply Matrix.ext; change ∀ i j, raw5652step1 i j = -(raw5652step0 i j); unfold raw5652step1 raw5652step0; decide +kernel
      have hl : raw5652step1Labels = raw5652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3179 node3179Labels := by rfl

def raw5653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5653 raw5653Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw5653 raw5653Labels = mixedMoment B raw5653step0 raw5653step0Labels := by
      have ha : raw5653step0 = (fun i j => raw5653 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5653step0 raw5653; decide +kernel
      have hl : raw5653step0Labels = raw5653Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5653 raw5653Labels permutation241 permutation4
    mixedMoment B raw5653step0 raw5653step0Labels = mixedMoment B raw5653step1 raw5653step1Labels := by
      have ha : raw5653step1 = -raw5653step0 := by apply Matrix.ext; change ∀ i j, raw5653step1 i j = -(raw5653step0 i j); unfold raw5653step1 raw5653step0; decide +kernel
      have hl : raw5653step1Labels = raw5653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3197 node3197Labels := by rfl

def raw5654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5654 raw5654Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw5654 raw5654Labels = mixedMoment B raw5654step0 raw5654step0Labels := by
      have ha : raw5654step0 = (fun i j => raw5654 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5654step0 raw5654; decide +kernel
      have hl : raw5654step0Labels = raw5654Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5654 raw5654Labels permutation240 permutation4
    mixedMoment B raw5654step0 raw5654step0Labels = mixedMoment B raw5654step1 raw5654step1Labels := by
      have ha : raw5654step1 = -raw5654step0 := by apply Matrix.ext; change ∀ i j, raw5654step1 i j = -(raw5654step0 i j); unfold raw5654step1 raw5654step0; decide +kernel
      have hl : raw5654step1Labels = raw5654step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3197 node3197Labels := by rfl

def raw5655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw5655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5655 raw5655Labels = mixedMoment B node2707 node2707Labels := by
  calc
    mixedMoment B raw5655 raw5655Labels = mixedMoment B raw5655step0 raw5655step0Labels := by
      have ha : raw5655step0 = (fun i j => raw5655 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5655step0 raw5655; decide +kernel
      have hl : raw5655step0Labels = raw5655Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5655 raw5655Labels permutation674 permutation2
    mixedMoment B raw5655step0 raw5655step0Labels = mixedMoment B raw5655step1 raw5655step1Labels := by
      have ha : raw5655step1 = -raw5655step0 := by apply Matrix.ext; change ∀ i j, raw5655step1 i j = -(raw5655step0 i j); unfold raw5655step1 raw5655step0; decide +kernel
      have hl : raw5655step1Labels = raw5655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2707 node2707Labels := by rfl

def raw5656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw5656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw5656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5656 raw5656Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw5656 raw5656Labels = mixedMoment B raw5656step0 raw5656step0Labels := by
      have ha : raw5656step0 = (fun i j => raw5656 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5656step0 raw5656; decide +kernel
      have hl : raw5656step0Labels = raw5656Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5656 raw5656Labels permutation676 permutation2
    mixedMoment B raw5656step0 raw5656step0Labels = mixedMoment B raw5656step1 raw5656step1Labels := by
      have ha : raw5656step1 = -raw5656step0 := by apply Matrix.ext; change ∀ i j, raw5656step1 i j = -(raw5656step0 i j); unfold raw5656step1 raw5656step0; decide +kernel
      have hl : raw5656step1Labels = raw5656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw5657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw5657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw5657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5657 raw5657Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw5657 raw5657Labels = mixedMoment B raw5657step0 raw5657step0Labels := by
      have ha : raw5657step0 = (fun i j => raw5657 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5657step0 raw5657; decide +kernel
      have hl : raw5657step0Labels = raw5657Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5657 raw5657Labels permutation674 permutation2
    mixedMoment B raw5657step0 raw5657step0Labels = mixedMoment B raw5657step1 raw5657step1Labels := by
      have ha : raw5657step1 = -raw5657step0 := by apply Matrix.ext; change ∀ i j, raw5657step1 i j = -(raw5657step0 i j); unfold raw5657step1 raw5657step0; decide +kernel
      have hl : raw5657step1Labels = raw5657step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw5658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5658step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5658 raw5658Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw5658 raw5658Labels = mixedMoment B raw5658step0 raw5658step0Labels := by
      have hz : ∀ j, raw5658 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5658step0 = (fun i j => raw5658 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5658step0 raw5658; decide +kernel
      have hl : raw5658step0Labels = raw5658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5658 raw5658Labels permutation265 hz
    mixedMoment B raw5658step0 raw5658step0Labels = mixedMoment B raw5658step1 raw5658step1Labels := by
      have ha : raw5658step1 = (fun i j => raw5658step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5658step1 raw5658step0; decide +kernel
      have hl : raw5658step1Labels = raw5658step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5658step0 raw5658step0Labels permutation32 permutation6
    mixedMoment B raw5658step1 raw5658step1Labels = mixedMoment B raw5658step2 raw5658step2Labels := by
      have ha : raw5658step2 = raw5658step1 := by apply Matrix.ext; unfold raw5658step2 raw5658step1; decide +kernel
      have hl : raw5658step1Labels = labelEmbedding9 ∘ raw5658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5658step1 raw5658step1Labels raw5658step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw5659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5659step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5659step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5659 raw5659Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw5659 raw5659Labels = mixedMoment B raw5659step0 raw5659step0Labels := by
      have hz : ∀ j, raw5659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5659step0 = (fun i j => raw5659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5659step0 raw5659; decide +kernel
      have hl : raw5659step0Labels = raw5659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5659 raw5659Labels permutation346 hz
    mixedMoment B raw5659step0 raw5659step0Labels = mixedMoment B raw5659step1 raw5659step1Labels := by
      have ha : raw5659step1 = (fun i j => raw5659step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5659step1 raw5659step0; decide +kernel
      have hl : raw5659step1Labels = raw5659step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5659step0 raw5659step0Labels permutation32 permutation6
    mixedMoment B raw5659step1 raw5659step1Labels = mixedMoment B raw5659step2 raw5659step2Labels := by
      have ha : raw5659step2 = raw5659step1 := by apply Matrix.ext; unfold raw5659step2 raw5659step1; decide +kernel
      have hl : raw5659step1Labels = labelEmbedding9 ∘ raw5659step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5659step1 raw5659step1Labels raw5659step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw5660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5660step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5660 raw5660Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw5660 raw5660Labels = mixedMoment B raw5660step0 raw5660step0Labels := by
      have hz : ∀ j, raw5660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5660step0 = (fun i j => raw5660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5660step0 raw5660; decide +kernel
      have hl : raw5660step0Labels = raw5660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5660 raw5660Labels permutation434 hz
    mixedMoment B raw5660step0 raw5660step0Labels = mixedMoment B raw5660step1 raw5660step1Labels := by
      have ha : raw5660step1 = (fun i j => raw5660step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5660step1 raw5660step0; decide +kernel
      have hl : raw5660step1Labels = raw5660step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5660step0 raw5660step0Labels permutation32 permutation6
    mixedMoment B raw5660step1 raw5660step1Labels = mixedMoment B raw5660step2 raw5660step2Labels := by
      have ha : raw5660step2 = raw5660step1 := by apply Matrix.ext; unfold raw5660step2 raw5660step1; decide +kernel
      have hl : raw5660step1Labels = labelEmbedding9 ∘ raw5660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5660step1 raw5660step1Labels raw5660step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw5661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw5661step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw5661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5661 raw5661Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw5661 raw5661Labels = mixedMoment B raw5661step0 raw5661step0Labels := by
      have ha : raw5661step0 = (fun i j => raw5661 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5661step0 raw5661; decide +kernel
      have hl : raw5661step0Labels = raw5661Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5661 raw5661Labels permutation152 permutation6
    mixedMoment B raw5661step0 raw5661step0Labels = mixedMoment B raw5661step1 raw5661step1Labels := by
      have ha : raw5661step1 = raw5661step0 := by apply Matrix.ext; unfold raw5661step1 raw5661step0; decide +kernel
      have hl : raw5661step0Labels = labelEmbedding9 ∘ raw5661step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5661step0 raw5661step0Labels raw5661step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5277 node5277Labels := by rfl

def raw5662 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5662 raw5662Labels = mixedMoment B node5097 node5097Labels := by
  calc
    mixedMoment B raw5662 raw5662Labels = mixedMoment B raw5662step0 raw5662step0Labels := by
      have ha : raw5662step0 = (fun i j => raw5662 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5662step0 raw5662; decide +kernel
      have hl : raw5662step0Labels = raw5662Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5662 raw5662Labels permutation674 permutation2
    _ = mixedMoment B node5097 node5097Labels := by rfl

def raw5663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5663step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5663step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5663step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5663 raw5663Labels = mixedMoment B node4446 node4446Labels := by
  calc
    mixedMoment B raw5663 raw5663Labels = mixedMoment B raw5663step0 raw5663step0Labels := by
      have ha : raw5663step0 = (fun i j => raw5663 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5663step0 raw5663; decide +kernel
      have hl : raw5663step0Labels = raw5663Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5663 raw5663Labels permutation243 permutation4
    mixedMoment B raw5663step0 raw5663step0Labels = mixedMoment B raw5663step1 raw5663step1Labels := by
      have ha : raw5663step1 = -raw5663step0 := by apply Matrix.ext; change ∀ i j, raw5663step1 i j = -(raw5663step0 i j); unfold raw5663step1 raw5663step0; decide +kernel
      have hl : raw5663step1Labels = raw5663step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5663step1 raw5663step1Labels = mixedMoment B raw5663step2 raw5663step2Labels := by
      have ha : raw5663step2 = raw5663step1 := by apply Matrix.ext; unfold raw5663step2 raw5663step1; decide +kernel
      have hl : raw5663step1Labels = labelEmbedding7 ∘ raw5663step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5663step1 raw5663step1Labels raw5663step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4446 node4446Labels := by rfl

def raw5664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5664step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5664step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5664step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5664step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5664 raw5664Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw5664 raw5664Labels = mixedMoment B raw5664step0 raw5664step0Labels := by
      have hz : ∀ j, raw5664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5664step0 = (fun i j => raw5664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5664step0 raw5664; decide +kernel
      have hl : raw5664step0Labels = raw5664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5664 raw5664Labels permutation346 hz
    mixedMoment B raw5664step0 raw5664step0Labels = mixedMoment B raw5664step1 raw5664step1Labels := by
      have ha : raw5664step1 = (fun i j => raw5664step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5664step1 raw5664step0; decide +kernel
      have hl : raw5664step1Labels = raw5664step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5664step0 raw5664step0Labels permutation49 permutation4
    mixedMoment B raw5664step1 raw5664step1Labels = mixedMoment B raw5664step2 raw5664step2Labels := by
      have ha : raw5664step2 = -raw5664step1 := by apply Matrix.ext; change ∀ i j, raw5664step2 i j = -(raw5664step1 i j); unfold raw5664step2 raw5664step1; decide +kernel
      have hl : raw5664step2Labels = raw5664step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5664step2 raw5664step2Labels = mixedMoment B raw5664step3 raw5664step3Labels := by
      have ha : raw5664step3 = raw5664step2 := by apply Matrix.ext; unfold raw5664step3 raw5664step2; decide +kernel
      have hl : raw5664step2Labels = labelEmbedding7 ∘ raw5664step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5664step2 raw5664step2Labels raw5664step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw5665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5665step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5665step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5665 raw5665Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw5665 raw5665Labels = mixedMoment B raw5665step0 raw5665step0Labels := by
      have hz : ∀ j, raw5665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5665step0 = (fun i j => raw5665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5665step0 raw5665; decide +kernel
      have hl : raw5665step0Labels = raw5665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5665 raw5665Labels permutation434 hz
    mixedMoment B raw5665step0 raw5665step0Labels = mixedMoment B raw5665step1 raw5665step1Labels := by
      have ha : raw5665step1 = (fun i j => raw5665step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5665step1 raw5665step0; decide +kernel
      have hl : raw5665step1Labels = raw5665step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5665step0 raw5665step0Labels permutation49 permutation4
    mixedMoment B raw5665step1 raw5665step1Labels = mixedMoment B raw5665step2 raw5665step2Labels := by
      have ha : raw5665step2 = -raw5665step1 := by apply Matrix.ext; change ∀ i j, raw5665step2 i j = -(raw5665step1 i j); unfold raw5665step2 raw5665step1; decide +kernel
      have hl : raw5665step2Labels = raw5665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5665step2 raw5665step2Labels = mixedMoment B raw5665step3 raw5665step3Labels := by
      have ha : raw5665step3 = raw5665step2 := by apply Matrix.ext; unfold raw5665step3 raw5665step2; decide +kernel
      have hl : raw5665step2Labels = labelEmbedding7 ∘ raw5665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5665step2 raw5665step2Labels raw5665step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw5666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5666step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5666step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5666step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5666 raw5666Labels = mixedMoment B node4857 node4857Labels := by
  calc
    mixedMoment B raw5666 raw5666Labels = mixedMoment B raw5666step0 raw5666step0Labels := by
      have ha : raw5666step0 = (fun i j => raw5666 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5666step0 raw5666; decide +kernel
      have hl : raw5666step0Labels = raw5666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5666 raw5666Labels permutation243 permutation4
    mixedMoment B raw5666step0 raw5666step0Labels = mixedMoment B raw5666step1 raw5666step1Labels := by
      have ha : raw5666step1 = -raw5666step0 := by apply Matrix.ext; change ∀ i j, raw5666step1 i j = -(raw5666step0 i j); unfold raw5666step1 raw5666step0; decide +kernel
      have hl : raw5666step1Labels = raw5666step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5666step1 raw5666step1Labels = mixedMoment B raw5666step2 raw5666step2Labels := by
      have ha : raw5666step2 = raw5666step1 := by apply Matrix.ext; unfold raw5666step2 raw5666step1; decide +kernel
      have hl : raw5666step1Labels = labelEmbedding7 ∘ raw5666step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5666step1 raw5666step1Labels raw5666step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4857 node4857Labels := by rfl

def raw5667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5667step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5667step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5667step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5667 raw5667Labels = mixedMoment B node4876 node4876Labels := by
  calc
    mixedMoment B raw5667 raw5667Labels = mixedMoment B raw5667step0 raw5667step0Labels := by
      have ha : raw5667step0 = (fun i j => raw5667 (permutation263 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5667step0 raw5667; decide +kernel
      have hl : raw5667step0Labels = raw5667Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5667 raw5667Labels permutation263 permutation4
    mixedMoment B raw5667step0 raw5667step0Labels = mixedMoment B raw5667step1 raw5667step1Labels := by
      have ha : raw5667step1 = -raw5667step0 := by apply Matrix.ext; change ∀ i j, raw5667step1 i j = -(raw5667step0 i j); unfold raw5667step1 raw5667step0; decide +kernel
      have hl : raw5667step1Labels = raw5667step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5667step1 raw5667step1Labels = mixedMoment B raw5667step2 raw5667step2Labels := by
      have ha : raw5667step2 = raw5667step1 := by apply Matrix.ext; unfold raw5667step2 raw5667step1; decide +kernel
      have hl : raw5667step1Labels = labelEmbedding7 ∘ raw5667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5667step1 raw5667step1Labels raw5667step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4876 node4876Labels := by rfl

def raw5668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5668step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5668step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5668step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5668 raw5668Labels = mixedMoment B node4446 node4446Labels := by
  calc
    mixedMoment B raw5668 raw5668Labels = mixedMoment B raw5668step0 raw5668step0Labels := by
      have ha : raw5668step0 = (fun i j => raw5668 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5668step0 raw5668; decide +kernel
      have hl : raw5668step0Labels = raw5668Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5668 raw5668Labels permutation241 permutation4
    mixedMoment B raw5668step0 raw5668step0Labels = mixedMoment B raw5668step1 raw5668step1Labels := by
      have ha : raw5668step1 = -raw5668step0 := by apply Matrix.ext; change ∀ i j, raw5668step1 i j = -(raw5668step0 i j); unfold raw5668step1 raw5668step0; decide +kernel
      have hl : raw5668step1Labels = raw5668step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5668step1 raw5668step1Labels = mixedMoment B raw5668step2 raw5668step2Labels := by
      have ha : raw5668step2 = raw5668step1 := by apply Matrix.ext; unfold raw5668step2 raw5668step1; decide +kernel
      have hl : raw5668step1Labels = labelEmbedding7 ∘ raw5668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5668step1 raw5668step1Labels raw5668step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4446 node4446Labels := by rfl

def raw5669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5669step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5669step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5669step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5669step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5669 raw5669Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw5669 raw5669Labels = mixedMoment B raw5669step0 raw5669step0Labels := by
      have hz : ∀ j, raw5669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5669step0 = (fun i j => raw5669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5669step0 raw5669; decide +kernel
      have hl : raw5669step0Labels = raw5669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5669 raw5669Labels permutation265 hz
    mixedMoment B raw5669step0 raw5669step0Labels = mixedMoment B raw5669step1 raw5669step1Labels := by
      have ha : raw5669step1 = (fun i j => raw5669step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5669step1 raw5669step0; decide +kernel
      have hl : raw5669step1Labels = raw5669step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5669step0 raw5669step0Labels permutation49 permutation4
    mixedMoment B raw5669step1 raw5669step1Labels = mixedMoment B raw5669step2 raw5669step2Labels := by
      have ha : raw5669step2 = -raw5669step1 := by apply Matrix.ext; change ∀ i j, raw5669step2 i j = -(raw5669step1 i j); unfold raw5669step2 raw5669step1; decide +kernel
      have hl : raw5669step2Labels = raw5669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5669step2 raw5669step2Labels = mixedMoment B raw5669step3 raw5669step3Labels := by
      have ha : raw5669step3 = raw5669step2 := by apply Matrix.ext; unfold raw5669step3 raw5669step2; decide +kernel
      have hl : raw5669step2Labels = labelEmbedding7 ∘ raw5669step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5669step2 raw5669step2Labels raw5669step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw5670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5670step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5670step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5670step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5670 raw5670Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw5670 raw5670Labels = mixedMoment B raw5670step0 raw5670step0Labels := by
      have hz : ∀ j, raw5670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5670step0 = (fun i j => raw5670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5670step0 raw5670; decide +kernel
      have hl : raw5670step0Labels = raw5670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5670 raw5670Labels permutation434 hz
    mixedMoment B raw5670step0 raw5670step0Labels = mixedMoment B raw5670step1 raw5670step1Labels := by
      have ha : raw5670step1 = (fun i j => raw5670step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5670step1 raw5670step0; decide +kernel
      have hl : raw5670step1Labels = raw5670step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5670step0 raw5670step0Labels permutation48 permutation4
    mixedMoment B raw5670step1 raw5670step1Labels = mixedMoment B raw5670step2 raw5670step2Labels := by
      have ha : raw5670step2 = -raw5670step1 := by apply Matrix.ext; change ∀ i j, raw5670step2 i j = -(raw5670step1 i j); unfold raw5670step2 raw5670step1; decide +kernel
      have hl : raw5670step2Labels = raw5670step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5670step2 raw5670step2Labels = mixedMoment B raw5670step3 raw5670step3Labels := by
      have ha : raw5670step3 = raw5670step2 := by apply Matrix.ext; unfold raw5670step3 raw5670step2; decide +kernel
      have hl : raw5670step2Labels = labelEmbedding7 ∘ raw5670step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5670step2 raw5670step2Labels raw5670step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw5671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5671step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5671step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5671step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5671 raw5671Labels = mixedMoment B node4857 node4857Labels := by
  calc
    mixedMoment B raw5671 raw5671Labels = mixedMoment B raw5671step0 raw5671step0Labels := by
      have ha : raw5671step0 = (fun i j => raw5671 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5671step0 raw5671; decide +kernel
      have hl : raw5671step0Labels = raw5671Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5671 raw5671Labels permutation241 permutation4
    mixedMoment B raw5671step0 raw5671step0Labels = mixedMoment B raw5671step1 raw5671step1Labels := by
      have ha : raw5671step1 = -raw5671step0 := by apply Matrix.ext; change ∀ i j, raw5671step1 i j = -(raw5671step0 i j); unfold raw5671step1 raw5671step0; decide +kernel
      have hl : raw5671step1Labels = raw5671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5671step1 raw5671step1Labels = mixedMoment B raw5671step2 raw5671step2Labels := by
      have ha : raw5671step2 = raw5671step1 := by apply Matrix.ext; unfold raw5671step2 raw5671step1; decide +kernel
      have hl : raw5671step1Labels = labelEmbedding7 ∘ raw5671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5671step1 raw5671step1Labels raw5671step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4857 node4857Labels := by rfl

def raw5672 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5672step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5672step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5672step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5672 raw5672Labels = mixedMoment B node4876 node4876Labels := by
  calc
    mixedMoment B raw5672 raw5672Labels = mixedMoment B raw5672step0 raw5672step0Labels := by
      have ha : raw5672step0 = (fun i j => raw5672 (permutation261 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5672step0 raw5672; decide +kernel
      have hl : raw5672step0Labels = raw5672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5672 raw5672Labels permutation261 permutation4
    mixedMoment B raw5672step0 raw5672step0Labels = mixedMoment B raw5672step1 raw5672step1Labels := by
      have ha : raw5672step1 = -raw5672step0 := by apply Matrix.ext; change ∀ i j, raw5672step1 i j = -(raw5672step0 i j); unfold raw5672step1 raw5672step0; decide +kernel
      have hl : raw5672step1Labels = raw5672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5672step1 raw5672step1Labels = mixedMoment B raw5672step2 raw5672step2Labels := by
      have ha : raw5672step2 = raw5672step1 := by apply Matrix.ext; unfold raw5672step2 raw5672step1; decide +kernel
      have hl : raw5672step1Labels = labelEmbedding7 ∘ raw5672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5672step1 raw5672step1Labels raw5672step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4876 node4876Labels := by rfl

def raw5673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5673step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5673step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5673step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5673 raw5673Labels = mixedMoment B node4446 node4446Labels := by
  calc
    mixedMoment B raw5673 raw5673Labels = mixedMoment B raw5673step0 raw5673step0Labels := by
      have ha : raw5673step0 = (fun i j => raw5673 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5673step0 raw5673; decide +kernel
      have hl : raw5673step0Labels = raw5673Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5673 raw5673Labels permutation240 permutation4
    mixedMoment B raw5673step0 raw5673step0Labels = mixedMoment B raw5673step1 raw5673step1Labels := by
      have ha : raw5673step1 = -raw5673step0 := by apply Matrix.ext; change ∀ i j, raw5673step1 i j = -(raw5673step0 i j); unfold raw5673step1 raw5673step0; decide +kernel
      have hl : raw5673step1Labels = raw5673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5673step1 raw5673step1Labels = mixedMoment B raw5673step2 raw5673step2Labels := by
      have ha : raw5673step2 = raw5673step1 := by apply Matrix.ext; unfold raw5673step2 raw5673step1; decide +kernel
      have hl : raw5673step1Labels = labelEmbedding7 ∘ raw5673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5673step1 raw5673step1Labels raw5673step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4446 node4446Labels := by rfl

def raw5674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5674step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5674step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5674step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5674 raw5674Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw5674 raw5674Labels = mixedMoment B raw5674step0 raw5674step0Labels := by
      have hz : ∀ j, raw5674 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5674step0 = (fun i j => raw5674 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5674step0 raw5674; decide +kernel
      have hl : raw5674step0Labels = raw5674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5674 raw5674Labels permutation265 hz
    mixedMoment B raw5674step0 raw5674step0Labels = mixedMoment B raw5674step1 raw5674step1Labels := by
      have ha : raw5674step1 = (fun i j => raw5674step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5674step1 raw5674step0; decide +kernel
      have hl : raw5674step1Labels = raw5674step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5674step0 raw5674step0Labels permutation48 permutation4
    mixedMoment B raw5674step1 raw5674step1Labels = mixedMoment B raw5674step2 raw5674step2Labels := by
      have ha : raw5674step2 = -raw5674step1 := by apply Matrix.ext; change ∀ i j, raw5674step2 i j = -(raw5674step1 i j); unfold raw5674step2 raw5674step1; decide +kernel
      have hl : raw5674step2Labels = raw5674step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5674step2 raw5674step2Labels = mixedMoment B raw5674step3 raw5674step3Labels := by
      have ha : raw5674step3 = raw5674step2 := by apply Matrix.ext; unfold raw5674step3 raw5674step2; decide +kernel
      have hl : raw5674step2Labels = labelEmbedding7 ∘ raw5674step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5674step2 raw5674step2Labels raw5674step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw5675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5675step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5675step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5675step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5675 raw5675Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw5675 raw5675Labels = mixedMoment B raw5675step0 raw5675step0Labels := by
      have hz : ∀ j, raw5675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5675step0 = (fun i j => raw5675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5675step0 raw5675; decide +kernel
      have hl : raw5675step0Labels = raw5675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5675 raw5675Labels permutation346 hz
    mixedMoment B raw5675step0 raw5675step0Labels = mixedMoment B raw5675step1 raw5675step1Labels := by
      have ha : raw5675step1 = (fun i j => raw5675step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5675step1 raw5675step0; decide +kernel
      have hl : raw5675step1Labels = raw5675step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5675step0 raw5675step0Labels permutation48 permutation4
    mixedMoment B raw5675step1 raw5675step1Labels = mixedMoment B raw5675step2 raw5675step2Labels := by
      have ha : raw5675step2 = -raw5675step1 := by apply Matrix.ext; change ∀ i j, raw5675step2 i j = -(raw5675step1 i j); unfold raw5675step2 raw5675step1; decide +kernel
      have hl : raw5675step2Labels = raw5675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5675step2 raw5675step2Labels = mixedMoment B raw5675step3 raw5675step3Labels := by
      have ha : raw5675step3 = raw5675step2 := by apply Matrix.ext; unfold raw5675step3 raw5675step2; decide +kernel
      have hl : raw5675step2Labels = labelEmbedding7 ∘ raw5675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5675step2 raw5675step2Labels raw5675step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw5676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5676step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5676step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5676step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5676 raw5676Labels = mixedMoment B node4857 node4857Labels := by
  calc
    mixedMoment B raw5676 raw5676Labels = mixedMoment B raw5676step0 raw5676step0Labels := by
      have ha : raw5676step0 = (fun i j => raw5676 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5676step0 raw5676; decide +kernel
      have hl : raw5676step0Labels = raw5676Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5676 raw5676Labels permutation240 permutation4
    mixedMoment B raw5676step0 raw5676step0Labels = mixedMoment B raw5676step1 raw5676step1Labels := by
      have ha : raw5676step1 = -raw5676step0 := by apply Matrix.ext; change ∀ i j, raw5676step1 i j = -(raw5676step0 i j); unfold raw5676step1 raw5676step0; decide +kernel
      have hl : raw5676step1Labels = raw5676step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5676step1 raw5676step1Labels = mixedMoment B raw5676step2 raw5676step2Labels := by
      have ha : raw5676step2 = raw5676step1 := by apply Matrix.ext; unfold raw5676step2 raw5676step1; decide +kernel
      have hl : raw5676step1Labels = labelEmbedding7 ∘ raw5676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5676step1 raw5676step1Labels raw5676step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4857 node4857Labels := by rfl

def raw5677 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5677step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5677step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5677step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5677step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5677 raw5677Labels = mixedMoment B node4876 node4876Labels := by
  calc
    mixedMoment B raw5677 raw5677Labels = mixedMoment B raw5677step0 raw5677step0Labels := by
      have ha : raw5677step0 = (fun i j => raw5677 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5677step0 raw5677; decide +kernel
      have hl : raw5677step0Labels = raw5677Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5677 raw5677Labels permutation260 permutation4
    mixedMoment B raw5677step0 raw5677step0Labels = mixedMoment B raw5677step1 raw5677step1Labels := by
      have ha : raw5677step1 = -raw5677step0 := by apply Matrix.ext; change ∀ i j, raw5677step1 i j = -(raw5677step0 i j); unfold raw5677step1 raw5677step0; decide +kernel
      have hl : raw5677step1Labels = raw5677step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5677step1 raw5677step1Labels = mixedMoment B raw5677step2 raw5677step2Labels := by
      have ha : raw5677step2 = raw5677step1 := by apply Matrix.ext; unfold raw5677step2 raw5677step1; decide +kernel
      have hl : raw5677step1Labels = labelEmbedding7 ∘ raw5677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5677step1 raw5677step1Labels raw5677step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4876 node4876Labels := by rfl

def raw5678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5678step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5678step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5678step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5678 raw5678Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw5678 raw5678Labels = mixedMoment B raw5678step0 raw5678step0Labels := by
      have ha : raw5678step0 = (fun i j => raw5678 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5678step0 raw5678; decide +kernel
      have hl : raw5678step0Labels = raw5678Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5678 raw5678Labels permutation246 permutation4
    mixedMoment B raw5678step0 raw5678step0Labels = mixedMoment B raw5678step1 raw5678step1Labels := by
      have ha : raw5678step1 = -raw5678step0 := by apply Matrix.ext; change ∀ i j, raw5678step1 i j = -(raw5678step0 i j); unfold raw5678step1 raw5678step0; decide +kernel
      have hl : raw5678step1Labels = raw5678step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5678step1 raw5678step1Labels = mixedMoment B raw5678step2 raw5678step2Labels := by
      have ha : raw5678step2 = raw5678step1 := by apply Matrix.ext; unfold raw5678step2 raw5678step1; decide +kernel
      have hl : raw5678step1Labels = labelEmbedding7 ∘ raw5678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5678step1 raw5678step1Labels raw5678step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4473 node4473Labels := by rfl

def raw5679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5679step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5679 raw5679Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw5679 raw5679Labels = mixedMoment B raw5679step0 raw5679step0Labels := by
      have hz : ∀ j, raw5679 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5679step0 = (fun i j => raw5679 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5679step0 raw5679; decide +kernel
      have hl : raw5679step0Labels = raw5679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5679 raw5679Labels permutation265 hz
    mixedMoment B raw5679step0 raw5679step0Labels = mixedMoment B raw5679step1 raw5679step1Labels := by
      have ha : raw5679step1 = (fun i j => raw5679step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5679step1 raw5679step0; decide +kernel
      have hl : raw5679step1Labels = raw5679step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5679step0 raw5679step0Labels permutation32 permutation6
    mixedMoment B raw5679step1 raw5679step1Labels = mixedMoment B raw5679step2 raw5679step2Labels := by
      have ha : raw5679step2 = raw5679step1 := by apply Matrix.ext; unfold raw5679step2 raw5679step1; decide +kernel
      have hl : raw5679step1Labels = labelEmbedding9 ∘ raw5679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5679step1 raw5679step1Labels raw5679step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw5680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5680step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5680 raw5680Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw5680 raw5680Labels = mixedMoment B raw5680step0 raw5680step0Labels := by
      have hz : ∀ j, raw5680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5680step0 = (fun i j => raw5680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5680step0 raw5680; decide +kernel
      have hl : raw5680step0Labels = raw5680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5680 raw5680Labels permutation346 hz
    mixedMoment B raw5680step0 raw5680step0Labels = mixedMoment B raw5680step1 raw5680step1Labels := by
      have ha : raw5680step1 = (fun i j => raw5680step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5680step1 raw5680step0; decide +kernel
      have hl : raw5680step1Labels = raw5680step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5680step0 raw5680step0Labels permutation32 permutation6
    mixedMoment B raw5680step1 raw5680step1Labels = mixedMoment B raw5680step2 raw5680step2Labels := by
      have ha : raw5680step2 = raw5680step1 := by apply Matrix.ext; unfold raw5680step2 raw5680step1; decide +kernel
      have hl : raw5680step1Labels = labelEmbedding9 ∘ raw5680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5680step1 raw5680step1Labels raw5680step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw5681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5681step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5681 raw5681Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw5681 raw5681Labels = mixedMoment B raw5681step0 raw5681step0Labels := by
      have hz : ∀ j, raw5681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5681step0 = (fun i j => raw5681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5681step0 raw5681; decide +kernel
      have hl : raw5681step0Labels = raw5681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5681 raw5681Labels permutation434 hz
    mixedMoment B raw5681step0 raw5681step0Labels = mixedMoment B raw5681step1 raw5681step1Labels := by
      have ha : raw5681step1 = (fun i j => raw5681step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5681step1 raw5681step0; decide +kernel
      have hl : raw5681step1Labels = raw5681step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5681step0 raw5681step0Labels permutation32 permutation6
    mixedMoment B raw5681step1 raw5681step1Labels = mixedMoment B raw5681step2 raw5681step2Labels := by
      have ha : raw5681step2 = raw5681step1 := by apply Matrix.ext; unfold raw5681step2 raw5681step1; decide +kernel
      have hl : raw5681step1Labels = labelEmbedding9 ∘ raw5681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5681step1 raw5681step1Labels raw5681step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw5682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw5682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5682step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5682step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5682step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5682 raw5682Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw5682 raw5682Labels = mixedMoment B raw5682step0 raw5682step0Labels := by
      have ha : raw5682step0 = (fun i j => raw5682 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5682step0 raw5682; decide +kernel
      have hl : raw5682step0Labels = raw5682Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5682 raw5682Labels permutation246 permutation4
    mixedMoment B raw5682step0 raw5682step0Labels = mixedMoment B raw5682step1 raw5682step1Labels := by
      have ha : raw5682step1 = -raw5682step0 := by apply Matrix.ext; change ∀ i j, raw5682step1 i j = -(raw5682step0 i j); unfold raw5682step1 raw5682step0; decide +kernel
      have hl : raw5682step1Labels = raw5682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5682step1 raw5682step1Labels = mixedMoment B raw5682step2 raw5682step2Labels := by
      have ha : raw5682step2 = raw5682step1 := by apply Matrix.ext; unfold raw5682step2 raw5682step1; decide +kernel
      have hl : raw5682step1Labels = labelEmbedding7 ∘ raw5682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5682step1 raw5682step1Labels raw5682step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

def raw5683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5683step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5683step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5683step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5683 raw5683Labels = mixedMoment B node4455 node4455Labels := by
  calc
    mixedMoment B raw5683 raw5683Labels = mixedMoment B raw5683step0 raw5683step0Labels := by
      have ha : raw5683step0 = (fun i j => raw5683 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5683step0 raw5683; decide +kernel
      have hl : raw5683step0Labels = raw5683Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5683 raw5683Labels permutation224 permutation4
    mixedMoment B raw5683step0 raw5683step0Labels = mixedMoment B raw5683step1 raw5683step1Labels := by
      have ha : raw5683step1 = -raw5683step0 := by apply Matrix.ext; change ∀ i j, raw5683step1 i j = -(raw5683step0 i j); unfold raw5683step1 raw5683step0; decide +kernel
      have hl : raw5683step1Labels = raw5683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5683step1 raw5683step1Labels = mixedMoment B raw5683step2 raw5683step2Labels := by
      have ha : raw5683step2 = raw5683step1 := by apply Matrix.ext; unfold raw5683step2 raw5683step1; decide +kernel
      have hl : raw5683step1Labels = labelEmbedding7 ∘ raw5683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5683step1 raw5683step1Labels raw5683step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4455 node4455Labels := by rfl

def raw5684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5684step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5684 raw5684Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw5684 raw5684Labels = mixedMoment B raw5684step0 raw5684step0Labels := by
      have hz : ∀ j, raw5684 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5684step0 = (fun i j => raw5684 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5684step0 raw5684; decide +kernel
      have hl : raw5684step0Labels = raw5684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5684 raw5684Labels permutation265 hz
    mixedMoment B raw5684step0 raw5684step0Labels = mixedMoment B raw5684step1 raw5684step1Labels := by
      have ha : raw5684step1 = (fun i j => raw5684step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5684step1 raw5684step0; decide +kernel
      have hl : raw5684step1Labels = raw5684step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5684step0 raw5684step0Labels permutation32 permutation6
    mixedMoment B raw5684step1 raw5684step1Labels = mixedMoment B raw5684step2 raw5684step2Labels := by
      have ha : raw5684step2 = raw5684step1 := by apply Matrix.ext; unfold raw5684step2 raw5684step1; decide +kernel
      have hl : raw5684step1Labels = labelEmbedding9 ∘ raw5684step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5684step1 raw5684step1Labels raw5684step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw5685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5685step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5685 raw5685Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw5685 raw5685Labels = mixedMoment B raw5685step0 raw5685step0Labels := by
      have hz : ∀ j, raw5685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5685step0 = (fun i j => raw5685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5685step0 raw5685; decide +kernel
      have hl : raw5685step0Labels = raw5685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5685 raw5685Labels permutation346 hz
    mixedMoment B raw5685step0 raw5685step0Labels = mixedMoment B raw5685step1 raw5685step1Labels := by
      have ha : raw5685step1 = (fun i j => raw5685step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5685step1 raw5685step0; decide +kernel
      have hl : raw5685step1Labels = raw5685step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5685step0 raw5685step0Labels permutation32 permutation6
    mixedMoment B raw5685step1 raw5685step1Labels = mixedMoment B raw5685step2 raw5685step2Labels := by
      have ha : raw5685step2 = raw5685step1 := by apply Matrix.ext; unfold raw5685step2 raw5685step1; decide +kernel
      have hl : raw5685step1Labels = labelEmbedding9 ∘ raw5685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5685step1 raw5685step1Labels raw5685step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw5686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5686step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5686 raw5686Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw5686 raw5686Labels = mixedMoment B raw5686step0 raw5686step0Labels := by
      have hz : ∀ j, raw5686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5686step0 = (fun i j => raw5686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5686step0 raw5686; decide +kernel
      have hl : raw5686step0Labels = raw5686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5686 raw5686Labels permutation434 hz
    mixedMoment B raw5686step0 raw5686step0Labels = mixedMoment B raw5686step1 raw5686step1Labels := by
      have ha : raw5686step1 = (fun i j => raw5686step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5686step1 raw5686step0; decide +kernel
      have hl : raw5686step1Labels = raw5686step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5686step0 raw5686step0Labels permutation32 permutation6
    mixedMoment B raw5686step1 raw5686step1Labels = mixedMoment B raw5686step2 raw5686step2Labels := by
      have ha : raw5686step2 = raw5686step1 := by apply Matrix.ext; unfold raw5686step2 raw5686step1; decide +kernel
      have hl : raw5686step1Labels = labelEmbedding9 ∘ raw5686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5686step1 raw5686step1Labels raw5686step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw5687 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw5687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5687step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5687step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5687step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5687step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5687 raw5687Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw5687 raw5687Labels = mixedMoment B raw5687step0 raw5687step0Labels := by
      have ha : raw5687step0 = (fun i j => raw5687 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5687step0 raw5687; decide +kernel
      have hl : raw5687step0Labels = raw5687Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5687 raw5687Labels permutation224 permutation4
    mixedMoment B raw5687step0 raw5687step0Labels = mixedMoment B raw5687step1 raw5687step1Labels := by
      have ha : raw5687step1 = -raw5687step0 := by apply Matrix.ext; change ∀ i j, raw5687step1 i j = -(raw5687step0 i j); unfold raw5687step1 raw5687step0; decide +kernel
      have hl : raw5687step1Labels = raw5687step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5687step1 raw5687step1Labels = mixedMoment B raw5687step2 raw5687step2Labels := by
      have ha : raw5687step2 = raw5687step1 := by apply Matrix.ext; unfold raw5687step2 raw5687step1; decide +kernel
      have hl : raw5687step1Labels = labelEmbedding7 ∘ raw5687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5687step1 raw5687step1Labels raw5687step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

def raw5688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5688 raw5688Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw5688 raw5688Labels = mixedMoment B raw5688step0 raw5688step0Labels := by
      have hz : ∀ j, raw5688 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5688step0 = (fun i j => raw5688 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5688step0 raw5688; decide +kernel
      have hl : raw5688step0Labels = raw5688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5688 raw5688Labels permutation265 hz
    mixedMoment B raw5688step0 raw5688step0Labels = mixedMoment B raw5688step1 raw5688step1Labels := by
      have ha : raw5688step1 = (fun i j => raw5688step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5688step1 raw5688step0; decide +kernel
      have hl : raw5688step1Labels = raw5688step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5688step0 raw5688step0Labels permutation32 permutation6
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw5689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5689 raw5689Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw5689 raw5689Labels = mixedMoment B raw5689step0 raw5689step0Labels := by
      have hz : ∀ j, raw5689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5689step0 = (fun i j => raw5689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5689step0 raw5689; decide +kernel
      have hl : raw5689step0Labels = raw5689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5689 raw5689Labels permutation346 hz
    mixedMoment B raw5689step0 raw5689step0Labels = mixedMoment B raw5689step1 raw5689step1Labels := by
      have ha : raw5689step1 = (fun i j => raw5689step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5689step1 raw5689step0; decide +kernel
      have hl : raw5689step1Labels = raw5689step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5689step0 raw5689step0Labels permutation32 permutation6
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw5690 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5690 raw5690Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw5690 raw5690Labels = mixedMoment B raw5690step0 raw5690step0Labels := by
      have hz : ∀ j, raw5690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5690step0 = (fun i j => raw5690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5690step0 raw5690; decide +kernel
      have hl : raw5690step0Labels = raw5690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5690 raw5690Labels permutation434 hz
    mixedMoment B raw5690step0 raw5690step0Labels = mixedMoment B raw5690step1 raw5690step1Labels := by
      have ha : raw5690step1 = (fun i j => raw5690step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5690step1 raw5690step0; decide +kernel
      have hl : raw5690step1Labels = raw5690step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5690step0 raw5690step0Labels permutation32 permutation6
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw5691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw5691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5691 raw5691Labels = mixedMoment B node2745 node2745Labels := by
  calc
    mixedMoment B raw5691 raw5691Labels = mixedMoment B raw5691step0 raw5691step0Labels := by
      have ha : raw5691step0 = (fun i j => raw5691 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5691step0 raw5691; decide +kernel
      have hl : raw5691step0Labels = raw5691Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5691 raw5691Labels permutation152 permutation6
    _ = mixedMoment B node2745 node2745Labels := by rfl

def raw5692 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -3, 1]]
def raw5692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5692 raw5692Labels = mixedMoment B node2746 node2746Labels := by
  calc
    mixedMoment B raw5692 raw5692Labels = mixedMoment B raw5692step0 raw5692step0Labels := by
      have ha : raw5692step0 = (fun i j => raw5692 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5692step0 raw5692; decide +kernel
      have hl : raw5692step0Labels = raw5692Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5692 raw5692Labels permutation152 permutation6
    _ = mixedMoment B node2746 node2746Labels := by rfl

def raw5693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5693 raw5693Labels = mixedMoment B node1701 node1701Labels := by
  calc
    mixedMoment B raw5693 raw5693Labels = mixedMoment B raw5693step0 raw5693step0Labels := by
      have ha : raw5693step0 = (fun i j => raw5693 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5693step0 raw5693; decide +kernel
      have hl : raw5693step0Labels = raw5693Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5693 raw5693Labels permutation182 permutation6
    _ = mixedMoment B node1701 node1701Labels := by rfl

def raw5694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5694 raw5694Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5694 raw5694Labels = mixedMoment B raw5694step0 raw5694step0Labels := by
      have hz : ∀ j, raw5694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5694step0 = (fun i j => raw5694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5694step0 raw5694; decide +kernel
      have hl : raw5694step0Labels = raw5694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5694 raw5694Labels permutation346 hz
    mixedMoment B raw5694step0 raw5694step0Labels = mixedMoment B raw5694step1 raw5694step1Labels := by
      have ha : raw5694step1 = (fun i j => raw5694step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5694step1 raw5694step0; decide +kernel
      have hl : raw5694step1Labels = raw5694step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5694step0 raw5694step0Labels permutation38 permutation6
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5695 raw5695Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5695 raw5695Labels = mixedMoment B raw5695step0 raw5695step0Labels := by
      have hz : ∀ j, raw5695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5695step0 = (fun i j => raw5695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5695step0 raw5695; decide +kernel
      have hl : raw5695step0Labels = raw5695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5695 raw5695Labels permutation434 hz
    mixedMoment B raw5695step0 raw5695step0Labels = mixedMoment B raw5695step1 raw5695step1Labels := by
      have ha : raw5695step1 = (fun i j => raw5695step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5695step1 raw5695step0; decide +kernel
      have hl : raw5695step1Labels = raw5695step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5695step0 raw5695step0Labels permutation38 permutation6
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5696 raw5696Labels = mixedMoment B node2236 node2236Labels := by
  calc
    mixedMoment B raw5696 raw5696Labels = mixedMoment B raw5696step0 raw5696step0Labels := by
      have ha : raw5696step0 = (fun i j => raw5696 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5696step0 raw5696; decide +kernel
      have hl : raw5696step0Labels = raw5696Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5696 raw5696Labels permutation182 permutation6
    _ = mixedMoment B node2236 node2236Labels := by rfl

def raw5697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5697 raw5697Labels = mixedMoment B node2237 node2237Labels := by
  calc
    mixedMoment B raw5697 raw5697Labels = mixedMoment B raw5697step0 raw5697step0Labels := by
      have ha : raw5697step0 = (fun i j => raw5697 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5697step0 raw5697; decide +kernel
      have hl : raw5697step0Labels = raw5697Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5697 raw5697Labels permutation182 permutation6
    _ = mixedMoment B node2237 node2237Labels := by rfl

def raw5698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5698 raw5698Labels = mixedMoment B node1701 node1701Labels := by
  calc
    mixedMoment B raw5698 raw5698Labels = mixedMoment B raw5698step0 raw5698step0Labels := by
      have ha : raw5698step0 = (fun i j => raw5698 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5698step0 raw5698; decide +kernel
      have hl : raw5698step0Labels = raw5698Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5698 raw5698Labels permutation158 permutation6
    _ = mixedMoment B node1701 node1701Labels := by rfl

def raw5699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5699 raw5699Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5699 raw5699Labels = mixedMoment B raw5699step0 raw5699step0Labels := by
      have hz : ∀ j, raw5699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5699step0 = (fun i j => raw5699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5699step0 raw5699; decide +kernel
      have hl : raw5699step0Labels = raw5699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5699 raw5699Labels permutation265 hz
    mixedMoment B raw5699step0 raw5699step0Labels = mixedMoment B raw5699step1 raw5699step1Labels := by
      have ha : raw5699step1 = (fun i j => raw5699step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5699step1 raw5699step0; decide +kernel
      have hl : raw5699step1Labels = raw5699step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5699step0 raw5699step0Labels permutation38 permutation6
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5700 raw5700Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5700 raw5700Labels = mixedMoment B raw5700step0 raw5700step0Labels := by
      have hz : ∀ j, raw5700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5700step0 = (fun i j => raw5700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5700step0 raw5700; decide +kernel
      have hl : raw5700step0Labels = raw5700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5700 raw5700Labels permutation434 hz
    mixedMoment B raw5700step0 raw5700step0Labels = mixedMoment B raw5700step1 raw5700step1Labels := by
      have ha : raw5700step1 = (fun i j => raw5700step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5700step1 raw5700step0; decide +kernel
      have hl : raw5700step1Labels = raw5700step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5700step0 raw5700step0Labels permutation32 permutation6
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5701 raw5701Labels = mixedMoment B node2236 node2236Labels := by
  calc
    mixedMoment B raw5701 raw5701Labels = mixedMoment B raw5701step0 raw5701step0Labels := by
      have ha : raw5701step0 = (fun i j => raw5701 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5701step0 raw5701; decide +kernel
      have hl : raw5701step0Labels = raw5701Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5701 raw5701Labels permutation158 permutation6
    _ = mixedMoment B node2236 node2236Labels := by rfl

def raw5702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5702 raw5702Labels = mixedMoment B node2237 node2237Labels := by
  calc
    mixedMoment B raw5702 raw5702Labels = mixedMoment B raw5702step0 raw5702step0Labels := by
      have ha : raw5702step0 = (fun i j => raw5702 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5702step0 raw5702; decide +kernel
      have hl : raw5702step0Labels = raw5702Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5702 raw5702Labels permutation158 permutation6
    _ = mixedMoment B node2237 node2237Labels := by rfl

def raw5703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5703 raw5703Labels = mixedMoment B node1701 node1701Labels := by
  calc
    mixedMoment B raw5703 raw5703Labels = mixedMoment B raw5703step0 raw5703step0Labels := by
      have ha : raw5703step0 = (fun i j => raw5703 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5703step0 raw5703; decide +kernel
      have hl : raw5703step0Labels = raw5703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5703 raw5703Labels permutation152 permutation6
    _ = mixedMoment B node1701 node1701Labels := by rfl

def raw5704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5704 raw5704Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5704 raw5704Labels = mixedMoment B raw5704step0 raw5704step0Labels := by
      have hz : ∀ j, raw5704 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5704step0 = (fun i j => raw5704 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5704step0 raw5704; decide +kernel
      have hl : raw5704step0Labels = raw5704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5704 raw5704Labels permutation265 hz
    mixedMoment B raw5704step0 raw5704step0Labels = mixedMoment B raw5704step1 raw5704step1Labels := by
      have ha : raw5704step1 = (fun i j => raw5704step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5704step1 raw5704step0; decide +kernel
      have hl : raw5704step1Labels = raw5704step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5704step0 raw5704step0Labels permutation32 permutation6
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5705 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5705step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5705 raw5705Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5705 raw5705Labels = mixedMoment B raw5705step0 raw5705step0Labels := by
      have hz : ∀ j, raw5705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5705step0 = (fun i j => raw5705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5705step0 raw5705; decide +kernel
      have hl : raw5705step0Labels = raw5705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5705 raw5705Labels permutation346 hz
    mixedMoment B raw5705step0 raw5705step0Labels = mixedMoment B raw5705step1 raw5705step1Labels := by
      have ha : raw5705step1 = (fun i j => raw5705step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5705step1 raw5705step0; decide +kernel
      have hl : raw5705step1Labels = raw5705step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5705step0 raw5705step0Labels permutation32 permutation6
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5706 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5706 raw5706Labels = mixedMoment B node2236 node2236Labels := by
  calc
    mixedMoment B raw5706 raw5706Labels = mixedMoment B raw5706step0 raw5706step0Labels := by
      have ha : raw5706step0 = (fun i j => raw5706 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5706step0 raw5706; decide +kernel
      have hl : raw5706step0Labels = raw5706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5706 raw5706Labels permutation152 permutation6
    _ = mixedMoment B node2236 node2236Labels := by rfl

def raw5707 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5707 raw5707Labels = mixedMoment B node2237 node2237Labels := by
  calc
    mixedMoment B raw5707 raw5707Labels = mixedMoment B raw5707step0 raw5707step0Labels := by
      have ha : raw5707step0 = (fun i j => raw5707 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5707step0 raw5707; decide +kernel
      have hl : raw5707step0Labels = raw5707Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5707 raw5707Labels permutation152 permutation6
    _ = mixedMoment B node2237 node2237Labels := by rfl

def raw5708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5708 raw5708Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw5708 raw5708Labels = mixedMoment B raw5708step0 raw5708step0Labels := by
      have ha : raw5708step0 = (fun i j => raw5708 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5708step0 raw5708; decide +kernel
      have hl : raw5708step0Labels = raw5708Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5708 raw5708Labels permutation152 permutation6
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw5709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5709step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5709 raw5709Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw5709 raw5709Labels = mixedMoment B raw5709step0 raw5709step0Labels := by
      have hz : ∀ j, raw5709 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5709step0 = (fun i j => raw5709 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5709step0 raw5709; decide +kernel
      have hl : raw5709step0Labels = raw5709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5709 raw5709Labels permutation265 hz
    mixedMoment B raw5709step0 raw5709step0Labels = mixedMoment B raw5709step1 raw5709step1Labels := by
      have ha : raw5709step1 = (fun i j => raw5709step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5709step1 raw5709step0; decide +kernel
      have hl : raw5709step1Labels = raw5709step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5709step0 raw5709step0Labels permutation32 permutation6
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw5710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5710step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5710 raw5710Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw5710 raw5710Labels = mixedMoment B raw5710step0 raw5710step0Labels := by
      have hz : ∀ j, raw5710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5710step0 = (fun i j => raw5710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5710step0 raw5710; decide +kernel
      have hl : raw5710step0Labels = raw5710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5710 raw5710Labels permutation346 hz
    mixedMoment B raw5710step0 raw5710step0Labels = mixedMoment B raw5710step1 raw5710step1Labels := by
      have ha : raw5710step1 = (fun i j => raw5710step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5710step1 raw5710step0; decide +kernel
      have hl : raw5710step1Labels = raw5710step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5710step0 raw5710step0Labels permutation32 permutation6
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw5711 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5711 raw5711Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw5711 raw5711Labels = mixedMoment B raw5711step0 raw5711step0Labels := by
      have hz : ∀ j, raw5711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5711step0 = (fun i j => raw5711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5711step0 raw5711; decide +kernel
      have hl : raw5711step0Labels = raw5711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5711 raw5711Labels permutation434 hz
    mixedMoment B raw5711step0 raw5711step0Labels = mixedMoment B raw5711step1 raw5711step1Labels := by
      have ha : raw5711step1 = (fun i j => raw5711step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5711step1 raw5711step0; decide +kernel
      have hl : raw5711step1Labels = raw5711step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5711step0 raw5711step0Labels permutation32 permutation6
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw5712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw5712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw5712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5712 raw5712Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw5712 raw5712Labels = mixedMoment B raw5712step0 raw5712step0Labels := by
      have ha : raw5712step0 = (fun i j => raw5712 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5712step0 raw5712; decide +kernel
      have hl : raw5712step0Labels = raw5712Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5712 raw5712Labels permutation152 permutation6
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw5713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5713 raw5713Labels = mixedMoment B node1698 node1698Labels := by
  calc
    mixedMoment B raw5713 raw5713Labels = mixedMoment B raw5713step0 raw5713step0Labels := by
      have ha : raw5713step0 = (fun i j => raw5713 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5713step0 raw5713; decide +kernel
      have hl : raw5713step0Labels = raw5713Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5713 raw5713Labels permutation152 permutation6
    _ = mixedMoment B node1698 node1698Labels := by rfl

def raw5714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5714 raw5714Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw5714 raw5714Labels = mixedMoment B raw5714step0 raw5714step0Labels := by
      have hz : ∀ j, raw5714 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5714step0 = (fun i j => raw5714 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5714step0 raw5714; decide +kernel
      have hl : raw5714step0Labels = raw5714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5714 raw5714Labels permutation265 hz
    mixedMoment B raw5714step0 raw5714step0Labels = mixedMoment B raw5714step1 raw5714step1Labels := by
      have ha : raw5714step1 = (fun i j => raw5714step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5714step1 raw5714step0; decide +kernel
      have hl : raw5714step1Labels = raw5714step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5714step0 raw5714step0Labels permutation32 permutation6
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw5715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5715step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5715 raw5715Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw5715 raw5715Labels = mixedMoment B raw5715step0 raw5715step0Labels := by
      have hz : ∀ j, raw5715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5715step0 = (fun i j => raw5715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5715step0 raw5715; decide +kernel
      have hl : raw5715step0Labels = raw5715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5715 raw5715Labels permutation346 hz
    mixedMoment B raw5715step0 raw5715step0Labels = mixedMoment B raw5715step1 raw5715step1Labels := by
      have ha : raw5715step1 = (fun i j => raw5715step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5715step1 raw5715step0; decide +kernel
      have hl : raw5715step1Labels = raw5715step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5715step0 raw5715step0Labels permutation32 permutation6
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw5716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5716step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5716step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5716 raw5716Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw5716 raw5716Labels = mixedMoment B raw5716step0 raw5716step0Labels := by
      have hz : ∀ j, raw5716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5716step0 = (fun i j => raw5716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5716step0 raw5716; decide +kernel
      have hl : raw5716step0Labels = raw5716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5716 raw5716Labels permutation434 hz
    mixedMoment B raw5716step0 raw5716step0Labels = mixedMoment B raw5716step1 raw5716step1Labels := by
      have ha : raw5716step1 = (fun i j => raw5716step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5716step1 raw5716step0; decide +kernel
      have hl : raw5716step1Labels = raw5716step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5716step0 raw5716step0Labels permutation32 permutation6
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw5717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw5717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw5717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5717 raw5717Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw5717 raw5717Labels = mixedMoment B raw5717step0 raw5717step0Labels := by
      have ha : raw5717step0 = (fun i j => raw5717 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5717step0 raw5717; decide +kernel
      have hl : raw5717step0Labels = raw5717Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5717 raw5717Labels permutation152 permutation6
    _ = mixedMoment B node2232 node2232Labels := by rfl

def raw5718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5718 raw5718Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw5718 raw5718Labels = mixedMoment B raw5718step0 raw5718step0Labels := by
      have hz : ∀ j, raw5718 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5718step0 = (fun i j => raw5718 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5718step0 raw5718; decide +kernel
      have hl : raw5718step0Labels = raw5718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5718 raw5718Labels permutation265 hz
    mixedMoment B raw5718step0 raw5718step0Labels = mixedMoment B raw5718step1 raw5718step1Labels := by
      have ha : raw5718step1 = (fun i j => raw5718step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5718step1 raw5718step0; decide +kernel
      have hl : raw5718step1Labels = raw5718step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5718step0 raw5718step0Labels permutation32 permutation7
    mixedMoment B raw5718step1 raw5718step1Labels = mixedMoment B raw5718step2 raw5718step2Labels := by
      have ha : raw5718step2 = raw5718step1 := by apply Matrix.ext; unfold raw5718step2 raw5718step1; decide +kernel
      have hl : raw5718step1Labels = labelEmbedding1 ∘ raw5718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5718step1 raw5718step1Labels raw5718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw5719 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5719 raw5719Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw5719 raw5719Labels = mixedMoment B raw5719step0 raw5719step0Labels := by
      have hz : ∀ j, raw5719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5719step0 = (fun i j => raw5719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5719step0 raw5719; decide +kernel
      have hl : raw5719step0Labels = raw5719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5719 raw5719Labels permutation346 hz
    mixedMoment B raw5719step0 raw5719step0Labels = mixedMoment B raw5719step1 raw5719step1Labels := by
      have ha : raw5719step1 = (fun i j => raw5719step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5719step1 raw5719step0; decide +kernel
      have hl : raw5719step1Labels = raw5719step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5719step0 raw5719step0Labels permutation32 permutation7
    mixedMoment B raw5719step1 raw5719step1Labels = mixedMoment B raw5719step2 raw5719step2Labels := by
      have ha : raw5719step2 = raw5719step1 := by apply Matrix.ext; unfold raw5719step2 raw5719step1; decide +kernel
      have hl : raw5719step1Labels = labelEmbedding1 ∘ raw5719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5719step1 raw5719step1Labels raw5719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw5720 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5720 raw5720Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw5720 raw5720Labels = mixedMoment B raw5720step0 raw5720step0Labels := by
      have hz : ∀ j, raw5720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5720step0 = (fun i j => raw5720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5720step0 raw5720; decide +kernel
      have hl : raw5720step0Labels = raw5720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5720 raw5720Labels permutation434 hz
    mixedMoment B raw5720step0 raw5720step0Labels = mixedMoment B raw5720step1 raw5720step1Labels := by
      have ha : raw5720step1 = (fun i j => raw5720step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5720step1 raw5720step0; decide +kernel
      have hl : raw5720step1Labels = raw5720step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5720step0 raw5720step0Labels permutation32 permutation7
    mixedMoment B raw5720step1 raw5720step1Labels = mixedMoment B raw5720step2 raw5720step2Labels := by
      have ha : raw5720step2 = raw5720step1 := by apply Matrix.ext; unfold raw5720step2 raw5720step1; decide +kernel
      have hl : raw5720step1Labels = labelEmbedding1 ∘ raw5720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5720step1 raw5720step1Labels raw5720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw5721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw5721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw5721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5721 raw5721Labels = mixedMoment B node3059 node3059Labels := by
  calc
    mixedMoment B raw5721 raw5721Labels = mixedMoment B raw5721step0 raw5721step0Labels := by
      have ha : raw5721step0 = (fun i j => raw5721 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5721step0 raw5721; decide +kernel
      have hl : raw5721step0Labels = raw5721Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5721 raw5721Labels permutation152 permutation7
    mixedMoment B raw5721step0 raw5721step0Labels = mixedMoment B raw5721step1 raw5721step1Labels := by
      have ha : raw5721step1 = raw5721step0 := by apply Matrix.ext; unfold raw5721step1 raw5721step0; decide +kernel
      have hl : raw5721step0Labels = labelEmbedding1 ∘ raw5721step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5721step0 raw5721step0Labels raw5721step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3059 node3059Labels := by rfl

def raw5722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5722 raw5722Labels = mixedMoment B node3058 node3058Labels := by
  calc
    mixedMoment B raw5722 raw5722Labels = mixedMoment B raw5722step0 raw5722step0Labels := by
      have ha : raw5722step0 = (fun i j => raw5722 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5722step0 raw5722; decide +kernel
      have hl : raw5722step0Labels = raw5722Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5722 raw5722Labels permutation152 permutation7
    mixedMoment B raw5722step0 raw5722step0Labels = mixedMoment B raw5722step1 raw5722step1Labels := by
      have ha : raw5722step1 = raw5722step0 := by apply Matrix.ext; unfold raw5722step1 raw5722step0; decide +kernel
      have hl : raw5722step0Labels = labelEmbedding1 ∘ raw5722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5722step0 raw5722step0Labels raw5722step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3058 node3058Labels := by rfl

def raw5723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5723step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5723step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5723 raw5723Labels = mixedMoment B node1354 node1354Labels := by
  calc
    mixedMoment B raw5723 raw5723Labels = mixedMoment B raw5723step0 raw5723step0Labels := by
      have ha : raw5723step0 = (fun i j => raw5723 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5723step0 raw5723; decide +kernel
      have hl : raw5723step0Labels = raw5723Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5723 raw5723Labels permutation263 permutation5
    mixedMoment B raw5723step0 raw5723step0Labels = mixedMoment B raw5723step1 raw5723step1Labels := by
      have ha : raw5723step1 = -raw5723step0 := by apply Matrix.ext; change ∀ i j, raw5723step1 i j = -(raw5723step0 i j); unfold raw5723step1 raw5723step0; decide +kernel
      have hl : raw5723step1Labels = raw5723step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5723step1 raw5723step1Labels = mixedMoment B raw5723step2 raw5723step2Labels := by
      have ha : raw5723step2 = raw5723step1 := by apply Matrix.ext; unfold raw5723step2 raw5723step1; decide +kernel
      have hl : raw5723step1Labels = labelEmbedding1 ∘ raw5723step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5723step1 raw5723step1Labels raw5723step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1354 node1354Labels := by rfl

def raw5724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5724 raw5724Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5724 raw5724Labels = mixedMoment B raw5724step0 raw5724step0Labels := by
      have hz : ∀ j, raw5724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5724step0 = (fun i j => raw5724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5724step0 raw5724; decide +kernel
      have hl : raw5724step0Labels = raw5724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5724 raw5724Labels permutation346 hz
    mixedMoment B raw5724step0 raw5724step0Labels = mixedMoment B raw5724step1 raw5724step1Labels := by
      have ha : raw5724step1 = (fun i j => raw5724step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5724step1 raw5724step0; decide +kernel
      have hl : raw5724step1Labels = raw5724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5724step0 raw5724step0Labels permutation55 permutation5
    mixedMoment B raw5724step1 raw5724step1Labels = mixedMoment B raw5724step2 raw5724step2Labels := by
      have ha : raw5724step2 = -raw5724step1 := by apply Matrix.ext; change ∀ i j, raw5724step2 i j = -(raw5724step1 i j); unfold raw5724step2 raw5724step1; decide +kernel
      have hl : raw5724step2Labels = raw5724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5724step2 raw5724step2Labels = mixedMoment B raw5724step3 raw5724step3Labels := by
      have ha : raw5724step3 = raw5724step2 := by apply Matrix.ext; unfold raw5724step3 raw5724step2; decide +kernel
      have hl : raw5724step2Labels = labelEmbedding1 ∘ raw5724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5724step2 raw5724step2Labels raw5724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw5725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5725 raw5725Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5725 raw5725Labels = mixedMoment B raw5725step0 raw5725step0Labels := by
      have hz : ∀ j, raw5725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5725step0 = (fun i j => raw5725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5725step0 raw5725; decide +kernel
      have hl : raw5725step0Labels = raw5725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5725 raw5725Labels permutation434 hz
    mixedMoment B raw5725step0 raw5725step0Labels = mixedMoment B raw5725step1 raw5725step1Labels := by
      have ha : raw5725step1 = (fun i j => raw5725step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5725step1 raw5725step0; decide +kernel
      have hl : raw5725step1Labels = raw5725step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5725step0 raw5725step0Labels permutation55 permutation5
    mixedMoment B raw5725step1 raw5725step1Labels = mixedMoment B raw5725step2 raw5725step2Labels := by
      have ha : raw5725step2 = -raw5725step1 := by apply Matrix.ext; change ∀ i j, raw5725step2 i j = -(raw5725step1 i j); unfold raw5725step2 raw5725step1; decide +kernel
      have hl : raw5725step2Labels = raw5725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5725step2 raw5725step2Labels = mixedMoment B raw5725step3 raw5725step3Labels := by
      have ha : raw5725step3 = raw5725step2 := by apply Matrix.ext; unfold raw5725step3 raw5725step2; decide +kernel
      have hl : raw5725step2Labels = labelEmbedding1 ∘ raw5725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5725step2 raw5725step2Labels raw5725step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw5726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5726step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5726 raw5726Labels = mixedMoment B node3165 node3165Labels := by
  calc
    mixedMoment B raw5726 raw5726Labels = mixedMoment B raw5726step0 raw5726step0Labels := by
      have ha : raw5726step0 = (fun i j => raw5726 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5726step0 raw5726; decide +kernel
      have hl : raw5726step0Labels = raw5726Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5726 raw5726Labels permutation243 permutation5
    mixedMoment B raw5726step0 raw5726step0Labels = mixedMoment B raw5726step1 raw5726step1Labels := by
      have ha : raw5726step1 = -raw5726step0 := by apply Matrix.ext; change ∀ i j, raw5726step1 i j = -(raw5726step0 i j); unfold raw5726step1 raw5726step0; decide +kernel
      have hl : raw5726step1Labels = raw5726step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5726step1 raw5726step1Labels = mixedMoment B raw5726step2 raw5726step2Labels := by
      have ha : raw5726step2 = raw5726step1 := by apply Matrix.ext; unfold raw5726step2 raw5726step1; decide +kernel
      have hl : raw5726step1Labels = labelEmbedding1 ∘ raw5726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5726step1 raw5726step1Labels raw5726step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3165 node3165Labels := by rfl

def raw5727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5727step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5727step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5727 raw5727Labels = mixedMoment B node3146 node3146Labels := by
  calc
    mixedMoment B raw5727 raw5727Labels = mixedMoment B raw5727step0 raw5727step0Labels := by
      have ha : raw5727step0 = (fun i j => raw5727 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5727step0 raw5727; decide +kernel
      have hl : raw5727step0Labels = raw5727Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5727 raw5727Labels permutation263 permutation5
    mixedMoment B raw5727step0 raw5727step0Labels = mixedMoment B raw5727step1 raw5727step1Labels := by
      have ha : raw5727step1 = -raw5727step0 := by apply Matrix.ext; change ∀ i j, raw5727step1 i j = -(raw5727step0 i j); unfold raw5727step1 raw5727step0; decide +kernel
      have hl : raw5727step1Labels = raw5727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5727step1 raw5727step1Labels = mixedMoment B raw5727step2 raw5727step2Labels := by
      have ha : raw5727step2 = raw5727step1 := by apply Matrix.ext; unfold raw5727step2 raw5727step1; decide +kernel
      have hl : raw5727step1Labels = labelEmbedding1 ∘ raw5727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5727step1 raw5727step1Labels raw5727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3146 node3146Labels := by rfl

def raw5728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5728step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5728 raw5728Labels = mixedMoment B node1354 node1354Labels := by
  calc
    mixedMoment B raw5728 raw5728Labels = mixedMoment B raw5728step0 raw5728step0Labels := by
      have ha : raw5728step0 = (fun i j => raw5728 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5728step0 raw5728; decide +kernel
      have hl : raw5728step0Labels = raw5728Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5728 raw5728Labels permutation261 permutation5
    mixedMoment B raw5728step0 raw5728step0Labels = mixedMoment B raw5728step1 raw5728step1Labels := by
      have ha : raw5728step1 = -raw5728step0 := by apply Matrix.ext; change ∀ i j, raw5728step1 i j = -(raw5728step0 i j); unfold raw5728step1 raw5728step0; decide +kernel
      have hl : raw5728step1Labels = raw5728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5728step1 raw5728step1Labels = mixedMoment B raw5728step2 raw5728step2Labels := by
      have ha : raw5728step2 = raw5728step1 := by apply Matrix.ext; unfold raw5728step2 raw5728step1; decide +kernel
      have hl : raw5728step1Labels = labelEmbedding1 ∘ raw5728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5728step1 raw5728step1Labels raw5728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1354 node1354Labels := by rfl

def raw5729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5729 raw5729Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5729 raw5729Labels = mixedMoment B raw5729step0 raw5729step0Labels := by
      have hz : ∀ j, raw5729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5729step0 = (fun i j => raw5729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5729step0 raw5729; decide +kernel
      have hl : raw5729step0Labels = raw5729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5729 raw5729Labels permutation265 hz
    mixedMoment B raw5729step0 raw5729step0Labels = mixedMoment B raw5729step1 raw5729step1Labels := by
      have ha : raw5729step1 = (fun i j => raw5729step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5729step1 raw5729step0; decide +kernel
      have hl : raw5729step1Labels = raw5729step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5729step0 raw5729step0Labels permutation55 permutation5
    mixedMoment B raw5729step1 raw5729step1Labels = mixedMoment B raw5729step2 raw5729step2Labels := by
      have ha : raw5729step2 = -raw5729step1 := by apply Matrix.ext; change ∀ i j, raw5729step2 i j = -(raw5729step1 i j); unfold raw5729step2 raw5729step1; decide +kernel
      have hl : raw5729step2Labels = raw5729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5729step2 raw5729step2Labels = mixedMoment B raw5729step3 raw5729step3Labels := by
      have ha : raw5729step3 = raw5729step2 := by apply Matrix.ext; unfold raw5729step3 raw5729step2; decide +kernel
      have hl : raw5729step2Labels = labelEmbedding1 ∘ raw5729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5729step2 raw5729step2Labels raw5729step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw5730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5730 raw5730Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5730 raw5730Labels = mixedMoment B raw5730step0 raw5730step0Labels := by
      have hz : ∀ j, raw5730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5730step0 = (fun i j => raw5730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5730step0 raw5730; decide +kernel
      have hl : raw5730step0Labels = raw5730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5730 raw5730Labels permutation434 hz
    mixedMoment B raw5730step0 raw5730step0Labels = mixedMoment B raw5730step1 raw5730step1Labels := by
      have ha : raw5730step1 = (fun i j => raw5730step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5730step1 raw5730step0; decide +kernel
      have hl : raw5730step1Labels = raw5730step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5730step0 raw5730step0Labels permutation54 permutation5
    mixedMoment B raw5730step1 raw5730step1Labels = mixedMoment B raw5730step2 raw5730step2Labels := by
      have ha : raw5730step2 = -raw5730step1 := by apply Matrix.ext; change ∀ i j, raw5730step2 i j = -(raw5730step1 i j); unfold raw5730step2 raw5730step1; decide +kernel
      have hl : raw5730step2Labels = raw5730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5730step2 raw5730step2Labels = mixedMoment B raw5730step3 raw5730step3Labels := by
      have ha : raw5730step3 = raw5730step2 := by apply Matrix.ext; unfold raw5730step3 raw5730step2; decide +kernel
      have hl : raw5730step2Labels = labelEmbedding1 ∘ raw5730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5730step2 raw5730step2Labels raw5730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw5731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5731step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5731 raw5731Labels = mixedMoment B node3165 node3165Labels := by
  calc
    mixedMoment B raw5731 raw5731Labels = mixedMoment B raw5731step0 raw5731step0Labels := by
      have ha : raw5731step0 = (fun i j => raw5731 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5731step0 raw5731; decide +kernel
      have hl : raw5731step0Labels = raw5731Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5731 raw5731Labels permutation241 permutation5
    mixedMoment B raw5731step0 raw5731step0Labels = mixedMoment B raw5731step1 raw5731step1Labels := by
      have ha : raw5731step1 = -raw5731step0 := by apply Matrix.ext; change ∀ i j, raw5731step1 i j = -(raw5731step0 i j); unfold raw5731step1 raw5731step0; decide +kernel
      have hl : raw5731step1Labels = raw5731step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5731step1 raw5731step1Labels = mixedMoment B raw5731step2 raw5731step2Labels := by
      have ha : raw5731step2 = raw5731step1 := by apply Matrix.ext; unfold raw5731step2 raw5731step1; decide +kernel
      have hl : raw5731step1Labels = labelEmbedding1 ∘ raw5731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5731step1 raw5731step1Labels raw5731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3165 node3165Labels := by rfl

def raw5732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5732step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5732step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5732 raw5732Labels = mixedMoment B node3146 node3146Labels := by
  calc
    mixedMoment B raw5732 raw5732Labels = mixedMoment B raw5732step0 raw5732step0Labels := by
      have ha : raw5732step0 = (fun i j => raw5732 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5732step0 raw5732; decide +kernel
      have hl : raw5732step0Labels = raw5732Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5732 raw5732Labels permutation261 permutation5
    mixedMoment B raw5732step0 raw5732step0Labels = mixedMoment B raw5732step1 raw5732step1Labels := by
      have ha : raw5732step1 = -raw5732step0 := by apply Matrix.ext; change ∀ i j, raw5732step1 i j = -(raw5732step0 i j); unfold raw5732step1 raw5732step0; decide +kernel
      have hl : raw5732step1Labels = raw5732step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5732step1 raw5732step1Labels = mixedMoment B raw5732step2 raw5732step2Labels := by
      have ha : raw5732step2 = raw5732step1 := by apply Matrix.ext; unfold raw5732step2 raw5732step1; decide +kernel
      have hl : raw5732step1Labels = labelEmbedding1 ∘ raw5732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5732step1 raw5732step1Labels raw5732step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3146 node3146Labels := by rfl

def raw5733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5733 raw5733Labels = mixedMoment B node1354 node1354Labels := by
  calc
    mixedMoment B raw5733 raw5733Labels = mixedMoment B raw5733step0 raw5733step0Labels := by
      have ha : raw5733step0 = (fun i j => raw5733 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5733step0 raw5733; decide +kernel
      have hl : raw5733step0Labels = raw5733Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5733 raw5733Labels permutation260 permutation5
    mixedMoment B raw5733step0 raw5733step0Labels = mixedMoment B raw5733step1 raw5733step1Labels := by
      have ha : raw5733step1 = -raw5733step0 := by apply Matrix.ext; change ∀ i j, raw5733step1 i j = -(raw5733step0 i j); unfold raw5733step1 raw5733step0; decide +kernel
      have hl : raw5733step1Labels = raw5733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5733step1 raw5733step1Labels = mixedMoment B raw5733step2 raw5733step2Labels := by
      have ha : raw5733step2 = raw5733step1 := by apply Matrix.ext; unfold raw5733step2 raw5733step1; decide +kernel
      have hl : raw5733step1Labels = labelEmbedding1 ∘ raw5733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5733step1 raw5733step1Labels raw5733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1354 node1354Labels := by rfl

def raw5734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5734 raw5734Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5734 raw5734Labels = mixedMoment B raw5734step0 raw5734step0Labels := by
      have hz : ∀ j, raw5734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5734step0 = (fun i j => raw5734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5734step0 raw5734; decide +kernel
      have hl : raw5734step0Labels = raw5734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5734 raw5734Labels permutation265 hz
    mixedMoment B raw5734step0 raw5734step0Labels = mixedMoment B raw5734step1 raw5734step1Labels := by
      have ha : raw5734step1 = (fun i j => raw5734step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5734step1 raw5734step0; decide +kernel
      have hl : raw5734step1Labels = raw5734step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5734step0 raw5734step0Labels permutation54 permutation5
    mixedMoment B raw5734step1 raw5734step1Labels = mixedMoment B raw5734step2 raw5734step2Labels := by
      have ha : raw5734step2 = -raw5734step1 := by apply Matrix.ext; change ∀ i j, raw5734step2 i j = -(raw5734step1 i j); unfold raw5734step2 raw5734step1; decide +kernel
      have hl : raw5734step2Labels = raw5734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5734step2 raw5734step2Labels = mixedMoment B raw5734step3 raw5734step3Labels := by
      have ha : raw5734step3 = raw5734step2 := by apply Matrix.ext; unfold raw5734step3 raw5734step2; decide +kernel
      have hl : raw5734step2Labels = labelEmbedding1 ∘ raw5734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5734step2 raw5734step2Labels raw5734step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw5735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5735 raw5735Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5735 raw5735Labels = mixedMoment B raw5735step0 raw5735step0Labels := by
      have hz : ∀ j, raw5735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5735step0 = (fun i j => raw5735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5735step0 raw5735; decide +kernel
      have hl : raw5735step0Labels = raw5735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5735 raw5735Labels permutation346 hz
    mixedMoment B raw5735step0 raw5735step0Labels = mixedMoment B raw5735step1 raw5735step1Labels := by
      have ha : raw5735step1 = (fun i j => raw5735step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5735step1 raw5735step0; decide +kernel
      have hl : raw5735step1Labels = raw5735step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5735step0 raw5735step0Labels permutation54 permutation5
    mixedMoment B raw5735step1 raw5735step1Labels = mixedMoment B raw5735step2 raw5735step2Labels := by
      have ha : raw5735step2 = -raw5735step1 := by apply Matrix.ext; change ∀ i j, raw5735step2 i j = -(raw5735step1 i j); unfold raw5735step2 raw5735step1; decide +kernel
      have hl : raw5735step2Labels = raw5735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5735step2 raw5735step2Labels = mixedMoment B raw5735step3 raw5735step3Labels := by
      have ha : raw5735step3 = raw5735step2 := by apply Matrix.ext; unfold raw5735step3 raw5735step2; decide +kernel
      have hl : raw5735step2Labels = labelEmbedding1 ∘ raw5735step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5735step2 raw5735step2Labels raw5735step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw5736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5736 raw5736Labels = mixedMoment B node3165 node3165Labels := by
  calc
    mixedMoment B raw5736 raw5736Labels = mixedMoment B raw5736step0 raw5736step0Labels := by
      have ha : raw5736step0 = (fun i j => raw5736 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5736step0 raw5736; decide +kernel
      have hl : raw5736step0Labels = raw5736Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5736 raw5736Labels permutation240 permutation5
    mixedMoment B raw5736step0 raw5736step0Labels = mixedMoment B raw5736step1 raw5736step1Labels := by
      have ha : raw5736step1 = -raw5736step0 := by apply Matrix.ext; change ∀ i j, raw5736step1 i j = -(raw5736step0 i j); unfold raw5736step1 raw5736step0; decide +kernel
      have hl : raw5736step1Labels = raw5736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5736step1 raw5736step1Labels = mixedMoment B raw5736step2 raw5736step2Labels := by
      have ha : raw5736step2 = raw5736step1 := by apply Matrix.ext; unfold raw5736step2 raw5736step1; decide +kernel
      have hl : raw5736step1Labels = labelEmbedding1 ∘ raw5736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5736step1 raw5736step1Labels raw5736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3165 node3165Labels := by rfl

def raw5737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5737step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5737 raw5737Labels = mixedMoment B node3146 node3146Labels := by
  calc
    mixedMoment B raw5737 raw5737Labels = mixedMoment B raw5737step0 raw5737step0Labels := by
      have ha : raw5737step0 = (fun i j => raw5737 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5737step0 raw5737; decide +kernel
      have hl : raw5737step0Labels = raw5737Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5737 raw5737Labels permutation260 permutation5
    mixedMoment B raw5737step0 raw5737step0Labels = mixedMoment B raw5737step1 raw5737step1Labels := by
      have ha : raw5737step1 = -raw5737step0 := by apply Matrix.ext; change ∀ i j, raw5737step1 i j = -(raw5737step0 i j); unfold raw5737step1 raw5737step0; decide +kernel
      have hl : raw5737step1Labels = raw5737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5737step1 raw5737step1Labels = mixedMoment B raw5737step2 raw5737step2Labels := by
      have ha : raw5737step2 = raw5737step1 := by apply Matrix.ext; unfold raw5737step2 raw5737step1; decide +kernel
      have hl : raw5737step1Labels = labelEmbedding1 ∘ raw5737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5737step1 raw5737step1Labels raw5737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3146 node3146Labels := by rfl

def raw5738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5738step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5738step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5738 raw5738Labels = mixedMoment B node1366 node1366Labels := by
  calc
    mixedMoment B raw5738 raw5738Labels = mixedMoment B raw5738step0 raw5738step0Labels := by
      have ha : raw5738step0 = (fun i j => raw5738 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5738step0 raw5738; decide +kernel
      have hl : raw5738step0Labels = raw5738Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5738 raw5738Labels permutation260 permutation5
    mixedMoment B raw5738step0 raw5738step0Labels = mixedMoment B raw5738step1 raw5738step1Labels := by
      have ha : raw5738step1 = -raw5738step0 := by apply Matrix.ext; change ∀ i j, raw5738step1 i j = -(raw5738step0 i j); unfold raw5738step1 raw5738step0; decide +kernel
      have hl : raw5738step1Labels = raw5738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5738step1 raw5738step1Labels = mixedMoment B raw5738step2 raw5738step2Labels := by
      have ha : raw5738step2 = raw5738step1 := by apply Matrix.ext; unfold raw5738step2 raw5738step1; decide +kernel
      have hl : raw5738step1Labels = labelEmbedding1 ∘ raw5738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5738step1 raw5738step1Labels raw5738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1366 node1366Labels := by rfl

def raw5739 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw5739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5739 raw5739Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw5739 raw5739Labels = mixedMoment B raw5739step0 raw5739step0Labels := by
      have hz : ∀ j, raw5739 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5739step0 = (fun i j => raw5739 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5739step0 raw5739; decide +kernel
      have hl : raw5739step0Labels = raw5739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5739 raw5739Labels permutation265 hz
    mixedMoment B raw5739step0 raw5739step0Labels = mixedMoment B raw5739step1 raw5739step1Labels := by
      have ha : raw5739step1 = (fun i j => raw5739step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5739step1 raw5739step0; decide +kernel
      have hl : raw5739step1Labels = raw5739step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5739step0 raw5739step0Labels permutation54 permutation5
    mixedMoment B raw5739step1 raw5739step1Labels = mixedMoment B raw5739step2 raw5739step2Labels := by
      have ha : raw5739step2 = -raw5739step1 := by apply Matrix.ext; change ∀ i j, raw5739step2 i j = -(raw5739step1 i j); unfold raw5739step2 raw5739step1; decide +kernel
      have hl : raw5739step2Labels = raw5739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5739step2 raw5739step2Labels = mixedMoment B raw5739step3 raw5739step3Labels := by
      have ha : raw5739step3 = raw5739step2 := by apply Matrix.ext; unfold raw5739step3 raw5739step2; decide +kernel
      have hl : raw5739step2Labels = labelEmbedding1 ∘ raw5739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5739step2 raw5739step2Labels raw5739step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw5740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw5740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5740step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5740 raw5740Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw5740 raw5740Labels = mixedMoment B raw5740step0 raw5740step0Labels := by
      have hz : ∀ j, raw5740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5740step0 = (fun i j => raw5740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5740step0 raw5740; decide +kernel
      have hl : raw5740step0Labels = raw5740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5740 raw5740Labels permutation346 hz
    mixedMoment B raw5740step0 raw5740step0Labels = mixedMoment B raw5740step1 raw5740step1Labels := by
      have ha : raw5740step1 = (fun i j => raw5740step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5740step1 raw5740step0; decide +kernel
      have hl : raw5740step1Labels = raw5740step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5740step0 raw5740step0Labels permutation54 permutation5
    mixedMoment B raw5740step1 raw5740step1Labels = mixedMoment B raw5740step2 raw5740step2Labels := by
      have ha : raw5740step2 = -raw5740step1 := by apply Matrix.ext; change ∀ i j, raw5740step2 i j = -(raw5740step1 i j); unfold raw5740step2 raw5740step1; decide +kernel
      have hl : raw5740step2Labels = raw5740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5740step2 raw5740step2Labels = mixedMoment B raw5740step3 raw5740step3Labels := by
      have ha : raw5740step3 = raw5740step2 := by apply Matrix.ext; unfold raw5740step3 raw5740step2; decide +kernel
      have hl : raw5740step2Labels = labelEmbedding1 ∘ raw5740step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5740step2 raw5740step2Labels raw5740step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw5741 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw5741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5741step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5741 raw5741Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw5741 raw5741Labels = mixedMoment B raw5741step0 raw5741step0Labels := by
      have hz : ∀ j, raw5741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5741step0 = (fun i j => raw5741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5741step0 raw5741; decide +kernel
      have hl : raw5741step0Labels = raw5741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5741 raw5741Labels permutation434 hz
    mixedMoment B raw5741step0 raw5741step0Labels = mixedMoment B raw5741step1 raw5741step1Labels := by
      have ha : raw5741step1 = (fun i j => raw5741step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5741step1 raw5741step0; decide +kernel
      have hl : raw5741step1Labels = raw5741step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5741step0 raw5741step0Labels permutation54 permutation5
    mixedMoment B raw5741step1 raw5741step1Labels = mixedMoment B raw5741step2 raw5741step2Labels := by
      have ha : raw5741step2 = -raw5741step1 := by apply Matrix.ext; change ∀ i j, raw5741step2 i j = -(raw5741step1 i j); unfold raw5741step2 raw5741step1; decide +kernel
      have hl : raw5741step2Labels = raw5741step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5741step2 raw5741step2Labels = mixedMoment B raw5741step3 raw5741step3Labels := by
      have ha : raw5741step3 = raw5741step2 := by apply Matrix.ext; unfold raw5741step3 raw5741step2; decide +kernel
      have hl : raw5741step2Labels = labelEmbedding1 ∘ raw5741step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5741step2 raw5741step2Labels raw5741step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw5742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw5742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5742step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5742step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5742 raw5742Labels = mixedMoment B node3155 node3155Labels := by
  calc
    mixedMoment B raw5742 raw5742Labels = mixedMoment B raw5742step0 raw5742step0Labels := by
      have ha : raw5742step0 = (fun i j => raw5742 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5742step0 raw5742; decide +kernel
      have hl : raw5742step0Labels = raw5742Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5742 raw5742Labels permutation260 permutation5
    mixedMoment B raw5742step0 raw5742step0Labels = mixedMoment B raw5742step1 raw5742step1Labels := by
      have ha : raw5742step1 = -raw5742step0 := by apply Matrix.ext; change ∀ i j, raw5742step1 i j = -(raw5742step0 i j); unfold raw5742step1 raw5742step0; decide +kernel
      have hl : raw5742step1Labels = raw5742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5742step1 raw5742step1Labels = mixedMoment B raw5742step2 raw5742step2Labels := by
      have ha : raw5742step2 = raw5742step1 := by apply Matrix.ext; unfold raw5742step2 raw5742step1; decide +kernel
      have hl : raw5742step1Labels = labelEmbedding1 ∘ raw5742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5742step1 raw5742step1Labels raw5742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3155 node3155Labels := by rfl

def raw5743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5743step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5743 raw5743Labels = mixedMoment B node1405 node1405Labels := by
  calc
    mixedMoment B raw5743 raw5743Labels = mixedMoment B raw5743step0 raw5743step0Labels := by
      have ha : raw5743step0 = (fun i j => raw5743 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5743step0 raw5743; decide +kernel
      have hl : raw5743step0Labels = raw5743Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5743 raw5743Labels permutation240 permutation5
    mixedMoment B raw5743step0 raw5743step0Labels = mixedMoment B raw5743step1 raw5743step1Labels := by
      have ha : raw5743step1 = -raw5743step0 := by apply Matrix.ext; change ∀ i j, raw5743step1 i j = -(raw5743step0 i j); unfold raw5743step1 raw5743step0; decide +kernel
      have hl : raw5743step1Labels = raw5743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5743step1 raw5743step1Labels = mixedMoment B raw5743step2 raw5743step2Labels := by
      have ha : raw5743step2 = raw5743step1 := by apply Matrix.ext; unfold raw5743step2 raw5743step1; decide +kernel
      have hl : raw5743step1Labels = labelEmbedding1 ∘ raw5743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5743step1 raw5743step1Labels raw5743step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1405 node1405Labels := by rfl

def raw5744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5744 raw5744Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw5744 raw5744Labels = mixedMoment B raw5744step0 raw5744step0Labels := by
      have hz : ∀ j, raw5744 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5744step0 = (fun i j => raw5744 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5744step0 raw5744; decide +kernel
      have hl : raw5744step0Labels = raw5744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5744 raw5744Labels permutation265 hz
    mixedMoment B raw5744step0 raw5744step0Labels = mixedMoment B raw5744step1 raw5744step1Labels := by
      have ha : raw5744step1 = (fun i j => raw5744step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5744step1 raw5744step0; decide +kernel
      have hl : raw5744step1Labels = raw5744step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5744step0 raw5744step0Labels permutation32 permutation7
    mixedMoment B raw5744step1 raw5744step1Labels = mixedMoment B raw5744step2 raw5744step2Labels := by
      have ha : raw5744step2 = raw5744step1 := by apply Matrix.ext; unfold raw5744step2 raw5744step1; decide +kernel
      have hl : raw5744step1Labels = labelEmbedding1 ∘ raw5744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5744step1 raw5744step1Labels raw5744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw5745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5745 raw5745Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw5745 raw5745Labels = mixedMoment B raw5745step0 raw5745step0Labels := by
      have hz : ∀ j, raw5745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5745step0 = (fun i j => raw5745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5745step0 raw5745; decide +kernel
      have hl : raw5745step0Labels = raw5745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5745 raw5745Labels permutation346 hz
    mixedMoment B raw5745step0 raw5745step0Labels = mixedMoment B raw5745step1 raw5745step1Labels := by
      have ha : raw5745step1 = (fun i j => raw5745step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5745step1 raw5745step0; decide +kernel
      have hl : raw5745step1Labels = raw5745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5745step0 raw5745step0Labels permutation32 permutation7
    mixedMoment B raw5745step1 raw5745step1Labels = mixedMoment B raw5745step2 raw5745step2Labels := by
      have ha : raw5745step2 = raw5745step1 := by apply Matrix.ext; unfold raw5745step2 raw5745step1; decide +kernel
      have hl : raw5745step1Labels = labelEmbedding1 ∘ raw5745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5745step1 raw5745step1Labels raw5745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw5746 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5746 raw5746Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw5746 raw5746Labels = mixedMoment B raw5746step0 raw5746step0Labels := by
      have hz : ∀ j, raw5746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5746step0 = (fun i j => raw5746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5746step0 raw5746; decide +kernel
      have hl : raw5746step0Labels = raw5746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5746 raw5746Labels permutation434 hz
    mixedMoment B raw5746step0 raw5746step0Labels = mixedMoment B raw5746step1 raw5746step1Labels := by
      have ha : raw5746step1 = (fun i j => raw5746step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5746step1 raw5746step0; decide +kernel
      have hl : raw5746step1Labels = raw5746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5746step0 raw5746step0Labels permutation32 permutation7
    mixedMoment B raw5746step1 raw5746step1Labels = mixedMoment B raw5746step2 raw5746step2Labels := by
      have ha : raw5746step2 = raw5746step1 := by apply Matrix.ext; unfold raw5746step2 raw5746step1; decide +kernel
      have hl : raw5746step1Labels = labelEmbedding1 ∘ raw5746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5746step1 raw5746step1Labels raw5746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw5747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw5747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5747step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5747step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5747 raw5747Labels = mixedMoment B node3179 node3179Labels := by
  calc
    mixedMoment B raw5747 raw5747Labels = mixedMoment B raw5747step0 raw5747step0Labels := by
      have ha : raw5747step0 = (fun i j => raw5747 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5747step0 raw5747; decide +kernel
      have hl : raw5747step0Labels = raw5747Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5747 raw5747Labels permutation240 permutation5
    mixedMoment B raw5747step0 raw5747step0Labels = mixedMoment B raw5747step1 raw5747step1Labels := by
      have ha : raw5747step1 = -raw5747step0 := by apply Matrix.ext; change ∀ i j, raw5747step1 i j = -(raw5747step0 i j); unfold raw5747step1 raw5747step0; decide +kernel
      have hl : raw5747step1Labels = raw5747step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5747step1 raw5747step1Labels = mixedMoment B raw5747step2 raw5747step2Labels := by
      have ha : raw5747step2 = raw5747step1 := by apply Matrix.ext; unfold raw5747step2 raw5747step1; decide +kernel
      have hl : raw5747step1Labels = labelEmbedding1 ∘ raw5747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5747step1 raw5747step1Labels raw5747step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3179 node3179Labels := by rfl

def raw5748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5748 raw5748Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw5748 raw5748Labels = mixedMoment B raw5748step0 raw5748step0Labels := by
      have ha : raw5748step0 = (fun i j => raw5748 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5748step0 raw5748; decide +kernel
      have hl : raw5748step0Labels = raw5748Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5748 raw5748Labels permutation240 permutation4
    mixedMoment B raw5748step0 raw5748step0Labels = mixedMoment B raw5748step1 raw5748step1Labels := by
      have ha : raw5748step1 = -raw5748step0 := by apply Matrix.ext; change ∀ i j, raw5748step1 i j = -(raw5748step0 i j); unfold raw5748step1 raw5748step0; decide +kernel
      have hl : raw5748step1Labels = raw5748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw5749 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw5749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5749 raw5749Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw5749 raw5749Labels = mixedMoment B raw5749step0 raw5749step0Labels := by
      have hz : ∀ j, raw5749 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5749step0 = (fun i j => raw5749 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5749step0 raw5749; decide +kernel
      have hl : raw5749step0Labels = raw5749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5749 raw5749Labels permutation265 hz
    mixedMoment B raw5749step0 raw5749step0Labels = mixedMoment B raw5749step1 raw5749step1Labels := by
      have ha : raw5749step1 = (fun i j => raw5749step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5749step1 raw5749step0; decide +kernel
      have hl : raw5749step1Labels = raw5749step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5749step0 raw5749step0Labels permutation48 permutation4
    mixedMoment B raw5749step1 raw5749step1Labels = mixedMoment B raw5749step2 raw5749step2Labels := by
      have ha : raw5749step2 = -raw5749step1 := by apply Matrix.ext; change ∀ i j, raw5749step2 i j = -(raw5749step1 i j); unfold raw5749step2 raw5749step1; decide +kernel
      have hl : raw5749step2Labels = raw5749step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw5750 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw5750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5750 raw5750Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw5750 raw5750Labels = mixedMoment B raw5750step0 raw5750step0Labels := by
      have hz : ∀ j, raw5750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5750step0 = (fun i j => raw5750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5750step0 raw5750; decide +kernel
      have hl : raw5750step0Labels = raw5750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5750 raw5750Labels permutation346 hz
    mixedMoment B raw5750step0 raw5750step0Labels = mixedMoment B raw5750step1 raw5750step1Labels := by
      have ha : raw5750step1 = (fun i j => raw5750step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5750step1 raw5750step0; decide +kernel
      have hl : raw5750step1Labels = raw5750step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5750step0 raw5750step0Labels permutation48 permutation4
    mixedMoment B raw5750step1 raw5750step1Labels = mixedMoment B raw5750step2 raw5750step2Labels := by
      have ha : raw5750step2 = -raw5750step1 := by apply Matrix.ext; change ∀ i j, raw5750step2 i j = -(raw5750step1 i j); unfold raw5750step2 raw5750step1; decide +kernel
      have hl : raw5750step2Labels = raw5750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw5751 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw5751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5751 raw5751Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw5751 raw5751Labels = mixedMoment B raw5751step0 raw5751step0Labels := by
      have hz : ∀ j, raw5751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5751step0 = (fun i j => raw5751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5751step0 raw5751; decide +kernel
      have hl : raw5751step0Labels = raw5751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5751 raw5751Labels permutation434 hz
    mixedMoment B raw5751step0 raw5751step0Labels = mixedMoment B raw5751step1 raw5751step1Labels := by
      have ha : raw5751step1 = (fun i j => raw5751step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5751step1 raw5751step0; decide +kernel
      have hl : raw5751step1Labels = raw5751step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5751step0 raw5751step0Labels permutation48 permutation4
    mixedMoment B raw5751step1 raw5751step1Labels = mixedMoment B raw5751step2 raw5751step2Labels := by
      have ha : raw5751step2 = -raw5751step1 := by apply Matrix.ext; change ∀ i j, raw5751step2 i j = -(raw5751step1 i j); unfold raw5751step2 raw5751step1; decide +kernel
      have hl : raw5751step2Labels = raw5751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw5752 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5752 raw5752Labels = mixedMoment B node3576 node3576Labels := by
  calc
    mixedMoment B raw5752 raw5752Labels = mixedMoment B raw5752step0 raw5752step0Labels := by
      have ha : raw5752step0 = (fun i j => raw5752 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5752step0 raw5752; decide +kernel
      have hl : raw5752step0Labels = raw5752Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5752 raw5752Labels permutation240 permutation4
    mixedMoment B raw5752step0 raw5752step0Labels = mixedMoment B raw5752step1 raw5752step1Labels := by
      have ha : raw5752step1 = -raw5752step0 := by apply Matrix.ext; change ∀ i j, raw5752step1 i j = -(raw5752step0 i j); unfold raw5752step1 raw5752step0; decide +kernel
      have hl : raw5752step1Labels = raw5752step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3576 node3576Labels := by rfl

def raw5753 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5753 raw5753Labels = mixedMoment B node2507 node2507Labels := by
  calc
    mixedMoment B raw5753 raw5753Labels = mixedMoment B raw5753step0 raw5753step0Labels := by
      have ha : raw5753step0 = (fun i j => raw5753 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5753step0 raw5753; decide +kernel
      have hl : raw5753step0Labels = raw5753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5753 raw5753Labels permutation674 permutation2
    _ = mixedMoment B node2507 node2507Labels := by rfl

def raw5754 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2]]
def raw5754Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5754step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2]]
def raw5754step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5754step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![-1, 1], ![-2, 2]]
def raw5754step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5754step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw5754step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5754step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5754step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5754 raw5754Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5754 raw5754Labels = mixedMoment B raw5754step0 raw5754step0Labels := by
      have hz : ∀ j, raw5754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5754step0 = (fun i j => raw5754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5754step0 raw5754; decide +kernel
      have hl : raw5754step0Labels = raw5754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754 raw5754Labels permutation434 hz
    mixedMoment B raw5754step0 raw5754step0Labels = mixedMoment B raw5754step1 raw5754step1Labels := by
      have hz : ∀ j, raw5754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5754step1 = (fun i j => raw5754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5754step1 raw5754step0; decide +kernel
      have hl : raw5754step1Labels = raw5754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step0 raw5754step0Labels permutation80 hz
    mixedMoment B raw5754step1 raw5754step1Labels = mixedMoment B raw5754step2 raw5754step2Labels := by
      have hz : ∀ j, raw5754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5754step2 = (fun i j => raw5754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5754step2 raw5754step1; decide +kernel
      have hl : raw5754step2Labels = raw5754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step1 raw5754step1Labels permutation14 hz
    mixedMoment B raw5754step2 raw5754step2Labels = mixedMoment B raw5754step3 raw5754step3Labels := by
      have ha : raw5754step3 = -raw5754step2 := by apply Matrix.ext; change ∀ i j, raw5754step3 i j = -(raw5754step2 i j); unfold raw5754step3 raw5754step2; decide +kernel
      have hl : raw5754step3Labels = raw5754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw5755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5755 raw5755Labels = mixedMoment B node1028 node1028Labels := by
  calc
    mixedMoment B raw5755 raw5755Labels = mixedMoment B raw5755step0 raw5755step0Labels := by
      have ha : raw5755step0 = (fun i j => raw5755 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5755step0 raw5755; decide +kernel
      have hl : raw5755step0Labels = raw5755Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5755 raw5755Labels permutation243 permutation4
    mixedMoment B raw5755step0 raw5755step0Labels = mixedMoment B raw5755step1 raw5755step1Labels := by
      have ha : raw5755step1 = -raw5755step0 := by apply Matrix.ext; change ∀ i j, raw5755step1 i j = -(raw5755step0 i j); unfold raw5755step1 raw5755step0; decide +kernel
      have hl : raw5755step1Labels = raw5755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1028 node1028Labels := by rfl

def raw5756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5756 raw5756Labels = mixedMoment B node1028 node1028Labels := by
  calc
    mixedMoment B raw5756 raw5756Labels = mixedMoment B raw5756step0 raw5756step0Labels := by
      have ha : raw5756step0 = (fun i j => raw5756 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5756step0 raw5756; decide +kernel
      have hl : raw5756step0Labels = raw5756Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5756 raw5756Labels permutation241 permutation4
    mixedMoment B raw5756step0 raw5756step0Labels = mixedMoment B raw5756step1 raw5756step1Labels := by
      have ha : raw5756step1 = -raw5756step0 := by apply Matrix.ext; change ∀ i j, raw5756step1 i j = -(raw5756step0 i j); unfold raw5756step1 raw5756step0; decide +kernel
      have hl : raw5756step1Labels = raw5756step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1028 node1028Labels := by rfl

def raw5757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5757 raw5757Labels = mixedMoment B node1028 node1028Labels := by
  calc
    mixedMoment B raw5757 raw5757Labels = mixedMoment B raw5757step0 raw5757step0Labels := by
      have ha : raw5757step0 = (fun i j => raw5757 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5757step0 raw5757; decide +kernel
      have hl : raw5757step0Labels = raw5757Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5757 raw5757Labels permutation240 permutation4
    mixedMoment B raw5757step0 raw5757step0Labels = mixedMoment B raw5757step1 raw5757step1Labels := by
      have ha : raw5757step1 = -raw5757step0 := by apply Matrix.ext; change ∀ i j, raw5757step1 i j = -(raw5757step0 i j); unfold raw5757step1 raw5757step0; decide +kernel
      have hl : raw5757step1Labels = raw5757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1028 node1028Labels := by rfl

def raw5758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5758 raw5758Labels = mixedMoment B node1056 node1056Labels := by
  calc
    mixedMoment B raw5758 raw5758Labels = mixedMoment B raw5758step0 raw5758step0Labels := by
      have ha : raw5758step0 = (fun i j => raw5758 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5758step0 raw5758; decide +kernel
      have hl : raw5758step0Labels = raw5758Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5758 raw5758Labels permutation246 permutation4
    mixedMoment B raw5758step0 raw5758step0Labels = mixedMoment B raw5758step1 raw5758step1Labels := by
      have ha : raw5758step1 = -raw5758step0 := by apply Matrix.ext; change ∀ i j, raw5758step1 i j = -(raw5758step0 i j); unfold raw5758step1 raw5758step0; decide +kernel
      have hl : raw5758step1Labels = raw5758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1056 node1056Labels := by rfl

def raw5759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5759 raw5759Labels = mixedMoment B node1038 node1038Labels := by
  calc
    mixedMoment B raw5759 raw5759Labels = mixedMoment B raw5759step0 raw5759step0Labels := by
      have ha : raw5759step0 = (fun i j => raw5759 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5759step0 raw5759; decide +kernel
      have hl : raw5759step0Labels = raw5759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5759 raw5759Labels permutation224 permutation4
    mixedMoment B raw5759step0 raw5759step0Labels = mixedMoment B raw5759step1 raw5759step1Labels := by
      have ha : raw5759step1 = -raw5759step0 := by apply Matrix.ext; change ∀ i j, raw5759step1 i j = -(raw5759step0 i j); unfold raw5759step1 raw5759step0; decide +kernel
      have hl : raw5759step1Labels = raw5759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1038 node1038Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
