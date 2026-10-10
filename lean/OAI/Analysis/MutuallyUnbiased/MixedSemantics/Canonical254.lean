import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32512 raw32512Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw32512 raw32512Labels = mixedMoment B raw32512step0 raw32512step0Labels := by
      have ha : raw32512step0 = (fun i j => raw32512 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32512step0 raw32512; decide +kernel
      have hl : raw32512step0Labels = raw32512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32512 raw32512Labels permutation265 permutation2
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw32513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32513 raw32513Labels = mixedMoment B node2864 node2864Labels := by
  calc
    _ = mixedMoment B node2864 node2864Labels := by rfl

def raw32514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32514 raw32514Labels = mixedMoment B node2814 node2814Labels := by
  calc
    _ = mixedMoment B node2814 node2814Labels := by rfl

def raw32515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32515 raw32515Labels = mixedMoment B node2801 node2801Labels := by
  calc
    mixedMoment B raw32515 raw32515Labels = mixedMoment B raw32515step0 raw32515step0Labels := by
      have ha : raw32515step0 = (fun i j => raw32515 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32515step0 raw32515; decide +kernel
      have hl : raw32515step0Labels = raw32515Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32515 raw32515Labels permutation155 permutation2
    _ = mixedMoment B node2801 node2801Labels := by rfl

def raw32516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32516 raw32516Labels = mixedMoment B node2801 node2801Labels := by
  calc
    mixedMoment B raw32516 raw32516Labels = mixedMoment B raw32516step0 raw32516step0Labels := by
      have ha : raw32516step0 = (fun i j => raw32516 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32516step0 raw32516; decide +kernel
      have hl : raw32516step0Labels = raw32516Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32516 raw32516Labels permutation153 permutation2
    _ = mixedMoment B node2801 node2801Labels := by rfl

def raw32517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw32517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32517 raw32517Labels = mixedMoment B node2800 node2800Labels := by
  calc
    _ = mixedMoment B node2800 node2800Labels := by rfl

def raw32518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32518 raw32518Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw32518 raw32518Labels = mixedMoment B raw32518step0 raw32518step0Labels := by
      have ha : raw32518step0 = (fun i j => raw32518 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32518step0 raw32518; decide +kernel
      have hl : raw32518step0Labels = raw32518Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32518 raw32518Labels permutation164 permutation2
    _ = mixedMoment B node2809 node2809Labels := by rfl

def raw32519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32519 raw32519Labels = mixedMoment B node2799 node2799Labels := by
  calc
    mixedMoment B raw32519 raw32519Labels = mixedMoment B raw32519step0 raw32519step0Labels := by
      have ha : raw32519step0 = (fun i j => raw32519 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32519step0 raw32519; decide +kernel
      have hl : raw32519step0Labels = raw32519Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32519 raw32519Labels permutation154 permutation2
    _ = mixedMoment B node2799 node2799Labels := by rfl

def raw32520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32520 raw32520Labels = mixedMoment B node2801 node2801Labels := by
  calc
    _ = mixedMoment B node2801 node2801Labels := by rfl

def raw32521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32521 raw32521Labels = mixedMoment B node2797 node2797Labels := by
  calc
    mixedMoment B raw32521 raw32521Labels = mixedMoment B raw32521step0 raw32521step0Labels := by
      have ha : raw32521step0 = (fun i j => raw32521 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32521step0 raw32521; decide +kernel
      have hl : raw32521step0Labels = raw32521Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32521 raw32521Labels permutation154 permutation2
    _ = mixedMoment B node2797 node2797Labels := by rfl

def raw32522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32522 raw32522Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw32522 raw32522Labels = mixedMoment B raw32522step0 raw32522step0Labels := by
      have ha : raw32522step0 = (fun i j => raw32522 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32522step0 raw32522; decide +kernel
      have hl : raw32522step0Labels = raw32522Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32522 raw32522Labels permutation265 permutation2
    _ = mixedMoment B node3689 node3689Labels := by rfl

def raw32523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32523 raw32523Labels = mixedMoment B node2861 node2861Labels := by
  calc
    _ = mixedMoment B node2861 node2861Labels := by rfl

def raw32524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32524 raw32524Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw32524 raw32524Labels = mixedMoment B raw32524step0 raw32524step0Labels := by
      have ha : raw32524step0 = (fun i j => raw32524 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32524step0 raw32524; decide +kernel
      have hl : raw32524step0Labels = raw32524Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32524 raw32524Labels permutation160 permutation2
    _ = mixedMoment B node2807 node2807Labels := by rfl

def raw32525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32525 raw32525Labels = mixedMoment B node2798 node2798Labels := by
  calc
    mixedMoment B raw32525 raw32525Labels = mixedMoment B raw32525step0 raw32525step0Labels := by
      have ha : raw32525step0 = (fun i j => raw32525 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32525step0 raw32525; decide +kernel
      have hl : raw32525step0Labels = raw32525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32525 raw32525Labels permutation154 permutation2
    _ = mixedMoment B node2798 node2798Labels := by rfl

def raw32526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32526 raw32526Labels = mixedMoment B node2798 node2798Labels := by
  calc
    _ = mixedMoment B node2798 node2798Labels := by rfl

def raw32527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw32527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw32527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32527 raw32527Labels = mixedMoment B node2524 node2524Labels := by
  calc
    mixedMoment B raw32527 raw32527Labels = mixedMoment B raw32527step0 raw32527step0Labels := by
      have ha : raw32527step0 = (fun i j => raw32527 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32527step0 raw32527; decide +kernel
      have hl : raw32527step0Labels = raw32527Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32527 raw32527Labels permutation664 permutation2
    mixedMoment B raw32527step0 raw32527step0Labels = mixedMoment B raw32527step1 raw32527step1Labels := by
      have ha : raw32527step1 = -raw32527step0 := by apply Matrix.ext; change ∀ i j, raw32527step1 i j = -(raw32527step0 i j); unfold raw32527step1 raw32527step0; decide +kernel
      have hl : raw32527step1Labels = raw32527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2524 node2524Labels := by rfl

def raw32528 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw32528Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32528step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw32528step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32528step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw32528step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32528step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw32528step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical32528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32528 raw32528Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw32528 raw32528Labels = mixedMoment B raw32528step0 raw32528step0Labels := by
      have hz : ∀ j, raw32528 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32528step0 = (fun i j => raw32528 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32528step0 raw32528; decide +kernel
      have hl : raw32528step0Labels = raw32528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32528 raw32528Labels permutation520 hz
    mixedMoment B raw32528step0 raw32528step0Labels = mixedMoment B raw32528step1 raw32528step1Labels := by
      have hz : ∀ j, raw32528step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw32528step1 = (fun i j => raw32528step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw32528step1 raw32528step0; decide +kernel
      have hl : raw32528step1Labels = raw32528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32528step0 raw32528step0Labels permutation104 hz
    mixedMoment B raw32528step1 raw32528step1Labels = mixedMoment B raw32528step2 raw32528step2Labels := by
      have ha : raw32528step2 = (fun i j => raw32528step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32528step2 raw32528step1; decide +kernel
      have hl : raw32528step2Labels = raw32528step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32528step1 raw32528step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw32529 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32529 raw32529Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw32529 raw32529Labels = mixedMoment B raw32529step0 raw32529step0Labels := by
      have ha : raw32529step0 = (fun i j => raw32529 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32529step0 raw32529; decide +kernel
      have hl : raw32529step0Labels = raw32529Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32529 raw32529Labels permutation194 permutation4
    mixedMoment B raw32529step0 raw32529step0Labels = mixedMoment B raw32529step1 raw32529step1Labels := by
      have ha : raw32529step1 = -raw32529step0 := by apply Matrix.ext; change ∀ i j, raw32529step1 i j = -(raw32529step0 i j); unfold raw32529step1 raw32529step0; decide +kernel
      have hl : raw32529step1Labels = raw32529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw32530 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw32530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32530 raw32530Labels = mixedMoment B node2036 node2036Labels := by
  calc
    mixedMoment B raw32530 raw32530Labels = mixedMoment B raw32530step0 raw32530step0Labels := by
      have ha : raw32530step0 = (fun i j => raw32530 (permutation197 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32530step0 raw32530; decide +kernel
      have hl : raw32530step0Labels = raw32530Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32530 raw32530Labels permutation197 permutation4
    mixedMoment B raw32530step0 raw32530step0Labels = mixedMoment B raw32530step1 raw32530step1Labels := by
      have ha : raw32530step1 = -raw32530step0 := by apply Matrix.ext; change ∀ i j, raw32530step1 i j = -(raw32530step0 i j); unfold raw32530step1 raw32530step0; decide +kernel
      have hl : raw32530step1Labels = raw32530step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2036 node2036Labels := by rfl

def raw32531 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32531 raw32531Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw32531 raw32531Labels = mixedMoment B raw32531step0 raw32531step0Labels := by
      have hz : ∀ j, raw32531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32531step0 = (fun i j => raw32531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32531step0 raw32531; decide +kernel
      have hl : raw32531step0Labels = raw32531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32531 raw32531Labels permutation346 hz
    mixedMoment B raw32531step0 raw32531step0Labels = mixedMoment B raw32531step1 raw32531step1Labels := by
      have ha : raw32531step1 = (fun i j => raw32531step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32531step1 raw32531step0; decide +kernel
      have hl : raw32531step1Labels = raw32531step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32531step0 raw32531step0Labels permutation50 permutation4
    mixedMoment B raw32531step1 raw32531step1Labels = mixedMoment B raw32531step2 raw32531step2Labels := by
      have ha : raw32531step2 = -raw32531step1 := by apply Matrix.ext; change ∀ i j, raw32531step2 i j = -(raw32531step1 i j); unfold raw32531step2 raw32531step1; decide +kernel
      have hl : raw32531step2Labels = raw32531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw32532 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32532 raw32532Labels = mixedMoment B node2031 node2031Labels := by
  calc
    mixedMoment B raw32532 raw32532Labels = mixedMoment B raw32532step0 raw32532step0Labels := by
      have ha : raw32532step0 = (fun i j => raw32532 (permutation195 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32532step0 raw32532; decide +kernel
      have hl : raw32532step0Labels = raw32532Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32532 raw32532Labels permutation195 permutation4
    mixedMoment B raw32532step0 raw32532step0Labels = mixedMoment B raw32532step1 raw32532step1Labels := by
      have ha : raw32532step1 = -raw32532step0 := by apply Matrix.ext; change ∀ i j, raw32532step1 i j = -(raw32532step0 i j); unfold raw32532step1 raw32532step0; decide +kernel
      have hl : raw32532step1Labels = raw32532step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2031 node2031Labels := by rfl

def raw32533 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32533 raw32533Labels = mixedMoment B node2031 node2031Labels := by
  calc
    mixedMoment B raw32533 raw32533Labels = mixedMoment B raw32533step0 raw32533step0Labels := by
      have ha : raw32533step0 = (fun i j => raw32533 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32533step0 raw32533; decide +kernel
      have hl : raw32533step0Labels = raw32533Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32533 raw32533Labels permutation194 permutation4
    mixedMoment B raw32533step0 raw32533step0Labels = mixedMoment B raw32533step1 raw32533step1Labels := by
      have ha : raw32533step1 = -raw32533step0 := by apply Matrix.ext; change ∀ i j, raw32533step1 i j = -(raw32533step0 i j); unfold raw32533step1 raw32533step0; decide +kernel
      have hl : raw32533step1Labels = raw32533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2031 node2031Labels := by rfl

def raw32534 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32534 raw32534Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw32534 raw32534Labels = mixedMoment B raw32534step0 raw32534step0Labels := by
      have ha : raw32534step0 = (fun i j => raw32534 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32534step0 raw32534; decide +kernel
      have hl : raw32534step0Labels = raw32534Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32534 raw32534Labels permutation176 permutation4
    mixedMoment B raw32534step0 raw32534step0Labels = mixedMoment B raw32534step1 raw32534step1Labels := by
      have ha : raw32534step1 = -raw32534step0 := by apply Matrix.ext; change ∀ i j, raw32534step1 i j = -(raw32534step0 i j); unfold raw32534step1 raw32534step0; decide +kernel
      have hl : raw32534step1Labels = raw32534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2046 node2046Labels := by rfl

def raw32535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32535 raw32535Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw32535 raw32535Labels = mixedMoment B raw32535step0 raw32535step0Labels := by
      have hz : ∀ j, raw32535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32535step0 = (fun i j => raw32535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32535step0 raw32535; decide +kernel
      have hl : raw32535step0Labels = raw32535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32535 raw32535Labels permutation346 hz
    mixedMoment B raw32535step0 raw32535step0Labels = mixedMoment B raw32535step1 raw32535step1Labels := by
      have ha : raw32535step1 = (fun i j => raw32535step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32535step1 raw32535step0; decide +kernel
      have hl : raw32535step1Labels = raw32535step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32535step0 raw32535step0Labels permutation58 permutation2
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw32536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32536 raw32536Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw32536 raw32536Labels = mixedMoment B raw32536step0 raw32536step0Labels := by
      have hz : ∀ j, raw32536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32536step0 = (fun i j => raw32536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32536step0 raw32536; decide +kernel
      have hl : raw32536step0Labels = raw32536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32536 raw32536Labels permutation346 hz
    mixedMoment B raw32536step0 raw32536step0Labels = mixedMoment B raw32536step1 raw32536step1Labels := by
      have ha : raw32536step1 = (fun i j => raw32536step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32536step1 raw32536step0; decide +kernel
      have hl : raw32536step1Labels = raw32536step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32536step0 raw32536step0Labels permutation34 permutation2
    _ = mixedMoment B node2885 node2885Labels := by rfl

def raw32537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32537 raw32537Labels = mixedMoment B node2810 node2810Labels := by
  calc
    mixedMoment B raw32537 raw32537Labels = mixedMoment B raw32537step0 raw32537step0Labels := by
      have ha : raw32537step0 = (fun i j => raw32537 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32537step0 raw32537; decide +kernel
      have hl : raw32537step0Labels = raw32537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32537 raw32537Labels permutation154 permutation2
    _ = mixedMoment B node2810 node2810Labels := by rfl

def raw32538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32538 raw32538Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw32538 raw32538Labels = mixedMoment B raw32538step0 raw32538step0Labels := by
      have hz : ∀ j, raw32538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32538step0 = (fun i j => raw32538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32538step0 raw32538; decide +kernel
      have hl : raw32538step0Labels = raw32538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32538 raw32538Labels permutation346 hz
    mixedMoment B raw32538step0 raw32538step0Labels = mixedMoment B raw32538step1 raw32538step1Labels := by
      have ha : raw32538step1 = (fun i j => raw32538step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32538step1 raw32538step0; decide +kernel
      have hl : raw32538step1Labels = raw32538step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32538step0 raw32538step0Labels permutation35 permutation2
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw32539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw32539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw32539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32539 raw32539Labels = mixedMoment B node2819 node2819Labels := by
  calc
    mixedMoment B raw32539 raw32539Labels = mixedMoment B raw32539step0 raw32539step0Labels := by
      have hz : ∀ j, raw32539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32539step0 = (fun i j => raw32539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32539step0 raw32539; decide +kernel
      have hl : raw32539step0Labels = raw32539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32539 raw32539Labels permutation346 hz
    mixedMoment B raw32539step0 raw32539step0Labels = mixedMoment B raw32539step1 raw32539step1Labels := by
      have ha : raw32539step1 = (fun i j => raw32539step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32539step1 raw32539step0; decide +kernel
      have hl : raw32539step1Labels = raw32539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32539step0 raw32539step0Labels permutation33 permutation2
    _ = mixedMoment B node2819 node2819Labels := by rfl

def raw32540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw32540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw32540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw32540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32540 raw32540Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw32540 raw32540Labels = mixedMoment B raw32540step0 raw32540step0Labels := by
      have hz : ∀ j, raw32540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32540step0 = (fun i j => raw32540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32540step0 raw32540; decide +kernel
      have hl : raw32540step0Labels = raw32540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32540 raw32540Labels permutation346 hz
    mixedMoment B raw32540step0 raw32540step0Labels = mixedMoment B raw32540step1 raw32540step1Labels := by
      have ha : raw32540step1 = (fun i j => raw32540step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32540step1 raw32540step0; decide +kernel
      have hl : raw32540step1Labels = raw32540step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32540step0 raw32540step0Labels permutation34 permutation2
    _ = mixedMoment B node2816 node2816Labels := by rfl

def raw32541 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1], ![0, 0]]
def raw32541Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32541step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]
def raw32541step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32541step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw32541step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32541step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw32541step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical32541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32541 raw32541Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw32541 raw32541Labels = mixedMoment B raw32541step0 raw32541step0Labels := by
      have hz : ∀ j, raw32541 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw32541step0 = (fun i j => raw32541 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw32541step0 raw32541; decide +kernel
      have hl : raw32541step0Labels = raw32541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32541 raw32541Labels permutation590 hz
    mixedMoment B raw32541step0 raw32541step0Labels = mixedMoment B raw32541step1 raw32541step1Labels := by
      have hz : ∀ j, raw32541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32541step1 = (fun i j => raw32541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32541step1 raw32541step0; decide +kernel
      have hl : raw32541step1Labels = raw32541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32541step0 raw32541step0Labels permutation80 hz
    mixedMoment B raw32541step1 raw32541step1Labels = mixedMoment B raw32541step2 raw32541step2Labels := by
      have ha : raw32541step2 = (fun i j => raw32541step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32541step2 raw32541step1; decide +kernel
      have hl : raw32541step2Labels = raw32541step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32541step1 raw32541step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw32542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32542 raw32542Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw32542 raw32542Labels = mixedMoment B raw32542step0 raw32542step0Labels := by
      have hz : ∀ j, raw32542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32542step0 = (fun i j => raw32542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32542step0 raw32542; decide +kernel
      have hl : raw32542step0Labels = raw32542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32542 raw32542Labels permutation346 hz
    mixedMoment B raw32542step0 raw32542step0Labels = mixedMoment B raw32542step1 raw32542step1Labels := by
      have ha : raw32542step1 = (fun i j => raw32542step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32542step1 raw32542step0; decide +kernel
      have hl : raw32542step1Labels = raw32542step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32542step0 raw32542step0Labels permutation58 permutation2
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw32543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32543 raw32543Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw32543 raw32543Labels = mixedMoment B raw32543step0 raw32543step0Labels := by
      have hz : ∀ j, raw32543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32543step0 = (fun i j => raw32543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32543step0 raw32543; decide +kernel
      have hl : raw32543step0Labels = raw32543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32543 raw32543Labels permutation346 hz
    mixedMoment B raw32543step0 raw32543step0Labels = mixedMoment B raw32543step1 raw32543step1Labels := by
      have ha : raw32543step1 = (fun i j => raw32543step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32543step1 raw32543step0; decide +kernel
      have hl : raw32543step1Labels = raw32543step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32543step0 raw32543step0Labels permutation34 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw32544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32544 raw32544Labels = mixedMoment B node2808 node2808Labels := by
  calc
    mixedMoment B raw32544 raw32544Labels = mixedMoment B raw32544step0 raw32544step0Labels := by
      have ha : raw32544step0 = (fun i j => raw32544 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32544step0 raw32544; decide +kernel
      have hl : raw32544step0Labels = raw32544Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32544 raw32544Labels permutation154 permutation2
    _ = mixedMoment B node2808 node2808Labels := by rfl

def raw32545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32545 raw32545Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw32545 raw32545Labels = mixedMoment B raw32545step0 raw32545step0Labels := by
      have hz : ∀ j, raw32545 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32545step0 = (fun i j => raw32545 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32545step0 raw32545; decide +kernel
      have hl : raw32545step0Labels = raw32545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32545 raw32545Labels permutation346 hz
    mixedMoment B raw32545step0 raw32545step0Labels = mixedMoment B raw32545step1 raw32545step1Labels := by
      have ha : raw32545step1 = (fun i j => raw32545step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32545step1 raw32545step0; decide +kernel
      have hl : raw32545step1Labels = raw32545step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32545step0 raw32545step0Labels permutation35 permutation2
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw32546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32546 raw32546Labels = mixedMoment B node2819 node2819Labels := by
  calc
    mixedMoment B raw32546 raw32546Labels = mixedMoment B raw32546step0 raw32546step0Labels := by
      have hz : ∀ j, raw32546 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32546step0 = (fun i j => raw32546 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32546step0 raw32546; decide +kernel
      have hl : raw32546step0Labels = raw32546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32546 raw32546Labels permutation346 hz
    _ = mixedMoment B node2819 node2819Labels := by rfl

def raw32547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw32547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw32547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32547 raw32547Labels = mixedMoment B node2811 node2811Labels := by
  calc
    mixedMoment B raw32547 raw32547Labels = mixedMoment B raw32547step0 raw32547step0Labels := by
      have hz : ∀ j, raw32547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32547step0 = (fun i j => raw32547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32547step0 raw32547; decide +kernel
      have hl : raw32547step0Labels = raw32547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32547 raw32547Labels permutation346 hz
    mixedMoment B raw32547step0 raw32547step0Labels = mixedMoment B raw32547step1 raw32547step1Labels := by
      have ha : raw32547step1 = (fun i j => raw32547step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32547step1 raw32547step0; decide +kernel
      have hl : raw32547step1Labels = raw32547step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32547step0 raw32547step0Labels permutation34 permutation2
    _ = mixedMoment B node2811 node2811Labels := by rfl

def raw32548 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]
def raw32548Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32548step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]
def raw32548step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32548step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw32548step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32548step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw32548step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical32548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32548 raw32548Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw32548 raw32548Labels = mixedMoment B raw32548step0 raw32548step0Labels := by
      have hz : ∀ j, raw32548 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32548step0 = (fun i j => raw32548 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32548step0 raw32548; decide +kernel
      have hl : raw32548step0Labels = raw32548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32548 raw32548Labels permutation520 hz
    mixedMoment B raw32548step0 raw32548step0Labels = mixedMoment B raw32548step1 raw32548step1Labels := by
      have hz : ∀ j, raw32548step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32548step1 = (fun i j => raw32548step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32548step1 raw32548step0; decide +kernel
      have hl : raw32548step1Labels = raw32548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32548step0 raw32548step0Labels permutation80 hz
    mixedMoment B raw32548step1 raw32548step1Labels = mixedMoment B raw32548step2 raw32548step2Labels := by
      have ha : raw32548step2 = (fun i j => raw32548step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32548step2 raw32548step1; decide +kernel
      have hl : raw32548step2Labels = raw32548step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32548step1 raw32548step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw32549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32549 raw32549Labels = mixedMoment B node5148 node5148Labels := by
  calc
    mixedMoment B raw32549 raw32549Labels = mixedMoment B raw32549step0 raw32549step0Labels := by
      have ha : raw32549step0 = (fun i j => raw32549 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32549step0 raw32549; decide +kernel
      have hl : raw32549step0Labels = raw32549Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32549 raw32549Labels permutation176 permutation2
    _ = mixedMoment B node5148 node5148Labels := by rfl

def raw32550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32550 raw32550Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw32550 raw32550Labels = mixedMoment B raw32550step0 raw32550step0Labels := by
      have hz : ∀ j, raw32550 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32550step0 = (fun i j => raw32550 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32550step0 raw32550; decide +kernel
      have hl : raw32550step0Labels = raw32550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32550 raw32550Labels permutation520 hz
    mixedMoment B raw32550step0 raw32550step0Labels = mixedMoment B raw32550step1 raw32550step1Labels := by
      have hz : ∀ j, raw32550step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32550step1 = (fun i j => raw32550step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32550step1 raw32550step0; decide +kernel
      have hl : raw32550step1Labels = raw32550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32550step0 raw32550step0Labels permutation80 hz
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw32551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32551 raw32551Labels = mixedMoment B node4980 node4980Labels := by
  calc
    _ = mixedMoment B node4980 node4980Labels := by rfl

def raw32552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32552 raw32552Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw32552 raw32552Labels = mixedMoment B raw32552step0 raw32552step0Labels := by
      have hz : ∀ j, raw32552 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32552step0 = (fun i j => raw32552 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32552step0 raw32552; decide +kernel
      have hl : raw32552step0Labels = raw32552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32552 raw32552Labels permutation520 hz
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw32553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32553step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32553step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32553 raw32553Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw32553 raw32553Labels = mixedMoment B raw32553step0 raw32553step0Labels := by
      have hz : ∀ j, raw32553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32553step0 = (fun i j => raw32553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32553step0 raw32553; decide +kernel
      have hl : raw32553step0Labels = raw32553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32553 raw32553Labels permutation346 hz
    mixedMoment B raw32553step0 raw32553step0Labels = mixedMoment B raw32553step1 raw32553step1Labels := by
      have ha : raw32553step1 = (fun i j => raw32553step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32553step1 raw32553step0; decide +kernel
      have hl : raw32553step1Labels = raw32553step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32553step0 raw32553step0Labels permutation35 permutation3
    mixedMoment B raw32553step1 raw32553step1Labels = mixedMoment B raw32553step2 raw32553step2Labels := by
      have ha : raw32553step2 = raw32553step1 := by apply Matrix.ext; unfold raw32553step2 raw32553step1; decide +kernel
      have hl : raw32553step1Labels = labelEmbedding6 ∘ raw32553step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32553step1 raw32553step1Labels raw32553step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

def raw32554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32554 raw32554Labels = mixedMoment B node4983 node4983Labels := by
  calc
    mixedMoment B raw32554 raw32554Labels = mixedMoment B raw32554step0 raw32554step0Labels := by
      have hz : ∀ j, raw32554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32554step0 = (fun i j => raw32554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32554step0 raw32554; decide +kernel
      have hl : raw32554step0Labels = raw32554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32554 raw32554Labels permutation346 hz
    mixedMoment B raw32554step0 raw32554step0Labels = mixedMoment B raw32554step1 raw32554step1Labels := by
      have ha : raw32554step1 = (fun i j => raw32554step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32554step1 raw32554step0; decide +kernel
      have hl : raw32554step1Labels = raw32554step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32554step0 raw32554step0Labels permutation34 permutation2
    _ = mixedMoment B node4983 node4983Labels := by rfl

def raw32555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32555 raw32555Labels = mixedMoment B node5119 node5119Labels := by
  calc
    mixedMoment B raw32555 raw32555Labels = mixedMoment B raw32555step0 raw32555step0Labels := by
      have ha : raw32555step0 = (fun i j => raw32555 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32555step0 raw32555; decide +kernel
      have hl : raw32555step0Labels = raw32555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32555 raw32555Labels permutation178 permutation2
    _ = mixedMoment B node5119 node5119Labels := by rfl

def raw32556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32556 raw32556Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw32556 raw32556Labels = mixedMoment B raw32556step0 raw32556step0Labels := by
      have hz : ∀ j, raw32556 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32556step0 = (fun i j => raw32556 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32556step0 raw32556; decide +kernel
      have hl : raw32556step0Labels = raw32556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32556 raw32556Labels permutation520 hz
    mixedMoment B raw32556step0 raw32556step0Labels = mixedMoment B raw32556step1 raw32556step1Labels := by
      have hz : ∀ j, raw32556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32556step1 = (fun i j => raw32556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32556step1 raw32556step0; decide +kernel
      have hl : raw32556step1Labels = raw32556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32556step0 raw32556step0Labels permutation80 hz
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw32557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32557 raw32557Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw32557 raw32557Labels = mixedMoment B raw32557step0 raw32557step0Labels := by
      have hz : ∀ j, raw32557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32557step0 = (fun i j => raw32557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32557step0 raw32557; decide +kernel
      have hl : raw32557step0Labels = raw32557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32557 raw32557Labels permutation346 hz
    mixedMoment B raw32557step0 raw32557step0Labels = mixedMoment B raw32557step1 raw32557step1Labels := by
      have ha : raw32557step1 = (fun i j => raw32557step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32557step1 raw32557step0; decide +kernel
      have hl : raw32557step1Labels = raw32557step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32557step0 raw32557step0Labels permutation35 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw32558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32558 raw32558Labels = mixedMoment B node2927 node2927Labels := by
  calc
    mixedMoment B raw32558 raw32558Labels = mixedMoment B raw32558step0 raw32558step0Labels := by
      have ha : raw32558step0 = (fun i j => raw32558 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32558step0 raw32558; decide +kernel
      have hl : raw32558step0Labels = raw32558Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32558 raw32558Labels permutation176 permutation3
    _ = mixedMoment B node2927 node2927Labels := by rfl

def raw32559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32559step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32559 raw32559Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw32559 raw32559Labels = mixedMoment B raw32559step0 raw32559step0Labels := by
      have hz : ∀ j, raw32559 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32559step0 = (fun i j => raw32559 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32559step0 raw32559; decide +kernel
      have hl : raw32559step0Labels = raw32559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32559 raw32559Labels permutation520 hz
    mixedMoment B raw32559step0 raw32559step0Labels = mixedMoment B raw32559step1 raw32559step1Labels := by
      have hz : ∀ j, raw32559step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32559step1 = (fun i j => raw32559step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32559step1 raw32559step0; decide +kernel
      have hl : raw32559step1Labels = raw32559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32559step0 raw32559step0Labels permutation80 hz
    mixedMoment B raw32559step1 raw32559step1Labels = mixedMoment B raw32559step2 raw32559step2Labels := by
      have ha : raw32559step2 = (fun i j => raw32559step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32559step2 raw32559step1; decide +kernel
      have hl : raw32559step2Labels = raw32559step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32559step1 raw32559step1Labels permutation8 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw32560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32560 raw32560Labels = mixedMoment B node2793 node2793Labels := by
  calc
    mixedMoment B raw32560 raw32560Labels = mixedMoment B raw32560step0 raw32560step0Labels := by
      have ha : raw32560step0 = (fun i j => raw32560 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32560step0 raw32560; decide +kernel
      have hl : raw32560step0Labels = raw32560Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32560 raw32560Labels permutation152 permutation3
    _ = mixedMoment B node2793 node2793Labels := by rfl

def raw32561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32561step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32561 raw32561Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw32561 raw32561Labels = mixedMoment B raw32561step0 raw32561step0Labels := by
      have hz : ∀ j, raw32561 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32561step0 = (fun i j => raw32561 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32561step0 raw32561; decide +kernel
      have hl : raw32561step0Labels = raw32561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32561 raw32561Labels permutation520 hz
    mixedMoment B raw32561step0 raw32561step0Labels = mixedMoment B raw32561step1 raw32561step1Labels := by
      have ha : raw32561step1 = (fun i j => raw32561step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32561step1 raw32561step0; decide +kernel
      have hl : raw32561step1Labels = raw32561step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32561step0 raw32561step0Labels permutation32 permutation3
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw32562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32562 raw32562Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw32562 raw32562Labels = mixedMoment B raw32562step0 raw32562step0Labels := by
      have hz : ∀ j, raw32562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32562step0 = (fun i j => raw32562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32562step0 raw32562; decide +kernel
      have hl : raw32562step0Labels = raw32562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32562 raw32562Labels permutation346 hz
    mixedMoment B raw32562step0 raw32562step0Labels = mixedMoment B raw32562step1 raw32562step1Labels := by
      have ha : raw32562step1 = (fun i j => raw32562step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32562step1 raw32562step0; decide +kernel
      have hl : raw32562step1Labels = raw32562step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32562step0 raw32562step0Labels permutation35 permutation3
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw32563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32563 raw32563Labels = mixedMoment B node2794 node2794Labels := by
  calc
    mixedMoment B raw32563 raw32563Labels = mixedMoment B raw32563step0 raw32563step0Labels := by
      have hz : ∀ j, raw32563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32563step0 = (fun i j => raw32563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32563step0 raw32563; decide +kernel
      have hl : raw32563step0Labels = raw32563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32563 raw32563Labels permutation346 hz
    mixedMoment B raw32563step0 raw32563step0Labels = mixedMoment B raw32563step1 raw32563step1Labels := by
      have ha : raw32563step1 = (fun i j => raw32563step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32563step1 raw32563step0; decide +kernel
      have hl : raw32563step1Labels = raw32563step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32563step0 raw32563step0Labels permutation35 permutation3
    _ = mixedMoment B node2794 node2794Labels := by rfl

def raw32564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32564 raw32564Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw32564 raw32564Labels = mixedMoment B raw32564step0 raw32564step0Labels := by
      have ha : raw32564step0 = (fun i j => raw32564 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32564step0 raw32564; decide +kernel
      have hl : raw32564step0Labels = raw32564Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32564 raw32564Labels permutation155 permutation3
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw32565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32565step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw32565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32565 raw32565Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw32565 raw32565Labels = mixedMoment B raw32565step0 raw32565step0Labels := by
      have hz : ∀ j, raw32565 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32565step0 = (fun i j => raw32565 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32565step0 raw32565; decide +kernel
      have hl : raw32565step0Labels = raw32565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32565 raw32565Labels permutation520 hz
    mixedMoment B raw32565step0 raw32565step0Labels = mixedMoment B raw32565step1 raw32565step1Labels := by
      have hz : ∀ j, raw32565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32565step1 = (fun i j => raw32565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32565step1 raw32565step0; decide +kernel
      have hl : raw32565step1Labels = raw32565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32565step0 raw32565step0Labels permutation80 hz
    mixedMoment B raw32565step1 raw32565step1Labels = mixedMoment B raw32565step2 raw32565step2Labels := by
      have ha : raw32565step2 = (fun i j => raw32565step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32565step2 raw32565step1; decide +kernel
      have hl : raw32565step2Labels = raw32565step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32565step1 raw32565step1Labels permutation9 permutation3
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw32566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32566step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32566 raw32566Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw32566 raw32566Labels = mixedMoment B raw32566step0 raw32566step0Labels := by
      have hz : ∀ j, raw32566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32566step0 = (fun i j => raw32566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32566step0 raw32566; decide +kernel
      have hl : raw32566step0Labels = raw32566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32566 raw32566Labels permutation346 hz
    mixedMoment B raw32566step0 raw32566step0Labels = mixedMoment B raw32566step1 raw32566step1Labels := by
      have ha : raw32566step1 = (fun i j => raw32566step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32566step1 raw32566step0; decide +kernel
      have hl : raw32566step1Labels = raw32566step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32566step0 raw32566step0Labels permutation37 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw32567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32567 raw32567Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw32567 raw32567Labels = mixedMoment B raw32567step0 raw32567step0Labels := by
      have hz : ∀ j, raw32567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32567step0 = (fun i j => raw32567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32567step0 raw32567; decide +kernel
      have hl : raw32567step0Labels = raw32567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32567 raw32567Labels permutation346 hz
    mixedMoment B raw32567step0 raw32567step0Labels = mixedMoment B raw32567step1 raw32567step1Labels := by
      have ha : raw32567step1 = (fun i j => raw32567step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32567step1 raw32567step0; decide +kernel
      have hl : raw32567step1Labels = raw32567step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32567step0 raw32567step0Labels permutation56 permutation2
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw32568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32568 raw32568Labels = mixedMoment B node5469 node5469Labels := by
  calc
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw32569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32569 raw32569Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw32569 raw32569Labels = mixedMoment B raw32569step0 raw32569step0Labels := by
      have hz : ∀ j, raw32569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32569step0 = (fun i j => raw32569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32569step0 raw32569; decide +kernel
      have hl : raw32569step0Labels = raw32569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32569 raw32569Labels permutation346 hz
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw32570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32570 raw32570Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw32570 raw32570Labels = mixedMoment B raw32570step0 raw32570step0Labels := by
      have hz : ∀ j, raw32570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32570step0 = (fun i j => raw32570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32570step0 raw32570; decide +kernel
      have hl : raw32570step0Labels = raw32570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32570 raw32570Labels permutation346 hz
    mixedMoment B raw32570step0 raw32570step0Labels = mixedMoment B raw32570step1 raw32570step1Labels := by
      have ha : raw32570step1 = (fun i j => raw32570step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32570step1 raw32570step0; decide +kernel
      have hl : raw32570step1Labels = raw32570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32570step0 raw32570step0Labels permutation34 permutation2
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw32571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32571 raw32571Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw32571 raw32571Labels = mixedMoment B raw32571step0 raw32571step0Labels := by
      have hz : ∀ j, raw32571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32571step0 = (fun i j => raw32571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32571step0 raw32571; decide +kernel
      have hl : raw32571step0Labels = raw32571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32571 raw32571Labels permutation346 hz
    _ = mixedMoment B node5474 node5474Labels := by rfl

def raw32572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32572step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32572 raw32572Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw32572 raw32572Labels = mixedMoment B raw32572step0 raw32572step0Labels := by
      have hz : ∀ j, raw32572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32572step0 = (fun i j => raw32572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32572step0 raw32572; decide +kernel
      have hl : raw32572step0Labels = raw32572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32572 raw32572Labels permutation346 hz
    mixedMoment B raw32572step0 raw32572step0Labels = mixedMoment B raw32572step1 raw32572step1Labels := by
      have ha : raw32572step1 = (fun i j => raw32572step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32572step1 raw32572step0; decide +kernel
      have hl : raw32572step1Labels = raw32572step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32572step0 raw32572step0Labels permutation32 permutation3
    mixedMoment B raw32572step1 raw32572step1Labels = mixedMoment B raw32572step2 raw32572step2Labels := by
      have ha : raw32572step2 = raw32572step1 := by apply Matrix.ext; unfold raw32572step2 raw32572step1; decide +kernel
      have hl : raw32572step1Labels = labelEmbedding6 ∘ raw32572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32572step1 raw32572step1Labels raw32572step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw32573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32573step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32573 raw32573Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw32573 raw32573Labels = mixedMoment B raw32573step0 raw32573step0Labels := by
      have ha : raw32573step0 = (fun i j => raw32573 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32573step0 raw32573; decide +kernel
      have hl : raw32573step0Labels = raw32573Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32573 raw32573Labels permutation176 permutation3
    mixedMoment B raw32573step0 raw32573step0Labels = mixedMoment B raw32573step1 raw32573step1Labels := by
      have ha : raw32573step1 = raw32573step0 := by apply Matrix.ext; unfold raw32573step1 raw32573step0; decide +kernel
      have hl : raw32573step0Labels = labelEmbedding6 ∘ raw32573step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32573step0 raw32573step0Labels raw32573step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw32574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32574step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32574 raw32574Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw32574 raw32574Labels = mixedMoment B raw32574step0 raw32574step0Labels := by
      have hz : ∀ j, raw32574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32574step0 = (fun i j => raw32574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32574step0 raw32574; decide +kernel
      have hl : raw32574step0Labels = raw32574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32574 raw32574Labels permutation346 hz
    mixedMoment B raw32574step0 raw32574step0Labels = mixedMoment B raw32574step1 raw32574step1Labels := by
      have ha : raw32574step1 = (fun i j => raw32574step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32574step1 raw32574step0; decide +kernel
      have hl : raw32574step1Labels = raw32574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32574step0 raw32574step0Labels permutation38 permutation3
    mixedMoment B raw32574step1 raw32574step1Labels = mixedMoment B raw32574step2 raw32574step2Labels := by
      have ha : raw32574step2 = raw32574step1 := by apply Matrix.ext; unfold raw32574step2 raw32574step1; decide +kernel
      have hl : raw32574step1Labels = labelEmbedding6 ∘ raw32574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32574step1 raw32574step1Labels raw32574step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw32575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32575step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32575 raw32575Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw32575 raw32575Labels = mixedMoment B raw32575step0 raw32575step0Labels := by
      have hz : ∀ j, raw32575 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32575step0 = (fun i j => raw32575 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32575step0 raw32575; decide +kernel
      have hl : raw32575step0Labels = raw32575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32575 raw32575Labels permutation346 hz
    mixedMoment B raw32575step0 raw32575step0Labels = mixedMoment B raw32575step1 raw32575step1Labels := by
      have ha : raw32575step1 = (fun i j => raw32575step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32575step1 raw32575step0; decide +kernel
      have hl : raw32575step1Labels = raw32575step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32575step0 raw32575step0Labels permutation44 permutation3
    mixedMoment B raw32575step1 raw32575step1Labels = mixedMoment B raw32575step2 raw32575step2Labels := by
      have ha : raw32575step2 = raw32575step1 := by apply Matrix.ext; unfold raw32575step2 raw32575step1; decide +kernel
      have hl : raw32575step1Labels = labelEmbedding6 ∘ raw32575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32575step1 raw32575step1Labels raw32575step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw32576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw32576step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw32576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32576 raw32576Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw32576 raw32576Labels = mixedMoment B raw32576step0 raw32576step0Labels := by
      have hz : ∀ j, raw32576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32576step0 = (fun i j => raw32576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32576step0 raw32576; decide +kernel
      have hl : raw32576step0Labels = raw32576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32576 raw32576Labels permutation346 hz
    mixedMoment B raw32576step0 raw32576step0Labels = mixedMoment B raw32576step1 raw32576step1Labels := by
      have ha : raw32576step1 = (fun i j => raw32576step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32576step1 raw32576step0; decide +kernel
      have hl : raw32576step1Labels = raw32576step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32576step0 raw32576step0Labels permutation32 permutation3
    mixedMoment B raw32576step1 raw32576step1Labels = mixedMoment B raw32576step2 raw32576step2Labels := by
      have ha : raw32576step2 = raw32576step1 := by apply Matrix.ext; unfold raw32576step2 raw32576step1; decide +kernel
      have hl : raw32576step1Labels = labelEmbedding6 ∘ raw32576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32576step1 raw32576step1Labels raw32576step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw32577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32577step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32577 raw32577Labels = mixedMoment B node4364 node4364Labels := by
  calc
    mixedMoment B raw32577 raw32577Labels = mixedMoment B raw32577step0 raw32577step0Labels := by
      have ha : raw32577step0 = (fun i j => raw32577 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32577step0 raw32577; decide +kernel
      have hl : raw32577step0Labels = raw32577Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32577 raw32577Labels permutation160 permutation3
    mixedMoment B raw32577step0 raw32577step0Labels = mixedMoment B raw32577step1 raw32577step1Labels := by
      have ha : raw32577step1 = raw32577step0 := by apply Matrix.ext; unfold raw32577step1 raw32577step0; decide +kernel
      have hl : raw32577step0Labels = labelEmbedding6 ∘ raw32577step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32577step0 raw32577step0Labels raw32577step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4364 node4364Labels := by rfl

def raw32578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32578step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32578 raw32578Labels = mixedMoment B node4968 node4968Labels := by
  calc
    mixedMoment B raw32578 raw32578Labels = mixedMoment B raw32578step0 raw32578step0Labels := by
      have ha : raw32578step0 = (fun i j => raw32578 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32578step0 raw32578; decide +kernel
      have hl : raw32578step0Labels = raw32578Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32578 raw32578Labels permutation160 permutation3
    mixedMoment B raw32578step0 raw32578step0Labels = mixedMoment B raw32578step1 raw32578step1Labels := by
      have ha : raw32578step1 = raw32578step0 := by apply Matrix.ext; unfold raw32578step1 raw32578step0; decide +kernel
      have hl : raw32578step0Labels = labelEmbedding6 ∘ raw32578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32578step0 raw32578step0Labels raw32578step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4968 node4968Labels := by rfl

def raw32579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32579step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32579 raw32579Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw32579 raw32579Labels = mixedMoment B raw32579step0 raw32579step0Labels := by
      have ha : raw32579step0 = (fun i j => raw32579 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32579step0 raw32579; decide +kernel
      have hl : raw32579step0Labels = raw32579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32579 raw32579Labels permutation160 permutation3
    mixedMoment B raw32579step0 raw32579step0Labels = mixedMoment B raw32579step1 raw32579step1Labels := by
      have ha : raw32579step1 = raw32579step0 := by apply Matrix.ext; unfold raw32579step1 raw32579step0; decide +kernel
      have hl : raw32579step0Labels = labelEmbedding6 ∘ raw32579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32579step0 raw32579step0Labels raw32579step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw32580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32580step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32580 raw32580Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw32580 raw32580Labels = mixedMoment B raw32580step0 raw32580step0Labels := by
      have ha : raw32580step0 = (fun i j => raw32580 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32580step0 raw32580; decide +kernel
      have hl : raw32580step0Labels = raw32580Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32580 raw32580Labels permutation166 permutation3
    mixedMoment B raw32580step0 raw32580step0Labels = mixedMoment B raw32580step1 raw32580step1Labels := by
      have ha : raw32580step1 = raw32580step0 := by apply Matrix.ext; unfold raw32580step1 raw32580step0; decide +kernel
      have hl : raw32580step0Labels = labelEmbedding6 ∘ raw32580step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32580step0 raw32580step0Labels raw32580step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw32581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32581step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32581 raw32581Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw32581 raw32581Labels = mixedMoment B raw32581step0 raw32581step0Labels := by
      have ha : raw32581step0 = (fun i j => raw32581 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32581step0 raw32581; decide +kernel
      have hl : raw32581step0Labels = raw32581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32581 raw32581Labels permutation161 permutation3
    mixedMoment B raw32581step0 raw32581step0Labels = mixedMoment B raw32581step1 raw32581step1Labels := by
      have ha : raw32581step1 = raw32581step0 := by apply Matrix.ext; unfold raw32581step1 raw32581step0; decide +kernel
      have hl : raw32581step0Labels = labelEmbedding6 ∘ raw32581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32581step0 raw32581step0Labels raw32581step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw32582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32582step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32582 raw32582Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw32582 raw32582Labels = mixedMoment B raw32582step0 raw32582step0Labels := by
      have hz : ∀ j, raw32582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32582step0 = (fun i j => raw32582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32582step0 raw32582; decide +kernel
      have hl : raw32582step0Labels = raw32582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32582 raw32582Labels permutation346 hz
    mixedMoment B raw32582step0 raw32582step0Labels = mixedMoment B raw32582step1 raw32582step1Labels := by
      have ha : raw32582step1 = (fun i j => raw32582step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32582step1 raw32582step0; decide +kernel
      have hl : raw32582step1Labels = raw32582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32582step0 raw32582step0Labels permutation34 permutation3
    mixedMoment B raw32582step1 raw32582step1Labels = mixedMoment B raw32582step2 raw32582step2Labels := by
      have ha : raw32582step2 = raw32582step1 := by apply Matrix.ext; unfold raw32582step2 raw32582step1; decide +kernel
      have hl : raw32582step1Labels = labelEmbedding6 ∘ raw32582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32582step1 raw32582step1Labels raw32582step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4369 node4369Labels := by rfl

def raw32583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32583step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32583step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32583step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32583 raw32583Labels = mixedMoment B node4974 node4974Labels := by
  calc
    mixedMoment B raw32583 raw32583Labels = mixedMoment B raw32583step0 raw32583step0Labels := by
      have hz : ∀ j, raw32583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32583step0 = (fun i j => raw32583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32583step0 raw32583; decide +kernel
      have hl : raw32583step0Labels = raw32583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32583 raw32583Labels permutation346 hz
    mixedMoment B raw32583step0 raw32583step0Labels = mixedMoment B raw32583step1 raw32583step1Labels := by
      have ha : raw32583step1 = (fun i j => raw32583step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32583step1 raw32583step0; decide +kernel
      have hl : raw32583step1Labels = raw32583step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32583step0 raw32583step0Labels permutation34 permutation3
    mixedMoment B raw32583step1 raw32583step1Labels = mixedMoment B raw32583step2 raw32583step2Labels := by
      have ha : raw32583step2 = raw32583step1 := by apply Matrix.ext; unfold raw32583step2 raw32583step1; decide +kernel
      have hl : raw32583step1Labels = labelEmbedding6 ∘ raw32583step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32583step1 raw32583step1Labels raw32583step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4974 node4974Labels := by rfl

def raw32584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32584step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32584 raw32584Labels = mixedMoment B node5043 node5043Labels := by
  calc
    mixedMoment B raw32584 raw32584Labels = mixedMoment B raw32584step0 raw32584step0Labels := by
      have ha : raw32584step0 = (fun i j => raw32584 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32584step0 raw32584; decide +kernel
      have hl : raw32584step0Labels = raw32584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32584 raw32584Labels permutation178 permutation3
    mixedMoment B raw32584step0 raw32584step0Labels = mixedMoment B raw32584step1 raw32584step1Labels := by
      have ha : raw32584step1 = raw32584step0 := by apply Matrix.ext; unfold raw32584step1 raw32584step0; decide +kernel
      have hl : raw32584step0Labels = labelEmbedding6 ∘ raw32584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32584step0 raw32584step0Labels raw32584step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5043 node5043Labels := by rfl

def raw32585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32585step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32585 raw32585Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw32585 raw32585Labels = mixedMoment B raw32585step0 raw32585step0Labels := by
      have hz : ∀ j, raw32585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32585step0 = (fun i j => raw32585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32585step0 raw32585; decide +kernel
      have hl : raw32585step0Labels = raw32585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32585 raw32585Labels permutation346 hz
    mixedMoment B raw32585step0 raw32585step0Labels = mixedMoment B raw32585step1 raw32585step1Labels := by
      have ha : raw32585step1 = (fun i j => raw32585step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32585step1 raw32585step0; decide +kernel
      have hl : raw32585step1Labels = raw32585step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32585step0 raw32585step0Labels permutation34 permutation3
    mixedMoment B raw32585step1 raw32585step1Labels = mixedMoment B raw32585step2 raw32585step2Labels := by
      have ha : raw32585step2 = raw32585step1 := by apply Matrix.ext; unfold raw32585step2 raw32585step1; decide +kernel
      have hl : raw32585step1Labels = labelEmbedding6 ∘ raw32585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32585step1 raw32585step1Labels raw32585step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw32586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32586 raw32586Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw32586 raw32586Labels = mixedMoment B raw32586step0 raw32586step0Labels := by
      have hz : ∀ j, raw32586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32586step0 = (fun i j => raw32586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32586step0 raw32586; decide +kernel
      have hl : raw32586step0Labels = raw32586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32586 raw32586Labels permutation346 hz
    mixedMoment B raw32586step0 raw32586step0Labels = mixedMoment B raw32586step1 raw32586step1Labels := by
      have ha : raw32586step1 = (fun i j => raw32586step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32586step1 raw32586step0; decide +kernel
      have hl : raw32586step1Labels = raw32586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32586step0 raw32586step0Labels permutation35 permutation3
    mixedMoment B raw32586step1 raw32586step1Labels = mixedMoment B raw32586step2 raw32586step2Labels := by
      have ha : raw32586step2 = raw32586step1 := by apply Matrix.ext; unfold raw32586step2 raw32586step1; decide +kernel
      have hl : raw32586step1Labels = labelEmbedding6 ∘ raw32586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32586step1 raw32586step1Labels raw32586step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw32587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32587step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32587step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32587 raw32587Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw32587 raw32587Labels = mixedMoment B raw32587step0 raw32587step0Labels := by
      have hz : ∀ j, raw32587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32587step0 = (fun i j => raw32587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32587step0 raw32587; decide +kernel
      have hl : raw32587step0Labels = raw32587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32587 raw32587Labels permutation346 hz
    mixedMoment B raw32587step0 raw32587step0Labels = mixedMoment B raw32587step1 raw32587step1Labels := by
      have ha : raw32587step1 = (fun i j => raw32587step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32587step1 raw32587step0; decide +kernel
      have hl : raw32587step1Labels = raw32587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32587step0 raw32587step0Labels permutation32 permutation3
    mixedMoment B raw32587step1 raw32587step1Labels = mixedMoment B raw32587step2 raw32587step2Labels := by
      have ha : raw32587step2 = raw32587step1 := by apply Matrix.ext; unfold raw32587step2 raw32587step1; decide +kernel
      have hl : raw32587step1Labels = labelEmbedding6 ∘ raw32587step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32587step1 raw32587step1Labels raw32587step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4369 node4369Labels := by rfl

def raw32588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32588step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32588 raw32588Labels = mixedMoment B node4974 node4974Labels := by
  calc
    mixedMoment B raw32588 raw32588Labels = mixedMoment B raw32588step0 raw32588step0Labels := by
      have hz : ∀ j, raw32588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32588step0 = (fun i j => raw32588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32588step0 raw32588; decide +kernel
      have hl : raw32588step0Labels = raw32588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32588 raw32588Labels permutation346 hz
    mixedMoment B raw32588step0 raw32588step0Labels = mixedMoment B raw32588step1 raw32588step1Labels := by
      have ha : raw32588step1 = (fun i j => raw32588step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32588step1 raw32588step0; decide +kernel
      have hl : raw32588step1Labels = raw32588step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32588step0 raw32588step0Labels permutation32 permutation3
    mixedMoment B raw32588step1 raw32588step1Labels = mixedMoment B raw32588step2 raw32588step2Labels := by
      have ha : raw32588step2 = raw32588step1 := by apply Matrix.ext; unfold raw32588step2 raw32588step1; decide +kernel
      have hl : raw32588step1Labels = labelEmbedding6 ∘ raw32588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32588step1 raw32588step1Labels raw32588step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4974 node4974Labels := by rfl

def raw32589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32589 raw32589Labels = mixedMoment B node5043 node5043Labels := by
  calc
    mixedMoment B raw32589 raw32589Labels = mixedMoment B raw32589step0 raw32589step0Labels := by
      have ha : raw32589step0 = (fun i j => raw32589 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32589step0 raw32589; decide +kernel
      have hl : raw32589step0Labels = raw32589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32589 raw32589Labels permutation176 permutation3
    mixedMoment B raw32589step0 raw32589step0Labels = mixedMoment B raw32589step1 raw32589step1Labels := by
      have ha : raw32589step1 = raw32589step0 := by apply Matrix.ext; unfold raw32589step1 raw32589step0; decide +kernel
      have hl : raw32589step0Labels = labelEmbedding6 ∘ raw32589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32589step0 raw32589step0Labels raw32589step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5043 node5043Labels := by rfl

def raw32590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32590step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32590 raw32590Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw32590 raw32590Labels = mixedMoment B raw32590step0 raw32590step0Labels := by
      have hz : ∀ j, raw32590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32590step0 = (fun i j => raw32590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32590step0 raw32590; decide +kernel
      have hl : raw32590step0Labels = raw32590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32590 raw32590Labels permutation346 hz
    mixedMoment B raw32590step0 raw32590step0Labels = mixedMoment B raw32590step1 raw32590step1Labels := by
      have ha : raw32590step1 = (fun i j => raw32590step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32590step1 raw32590step0; decide +kernel
      have hl : raw32590step1Labels = raw32590step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32590step0 raw32590step0Labels permutation32 permutation3
    mixedMoment B raw32590step1 raw32590step1Labels = mixedMoment B raw32590step2 raw32590step2Labels := by
      have ha : raw32590step2 = raw32590step1 := by apply Matrix.ext; unfold raw32590step2 raw32590step1; decide +kernel
      have hl : raw32590step1Labels = labelEmbedding6 ∘ raw32590step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32590step1 raw32590step1Labels raw32590step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw32591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw32591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw32591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32591step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32591 raw32591Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw32591 raw32591Labels = mixedMoment B raw32591step0 raw32591step0Labels := by
      have hz : ∀ j, raw32591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32591step0 = (fun i j => raw32591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32591step0 raw32591; decide +kernel
      have hl : raw32591step0Labels = raw32591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32591 raw32591Labels permutation346 hz
    mixedMoment B raw32591step0 raw32591step0Labels = mixedMoment B raw32591step1 raw32591step1Labels := by
      have ha : raw32591step1 = (fun i j => raw32591step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32591step1 raw32591step0; decide +kernel
      have hl : raw32591step1Labels = raw32591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32591step0 raw32591step0Labels permutation33 permutation3
    mixedMoment B raw32591step1 raw32591step1Labels = mixedMoment B raw32591step2 raw32591step2Labels := by
      have ha : raw32591step2 = raw32591step1 := by apply Matrix.ext; unfold raw32591step2 raw32591step1; decide +kernel
      have hl : raw32591step1Labels = labelEmbedding6 ∘ raw32591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32591step1 raw32591step1Labels raw32591step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw32592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32592step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32592step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32592 raw32592Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw32592 raw32592Labels = mixedMoment B raw32592step0 raw32592step0Labels := by
      have hz : ∀ j, raw32592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32592step0 = (fun i j => raw32592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32592step0 raw32592; decide +kernel
      have hl : raw32592step0Labels = raw32592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32592 raw32592Labels permutation346 hz
    mixedMoment B raw32592step0 raw32592step0Labels = mixedMoment B raw32592step1 raw32592step1Labels := by
      have ha : raw32592step1 = (fun i j => raw32592step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32592step1 raw32592step0; decide +kernel
      have hl : raw32592step1Labels = raw32592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32592step0 raw32592step0Labels permutation32 permutation3
    mixedMoment B raw32592step1 raw32592step1Labels = mixedMoment B raw32592step2 raw32592step2Labels := by
      have ha : raw32592step2 = raw32592step1 := by apply Matrix.ext; unfold raw32592step2 raw32592step1; decide +kernel
      have hl : raw32592step1Labels = labelEmbedding6 ∘ raw32592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32592step1 raw32592step1Labels raw32592step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4365 node4365Labels := by rfl

def raw32593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32593step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32593 raw32593Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw32593 raw32593Labels = mixedMoment B raw32593step0 raw32593step0Labels := by
      have hz : ∀ j, raw32593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32593step0 = (fun i j => raw32593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32593step0 raw32593; decide +kernel
      have hl : raw32593step0Labels = raw32593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32593 raw32593Labels permutation346 hz
    mixedMoment B raw32593step0 raw32593step0Labels = mixedMoment B raw32593step1 raw32593step1Labels := by
      have ha : raw32593step1 = (fun i j => raw32593step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32593step1 raw32593step0; decide +kernel
      have hl : raw32593step1Labels = raw32593step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32593step0 raw32593step0Labels permutation32 permutation3
    mixedMoment B raw32593step1 raw32593step1Labels = mixedMoment B raw32593step2 raw32593step2Labels := by
      have ha : raw32593step2 = raw32593step1 := by apply Matrix.ext; unfold raw32593step2 raw32593step1; decide +kernel
      have hl : raw32593step1Labels = labelEmbedding6 ∘ raw32593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32593step1 raw32593step1Labels raw32593step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4970 node4970Labels := by rfl

def raw32594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32594step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32594step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32594 raw32594Labels = mixedMoment B node5041 node5041Labels := by
  calc
    mixedMoment B raw32594 raw32594Labels = mixedMoment B raw32594step0 raw32594step0Labels := by
      have ha : raw32594step0 = (fun i j => raw32594 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32594step0 raw32594; decide +kernel
      have hl : raw32594step0Labels = raw32594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32594 raw32594Labels permutation176 permutation3
    mixedMoment B raw32594step0 raw32594step0Labels = mixedMoment B raw32594step1 raw32594step1Labels := by
      have ha : raw32594step1 = raw32594step0 := by apply Matrix.ext; unfold raw32594step1 raw32594step0; decide +kernel
      have hl : raw32594step0Labels = labelEmbedding6 ∘ raw32594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32594step0 raw32594step0Labels raw32594step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5041 node5041Labels := by rfl

def raw32595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw32595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32595step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32595step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32595 raw32595Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw32595 raw32595Labels = mixedMoment B raw32595step0 raw32595step0Labels := by
      have hz : ∀ j, raw32595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32595step0 = (fun i j => raw32595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32595step0 raw32595; decide +kernel
      have hl : raw32595step0Labels = raw32595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32595 raw32595Labels permutation346 hz
    mixedMoment B raw32595step0 raw32595step0Labels = mixedMoment B raw32595step1 raw32595step1Labels := by
      have ha : raw32595step1 = (fun i j => raw32595step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32595step1 raw32595step0; decide +kernel
      have hl : raw32595step1Labels = raw32595step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32595step0 raw32595step0Labels permutation151 permutation3
    mixedMoment B raw32595step1 raw32595step1Labels = mixedMoment B raw32595step2 raw32595step2Labels := by
      have ha : raw32595step2 = -raw32595step1 := by apply Matrix.ext; change ∀ i j, raw32595step2 i j = -(raw32595step1 i j); unfold raw32595step2 raw32595step1; decide +kernel
      have hl : raw32595step2Labels = raw32595step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32595step2 raw32595step2Labels = mixedMoment B raw32595step3 raw32595step3Labels := by
      have ha : raw32595step3 = raw32595step2 := by apply Matrix.ext; unfold raw32595step3 raw32595step2; decide +kernel
      have hl : raw32595step2Labels = labelEmbedding6 ∘ raw32595step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32595step2 raw32595step2Labels raw32595step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw32596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw32596step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32596step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32596step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32596step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32596 raw32596Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw32596 raw32596Labels = mixedMoment B raw32596step0 raw32596step0Labels := by
      have hz : ∀ j, raw32596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32596step0 = (fun i j => raw32596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32596step0 raw32596; decide +kernel
      have hl : raw32596step0Labels = raw32596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32596 raw32596Labels permutation346 hz
    mixedMoment B raw32596step0 raw32596step0Labels = mixedMoment B raw32596step1 raw32596step1Labels := by
      have ha : raw32596step1 = (fun i j => raw32596step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32596step1 raw32596step0; decide +kernel
      have hl : raw32596step1Labels = raw32596step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32596step0 raw32596step0Labels permutation145 permutation3
    mixedMoment B raw32596step1 raw32596step1Labels = mixedMoment B raw32596step2 raw32596step2Labels := by
      have ha : raw32596step2 = -raw32596step1 := by apply Matrix.ext; change ∀ i j, raw32596step2 i j = -(raw32596step1 i j); unfold raw32596step2 raw32596step1; decide +kernel
      have hl : raw32596step2Labels = raw32596step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32596step2 raw32596step2Labels = mixedMoment B raw32596step3 raw32596step3Labels := by
      have ha : raw32596step3 = raw32596step2 := by apply Matrix.ext; unfold raw32596step3 raw32596step2; decide +kernel
      have hl : raw32596step2Labels = labelEmbedding6 ∘ raw32596step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32596step2 raw32596step2Labels raw32596step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw32597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32597step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32597step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32597step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32597step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32597step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32597 raw32597Labels = mixedMoment B node3774 node3774Labels := by
  calc
    mixedMoment B raw32597 raw32597Labels = mixedMoment B raw32597step0 raw32597step0Labels := by
      have hz : ∀ j, raw32597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32597step0 = (fun i j => raw32597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32597step0 raw32597; decide +kernel
      have hl : raw32597step0Labels = raw32597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32597 raw32597Labels permutation346 hz
    mixedMoment B raw32597step0 raw32597step0Labels = mixedMoment B raw32597step1 raw32597step1Labels := by
      have ha : raw32597step1 = (fun i j => raw32597step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32597step1 raw32597step0; decide +kernel
      have hl : raw32597step1Labels = raw32597step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32597step0 raw32597step0Labels permutation56 permutation7
    mixedMoment B raw32597step1 raw32597step1Labels = mixedMoment B raw32597step2 raw32597step2Labels := by
      have ha : raw32597step2 = -raw32597step1 := by apply Matrix.ext; change ∀ i j, raw32597step2 i j = -(raw32597step1 i j); unfold raw32597step2 raw32597step1; decide +kernel
      have hl : raw32597step2Labels = raw32597step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32597step2 raw32597step2Labels = mixedMoment B raw32597step3 raw32597step3Labels := by
      have ha : raw32597step3 = raw32597step2 := by apply Matrix.ext; unfold raw32597step3 raw32597step2; decide +kernel
      have hl : raw32597step2Labels = labelEmbedding1 ∘ raw32597step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32597step2 raw32597step2Labels raw32597step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3774 node3774Labels := by rfl

def raw32598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32598step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32598 raw32598Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw32598 raw32598Labels = mixedMoment B raw32598step0 raw32598step0Labels := by
      have ha : raw32598step0 = (fun i j => raw32598 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32598step0 raw32598; decide +kernel
      have hl : raw32598step0Labels = raw32598Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32598 raw32598Labels permutation265 permutation7
    mixedMoment B raw32598step0 raw32598step0Labels = mixedMoment B raw32598step1 raw32598step1Labels := by
      have ha : raw32598step1 = -raw32598step0 := by apply Matrix.ext; change ∀ i j, raw32598step1 i j = -(raw32598step0 i j); unfold raw32598step1 raw32598step0; decide +kernel
      have hl : raw32598step1Labels = raw32598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32598step1 raw32598step1Labels = mixedMoment B raw32598step2 raw32598step2Labels := by
      have ha : raw32598step2 = raw32598step1 := by apply Matrix.ext; unfold raw32598step2 raw32598step1; decide +kernel
      have hl : raw32598step1Labels = labelEmbedding1 ∘ raw32598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32598step1 raw32598step1Labels raw32598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

def raw32599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32599step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32599step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32599step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32599 raw32599Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw32599 raw32599Labels = mixedMoment B raw32599step0 raw32599step0Labels := by
      have hz : ∀ j, raw32599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32599step0 = (fun i j => raw32599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32599step0 raw32599; decide +kernel
      have hl : raw32599step0Labels = raw32599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32599 raw32599Labels permutation346 hz
    mixedMoment B raw32599step0 raw32599step0Labels = mixedMoment B raw32599step1 raw32599step1Labels := by
      have ha : raw32599step1 = (fun i j => raw32599step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32599step1 raw32599step0; decide +kernel
      have hl : raw32599step1Labels = raw32599step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32599step0 raw32599step0Labels permutation56 permutation7
    mixedMoment B raw32599step1 raw32599step1Labels = mixedMoment B raw32599step2 raw32599step2Labels := by
      have ha : raw32599step2 = -raw32599step1 := by apply Matrix.ext; change ∀ i j, raw32599step2 i j = -(raw32599step1 i j); unfold raw32599step2 raw32599step1; decide +kernel
      have hl : raw32599step2Labels = raw32599step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32599step2 raw32599step2Labels = mixedMoment B raw32599step3 raw32599step3Labels := by
      have ha : raw32599step3 = raw32599step2 := by apply Matrix.ext; unfold raw32599step3 raw32599step2; decide +kernel
      have hl : raw32599step2Labels = labelEmbedding1 ∘ raw32599step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32599step2 raw32599step2Labels raw32599step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw32600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32600step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32600step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32600step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32600 raw32600Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw32600 raw32600Labels = mixedMoment B raw32600step0 raw32600step0Labels := by
      have hz : ∀ j, raw32600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32600step0 = (fun i j => raw32600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32600step0 raw32600; decide +kernel
      have hl : raw32600step0Labels = raw32600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32600 raw32600Labels permutation346 hz
    mixedMoment B raw32600step0 raw32600step0Labels = mixedMoment B raw32600step1 raw32600step1Labels := by
      have ha : raw32600step1 = (fun i j => raw32600step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32600step1 raw32600step0; decide +kernel
      have hl : raw32600step1Labels = raw32600step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32600step0 raw32600step0Labels permutation58 permutation7
    mixedMoment B raw32600step1 raw32600step1Labels = mixedMoment B raw32600step2 raw32600step2Labels := by
      have ha : raw32600step2 = -raw32600step1 := by apply Matrix.ext; change ∀ i j, raw32600step2 i j = -(raw32600step1 i j); unfold raw32600step2 raw32600step1; decide +kernel
      have hl : raw32600step2Labels = raw32600step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32600step2 raw32600step2Labels = mixedMoment B raw32600step3 raw32600step3Labels := by
      have ha : raw32600step3 = raw32600step2 := by apply Matrix.ext; unfold raw32600step3 raw32600step2; decide +kernel
      have hl : raw32600step2Labels = labelEmbedding1 ∘ raw32600step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32600step2 raw32600step2Labels raw32600step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw32601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32601step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32601step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32601 raw32601Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw32601 raw32601Labels = mixedMoment B raw32601step0 raw32601step0Labels := by
      have hz : ∀ j, raw32601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32601step0 = (fun i j => raw32601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32601step0 raw32601; decide +kernel
      have hl : raw32601step0Labels = raw32601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32601 raw32601Labels permutation346 hz
    mixedMoment B raw32601step0 raw32601step0Labels = mixedMoment B raw32601step1 raw32601step1Labels := by
      have ha : raw32601step1 = (fun i j => raw32601step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32601step1 raw32601step0; decide +kernel
      have hl : raw32601step1Labels = raw32601step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32601step0 raw32601step0Labels permutation56 permutation7
    mixedMoment B raw32601step1 raw32601step1Labels = mixedMoment B raw32601step2 raw32601step2Labels := by
      have ha : raw32601step2 = -raw32601step1 := by apply Matrix.ext; change ∀ i j, raw32601step2 i j = -(raw32601step1 i j); unfold raw32601step2 raw32601step1; decide +kernel
      have hl : raw32601step2Labels = raw32601step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32601step2 raw32601step2Labels = mixedMoment B raw32601step3 raw32601step3Labels := by
      have ha : raw32601step3 = raw32601step2 := by apply Matrix.ext; unfold raw32601step3 raw32601step2; decide +kernel
      have hl : raw32601step2Labels = labelEmbedding1 ∘ raw32601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32601step2 raw32601step2Labels raw32601step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3962 node3962Labels := by rfl

def raw32602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32602step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32602step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32602step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32602step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32602 raw32602Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw32602 raw32602Labels = mixedMoment B raw32602step0 raw32602step0Labels := by
      have hz : ∀ j, raw32602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32602step0 = (fun i j => raw32602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32602step0 raw32602; decide +kernel
      have hl : raw32602step0Labels = raw32602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32602 raw32602Labels permutation346 hz
    mixedMoment B raw32602step0 raw32602step0Labels = mixedMoment B raw32602step1 raw32602step1Labels := by
      have ha : raw32602step1 = (fun i j => raw32602step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32602step1 raw32602step0; decide +kernel
      have hl : raw32602step1Labels = raw32602step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32602step0 raw32602step0Labels permutation41 permutation5
    mixedMoment B raw32602step1 raw32602step1Labels = mixedMoment B raw32602step2 raw32602step2Labels := by
      have ha : raw32602step2 = -raw32602step1 := by apply Matrix.ext; change ∀ i j, raw32602step2 i j = -(raw32602step1 i j); unfold raw32602step2 raw32602step1; decide +kernel
      have hl : raw32602step2Labels = raw32602step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32602step2 raw32602step2Labels = mixedMoment B raw32602step3 raw32602step3Labels := by
      have ha : raw32602step3 = raw32602step2 := by apply Matrix.ext; unfold raw32602step3 raw32602step2; decide +kernel
      have hl : raw32602step2Labels = labelEmbedding1 ∘ raw32602step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32602step2 raw32602step2Labels raw32602step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw32603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32603step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32603step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32603 raw32603Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw32603 raw32603Labels = mixedMoment B raw32603step0 raw32603step0Labels := by
      have ha : raw32603step0 = (fun i j => raw32603 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32603step0 raw32603; decide +kernel
      have hl : raw32603step0Labels = raw32603Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32603 raw32603Labels permutation185 permutation5
    mixedMoment B raw32603step0 raw32603step0Labels = mixedMoment B raw32603step1 raw32603step1Labels := by
      have ha : raw32603step1 = -raw32603step0 := by apply Matrix.ext; change ∀ i j, raw32603step1 i j = -(raw32603step0 i j); unfold raw32603step1 raw32603step0; decide +kernel
      have hl : raw32603step1Labels = raw32603step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32603step1 raw32603step1Labels = mixedMoment B raw32603step2 raw32603step2Labels := by
      have ha : raw32603step2 = raw32603step1 := by apply Matrix.ext; unfold raw32603step2 raw32603step1; decide +kernel
      have hl : raw32603step1Labels = labelEmbedding1 ∘ raw32603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32603step1 raw32603step1Labels raw32603step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw32604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32604step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32604step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32604step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32604 raw32604Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw32604 raw32604Labels = mixedMoment B raw32604step0 raw32604step0Labels := by
      have hz : ∀ j, raw32604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32604step0 = (fun i j => raw32604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32604step0 raw32604; decide +kernel
      have hl : raw32604step0Labels = raw32604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32604 raw32604Labels permutation346 hz
    mixedMoment B raw32604step0 raw32604step0Labels = mixedMoment B raw32604step1 raw32604step1Labels := by
      have ha : raw32604step1 = (fun i j => raw32604step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32604step1 raw32604step0; decide +kernel
      have hl : raw32604step1Labels = raw32604step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32604step0 raw32604step0Labels permutation41 permutation5
    mixedMoment B raw32604step1 raw32604step1Labels = mixedMoment B raw32604step2 raw32604step2Labels := by
      have ha : raw32604step2 = -raw32604step1 := by apply Matrix.ext; change ∀ i j, raw32604step2 i j = -(raw32604step1 i j); unfold raw32604step2 raw32604step1; decide +kernel
      have hl : raw32604step2Labels = raw32604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32604step2 raw32604step2Labels = mixedMoment B raw32604step3 raw32604step3Labels := by
      have ha : raw32604step3 = raw32604step2 := by apply Matrix.ext; unfold raw32604step3 raw32604step2; decide +kernel
      have hl : raw32604step2Labels = labelEmbedding1 ∘ raw32604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32604step2 raw32604step2Labels raw32604step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw32605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32605step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32605step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32605step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32605step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32605step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32605 raw32605Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw32605 raw32605Labels = mixedMoment B raw32605step0 raw32605step0Labels := by
      have hz : ∀ j, raw32605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32605step0 = (fun i j => raw32605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32605step0 raw32605; decide +kernel
      have hl : raw32605step0Labels = raw32605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32605 raw32605Labels permutation346 hz
    mixedMoment B raw32605step0 raw32605step0Labels = mixedMoment B raw32605step1 raw32605step1Labels := by
      have ha : raw32605step1 = (fun i j => raw32605step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32605step1 raw32605step0; decide +kernel
      have hl : raw32605step1Labels = raw32605step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32605step0 raw32605step0Labels permutation47 permutation5
    mixedMoment B raw32605step1 raw32605step1Labels = mixedMoment B raw32605step2 raw32605step2Labels := by
      have ha : raw32605step2 = -raw32605step1 := by apply Matrix.ext; change ∀ i j, raw32605step2 i j = -(raw32605step1 i j); unfold raw32605step2 raw32605step1; decide +kernel
      have hl : raw32605step2Labels = raw32605step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32605step2 raw32605step2Labels = mixedMoment B raw32605step3 raw32605step3Labels := by
      have ha : raw32605step3 = raw32605step2 := by apply Matrix.ext; unfold raw32605step3 raw32605step2; decide +kernel
      have hl : raw32605step2Labels = labelEmbedding1 ∘ raw32605step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32605step2 raw32605step2Labels raw32605step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw32606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32606step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw32606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32606step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32606step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32606step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32606 raw32606Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw32606 raw32606Labels = mixedMoment B raw32606step0 raw32606step0Labels := by
      have hz : ∀ j, raw32606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32606step0 = (fun i j => raw32606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32606step0 raw32606; decide +kernel
      have hl : raw32606step0Labels = raw32606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32606 raw32606Labels permutation346 hz
    mixedMoment B raw32606step0 raw32606step0Labels = mixedMoment B raw32606step1 raw32606step1Labels := by
      have ha : raw32606step1 = (fun i j => raw32606step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32606step1 raw32606step0; decide +kernel
      have hl : raw32606step1Labels = raw32606step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32606step0 raw32606step0Labels permutation41 permutation5
    mixedMoment B raw32606step1 raw32606step1Labels = mixedMoment B raw32606step2 raw32606step2Labels := by
      have ha : raw32606step2 = -raw32606step1 := by apply Matrix.ext; change ∀ i j, raw32606step2 i j = -(raw32606step1 i j); unfold raw32606step2 raw32606step1; decide +kernel
      have hl : raw32606step2Labels = raw32606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32606step2 raw32606step2Labels = mixedMoment B raw32606step3 raw32606step3Labels := by
      have ha : raw32606step3 = raw32606step2 := by apply Matrix.ext; unfold raw32606step3 raw32606step2; decide +kernel
      have hl : raw32606step2Labels = labelEmbedding1 ∘ raw32606step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32606step2 raw32606step2Labels raw32606step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw32607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32607step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32607step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32607 raw32607Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw32607 raw32607Labels = mixedMoment B raw32607step0 raw32607step0Labels := by
      have ha : raw32607step0 = (fun i j => raw32607 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32607step0 raw32607; decide +kernel
      have hl : raw32607step0Labels = raw32607Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32607 raw32607Labels permutation212 permutation5
    mixedMoment B raw32607step0 raw32607step0Labels = mixedMoment B raw32607step1 raw32607step1Labels := by
      have ha : raw32607step1 = -raw32607step0 := by apply Matrix.ext; change ∀ i j, raw32607step1 i j = -(raw32607step0 i j); unfold raw32607step1 raw32607step0; decide +kernel
      have hl : raw32607step1Labels = raw32607step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32607step1 raw32607step1Labels = mixedMoment B raw32607step2 raw32607step2Labels := by
      have ha : raw32607step2 = raw32607step1 := by apply Matrix.ext; unfold raw32607step2 raw32607step1; decide +kernel
      have hl : raw32607step1Labels = labelEmbedding1 ∘ raw32607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32607step1 raw32607step1Labels raw32607step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

def raw32608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32608 raw32608Labels = mixedMoment B node3587 node3587Labels := by
  calc
    mixedMoment B raw32608 raw32608Labels = mixedMoment B raw32608step0 raw32608step0Labels := by
      have ha : raw32608step0 = (fun i j => raw32608 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32608step0 raw32608; decide +kernel
      have hl : raw32608step0Labels = raw32608Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32608 raw32608Labels permutation160 permutation5
    mixedMoment B raw32608step0 raw32608step0Labels = mixedMoment B raw32608step1 raw32608step1Labels := by
      have ha : raw32608step1 = -raw32608step0 := by apply Matrix.ext; change ∀ i j, raw32608step1 i j = -(raw32608step0 i j); unfold raw32608step1 raw32608step0; decide +kernel
      have hl : raw32608step1Labels = raw32608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32608step1 raw32608step1Labels = mixedMoment B raw32608step2 raw32608step2Labels := by
      have ha : raw32608step2 = raw32608step1 := by apply Matrix.ext; unfold raw32608step2 raw32608step1; decide +kernel
      have hl : raw32608step1Labels = labelEmbedding1 ∘ raw32608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32608step1 raw32608step1Labels raw32608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3587 node3587Labels := by rfl

def raw32609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32609 raw32609Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw32609 raw32609Labels = mixedMoment B raw32609step0 raw32609step0Labels := by
      have ha : raw32609step0 = (fun i j => raw32609 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32609step0 raw32609; decide +kernel
      have hl : raw32609step0Labels = raw32609Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32609 raw32609Labels permutation212 permutation5
    mixedMoment B raw32609step0 raw32609step0Labels = mixedMoment B raw32609step1 raw32609step1Labels := by
      have ha : raw32609step1 = -raw32609step0 := by apply Matrix.ext; change ∀ i j, raw32609step1 i j = -(raw32609step0 i j); unfold raw32609step1 raw32609step0; decide +kernel
      have hl : raw32609step1Labels = raw32609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32609step1 raw32609step1Labels = mixedMoment B raw32609step2 raw32609step2Labels := by
      have ha : raw32609step2 = raw32609step1 := by apply Matrix.ext; unfold raw32609step2 raw32609step1; decide +kernel
      have hl : raw32609step1Labels = labelEmbedding1 ∘ raw32609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32609step1 raw32609step1Labels raw32609step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw32610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32610 raw32610Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw32610 raw32610Labels = mixedMoment B raw32610step0 raw32610step0Labels := by
      have ha : raw32610step0 = (fun i j => raw32610 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32610step0 raw32610; decide +kernel
      have hl : raw32610step0Labels = raw32610Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32610 raw32610Labels permutation234 permutation5
    mixedMoment B raw32610step0 raw32610step0Labels = mixedMoment B raw32610step1 raw32610step1Labels := by
      have ha : raw32610step1 = -raw32610step0 := by apply Matrix.ext; change ∀ i j, raw32610step1 i j = -(raw32610step0 i j); unfold raw32610step1 raw32610step0; decide +kernel
      have hl : raw32610step1Labels = raw32610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32610step1 raw32610step1Labels = mixedMoment B raw32610step2 raw32610step2Labels := by
      have ha : raw32610step2 = raw32610step1 := by apply Matrix.ext; unfold raw32610step2 raw32610step1; decide +kernel
      have hl : raw32610step1Labels = labelEmbedding1 ∘ raw32610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32610step1 raw32610step1Labels raw32610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw32611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw32611step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw32611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32611step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw32611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32611 raw32611Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw32611 raw32611Labels = mixedMoment B raw32611step0 raw32611step0Labels := by
      have ha : raw32611step0 = (fun i j => raw32611 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32611step0 raw32611; decide +kernel
      have hl : raw32611step0Labels = raw32611Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32611 raw32611Labels permutation216 permutation5
    mixedMoment B raw32611step0 raw32611step0Labels = mixedMoment B raw32611step1 raw32611step1Labels := by
      have ha : raw32611step1 = -raw32611step0 := by apply Matrix.ext; change ∀ i j, raw32611step1 i j = -(raw32611step0 i j); unfold raw32611step1 raw32611step0; decide +kernel
      have hl : raw32611step1Labels = raw32611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32611step1 raw32611step1Labels = mixedMoment B raw32611step2 raw32611step2Labels := by
      have ha : raw32611step2 = raw32611step1 := by apply Matrix.ext; unfold raw32611step2 raw32611step1; decide +kernel
      have hl : raw32611step1Labels = labelEmbedding1 ∘ raw32611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32611step1 raw32611step1Labels raw32611step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

def raw32612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32612step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32612step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32612 raw32612Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw32612 raw32612Labels = mixedMoment B raw32612step0 raw32612step0Labels := by
      have hz : ∀ j, raw32612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32612step0 = (fun i j => raw32612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32612step0 raw32612; decide +kernel
      have hl : raw32612step0Labels = raw32612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32612 raw32612Labels permutation346 hz
    mixedMoment B raw32612step0 raw32612step0Labels = mixedMoment B raw32612step1 raw32612step1Labels := by
      have ha : raw32612step1 = (fun i j => raw32612step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32612step1 raw32612step0; decide +kernel
      have hl : raw32612step1Labels = raw32612step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32612step0 raw32612step0Labels permutation44 permutation5
    mixedMoment B raw32612step1 raw32612step1Labels = mixedMoment B raw32612step2 raw32612step2Labels := by
      have ha : raw32612step2 = -raw32612step1 := by apply Matrix.ext; change ∀ i j, raw32612step2 i j = -(raw32612step1 i j); unfold raw32612step2 raw32612step1; decide +kernel
      have hl : raw32612step2Labels = raw32612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32612step2 raw32612step2Labels = mixedMoment B raw32612step3 raw32612step3Labels := by
      have ha : raw32612step3 = raw32612step2 := by apply Matrix.ext; unfold raw32612step3 raw32612step2; decide +kernel
      have hl : raw32612step2Labels = labelEmbedding1 ∘ raw32612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32612step2 raw32612step2Labels raw32612step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

def raw32613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32613step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32613step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32613step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32613step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32613step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32613 raw32613Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw32613 raw32613Labels = mixedMoment B raw32613step0 raw32613step0Labels := by
      have hz : ∀ j, raw32613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32613step0 = (fun i j => raw32613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32613step0 raw32613; decide +kernel
      have hl : raw32613step0Labels = raw32613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32613 raw32613Labels permutation346 hz
    mixedMoment B raw32613step0 raw32613step0Labels = mixedMoment B raw32613step1 raw32613step1Labels := by
      have ha : raw32613step1 = (fun i j => raw32613step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32613step1 raw32613step0; decide +kernel
      have hl : raw32613step1Labels = raw32613step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32613step0 raw32613step0Labels permutation34 permutation5
    mixedMoment B raw32613step1 raw32613step1Labels = mixedMoment B raw32613step2 raw32613step2Labels := by
      have ha : raw32613step2 = -raw32613step1 := by apply Matrix.ext; change ∀ i j, raw32613step2 i j = -(raw32613step1 i j); unfold raw32613step2 raw32613step1; decide +kernel
      have hl : raw32613step2Labels = raw32613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32613step2 raw32613step2Labels = mixedMoment B raw32613step3 raw32613step3Labels := by
      have ha : raw32613step3 = raw32613step2 := by apply Matrix.ext; unfold raw32613step3 raw32613step2; decide +kernel
      have hl : raw32613step2Labels = labelEmbedding1 ∘ raw32613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32613step2 raw32613step2Labels raw32613step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3592 node3592Labels := by rfl

def raw32614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32614 raw32614Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw32614 raw32614Labels = mixedMoment B raw32614step0 raw32614step0Labels := by
      have ha : raw32614step0 = (fun i j => raw32614 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32614step0 raw32614; decide +kernel
      have hl : raw32614step0Labels = raw32614Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32614 raw32614Labels permutation188 permutation5
    mixedMoment B raw32614step0 raw32614step0Labels = mixedMoment B raw32614step1 raw32614step1Labels := by
      have ha : raw32614step1 = -raw32614step0 := by apply Matrix.ext; change ∀ i j, raw32614step1 i j = -(raw32614step0 i j); unfold raw32614step1 raw32614step0; decide +kernel
      have hl : raw32614step1Labels = raw32614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32614step1 raw32614step1Labels = mixedMoment B raw32614step2 raw32614step2Labels := by
      have ha : raw32614step2 = raw32614step1 := by apply Matrix.ext; unfold raw32614step2 raw32614step1; decide +kernel
      have hl : raw32614step1Labels = labelEmbedding1 ∘ raw32614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32614step1 raw32614step1Labels raw32614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

def raw32615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32615step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32615step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32615step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32615step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32615 raw32615Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw32615 raw32615Labels = mixedMoment B raw32615step0 raw32615step0Labels := by
      have hz : ∀ j, raw32615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32615step0 = (fun i j => raw32615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32615step0 raw32615; decide +kernel
      have hl : raw32615step0Labels = raw32615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32615 raw32615Labels permutation346 hz
    mixedMoment B raw32615step0 raw32615step0Labels = mixedMoment B raw32615step1 raw32615step1Labels := by
      have ha : raw32615step1 = (fun i j => raw32615step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32615step1 raw32615step0; decide +kernel
      have hl : raw32615step1Labels = raw32615step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32615step0 raw32615step0Labels permutation44 permutation5
    mixedMoment B raw32615step1 raw32615step1Labels = mixedMoment B raw32615step2 raw32615step2Labels := by
      have ha : raw32615step2 = -raw32615step1 := by apply Matrix.ext; change ∀ i j, raw32615step2 i j = -(raw32615step1 i j); unfold raw32615step2 raw32615step1; decide +kernel
      have hl : raw32615step2Labels = raw32615step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32615step2 raw32615step2Labels = mixedMoment B raw32615step3 raw32615step3Labels := by
      have ha : raw32615step3 = raw32615step2 := by apply Matrix.ext; unfold raw32615step3 raw32615step2; decide +kernel
      have hl : raw32615step2Labels = labelEmbedding1 ∘ raw32615step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32615step2 raw32615step2Labels raw32615step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw32616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32616step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw32616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32616step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32616 raw32616Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw32616 raw32616Labels = mixedMoment B raw32616step0 raw32616step0Labels := by
      have hz : ∀ j, raw32616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32616step0 = (fun i j => raw32616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32616step0 raw32616; decide +kernel
      have hl : raw32616step0Labels = raw32616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32616 raw32616Labels permutation346 hz
    mixedMoment B raw32616step0 raw32616step0Labels = mixedMoment B raw32616step1 raw32616step1Labels := by
      have ha : raw32616step1 = (fun i j => raw32616step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32616step1 raw32616step0; decide +kernel
      have hl : raw32616step1Labels = raw32616step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32616step0 raw32616step0Labels permutation48 permutation5
    mixedMoment B raw32616step1 raw32616step1Labels = mixedMoment B raw32616step2 raw32616step2Labels := by
      have ha : raw32616step2 = -raw32616step1 := by apply Matrix.ext; change ∀ i j, raw32616step2 i j = -(raw32616step1 i j); unfold raw32616step2 raw32616step1; decide +kernel
      have hl : raw32616step2Labels = raw32616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32616step2 raw32616step2Labels = mixedMoment B raw32616step3 raw32616step3Labels := by
      have ha : raw32616step3 = raw32616step2 := by apply Matrix.ext; unfold raw32616step3 raw32616step2; decide +kernel
      have hl : raw32616step2Labels = labelEmbedding1 ∘ raw32616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32616step2 raw32616step2Labels raw32616step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

def raw32617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32617step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32617 raw32617Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw32617 raw32617Labels = mixedMoment B raw32617step0 raw32617step0Labels := by
      have hz : ∀ j, raw32617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32617step0 = (fun i j => raw32617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32617step0 raw32617; decide +kernel
      have hl : raw32617step0Labels = raw32617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32617 raw32617Labels permutation346 hz
    mixedMoment B raw32617step0 raw32617step0Labels = mixedMoment B raw32617step1 raw32617step1Labels := by
      have ha : raw32617step1 = (fun i j => raw32617step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32617step1 raw32617step0; decide +kernel
      have hl : raw32617step1Labels = raw32617step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32617step0 raw32617step0Labels permutation38 permutation5
    mixedMoment B raw32617step1 raw32617step1Labels = mixedMoment B raw32617step2 raw32617step2Labels := by
      have ha : raw32617step2 = -raw32617step1 := by apply Matrix.ext; change ∀ i j, raw32617step2 i j = -(raw32617step1 i j); unfold raw32617step2 raw32617step1; decide +kernel
      have hl : raw32617step2Labels = raw32617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32617step2 raw32617step2Labels = mixedMoment B raw32617step3 raw32617step3Labels := by
      have ha : raw32617step3 = raw32617step2 := by apply Matrix.ext; unfold raw32617step3 raw32617step2; decide +kernel
      have hl : raw32617step2Labels = labelEmbedding1 ∘ raw32617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32617step2 raw32617step2Labels raw32617step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

def raw32618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32618step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32618step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32618step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32618step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32618 raw32618Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw32618 raw32618Labels = mixedMoment B raw32618step0 raw32618step0Labels := by
      have hz : ∀ j, raw32618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32618step0 = (fun i j => raw32618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32618step0 raw32618; decide +kernel
      have hl : raw32618step0Labels = raw32618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32618 raw32618Labels permutation346 hz
    mixedMoment B raw32618step0 raw32618step0Labels = mixedMoment B raw32618step1 raw32618step1Labels := by
      have ha : raw32618step1 = (fun i j => raw32618step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32618step1 raw32618step0; decide +kernel
      have hl : raw32618step1Labels = raw32618step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32618step0 raw32618step0Labels permutation32 permutation5
    mixedMoment B raw32618step1 raw32618step1Labels = mixedMoment B raw32618step2 raw32618step2Labels := by
      have ha : raw32618step2 = -raw32618step1 := by apply Matrix.ext; change ∀ i j, raw32618step2 i j = -(raw32618step1 i j); unfold raw32618step2 raw32618step1; decide +kernel
      have hl : raw32618step2Labels = raw32618step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32618step2 raw32618step2Labels = mixedMoment B raw32618step3 raw32618step3Labels := by
      have ha : raw32618step3 = raw32618step2 := by apply Matrix.ext; unfold raw32618step3 raw32618step2; decide +kernel
      have hl : raw32618step2Labels = labelEmbedding1 ∘ raw32618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32618step2 raw32618step2Labels raw32618step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3592 node3592Labels := by rfl

def raw32619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32619step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32619 raw32619Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw32619 raw32619Labels = mixedMoment B raw32619step0 raw32619step0Labels := by
      have ha : raw32619step0 = (fun i j => raw32619 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32619step0 raw32619; decide +kernel
      have hl : raw32619step0Labels = raw32619Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32619 raw32619Labels permutation182 permutation5
    mixedMoment B raw32619step0 raw32619step0Labels = mixedMoment B raw32619step1 raw32619step1Labels := by
      have ha : raw32619step1 = -raw32619step0 := by apply Matrix.ext; change ∀ i j, raw32619step1 i j = -(raw32619step0 i j); unfold raw32619step1 raw32619step0; decide +kernel
      have hl : raw32619step1Labels = raw32619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32619step1 raw32619step1Labels = mixedMoment B raw32619step2 raw32619step2Labels := by
      have ha : raw32619step2 = raw32619step1 := by apply Matrix.ext; unfold raw32619step2 raw32619step1; decide +kernel
      have hl : raw32619step1Labels = labelEmbedding1 ∘ raw32619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32619step1 raw32619step1Labels raw32619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

def raw32620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32620step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32620step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32620step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32620 raw32620Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw32620 raw32620Labels = mixedMoment B raw32620step0 raw32620step0Labels := by
      have hz : ∀ j, raw32620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32620step0 = (fun i j => raw32620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32620step0 raw32620; decide +kernel
      have hl : raw32620step0Labels = raw32620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32620 raw32620Labels permutation346 hz
    mixedMoment B raw32620step0 raw32620step0Labels = mixedMoment B raw32620step1 raw32620step1Labels := by
      have ha : raw32620step1 = (fun i j => raw32620step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32620step1 raw32620step0; decide +kernel
      have hl : raw32620step1Labels = raw32620step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32620step0 raw32620step0Labels permutation38 permutation5
    mixedMoment B raw32620step1 raw32620step1Labels = mixedMoment B raw32620step2 raw32620step2Labels := by
      have ha : raw32620step2 = -raw32620step1 := by apply Matrix.ext; change ∀ i j, raw32620step2 i j = -(raw32620step1 i j); unfold raw32620step2 raw32620step1; decide +kernel
      have hl : raw32620step2Labels = raw32620step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32620step2 raw32620step2Labels = mixedMoment B raw32620step3 raw32620step3Labels := by
      have ha : raw32620step3 = raw32620step2 := by apply Matrix.ext; unfold raw32620step3 raw32620step2; decide +kernel
      have hl : raw32620step2Labels = labelEmbedding1 ∘ raw32620step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32620step2 raw32620step2Labels raw32620step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw32621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw32621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw32621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw32621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32621 raw32621Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw32621 raw32621Labels = mixedMoment B raw32621step0 raw32621step0Labels := by
      have hz : ∀ j, raw32621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32621step0 = (fun i j => raw32621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32621step0 raw32621; decide +kernel
      have hl : raw32621step0Labels = raw32621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32621 raw32621Labels permutation346 hz
    mixedMoment B raw32621step0 raw32621step0Labels = mixedMoment B raw32621step1 raw32621step1Labels := by
      have ha : raw32621step1 = (fun i j => raw32621step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32621step1 raw32621step0; decide +kernel
      have hl : raw32621step1Labels = raw32621step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32621step0 raw32621step0Labels permutation42 permutation5
    mixedMoment B raw32621step1 raw32621step1Labels = mixedMoment B raw32621step2 raw32621step2Labels := by
      have ha : raw32621step2 = -raw32621step1 := by apply Matrix.ext; change ∀ i j, raw32621step2 i j = -(raw32621step1 i j); unfold raw32621step2 raw32621step1; decide +kernel
      have hl : raw32621step2Labels = raw32621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32621step2 raw32621step2Labels = mixedMoment B raw32621step3 raw32621step3Labels := by
      have ha : raw32621step3 = raw32621step2 := by apply Matrix.ext; unfold raw32621step3 raw32621step2; decide +kernel
      have hl : raw32621step2Labels = labelEmbedding1 ∘ raw32621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32621step2 raw32621step2Labels raw32621step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

def raw32622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw32622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32622 raw32622Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw32622 raw32622Labels = mixedMoment B raw32622step0 raw32622step0Labels := by
      have hz : ∀ j, raw32622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32622step0 = (fun i j => raw32622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32622step0 raw32622; decide +kernel
      have hl : raw32622step0Labels = raw32622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32622 raw32622Labels permutation346 hz
    mixedMoment B raw32622step0 raw32622step0Labels = mixedMoment B raw32622step1 raw32622step1Labels := by
      have ha : raw32622step1 = (fun i j => raw32622step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32622step1 raw32622step0; decide +kernel
      have hl : raw32622step1Labels = raw32622step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32622step0 raw32622step0Labels permutation40 permutation5
    mixedMoment B raw32622step1 raw32622step1Labels = mixedMoment B raw32622step2 raw32622step2Labels := by
      have ha : raw32622step2 = -raw32622step1 := by apply Matrix.ext; change ∀ i j, raw32622step2 i j = -(raw32622step1 i j); unfold raw32622step2 raw32622step1; decide +kernel
      have hl : raw32622step2Labels = raw32622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32622step2 raw32622step2Labels = mixedMoment B raw32622step3 raw32622step3Labels := by
      have ha : raw32622step3 = raw32622step2 := by apply Matrix.ext; unfold raw32622step3 raw32622step2; decide +kernel
      have hl : raw32622step2Labels = labelEmbedding1 ∘ raw32622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32622step2 raw32622step2Labels raw32622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

def raw32623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw32623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw32623step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw32623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32623 raw32623Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw32623 raw32623Labels = mixedMoment B raw32623step0 raw32623step0Labels := by
      have hz : ∀ j, raw32623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32623step0 = (fun i j => raw32623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32623step0 raw32623; decide +kernel
      have hl : raw32623step0Labels = raw32623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32623 raw32623Labels permutation346 hz
    mixedMoment B raw32623step0 raw32623step0Labels = mixedMoment B raw32623step1 raw32623step1Labels := by
      have ha : raw32623step1 = (fun i j => raw32623step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32623step1 raw32623step0; decide +kernel
      have hl : raw32623step1Labels = raw32623step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32623step0 raw32623step0Labels permutation32 permutation5
    mixedMoment B raw32623step1 raw32623step1Labels = mixedMoment B raw32623step2 raw32623step2Labels := by
      have ha : raw32623step2 = -raw32623step1 := by apply Matrix.ext; change ∀ i j, raw32623step2 i j = -(raw32623step1 i j); unfold raw32623step2 raw32623step1; decide +kernel
      have hl : raw32623step2Labels = raw32623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32623step2 raw32623step2Labels = mixedMoment B raw32623step3 raw32623step3Labels := by
      have ha : raw32623step3 = raw32623step2 := by apply Matrix.ext; unfold raw32623step3 raw32623step2; decide +kernel
      have hl : raw32623step2Labels = labelEmbedding1 ∘ raw32623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32623step2 raw32623step2Labels raw32623step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3588 node3588Labels := by rfl

def raw32624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw32624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32624 raw32624Labels = mixedMoment B node3458 node3458Labels := by
  calc
    mixedMoment B raw32624 raw32624Labels = mixedMoment B raw32624step0 raw32624step0Labels := by
      have ha : raw32624step0 = (fun i j => raw32624 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32624step0 raw32624; decide +kernel
      have hl : raw32624step0Labels = raw32624Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32624 raw32624Labels permutation184 permutation5
    mixedMoment B raw32624step0 raw32624step0Labels = mixedMoment B raw32624step1 raw32624step1Labels := by
      have ha : raw32624step1 = -raw32624step0 := by apply Matrix.ext; change ∀ i j, raw32624step1 i j = -(raw32624step0 i j); unfold raw32624step1 raw32624step0; decide +kernel
      have hl : raw32624step1Labels = raw32624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32624step1 raw32624step1Labels = mixedMoment B raw32624step2 raw32624step2Labels := by
      have ha : raw32624step2 = raw32624step1 := by apply Matrix.ext; unfold raw32624step2 raw32624step1; decide +kernel
      have hl : raw32624step1Labels = labelEmbedding1 ∘ raw32624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32624step1 raw32624step1Labels raw32624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3458 node3458Labels := by rfl

def raw32625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw32625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32625step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32625step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32625step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32625 raw32625Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw32625 raw32625Labels = mixedMoment B raw32625step0 raw32625step0Labels := by
      have hz : ∀ j, raw32625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32625step0 = (fun i j => raw32625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32625step0 raw32625; decide +kernel
      have hl : raw32625step0Labels = raw32625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32625 raw32625Labels permutation346 hz
    mixedMoment B raw32625step0 raw32625step0Labels = mixedMoment B raw32625step1 raw32625step1Labels := by
      have ha : raw32625step1 = (fun i j => raw32625step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32625step1 raw32625step0; decide +kernel
      have hl : raw32625step1Labels = raw32625step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32625step0 raw32625step0Labels permutation40 permutation5
    mixedMoment B raw32625step1 raw32625step1Labels = mixedMoment B raw32625step2 raw32625step2Labels := by
      have ha : raw32625step2 = -raw32625step1 := by apply Matrix.ext; change ∀ i j, raw32625step2 i j = -(raw32625step1 i j); unfold raw32625step2 raw32625step1; decide +kernel
      have hl : raw32625step2Labels = raw32625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32625step2 raw32625step2Labels = mixedMoment B raw32625step3 raw32625step3Labels := by
      have ha : raw32625step3 = raw32625step2 := by apply Matrix.ext; unfold raw32625step3 raw32625step2; decide +kernel
      have hl : raw32625step2Labels = labelEmbedding1 ∘ raw32625step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32625step2 raw32625step2Labels raw32625step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw32626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw32626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32626 raw32626Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw32626 raw32626Labels = mixedMoment B raw32626step0 raw32626step0Labels := by
      have hz : ∀ j, raw32626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32626step0 = (fun i j => raw32626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32626step0 raw32626; decide +kernel
      have hl : raw32626step0Labels = raw32626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32626 raw32626Labels permutation346 hz
    mixedMoment B raw32626step0 raw32626step0Labels = mixedMoment B raw32626step1 raw32626step1Labels := by
      have ha : raw32626step1 = (fun i j => raw32626step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32626step1 raw32626step0; decide +kernel
      have hl : raw32626step1Labels = raw32626step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32626step0 raw32626step0Labels permutation46 permutation5
    mixedMoment B raw32626step1 raw32626step1Labels = mixedMoment B raw32626step2 raw32626step2Labels := by
      have ha : raw32626step2 = -raw32626step1 := by apply Matrix.ext; change ∀ i j, raw32626step2 i j = -(raw32626step1 i j); unfold raw32626step2 raw32626step1; decide +kernel
      have hl : raw32626step2Labels = raw32626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32626step2 raw32626step2Labels = mixedMoment B raw32626step3 raw32626step3Labels := by
      have ha : raw32626step3 = raw32626step2 := by apply Matrix.ext; unfold raw32626step3 raw32626step2; decide +kernel
      have hl : raw32626step2Labels = labelEmbedding1 ∘ raw32626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32626step2 raw32626step2Labels raw32626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw32627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32627step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw32627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32627step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw32627step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32627step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32627 raw32627Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw32627 raw32627Labels = mixedMoment B raw32627step0 raw32627step0Labels := by
      have hz : ∀ j, raw32627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32627step0 = (fun i j => raw32627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32627step0 raw32627; decide +kernel
      have hl : raw32627step0Labels = raw32627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32627 raw32627Labels permutation346 hz
    mixedMoment B raw32627step0 raw32627step0Labels = mixedMoment B raw32627step1 raw32627step1Labels := by
      have ha : raw32627step1 = (fun i j => raw32627step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32627step1 raw32627step0; decide +kernel
      have hl : raw32627step1Labels = raw32627step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32627step0 raw32627step0Labels permutation58 permutation5
    mixedMoment B raw32627step1 raw32627step1Labels = mixedMoment B raw32627step2 raw32627step2Labels := by
      have ha : raw32627step2 = -raw32627step1 := by apply Matrix.ext; change ∀ i j, raw32627step2 i j = -(raw32627step1 i j); unfold raw32627step2 raw32627step1; decide +kernel
      have hl : raw32627step2Labels = raw32627step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32627step2 raw32627step2Labels = mixedMoment B raw32627step3 raw32627step3Labels := by
      have ha : raw32627step3 = raw32627step2 := by apply Matrix.ext; unfold raw32627step3 raw32627step2; decide +kernel
      have hl : raw32627step2Labels = labelEmbedding8 ∘ raw32627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32627step2 raw32627step2Labels raw32627step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw32628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32628step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32628step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32628 raw32628Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw32628 raw32628Labels = mixedMoment B raw32628step0 raw32628step0Labels := by
      have ha : raw32628step0 = (fun i j => raw32628 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32628step0 raw32628; decide +kernel
      have hl : raw32628step0Labels = raw32628Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32628 raw32628Labels permutation664 permutation3
    mixedMoment B raw32628step0 raw32628step0Labels = mixedMoment B raw32628step1 raw32628step1Labels := by
      have ha : raw32628step1 = -raw32628step0 := by apply Matrix.ext; change ∀ i j, raw32628step1 i j = -(raw32628step0 i j); unfold raw32628step1 raw32628step0; decide +kernel
      have hl : raw32628step1Labels = raw32628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32628step1 raw32628step1Labels = mixedMoment B raw32628step2 raw32628step2Labels := by
      have ha : raw32628step2 = raw32628step1 := by apply Matrix.ext; unfold raw32628step2 raw32628step1; decide +kernel
      have hl : raw32628step1Labels = labelEmbedding6 ∘ raw32628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32628step1 raw32628step1Labels raw32628step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw32629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32629step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32629step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32629step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32629step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32629 raw32629Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw32629 raw32629Labels = mixedMoment B raw32629step0 raw32629step0Labels := by
      have hz : ∀ j, raw32629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32629step0 = (fun i j => raw32629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32629step0 raw32629; decide +kernel
      have hl : raw32629step0Labels = raw32629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32629 raw32629Labels permutation346 hz
    mixedMoment B raw32629step0 raw32629step0Labels = mixedMoment B raw32629step1 raw32629step1Labels := by
      have ha : raw32629step1 = (fun i j => raw32629step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32629step1 raw32629step0; decide +kernel
      have hl : raw32629step1Labels = raw32629step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32629step0 raw32629step0Labels permutation145 permutation3
    mixedMoment B raw32629step1 raw32629step1Labels = mixedMoment B raw32629step2 raw32629step2Labels := by
      have ha : raw32629step2 = -raw32629step1 := by apply Matrix.ext; change ∀ i j, raw32629step2 i j = -(raw32629step1 i j); unfold raw32629step2 raw32629step1; decide +kernel
      have hl : raw32629step2Labels = raw32629step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32629step2 raw32629step2Labels = mixedMoment B raw32629step3 raw32629step3Labels := by
      have ha : raw32629step3 = raw32629step2 := by apply Matrix.ext; unfold raw32629step3 raw32629step2; decide +kernel
      have hl : raw32629step2Labels = labelEmbedding6 ∘ raw32629step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32629step2 raw32629step2Labels raw32629step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw32630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32630step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32630step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32630 raw32630Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw32630 raw32630Labels = mixedMoment B raw32630step0 raw32630step0Labels := by
      have hz : ∀ j, raw32630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32630step0 = (fun i j => raw32630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32630step0 raw32630; decide +kernel
      have hl : raw32630step0Labels = raw32630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32630 raw32630Labels permutation346 hz
    mixedMoment B raw32630step0 raw32630step0Labels = mixedMoment B raw32630step1 raw32630step1Labels := by
      have ha : raw32630step1 = (fun i j => raw32630step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32630step1 raw32630step0; decide +kernel
      have hl : raw32630step1Labels = raw32630step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32630step0 raw32630step0Labels permutation34 permutation3
    mixedMoment B raw32630step1 raw32630step1Labels = mixedMoment B raw32630step2 raw32630step2Labels := by
      have ha : raw32630step2 = raw32630step1 := by apply Matrix.ext; unfold raw32630step2 raw32630step1; decide +kernel
      have hl : raw32630step1Labels = labelEmbedding6 ∘ raw32630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32630step1 raw32630step1Labels raw32630step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw32631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32631 raw32631Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32631 raw32631Labels = mixedMoment B raw32631step0 raw32631step0Labels := by
      have ha : raw32631step0 = (fun i j => raw32631 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32631step0 raw32631; decide +kernel
      have hl : raw32631step0Labels = raw32631Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32631 raw32631Labels permutation176 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw32632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32632 raw32632Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw32632 raw32632Labels = mixedMoment B raw32632step0 raw32632step0Labels := by
      have hz : ∀ j, raw32632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32632step0 = (fun i j => raw32632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32632step0 raw32632; decide +kernel
      have hl : raw32632step0Labels = raw32632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32632 raw32632Labels permutation346 hz
    mixedMoment B raw32632step0 raw32632step0Labels = mixedMoment B raw32632step1 raw32632step1Labels := by
      have ha : raw32632step1 = (fun i j => raw32632step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32632step1 raw32632step0; decide +kernel
      have hl : raw32632step1Labels = raw32632step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32632step0 raw32632step0Labels permutation34 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw32633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32633step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32633 raw32633Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw32633 raw32633Labels = mixedMoment B raw32633step0 raw32633step0Labels := by
      have ha : raw32633step0 = (fun i j => raw32633 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32633step0 raw32633; decide +kernel
      have hl : raw32633step0Labels = raw32633Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32633 raw32633Labels permutation164 permutation3
    mixedMoment B raw32633step0 raw32633step0Labels = mixedMoment B raw32633step1 raw32633step1Labels := by
      have ha : raw32633step1 = raw32633step0 := by apply Matrix.ext; unfold raw32633step1 raw32633step0; decide +kernel
      have hl : raw32633step0Labels = labelEmbedding6 ∘ raw32633step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32633step0 raw32633step0Labels raw32633step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

def raw32634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32634 raw32634Labels = mixedMoment B node4981 node4981Labels := by
  calc
    _ = mixedMoment B node4981 node4981Labels := by rfl

def raw32635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw32635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32635 raw32635Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw32635 raw32635Labels = mixedMoment B raw32635step0 raw32635step0Labels := by
      have ha : raw32635step0 = (fun i j => raw32635 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32635step0 raw32635; decide +kernel
      have hl : raw32635step0Labels = raw32635Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32635 raw32635Labels permutation164 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw32636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32636 raw32636Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw32636 raw32636Labels = mixedMoment B raw32636step0 raw32636step0Labels := by
      have ha : raw32636step0 = (fun i j => raw32636 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32636step0 raw32636; decide +kernel
      have hl : raw32636step0Labels = raw32636Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32636 raw32636Labels permutation153 permutation2
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw32637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32637step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32637step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32637 raw32637Labels = mixedMoment B node4515 node4515Labels := by
  calc
    mixedMoment B raw32637 raw32637Labels = mixedMoment B raw32637step0 raw32637step0Labels := by
      have hz : ∀ j, raw32637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32637step0 = (fun i j => raw32637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32637step0 raw32637; decide +kernel
      have hl : raw32637step0Labels = raw32637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32637 raw32637Labels permutation346 hz
    mixedMoment B raw32637step0 raw32637step0Labels = mixedMoment B raw32637step1 raw32637step1Labels := by
      have ha : raw32637step1 = (fun i j => raw32637step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32637step1 raw32637step0; decide +kernel
      have hl : raw32637step1Labels = raw32637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32637step0 raw32637step0Labels permutation34 permutation3
    mixedMoment B raw32637step1 raw32637step1Labels = mixedMoment B raw32637step2 raw32637step2Labels := by
      have ha : raw32637step2 = raw32637step1 := by apply Matrix.ext; unfold raw32637step2 raw32637step1; decide +kernel
      have hl : raw32637step1Labels = labelEmbedding6 ∘ raw32637step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32637step1 raw32637step1Labels raw32637step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4515 node4515Labels := by rfl

def raw32638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw32638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32638 raw32638Labels = mixedMoment B node4984 node4984Labels := by
  calc
    mixedMoment B raw32638 raw32638Labels = mixedMoment B raw32638step0 raw32638step0Labels := by
      have hz : ∀ j, raw32638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32638step0 = (fun i j => raw32638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32638step0 raw32638; decide +kernel
      have hl : raw32638step0Labels = raw32638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32638 raw32638Labels permutation346 hz
    mixedMoment B raw32638step0 raw32638step0Labels = mixedMoment B raw32638step1 raw32638step1Labels := by
      have ha : raw32638step1 = (fun i j => raw32638step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32638step1 raw32638step0; decide +kernel
      have hl : raw32638step1Labels = raw32638step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32638step0 raw32638step0Labels permutation34 permutation2
    _ = mixedMoment B node4984 node4984Labels := by rfl

def raw32639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw32639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32639 raw32639Labels = mixedMoment B node5120 node5120Labels := by
  calc
    mixedMoment B raw32639 raw32639Labels = mixedMoment B raw32639step0 raw32639step0Labels := by
      have ha : raw32639step0 = (fun i j => raw32639 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32639step0 raw32639; decide +kernel
      have hl : raw32639step0Labels = raw32639Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32639 raw32639Labels permutation178 permutation2
    _ = mixedMoment B node5120 node5120Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
