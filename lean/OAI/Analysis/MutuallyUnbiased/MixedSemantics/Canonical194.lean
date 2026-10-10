import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24832 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw24832Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24832step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw24832step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24832step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24832step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24832step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24832step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24832 raw24832Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24832 raw24832Labels = mixedMoment B raw24832step0 raw24832step0Labels := by
      have hz : ∀ j, raw24832 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24832step0 = (fun i j => raw24832 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24832step0 raw24832; decide +kernel
      have hl : raw24832step0Labels = raw24832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24832 raw24832Labels permutation265 hz
    mixedMoment B raw24832step0 raw24832step0Labels = mixedMoment B raw24832step1 raw24832step1Labels := by
      have ha : raw24832step1 = (fun i j => raw24832step0 (permutation143 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24832step1 raw24832step0; decide +kernel
      have hl : raw24832step1Labels = raw24832step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24832step0 raw24832step0Labels permutation143 permutation0
    mixedMoment B raw24832step1 raw24832step1Labels = mixedMoment B raw24832step2 raw24832step2Labels := by
      have ha : raw24832step2 = -raw24832step1 := by apply Matrix.ext; change ∀ i j, raw24832step2 i j = -(raw24832step1 i j); unfold raw24832step2 raw24832step1; decide +kernel
      have hl : raw24832step2Labels = raw24832step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw24833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24833 raw24833Labels = mixedMoment B node1189 node1189Labels := by
  calc
    mixedMoment B raw24833 raw24833Labels = mixedMoment B raw24833step0 raw24833step0Labels := by
      have hz : ∀ j, raw24833 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24833step0 = (fun i j => raw24833 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24833step0 raw24833; decide +kernel
      have hl : raw24833step0Labels = raw24833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24833 raw24833Labels permutation265 hz
    mixedMoment B raw24833step0 raw24833step0Labels = mixedMoment B raw24833step1 raw24833step1Labels := by
      have ha : raw24833step1 = (fun i j => raw24833step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24833step1 raw24833step0; decide +kernel
      have hl : raw24833step1Labels = raw24833step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24833step0 raw24833step0Labels permutation34 permutation2
    _ = mixedMoment B node1189 node1189Labels := by rfl

def raw24834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24834 raw24834Labels = mixedMoment B node2537 node2537Labels := by
  calc
    mixedMoment B raw24834 raw24834Labels = mixedMoment B raw24834step0 raw24834step0Labels := by
      have ha : raw24834step0 = (fun i j => raw24834 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24834step0 raw24834; decide +kernel
      have hl : raw24834step0Labels = raw24834Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24834 raw24834Labels permutation154 permutation2
    _ = mixedMoment B node2537 node2537Labels := by rfl

def raw24835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24835 raw24835Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw24835 raw24835Labels = mixedMoment B raw24835step0 raw24835step0Labels := by
      have hz : ∀ j, raw24835 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24835step0 = (fun i j => raw24835 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24835step0 raw24835; decide +kernel
      have hl : raw24835step0Labels = raw24835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24835 raw24835Labels permutation265 hz
    mixedMoment B raw24835step0 raw24835step0Labels = mixedMoment B raw24835step1 raw24835step1Labels := by
      have ha : raw24835step1 = (fun i j => raw24835step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24835step1 raw24835step0; decide +kernel
      have hl : raw24835step1Labels = raw24835step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24835step0 raw24835step0Labels permutation34 permutation2
    _ = mixedMoment B node2404 node2404Labels := by rfl

def raw24836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24836 raw24836Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw24836 raw24836Labels = mixedMoment B raw24836step0 raw24836step0Labels := by
      have hz : ∀ j, raw24836 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24836step0 = (fun i j => raw24836 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24836step0 raw24836; decide +kernel
      have hl : raw24836step0Labels = raw24836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24836 raw24836Labels permutation265 hz
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw24837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw24837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw24837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24837 raw24837Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw24837 raw24837Labels = mixedMoment B raw24837step0 raw24837step0Labels := by
      have hz : ∀ j, raw24837 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24837step0 = (fun i j => raw24837 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24837step0 raw24837; decide +kernel
      have hl : raw24837step0Labels = raw24837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24837 raw24837Labels permutation265 hz
    mixedMoment B raw24837step0 raw24837step0Labels = mixedMoment B raw24837step1 raw24837step1Labels := by
      have ha : raw24837step1 = (fun i j => raw24837step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24837step1 raw24837step0; decide +kernel
      have hl : raw24837step1Labels = raw24837step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24837step0 raw24837step0Labels permutation34 permutation2
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw24838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24838 raw24838Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw24838 raw24838Labels = mixedMoment B raw24838step0 raw24838step0Labels := by
      have hz : ∀ j, raw24838 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24838step0 = (fun i j => raw24838 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24838step0 raw24838; decide +kernel
      have hl : raw24838step0Labels = raw24838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24838 raw24838Labels permutation265 hz
    mixedMoment B raw24838step0 raw24838step0Labels = mixedMoment B raw24838step1 raw24838step1Labels := by
      have ha : raw24838step1 = (fun i j => raw24838step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24838step1 raw24838step0; decide +kernel
      have hl : raw24838step1Labels = raw24838step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24838step0 raw24838step0Labels permutation35 permutation2
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw24839 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw24839Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24839step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw24839step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24839step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24839step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24839 raw24839Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw24839 raw24839Labels = mixedMoment B raw24839step0 raw24839step0Labels := by
      have hz : ∀ j, raw24839 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24839step0 = (fun i j => raw24839 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24839step0 raw24839; decide +kernel
      have hl : raw24839step0Labels = raw24839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24839 raw24839Labels permutation265 hz
    mixedMoment B raw24839step0 raw24839step0Labels = mixedMoment B raw24839step1 raw24839step1Labels := by
      have ha : raw24839step1 = (fun i j => raw24839step0 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24839step1 raw24839step0; decide +kernel
      have hl : raw24839step1Labels = raw24839step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24839step0 raw24839step0Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw24840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24840 raw24840Labels = mixedMoment B node1183 node1183Labels := by
  calc
    mixedMoment B raw24840 raw24840Labels = mixedMoment B raw24840step0 raw24840step0Labels := by
      have ha : raw24840step0 = (fun i j => raw24840 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24840step0 raw24840; decide +kernel
      have hl : raw24840step0Labels = raw24840Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24840 raw24840Labels permutation179 permutation2
    _ = mixedMoment B node1183 node1183Labels := by rfl

def raw24841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24841 raw24841Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw24841 raw24841Labels = mixedMoment B raw24841step0 raw24841step0Labels := by
      have hz : ∀ j, raw24841 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24841step0 = (fun i j => raw24841 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24841step0 raw24841; decide +kernel
      have hl : raw24841step0Labels = raw24841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24841 raw24841Labels permutation265 hz
    mixedMoment B raw24841step0 raw24841step0Labels = mixedMoment B raw24841step1 raw24841step1Labels := by
      have ha : raw24841step1 = (fun i j => raw24841step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24841step1 raw24841step0; decide +kernel
      have hl : raw24841step1Labels = raw24841step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24841step0 raw24841step0Labels permutation35 permutation2
    _ = mixedMoment B node1286 node1286Labels := by rfl

def raw24842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24842 raw24842Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw24842 raw24842Labels = mixedMoment B raw24842step0 raw24842step0Labels := by
      have hz : ∀ j, raw24842 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24842step0 = (fun i j => raw24842 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24842step0 raw24842; decide +kernel
      have hl : raw24842step0Labels = raw24842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24842 raw24842Labels permutation265 hz
    mixedMoment B raw24842step0 raw24842step0Labels = mixedMoment B raw24842step1 raw24842step1Labels := by
      have ha : raw24842step1 = (fun i j => raw24842step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24842step1 raw24842step0; decide +kernel
      have hl : raw24842step1Labels = raw24842step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24842step0 raw24842step0Labels permutation35 permutation2
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw24843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw24843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw24843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24843 raw24843Labels = mixedMoment B node1189 node1189Labels := by
  calc
    mixedMoment B raw24843 raw24843Labels = mixedMoment B raw24843step0 raw24843step0Labels := by
      have hz : ∀ j, raw24843 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24843step0 = (fun i j => raw24843 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24843step0 raw24843; decide +kernel
      have hl : raw24843step0Labels = raw24843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24843 raw24843Labels permutation265 hz
    mixedMoment B raw24843step0 raw24843step0Labels = mixedMoment B raw24843step1 raw24843step1Labels := by
      have ha : raw24843step1 = (fun i j => raw24843step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24843step1 raw24843step0; decide +kernel
      have hl : raw24843step1Labels = raw24843step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24843step0 raw24843step0Labels permutation36 permutation2
    _ = mixedMoment B node1189 node1189Labels := by rfl

def raw24844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24844 raw24844Labels = mixedMoment B node1185 node1185Labels := by
  calc
    mixedMoment B raw24844 raw24844Labels = mixedMoment B raw24844step0 raw24844step0Labels := by
      have hz : ∀ j, raw24844 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24844step0 = (fun i j => raw24844 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24844step0 raw24844; decide +kernel
      have hl : raw24844step0Labels = raw24844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24844 raw24844Labels permutation265 hz
    mixedMoment B raw24844step0 raw24844step0Labels = mixedMoment B raw24844step1 raw24844step1Labels := by
      have ha : raw24844step1 = (fun i j => raw24844step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24844step1 raw24844step0; decide +kernel
      have hl : raw24844step1Labels = raw24844step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24844step0 raw24844step0Labels permutation34 permutation2
    _ = mixedMoment B node1185 node1185Labels := by rfl

def raw24845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24845 raw24845Labels = mixedMoment B node2535 node2535Labels := by
  calc
    mixedMoment B raw24845 raw24845Labels = mixedMoment B raw24845step0 raw24845step0Labels := by
      have ha : raw24845step0 = (fun i j => raw24845 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24845step0 raw24845; decide +kernel
      have hl : raw24845step0Labels = raw24845Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24845 raw24845Labels permutation154 permutation2
    _ = mixedMoment B node2535 node2535Labels := by rfl

def raw24846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24846 raw24846Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw24846 raw24846Labels = mixedMoment B raw24846step0 raw24846step0Labels := by
      have hz : ∀ j, raw24846 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24846step0 = (fun i j => raw24846 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24846step0 raw24846; decide +kernel
      have hl : raw24846step0Labels = raw24846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24846 raw24846Labels permutation265 hz
    mixedMoment B raw24846step0 raw24846step0Labels = mixedMoment B raw24846step1 raw24846step1Labels := by
      have ha : raw24846step1 = (fun i j => raw24846step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24846step1 raw24846step0; decide +kernel
      have hl : raw24846step1Labels = raw24846step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24846step0 raw24846step0Labels permutation34 permutation2
    _ = mixedMoment B node2400 node2400Labels := by rfl

def raw24847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24847 raw24847Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw24847 raw24847Labels = mixedMoment B raw24847step0 raw24847step0Labels := by
      have hz : ∀ j, raw24847 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24847step0 = (fun i j => raw24847 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24847step0 raw24847; decide +kernel
      have hl : raw24847step0Labels = raw24847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24847 raw24847Labels permutation265 hz
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw24848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2]]
def raw24848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24848 raw24848Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw24848 raw24848Labels = mixedMoment B raw24848step0 raw24848step0Labels := by
      have hz : ∀ j, raw24848 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24848step0 = (fun i j => raw24848 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24848step0 raw24848; decide +kernel
      have hl : raw24848step0Labels = raw24848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24848 raw24848Labels permutation520 hz
    mixedMoment B raw24848step0 raw24848step0Labels = mixedMoment B raw24848step1 raw24848step1Labels := by
      have hz : ∀ j, raw24848step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24848step1 = (fun i j => raw24848step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24848step1 raw24848step0; decide +kernel
      have hl : raw24848step1Labels = raw24848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24848step0 raw24848step0Labels permutation56 hz
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw24849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw24849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw24849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24849 raw24849Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw24849 raw24849Labels = mixedMoment B raw24849step0 raw24849step0Labels := by
      have hz : ∀ j, raw24849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24849step0 = (fun i j => raw24849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24849step0 raw24849; decide +kernel
      have hl : raw24849step0Labels = raw24849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24849 raw24849Labels permutation265 hz
    mixedMoment B raw24849step0 raw24849step0Labels = mixedMoment B raw24849step1 raw24849step1Labels := by
      have ha : raw24849step1 = (fun i j => raw24849step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24849step1 raw24849step0; decide +kernel
      have hl : raw24849step1Labels = raw24849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24849step0 raw24849step0Labels permutation34 permutation2
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw24850 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![0, 0], ![2, -2]]
def raw24850Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24850step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw24850step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24850step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw24850step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24850 raw24850Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw24850 raw24850Labels = mixedMoment B raw24850step0 raw24850step0Labels := by
      have hz : ∀ j, raw24850 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24850step0 = (fun i j => raw24850 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24850step0 raw24850; decide +kernel
      have hl : raw24850step0Labels = raw24850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24850 raw24850Labels permutation520 hz
    mixedMoment B raw24850step0 raw24850step0Labels = mixedMoment B raw24850step1 raw24850step1Labels := by
      have hz : ∀ j, raw24850step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24850step1 = (fun i j => raw24850step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24850step1 raw24850step0; decide +kernel
      have hl : raw24850step1Labels = raw24850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24850step0 raw24850step0Labels permutation56 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

def raw24851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24851 raw24851Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw24851 raw24851Labels = mixedMoment B raw24851step0 raw24851step0Labels := by
      have hz : ∀ j, raw24851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24851step0 = (fun i j => raw24851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24851step0 raw24851; decide +kernel
      have hl : raw24851step0Labels = raw24851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24851 raw24851Labels permutation265 hz
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw24852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24852 raw24852Labels = mixedMoment B node2536 node2536Labels := by
  calc
    _ = mixedMoment B node2536 node2536Labels := by rfl

def raw24853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24853 raw24853Labels = mixedMoment B node2403 node2403Labels := by
  calc
    mixedMoment B raw24853 raw24853Labels = mixedMoment B raw24853step0 raw24853step0Labels := by
      have hz : ∀ j, raw24853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24853step0 = (fun i j => raw24853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24853step0 raw24853; decide +kernel
      have hl : raw24853step0Labels = raw24853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24853 raw24853Labels permutation265 hz
    _ = mixedMoment B node2403 node2403Labels := by rfl

def raw24854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24854 raw24854Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw24854 raw24854Labels = mixedMoment B raw24854step0 raw24854step0Labels := by
      have hz : ∀ j, raw24854 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24854step0 = (fun i j => raw24854 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24854step0 raw24854; decide +kernel
      have hl : raw24854step0Labels = raw24854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24854 raw24854Labels permutation265 hz
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw24855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24855 raw24855Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw24855 raw24855Labels = mixedMoment B raw24855step0 raw24855step0Labels := by
      have hz : ∀ j, raw24855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24855step0 = (fun i j => raw24855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24855step0 raw24855; decide +kernel
      have hl : raw24855step0Labels = raw24855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24855 raw24855Labels permutation265 hz
    mixedMoment B raw24855step0 raw24855step0Labels = mixedMoment B raw24855step1 raw24855step1Labels := by
      have ha : raw24855step1 = (fun i j => raw24855step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24855step1 raw24855step0; decide +kernel
      have hl : raw24855step1Labels = raw24855step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24855step0 raw24855step0Labels permutation34 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw24856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24856 raw24856Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw24856 raw24856Labels = mixedMoment B raw24856step0 raw24856step0Labels := by
      have hz : ∀ j, raw24856 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24856step0 = (fun i j => raw24856 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24856step0 raw24856; decide +kernel
      have hl : raw24856step0Labels = raw24856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24856 raw24856Labels permutation265 hz
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw24857 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24857Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24857step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24857step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24857 raw24857Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw24857 raw24857Labels = mixedMoment B raw24857step0 raw24857step0Labels := by
      have hz : ∀ j, raw24857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24857step0 = (fun i j => raw24857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24857step0 raw24857; decide +kernel
      have hl : raw24857step0Labels = raw24857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24857 raw24857Labels permutation265 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw24858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24858 raw24858Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw24858 raw24858Labels = mixedMoment B raw24858step0 raw24858step0Labels := by
      have ha : raw24858step0 = (fun i j => raw24858 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24858step0 raw24858; decide +kernel
      have hl : raw24858step0Labels = raw24858Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24858 raw24858Labels permutation176 permutation2
    _ = mixedMoment B node1097 node1097Labels := by rfl

def raw24859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24859 raw24859Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw24859 raw24859Labels = mixedMoment B raw24859step0 raw24859step0Labels := by
      have hz : ∀ j, raw24859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24859step0 = (fun i j => raw24859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24859step0 raw24859; decide +kernel
      have hl : raw24859step0Labels = raw24859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24859 raw24859Labels permutation265 hz
    mixedMoment B raw24859step0 raw24859step0Labels = mixedMoment B raw24859step1 raw24859step1Labels := by
      have ha : raw24859step1 = (fun i j => raw24859step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24859step1 raw24859step0; decide +kernel
      have hl : raw24859step1Labels = raw24859step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24859step0 raw24859step0Labels permutation34 permutation2
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw24860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24860 raw24860Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw24860 raw24860Labels = mixedMoment B raw24860step0 raw24860step0Labels := by
      have hz : ∀ j, raw24860 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24860step0 = (fun i j => raw24860 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24860step0 raw24860; decide +kernel
      have hl : raw24860step0Labels = raw24860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24860 raw24860Labels permutation265 hz
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw24861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24861 raw24861Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw24861 raw24861Labels = mixedMoment B raw24861step0 raw24861step0Labels := by
      have hz : ∀ j, raw24861 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24861step0 = (fun i j => raw24861 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24861step0 raw24861; decide +kernel
      have hl : raw24861step0Labels = raw24861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24861 raw24861Labels permutation265 hz
    _ = mixedMoment B node1101 node1101Labels := by rfl

def raw24862 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24862 raw24862Labels = mixedMoment B node3245 node3245Labels := by
  calc
    mixedMoment B raw24862 raw24862Labels = mixedMoment B raw24862step0 raw24862step0Labels := by
      have hz : ∀ j, raw24862 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24862step0 = (fun i j => raw24862 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24862step0 raw24862; decide +kernel
      have hl : raw24862step0Labels = raw24862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24862 raw24862Labels permutation265 hz
    mixedMoment B raw24862step0 raw24862step0Labels = mixedMoment B raw24862step1 raw24862step1Labels := by
      have ha : raw24862step1 = (fun i j => raw24862step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24862step1 raw24862step0; decide +kernel
      have hl : raw24862step1Labels = raw24862step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24862step0 raw24862step0Labels permutation32 permutation4
    mixedMoment B raw24862step1 raw24862step1Labels = mixedMoment B raw24862step2 raw24862step2Labels := by
      have ha : raw24862step2 = -raw24862step1 := by apply Matrix.ext; change ∀ i j, raw24862step2 i j = -(raw24862step1 i j); unfold raw24862step2 raw24862step1; decide +kernel
      have hl : raw24862step2Labels = raw24862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3245 node3245Labels := by rfl

def raw24863 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24863 raw24863Labels = mixedMoment B node1542 node1542Labels := by
  calc
    mixedMoment B raw24863 raw24863Labels = mixedMoment B raw24863step0 raw24863step0Labels := by
      have ha : raw24863step0 = (fun i j => raw24863 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24863step0 raw24863; decide +kernel
      have hl : raw24863step0Labels = raw24863Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24863 raw24863Labels permutation176 permutation4
    mixedMoment B raw24863step0 raw24863step0Labels = mixedMoment B raw24863step1 raw24863step1Labels := by
      have ha : raw24863step1 = -raw24863step0 := by apply Matrix.ext; change ∀ i j, raw24863step1 i j = -(raw24863step0 i j); unfold raw24863step1 raw24863step0; decide +kernel
      have hl : raw24863step1Labels = raw24863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1542 node1542Labels := by rfl

def raw24864 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24864 raw24864Labels = mixedMoment B node1622 node1622Labels := by
  calc
    mixedMoment B raw24864 raw24864Labels = mixedMoment B raw24864step0 raw24864step0Labels := by
      have hz : ∀ j, raw24864 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24864step0 = (fun i j => raw24864 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24864step0 raw24864; decide +kernel
      have hl : raw24864step0Labels = raw24864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24864 raw24864Labels permutation265 hz
    mixedMoment B raw24864step0 raw24864step0Labels = mixedMoment B raw24864step1 raw24864step1Labels := by
      have ha : raw24864step1 = (fun i j => raw24864step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24864step1 raw24864step0; decide +kernel
      have hl : raw24864step1Labels = raw24864step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24864step0 raw24864step0Labels permutation32 permutation4
    mixedMoment B raw24864step1 raw24864step1Labels = mixedMoment B raw24864step2 raw24864step2Labels := by
      have ha : raw24864step2 = -raw24864step1 := by apply Matrix.ext; change ∀ i j, raw24864step2 i j = -(raw24864step1 i j); unfold raw24864step2 raw24864step1; decide +kernel
      have hl : raw24864step2Labels = raw24864step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1622 node1622Labels := by rfl

def raw24865 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw24865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24865 raw24865Labels = mixedMoment B node1547 node1547Labels := by
  calc
    mixedMoment B raw24865 raw24865Labels = mixedMoment B raw24865step0 raw24865step0Labels := by
      have hz : ∀ j, raw24865 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24865step0 = (fun i j => raw24865 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24865step0 raw24865; decide +kernel
      have hl : raw24865step0Labels = raw24865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24865 raw24865Labels permutation265 hz
    mixedMoment B raw24865step0 raw24865step0Labels = mixedMoment B raw24865step1 raw24865step1Labels := by
      have ha : raw24865step1 = (fun i j => raw24865step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24865step1 raw24865step0; decide +kernel
      have hl : raw24865step1Labels = raw24865step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24865step0 raw24865step0Labels permutation34 permutation4
    mixedMoment B raw24865step1 raw24865step1Labels = mixedMoment B raw24865step2 raw24865step2Labels := by
      have ha : raw24865step2 = -raw24865step1 := by apply Matrix.ext; change ∀ i j, raw24865step2 i j = -(raw24865step1 i j); unfold raw24865step2 raw24865step1; decide +kernel
      have hl : raw24865step2Labels = raw24865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1547 node1547Labels := by rfl

def raw24866 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw24866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24866 raw24866Labels = mixedMoment B node1547 node1547Labels := by
  calc
    mixedMoment B raw24866 raw24866Labels = mixedMoment B raw24866step0 raw24866step0Labels := by
      have hz : ∀ j, raw24866 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24866step0 = (fun i j => raw24866 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24866step0 raw24866; decide +kernel
      have hl : raw24866step0Labels = raw24866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24866 raw24866Labels permutation265 hz
    mixedMoment B raw24866step0 raw24866step0Labels = mixedMoment B raw24866step1 raw24866step1Labels := by
      have ha : raw24866step1 = (fun i j => raw24866step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24866step1 raw24866step0; decide +kernel
      have hl : raw24866step1Labels = raw24866step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24866step0 raw24866step0Labels permutation32 permutation4
    mixedMoment B raw24866step1 raw24866step1Labels = mixedMoment B raw24866step2 raw24866step2Labels := by
      have ha : raw24866step2 = -raw24866step1 := by apply Matrix.ext; change ∀ i j, raw24866step2 i j = -(raw24866step1 i j); unfold raw24866step2 raw24866step1; decide +kernel
      have hl : raw24866step2Labels = raw24866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1547 node1547Labels := by rfl

def raw24867 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw24867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24867step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24867 raw24867Labels = mixedMoment B node1546 node1546Labels := by
  calc
    mixedMoment B raw24867 raw24867Labels = mixedMoment B raw24867step0 raw24867step0Labels := by
      have hz : ∀ j, raw24867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24867step0 = (fun i j => raw24867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24867step0 raw24867; decide +kernel
      have hl : raw24867step0Labels = raw24867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24867 raw24867Labels permutation265 hz
    mixedMoment B raw24867step0 raw24867step0Labels = mixedMoment B raw24867step1 raw24867step1Labels := by
      have ha : raw24867step1 = (fun i j => raw24867step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24867step1 raw24867step0; decide +kernel
      have hl : raw24867step1Labels = raw24867step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24867step0 raw24867step0Labels permutation32 permutation4
    mixedMoment B raw24867step1 raw24867step1Labels = mixedMoment B raw24867step2 raw24867step2Labels := by
      have ha : raw24867step2 = -raw24867step1 := by apply Matrix.ext; change ∀ i j, raw24867step2 i j = -(raw24867step1 i j); unfold raw24867step2 raw24867step1; decide +kernel
      have hl : raw24867step2Labels = raw24867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1546 node1546Labels := by rfl

def raw24868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24868 raw24868Labels = mixedMoment B node1184 node1184Labels := by
  calc
    mixedMoment B raw24868 raw24868Labels = mixedMoment B raw24868step0 raw24868step0Labels := by
      have hz : ∀ j, raw24868 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24868step0 = (fun i j => raw24868 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24868step0 raw24868; decide +kernel
      have hl : raw24868step0Labels = raw24868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24868 raw24868Labels permutation265 hz
    mixedMoment B raw24868step0 raw24868step0Labels = mixedMoment B raw24868step1 raw24868step1Labels := by
      have ha : raw24868step1 = (fun i j => raw24868step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24868step1 raw24868step0; decide +kernel
      have hl : raw24868step1Labels = raw24868step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24868step0 raw24868step0Labels permutation34 permutation2
    _ = mixedMoment B node1184 node1184Labels := by rfl

def raw24869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24869 raw24869Labels = mixedMoment B node2534 node2534Labels := by
  calc
    mixedMoment B raw24869 raw24869Labels = mixedMoment B raw24869step0 raw24869step0Labels := by
      have ha : raw24869step0 = (fun i j => raw24869 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24869step0 raw24869; decide +kernel
      have hl : raw24869step0Labels = raw24869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24869 raw24869Labels permutation154 permutation2
    _ = mixedMoment B node2534 node2534Labels := by rfl

def raw24870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24870 raw24870Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw24870 raw24870Labels = mixedMoment B raw24870step0 raw24870step0Labels := by
      have hz : ∀ j, raw24870 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24870step0 = (fun i j => raw24870 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24870step0 raw24870; decide +kernel
      have hl : raw24870step0Labels = raw24870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24870 raw24870Labels permutation265 hz
    mixedMoment B raw24870step0 raw24870step0Labels = mixedMoment B raw24870step1 raw24870step1Labels := by
      have ha : raw24870step1 = (fun i j => raw24870step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24870step1 raw24870step0; decide +kernel
      have hl : raw24870step1Labels = raw24870step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24870step0 raw24870step0Labels permutation34 permutation2
    _ = mixedMoment B node2399 node2399Labels := by rfl

def raw24871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24871 raw24871Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw24871 raw24871Labels = mixedMoment B raw24871step0 raw24871step0Labels := by
      have hz : ∀ j, raw24871 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24871step0 = (fun i j => raw24871 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24871step0 raw24871; decide +kernel
      have hl : raw24871step0Labels = raw24871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24871 raw24871Labels permutation265 hz
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw24872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 0, 0], ![2, 1, -3]]
def raw24872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24872 raw24872Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw24872 raw24872Labels = mixedMoment B raw24872step0 raw24872step0Labels := by
      have hz : ∀ j, raw24872 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24872step0 = (fun i j => raw24872 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24872step0 raw24872; decide +kernel
      have hl : raw24872step0Labels = raw24872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24872 raw24872Labels permutation520 hz
    mixedMoment B raw24872step0 raw24872step0Labels = mixedMoment B raw24872step1 raw24872step1Labels := by
      have hz : ∀ j, raw24872step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24872step1 = (fun i j => raw24872step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24872step1 raw24872step0; decide +kernel
      have hl : raw24872step1Labels = raw24872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24872step0 raw24872step0Labels permutation56 hz
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw24873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw24873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw24873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24873 raw24873Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw24873 raw24873Labels = mixedMoment B raw24873step0 raw24873step0Labels := by
      have hz : ∀ j, raw24873 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24873step0 = (fun i j => raw24873 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24873step0 raw24873; decide +kernel
      have hl : raw24873step0Labels = raw24873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24873 raw24873Labels permutation265 hz
    mixedMoment B raw24873step0 raw24873step0Labels = mixedMoment B raw24873step1 raw24873step1Labels := by
      have ha : raw24873step1 = (fun i j => raw24873step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24873step1 raw24873step0; decide +kernel
      have hl : raw24873step1Labels = raw24873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24873step0 raw24873step0Labels permutation34 permutation2
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw24874 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![3, -3]]
def raw24874Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![3, -3]]
def raw24874step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw24874step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw24874step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw24874step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24874 raw24874Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw24874 raw24874Labels = mixedMoment B raw24874step0 raw24874step0Labels := by
      have hz : ∀ j, raw24874 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24874step0 = (fun i j => raw24874 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24874step0 raw24874; decide +kernel
      have hl : raw24874step0Labels = raw24874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24874 raw24874Labels permutation520 hz
    mixedMoment B raw24874step0 raw24874step0Labels = mixedMoment B raw24874step1 raw24874step1Labels := by
      have hz : ∀ j, raw24874step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24874step1 = (fun i j => raw24874step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24874step1 raw24874step0; decide +kernel
      have hl : raw24874step1Labels = raw24874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24874step0 raw24874step0Labels permutation56 hz
    mixedMoment B raw24874step1 raw24874step1Labels = mixedMoment B raw24874step2 raw24874step2Labels := by
      have ha : raw24874step2 = (fun i j => raw24874step1 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24874step2 raw24874step1; decide +kernel
      have hl : raw24874step2Labels = raw24874step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24874step1 raw24874step1Labels permutation30 permutation0
    mixedMoment B raw24874step2 raw24874step2Labels = mixedMoment B raw24874step3 raw24874step3Labels := by
      have ha : raw24874step3 = -raw24874step2 := by apply Matrix.ext; change ∀ i j, raw24874step3 i j = -(raw24874step2 i j); unfold raw24874step3 raw24874step2; decide +kernel
      have hl : raw24874step3Labels = raw24874step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw24875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24875 raw24875Labels = mixedMoment B node1201 node1201Labels := by
  calc
    mixedMoment B raw24875 raw24875Labels = mixedMoment B raw24875step0 raw24875step0Labels := by
      have ha : raw24875step0 = (fun i j => raw24875 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24875step0 raw24875; decide +kernel
      have hl : raw24875step0Labels = raw24875Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24875 raw24875Labels permutation154 permutation2
    _ = mixedMoment B node1201 node1201Labels := by rfl

def raw24876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24876 raw24876Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw24876 raw24876Labels = mixedMoment B raw24876step0 raw24876step0Labels := by
      have ha : raw24876step0 = (fun i j => raw24876 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24876step0 raw24876; decide +kernel
      have hl : raw24876step0Labels = raw24876Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24876 raw24876Labels permutation154 permutation2
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw24877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24877 raw24877Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw24877 raw24877Labels = mixedMoment B raw24877step0 raw24877step0Labels := by
      have ha : raw24877step0 = (fun i j => raw24877 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24877step0 raw24877; decide +kernel
      have hl : raw24877step0Labels = raw24877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24877 raw24877Labels permutation178 permutation2
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw24878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24878 raw24878Labels = mixedMoment B node2698 node2698Labels := by
  calc
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw24879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw24879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24879 raw24879Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw24879 raw24879Labels = mixedMoment B raw24879step0 raw24879step0Labels := by
      have ha : raw24879step0 = (fun i j => raw24879 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24879step0 raw24879; decide +kernel
      have hl : raw24879step0Labels = raw24879Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24879 raw24879Labels permutation154 permutation2
    _ = mixedMoment B node2695 node2695Labels := by rfl

def raw24880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24880 raw24880Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw24880 raw24880Labels = mixedMoment B raw24880step0 raw24880step0Labels := by
      have ha : raw24880step0 = (fun i j => raw24880 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24880step0 raw24880; decide +kernel
      have hl : raw24880step0Labels = raw24880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24880 raw24880Labels permutation155 permutation2
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw24881 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw24881Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24881step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24881step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24881 raw24881Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw24881 raw24881Labels = mixedMoment B raw24881step0 raw24881step0Labels := by
      have ha : raw24881step0 = (fun i j => raw24881 (permutation155 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24881step0 raw24881; decide +kernel
      have hl : raw24881step0Labels = raw24881Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24881 raw24881Labels permutation155 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw24882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24882 raw24882Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw24882 raw24882Labels = mixedMoment B raw24882step0 raw24882step0Labels := by
      have ha : raw24882step0 = (fun i j => raw24882 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24882step0 raw24882; decide +kernel
      have hl : raw24882step0Labels = raw24882Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24882 raw24882Labels permutation179 permutation2
    _ = mixedMoment B node1228 node1228Labels := by rfl

def raw24883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24883 raw24883Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw24883 raw24883Labels = mixedMoment B raw24883step0 raw24883step0Labels := by
      have ha : raw24883step0 = (fun i j => raw24883 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24883step0 raw24883; decide +kernel
      have hl : raw24883step0Labels = raw24883Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24883 raw24883Labels permutation155 permutation2
    _ = mixedMoment B node1228 node1228Labels := by rfl

def raw24884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24884 raw24884Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw24884 raw24884Labels = mixedMoment B raw24884step0 raw24884step0Labels := by
      have ha : raw24884step0 = (fun i j => raw24884 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24884step0 raw24884; decide +kernel
      have hl : raw24884step0Labels = raw24884Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24884 raw24884Labels permutation155 permutation2
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw24885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw24885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24885 raw24885Labels = mixedMoment B node1201 node1201Labels := by
  calc
    mixedMoment B raw24885 raw24885Labels = mixedMoment B raw24885step0 raw24885step0Labels := by
      have ha : raw24885step0 = (fun i j => raw24885 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24885step0 raw24885; decide +kernel
      have hl : raw24885step0Labels = raw24885Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24885 raw24885Labels permutation156 permutation2
    _ = mixedMoment B node1201 node1201Labels := by rfl

def raw24886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24886 raw24886Labels = mixedMoment B node1198 node1198Labels := by
  calc
    mixedMoment B raw24886 raw24886Labels = mixedMoment B raw24886step0 raw24886step0Labels := by
      have ha : raw24886step0 = (fun i j => raw24886 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24886step0 raw24886; decide +kernel
      have hl : raw24886step0Labels = raw24886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24886 raw24886Labels permutation154 permutation2
    _ = mixedMoment B node1198 node1198Labels := by rfl

def raw24887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24887 raw24887Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw24887 raw24887Labels = mixedMoment B raw24887step0 raw24887step0Labels := by
      have ha : raw24887step0 = (fun i j => raw24887 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24887step0 raw24887; decide +kernel
      have hl : raw24887step0Labels = raw24887Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24887 raw24887Labels permutation154 permutation2
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw24888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24888 raw24888Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw24888 raw24888Labels = mixedMoment B raw24888step0 raw24888step0Labels := by
      have ha : raw24888step0 = (fun i j => raw24888 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24888step0 raw24888; decide +kernel
      have hl : raw24888step0Labels = raw24888Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24888 raw24888Labels permutation178 permutation2
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw24889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24889 raw24889Labels = mixedMoment B node2697 node2697Labels := by
  calc
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw24890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2]]
def raw24890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24890 raw24890Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw24890 raw24890Labels = mixedMoment B raw24890step0 raw24890step0Labels := by
      have hz : ∀ j, raw24890 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24890step0 = (fun i j => raw24890 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24890step0 raw24890; decide +kernel
      have hl : raw24890step0Labels = raw24890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24890 raw24890Labels permutation520 hz
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw24891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw24891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24891 raw24891Labels = mixedMoment B node2701 node2701Labels := by
  calc
    mixedMoment B raw24891 raw24891Labels = mixedMoment B raw24891step0 raw24891step0Labels := by
      have ha : raw24891step0 = (fun i j => raw24891 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24891step0 raw24891; decide +kernel
      have hl : raw24891step0Labels = raw24891Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24891 raw24891Labels permutation154 permutation2
    _ = mixedMoment B node2701 node2701Labels := by rfl

def raw24892 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![2, -2]]
def raw24892Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24892step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw24892step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24892step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24892step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24892step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24892step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24892 raw24892Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw24892 raw24892Labels = mixedMoment B raw24892step0 raw24892step0Labels := by
      have hz : ∀ j, raw24892 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24892step0 = (fun i j => raw24892 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24892step0 raw24892; decide +kernel
      have hl : raw24892step0Labels = raw24892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24892 raw24892Labels permutation520 hz
    mixedMoment B raw24892step0 raw24892step0Labels = mixedMoment B raw24892step1 raw24892step1Labels := by
      have ha : raw24892step1 = (fun i j => raw24892step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24892step1 raw24892step0; decide +kernel
      have hl : raw24892step1Labels = raw24892step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24892step0 raw24892step0Labels permutation125 permutation0
    mixedMoment B raw24892step1 raw24892step1Labels = mixedMoment B raw24892step2 raw24892step2Labels := by
      have ha : raw24892step2 = -raw24892step1 := by apply Matrix.ext; change ∀ i j, raw24892step2 i j = -(raw24892step1 i j); unfold raw24892step2 raw24892step1; decide +kernel
      have hl : raw24892step2Labels = raw24892step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw24893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24893 raw24893Labels = mixedMoment B node1200 node1200Labels := by
  calc
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw24894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24894 raw24894Labels = mixedMoment B node2461 node2461Labels := by
  calc
    _ = mixedMoment B node2461 node2461Labels := by rfl

def raw24895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24895 raw24895Labels = mixedMoment B node2461 node2461Labels := by
  calc
    mixedMoment B raw24895 raw24895Labels = mixedMoment B raw24895step0 raw24895step0Labels := by
      have ha : raw24895step0 = (fun i j => raw24895 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24895step0 raw24895; decide +kernel
      have hl : raw24895step0Labels = raw24895Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24895 raw24895Labels permutation176 permutation2
    _ = mixedMoment B node2461 node2461Labels := by rfl

def raw24896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24896 raw24896Labels = mixedMoment B node2694 node2694Labels := by
  calc
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw24897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24897 raw24897Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw24897 raw24897Labels = mixedMoment B raw24897step0 raw24897step0Labels := by
      have ha : raw24897step0 = (fun i j => raw24897 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24897step0 raw24897; decide +kernel
      have hl : raw24897step0Labels = raw24897Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24897 raw24897Labels permutation154 permutation2
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw24898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24898 raw24898Labels = mixedMoment B node2703 node2703Labels := by
  calc
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw24899 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24899Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24899 raw24899Labels = mixedMoment B node4090 node4090Labels := by
  calc
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw24900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24900 raw24900Labels = mixedMoment B node1122 node1122Labels := by
  calc
    _ = mixedMoment B node1122 node1122Labels := by rfl

def raw24901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24901 raw24901Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw24901 raw24901Labels = mixedMoment B raw24901step0 raw24901step0Labels := by
      have ha : raw24901step0 = (fun i j => raw24901 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24901step0 raw24901; decide +kernel
      have hl : raw24901step0Labels = raw24901Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24901 raw24901Labels permutation154 permutation2
    _ = mixedMoment B node1108 node1108Labels := by rfl

def raw24902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24902 raw24902Labels = mixedMoment B node1108 node1108Labels := by
  calc
    _ = mixedMoment B node1108 node1108Labels := by rfl

def raw24903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24903 raw24903Labels = mixedMoment B node1107 node1107Labels := by
  calc
    _ = mixedMoment B node1107 node1107Labels := by rfl

def raw24904 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24904 raw24904Labels = mixedMoment B node3281 node3281Labels := by
  calc
    mixedMoment B raw24904 raw24904Labels = mixedMoment B raw24904step0 raw24904step0Labels := by
      have ha : raw24904step0 = (fun i j => raw24904 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24904step0 raw24904; decide +kernel
      have hl : raw24904step0Labels = raw24904Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24904 raw24904Labels permutation152 permutation4
    mixedMoment B raw24904step0 raw24904step0Labels = mixedMoment B raw24904step1 raw24904step1Labels := by
      have ha : raw24904step1 = -raw24904step0 := by apply Matrix.ext; change ∀ i j, raw24904step1 i j = -(raw24904step0 i j); unfold raw24904step1 raw24904step0; decide +kernel
      have hl : raw24904step1Labels = raw24904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3281 node3281Labels := by rfl

def raw24905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24905 raw24905Labels = mixedMoment B node1622 node1622Labels := by
  calc
    mixedMoment B raw24905 raw24905Labels = mixedMoment B raw24905step0 raw24905step0Labels := by
      have hz : ∀ j, raw24905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24905step0 = (fun i j => raw24905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24905step0 raw24905; decide +kernel
      have hl : raw24905step0Labels = raw24905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24905 raw24905Labels permutation346 hz
    mixedMoment B raw24905step0 raw24905step0Labels = mixedMoment B raw24905step1 raw24905step1Labels := by
      have ha : raw24905step1 = (fun i j => raw24905step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24905step1 raw24905step0; decide +kernel
      have hl : raw24905step1Labels = raw24905step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24905step0 raw24905step0Labels permutation32 permutation4
    mixedMoment B raw24905step1 raw24905step1Labels = mixedMoment B raw24905step2 raw24905step2Labels := by
      have ha : raw24905step2 = -raw24905step1 := by apply Matrix.ext; change ∀ i j, raw24905step2 i j = -(raw24905step1 i j); unfold raw24905step2 raw24905step1; decide +kernel
      have hl : raw24905step2Labels = raw24905step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1622 node1622Labels := by rfl

def raw24906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw24906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24906 raw24906Labels = mixedMoment B node1583 node1583Labels := by
  calc
    mixedMoment B raw24906 raw24906Labels = mixedMoment B raw24906step0 raw24906step0Labels := by
      have ha : raw24906step0 = (fun i j => raw24906 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24906step0 raw24906; decide +kernel
      have hl : raw24906step0Labels = raw24906Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24906 raw24906Labels permutation154 permutation4
    mixedMoment B raw24906step0 raw24906step0Labels = mixedMoment B raw24906step1 raw24906step1Labels := by
      have ha : raw24906step1 = -raw24906step0 := by apply Matrix.ext; change ∀ i j, raw24906step1 i j = -(raw24906step0 i j); unfold raw24906step1 raw24906step0; decide +kernel
      have hl : raw24906step1Labels = raw24906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1583 node1583Labels := by rfl

def raw24907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw24907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw24907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24907 raw24907Labels = mixedMoment B node1583 node1583Labels := by
  calc
    mixedMoment B raw24907 raw24907Labels = mixedMoment B raw24907step0 raw24907step0Labels := by
      have ha : raw24907step0 = (fun i j => raw24907 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24907step0 raw24907; decide +kernel
      have hl : raw24907step0Labels = raw24907Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24907 raw24907Labels permutation152 permutation4
    mixedMoment B raw24907step0 raw24907step0Labels = mixedMoment B raw24907step1 raw24907step1Labels := by
      have ha : raw24907step1 = -raw24907step0 := by apply Matrix.ext; change ∀ i j, raw24907step1 i j = -(raw24907step0 i j); unfold raw24907step1 raw24907step0; decide +kernel
      have hl : raw24907step1Labels = raw24907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1583 node1583Labels := by rfl

def raw24908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw24908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw24908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24908 raw24908Labels = mixedMoment B node1582 node1582Labels := by
  calc
    mixedMoment B raw24908 raw24908Labels = mixedMoment B raw24908step0 raw24908step0Labels := by
      have ha : raw24908step0 = (fun i j => raw24908 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24908step0 raw24908; decide +kernel
      have hl : raw24908step0Labels = raw24908Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24908 raw24908Labels permutation152 permutation4
    mixedMoment B raw24908step0 raw24908step0Labels = mixedMoment B raw24908step1 raw24908step1Labels := by
      have ha : raw24908step1 = -raw24908step0 := by apply Matrix.ext; change ∀ i j, raw24908step1 i j = -(raw24908step0 i j); unfold raw24908step1 raw24908step0; decide +kernel
      have hl : raw24908step1Labels = raw24908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1582 node1582Labels := by rfl

def raw24909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24909 raw24909Labels = mixedMoment B node1197 node1197Labels := by
  calc
    mixedMoment B raw24909 raw24909Labels = mixedMoment B raw24909step0 raw24909step0Labels := by
      have ha : raw24909step0 = (fun i j => raw24909 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24909step0 raw24909; decide +kernel
      have hl : raw24909step0Labels = raw24909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24909 raw24909Labels permutation154 permutation2
    _ = mixedMoment B node1197 node1197Labels := by rfl

def raw24910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24910 raw24910Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw24910 raw24910Labels = mixedMoment B raw24910step0 raw24910step0Labels := by
      have ha : raw24910step0 = (fun i j => raw24910 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24910step0 raw24910; decide +kernel
      have hl : raw24910step0Labels = raw24910Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24910 raw24910Labels permutation154 permutation2
    _ = mixedMoment B node2458 node2458Labels := by rfl

def raw24911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24911 raw24911Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw24911 raw24911Labels = mixedMoment B raw24911step0 raw24911step0Labels := by
      have ha : raw24911step0 = (fun i j => raw24911 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24911step0 raw24911; decide +kernel
      have hl : raw24911step0Labels = raw24911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24911 raw24911Labels permutation178 permutation2
    _ = mixedMoment B node2458 node2458Labels := by rfl

def raw24912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24912 raw24912Labels = mixedMoment B node2693 node2693Labels := by
  calc
    _ = mixedMoment B node2693 node2693Labels := by rfl

def raw24913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 1, -3]]
def raw24913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24913 raw24913Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw24913 raw24913Labels = mixedMoment B raw24913step0 raw24913step0Labels := by
      have hz : ∀ j, raw24913 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24913step0 = (fun i j => raw24913 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24913step0 raw24913; decide +kernel
      have hl : raw24913step0Labels = raw24913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24913 raw24913Labels permutation520 hz
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw24914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw24914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24914 raw24914Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw24914 raw24914Labels = mixedMoment B raw24914step0 raw24914step0Labels := by
      have ha : raw24914step0 = (fun i j => raw24914 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24914step0 raw24914; decide +kernel
      have hl : raw24914step0Labels = raw24914Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24914 raw24914Labels permutation154 permutation2
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw24915 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![3, -3]]
def raw24915Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24915step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw24915step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24915step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24915step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24915step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24915step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24915 raw24915Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24915 raw24915Labels = mixedMoment B raw24915step0 raw24915step0Labels := by
      have hz : ∀ j, raw24915 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24915step0 = (fun i j => raw24915 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24915step0 raw24915; decide +kernel
      have hl : raw24915step0Labels = raw24915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24915 raw24915Labels permutation520 hz
    mixedMoment B raw24915step0 raw24915step0Labels = mixedMoment B raw24915step1 raw24915step1Labels := by
      have ha : raw24915step1 = (fun i j => raw24915step0 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24915step1 raw24915step0; decide +kernel
      have hl : raw24915step1Labels = raw24915step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24915step0 raw24915step0Labels permutation149 permutation0
    mixedMoment B raw24915step1 raw24915step1Labels = mixedMoment B raw24915step2 raw24915step2Labels := by
      have ha : raw24915step2 = -raw24915step1 := by apply Matrix.ext; change ∀ i j, raw24915step2 i j = -(raw24915step1 i j); unfold raw24915step2 raw24915step1; decide +kernel
      have hl : raw24915step2Labels = raw24915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw24916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24916 raw24916Labels = mixedMoment B node1060 node1060Labels := by
  calc
    mixedMoment B raw24916 raw24916Labels = mixedMoment B raw24916step0 raw24916step0Labels := by
      have hz : ∀ j, raw24916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24916step0 = (fun i j => raw24916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24916step0 raw24916; decide +kernel
      have hl : raw24916step0Labels = raw24916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24916 raw24916Labels permutation346 hz
    _ = mixedMoment B node1060 node1060Labels := by rfl

def raw24917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24917 raw24917Labels = mixedMoment B node2135 node2135Labels := by
  calc
    mixedMoment B raw24917 raw24917Labels = mixedMoment B raw24917step0 raw24917step0Labels := by
      have hz : ∀ j, raw24917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24917step0 = (fun i j => raw24917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24917step0 raw24917; decide +kernel
      have hl : raw24917step0Labels = raw24917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24917 raw24917Labels permutation346 hz
    _ = mixedMoment B node2135 node2135Labels := by rfl

def raw24918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24918 raw24918Labels = mixedMoment B node2036 node2036Labels := by
  calc
    mixedMoment B raw24918 raw24918Labels = mixedMoment B raw24918step0 raw24918step0Labels := by
      have ha : raw24918step0 = (fun i j => raw24918 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24918step0 raw24918; decide +kernel
      have hl : raw24918step0Labels = raw24918Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24918 raw24918Labels permutation176 permutation2
    _ = mixedMoment B node2036 node2036Labels := by rfl

def raw24919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24919 raw24919Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw24919 raw24919Labels = mixedMoment B raw24919step0 raw24919step0Labels := by
      have hz : ∀ j, raw24919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24919step0 = (fun i j => raw24919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24919step0 raw24919; decide +kernel
      have hl : raw24919step0Labels = raw24919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24919 raw24919Labels permutation346 hz
    mixedMoment B raw24919step0 raw24919step0Labels = mixedMoment B raw24919step1 raw24919step1Labels := by
      have ha : raw24919step1 = (fun i j => raw24919step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24919step1 raw24919step0; decide +kernel
      have hl : raw24919step1Labels = raw24919step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24919step0 raw24919step0Labels permutation38 permutation2
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw24920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw24920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw24920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24920 raw24920Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw24920 raw24920Labels = mixedMoment B raw24920step0 raw24920step0Labels := by
      have hz : ∀ j, raw24920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24920step0 = (fun i j => raw24920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24920step0 raw24920; decide +kernel
      have hl : raw24920step0Labels = raw24920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24920 raw24920Labels permutation346 hz
    mixedMoment B raw24920step0 raw24920step0Labels = mixedMoment B raw24920step1 raw24920step1Labels := by
      have ha : raw24920step1 = (fun i j => raw24920step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24920step1 raw24920step0; decide +kernel
      have hl : raw24920step1Labels = raw24920step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24920step0 raw24920step0Labels permutation44 permutation2
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw24921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24921 raw24921Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw24921 raw24921Labels = mixedMoment B raw24921step0 raw24921step0Labels := by
      have hz : ∀ j, raw24921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24921step0 = (fun i j => raw24921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24921step0 raw24921; decide +kernel
      have hl : raw24921step0Labels = raw24921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24921 raw24921Labels permutation346 hz
    mixedMoment B raw24921step0 raw24921step0Labels = mixedMoment B raw24921step1 raw24921step1Labels := by
      have ha : raw24921step1 = (fun i j => raw24921step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24921step1 raw24921step0; decide +kernel
      have hl : raw24921step1Labels = raw24921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24921step0 raw24921step0Labels permutation36 permutation2
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw24922 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]
def raw24922Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24922step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw24922step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24922step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24922step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24922 raw24922Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24922 raw24922Labels = mixedMoment B raw24922step0 raw24922step0Labels := by
      have hz : ∀ j, raw24922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24922step0 = (fun i j => raw24922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24922step0 raw24922; decide +kernel
      have hl : raw24922step0Labels = raw24922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24922 raw24922Labels permutation346 hz
    mixedMoment B raw24922step0 raw24922step0Labels = mixedMoment B raw24922step1 raw24922step1Labels := by
      have ha : raw24922step1 = (fun i j => raw24922step0 (permutation53 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24922step1 raw24922step0; decide +kernel
      have hl : raw24922step1Labels = raw24922step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24922step0 raw24922step0Labels permutation53 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw24923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24923 raw24923Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw24923 raw24923Labels = mixedMoment B raw24923step0 raw24923step0Labels := by
      have hz : ∀ j, raw24923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24923step0 = (fun i j => raw24923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24923step0 raw24923; decide +kernel
      have hl : raw24923step0Labels = raw24923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24923 raw24923Labels permutation346 hz
    mixedMoment B raw24923step0 raw24923step0Labels = mixedMoment B raw24923step1 raw24923step1Labels := by
      have ha : raw24923step1 = (fun i j => raw24923step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24923step1 raw24923step0; decide +kernel
      have hl : raw24923step1Labels = raw24923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24923step0 raw24923step0Labels permutation53 permutation2
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw24924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24924 raw24924Labels = mixedMoment B node1052 node1052Labels := by
  calc
    mixedMoment B raw24924 raw24924Labels = mixedMoment B raw24924step0 raw24924step0Labels := by
      have ha : raw24924step0 = (fun i j => raw24924 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24924step0 raw24924; decide +kernel
      have hl : raw24924step0Labels = raw24924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24924 raw24924Labels permutation170 permutation2
    _ = mixedMoment B node1052 node1052Labels := by rfl

def raw24925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24925 raw24925Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw24925 raw24925Labels = mixedMoment B raw24925step0 raw24925step0Labels := by
      have hz : ∀ j, raw24925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24925step0 = (fun i j => raw24925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24925step0 raw24925; decide +kernel
      have hl : raw24925step0Labels = raw24925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24925 raw24925Labels permutation346 hz
    mixedMoment B raw24925step0 raw24925step0Labels = mixedMoment B raw24925step1 raw24925step1Labels := by
      have ha : raw24925step1 = (fun i j => raw24925step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24925step1 raw24925step0; decide +kernel
      have hl : raw24925step1Labels = raw24925step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24925step0 raw24925step0Labels permutation37 permutation2
    _ = mixedMoment B node1054 node1054Labels := by rfl

def raw24926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw24926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw24926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24926 raw24926Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw24926 raw24926Labels = mixedMoment B raw24926step0 raw24926step0Labels := by
      have hz : ∀ j, raw24926 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24926step0 = (fun i j => raw24926 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24926step0 raw24926; decide +kernel
      have hl : raw24926step0Labels = raw24926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24926 raw24926Labels permutation346 hz
    mixedMoment B raw24926step0 raw24926step0Labels = mixedMoment B raw24926step1 raw24926step1Labels := by
      have ha : raw24926step1 = (fun i j => raw24926step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24926step1 raw24926step0; decide +kernel
      have hl : raw24926step1Labels = raw24926step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24926step0 raw24926step0Labels permutation36 permutation2
    _ = mixedMoment B node1054 node1054Labels := by rfl

def raw24927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24927 raw24927Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw24927 raw24927Labels = mixedMoment B raw24927step0 raw24927step0Labels := by
      have hz : ∀ j, raw24927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24927step0 = (fun i j => raw24927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24927step0 raw24927; decide +kernel
      have hl : raw24927step0Labels = raw24927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24927 raw24927Labels permutation346 hz
    mixedMoment B raw24927step0 raw24927step0Labels = mixedMoment B raw24927step1 raw24927step1Labels := by
      have ha : raw24927step1 = (fun i j => raw24927step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24927step1 raw24927step0; decide +kernel
      have hl : raw24927step1Labels = raw24927step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24927step0 raw24927step0Labels permutation34 permutation2
    _ = mixedMoment B node1054 node1054Labels := by rfl

def raw24928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24928 raw24928Labels = mixedMoment B node2129 node2129Labels := by
  calc
    mixedMoment B raw24928 raw24928Labels = mixedMoment B raw24928step0 raw24928step0Labels := by
      have hz : ∀ j, raw24928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24928step0 = (fun i j => raw24928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24928step0 raw24928; decide +kernel
      have hl : raw24928step0Labels = raw24928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24928 raw24928Labels permutation346 hz
    mixedMoment B raw24928step0 raw24928step0Labels = mixedMoment B raw24928step1 raw24928step1Labels := by
      have ha : raw24928step1 = (fun i j => raw24928step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24928step1 raw24928step0; decide +kernel
      have hl : raw24928step1Labels = raw24928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24928step0 raw24928step0Labels permutation34 permutation2
    _ = mixedMoment B node2129 node2129Labels := by rfl

def raw24929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24929 raw24929Labels = mixedMoment B node2031 node2031Labels := by
  calc
    mixedMoment B raw24929 raw24929Labels = mixedMoment B raw24929step0 raw24929step0Labels := by
      have ha : raw24929step0 = (fun i j => raw24929 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24929step0 raw24929; decide +kernel
      have hl : raw24929step0Labels = raw24929Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24929 raw24929Labels permutation178 permutation2
    _ = mixedMoment B node2031 node2031Labels := by rfl

def raw24930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24930 raw24930Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw24930 raw24930Labels = mixedMoment B raw24930step0 raw24930step0Labels := by
      have hz : ∀ j, raw24930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24930step0 = (fun i j => raw24930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24930step0 raw24930; decide +kernel
      have hl : raw24930step0Labels = raw24930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24930 raw24930Labels permutation346 hz
    mixedMoment B raw24930step0 raw24930step0Labels = mixedMoment B raw24930step1 raw24930step1Labels := by
      have ha : raw24930step1 = (fun i j => raw24930step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24930step1 raw24930step0; decide +kernel
      have hl : raw24930step1Labels = raw24930step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24930step0 raw24930step0Labels permutation38 permutation2
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw24931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw24931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw24931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24931 raw24931Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw24931 raw24931Labels = mixedMoment B raw24931step0 raw24931step0Labels := by
      have hz : ∀ j, raw24931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24931step0 = (fun i j => raw24931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24931step0 raw24931; decide +kernel
      have hl : raw24931step0Labels = raw24931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24931 raw24931Labels permutation346 hz
    mixedMoment B raw24931step0 raw24931step0Labels = mixedMoment B raw24931step1 raw24931step1Labels := by
      have ha : raw24931step1 = (fun i j => raw24931step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24931step1 raw24931step0; decide +kernel
      have hl : raw24931step1Labels = raw24931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24931step0 raw24931step0Labels permutation44 permutation2
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw24932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw24932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw24932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24932 raw24932Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw24932 raw24932Labels = mixedMoment B raw24932step0 raw24932step0Labels := by
      have hz : ∀ j, raw24932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24932step0 = (fun i j => raw24932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24932step0 raw24932; decide +kernel
      have hl : raw24932step0Labels = raw24932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24932 raw24932Labels permutation346 hz
    mixedMoment B raw24932step0 raw24932step0Labels = mixedMoment B raw24932step1 raw24932step1Labels := by
      have ha : raw24932step1 = (fun i j => raw24932step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24932step1 raw24932step0; decide +kernel
      have hl : raw24932step1Labels = raw24932step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24932step0 raw24932step0Labels permutation34 permutation2
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw24933 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1], ![-1, 1], ![1, -1]]
def raw24933Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24933step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![-1, 1], ![1, -1]]
def raw24933step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24933step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24933step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24933 raw24933Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24933 raw24933Labels = mixedMoment B raw24933step0 raw24933step0Labels := by
      have hz : ∀ j, raw24933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24933step0 = (fun i j => raw24933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24933step0 raw24933; decide +kernel
      have hl : raw24933step0Labels = raw24933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24933 raw24933Labels permutation346 hz
    mixedMoment B raw24933step0 raw24933step0Labels = mixedMoment B raw24933step1 raw24933step1Labels := by
      have ha : raw24933step1 = (fun i j => raw24933step0 (permutation47 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24933step1 raw24933step0; decide +kernel
      have hl : raw24933step1Labels = raw24933step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24933step0 raw24933step0Labels permutation47 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw24934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24934 raw24934Labels = mixedMoment B node2128 node2128Labels := by
  calc
    mixedMoment B raw24934 raw24934Labels = mixedMoment B raw24934step0 raw24934step0Labels := by
      have hz : ∀ j, raw24934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24934step0 = (fun i j => raw24934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24934step0 raw24934; decide +kernel
      have hl : raw24934step0Labels = raw24934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24934 raw24934Labels permutation346 hz
    mixedMoment B raw24934step0 raw24934step0Labels = mixedMoment B raw24934step1 raw24934step1Labels := by
      have ha : raw24934step1 = (fun i j => raw24934step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24934step1 raw24934step0; decide +kernel
      have hl : raw24934step1Labels = raw24934step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24934step0 raw24934step0Labels permutation34 permutation2
    _ = mixedMoment B node2128 node2128Labels := by rfl

def raw24935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24935 raw24935Labels = mixedMoment B node2030 node2030Labels := by
  calc
    mixedMoment B raw24935 raw24935Labels = mixedMoment B raw24935step0 raw24935step0Labels := by
      have ha : raw24935step0 = (fun i j => raw24935 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24935step0 raw24935; decide +kernel
      have hl : raw24935step0Labels = raw24935Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24935 raw24935Labels permutation178 permutation2
    _ = mixedMoment B node2030 node2030Labels := by rfl

def raw24936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw24936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw24936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24936 raw24936Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw24936 raw24936Labels = mixedMoment B raw24936step0 raw24936step0Labels := by
      have hz : ∀ j, raw24936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24936step0 = (fun i j => raw24936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24936step0 raw24936; decide +kernel
      have hl : raw24936step0Labels = raw24936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24936 raw24936Labels permutation346 hz
    mixedMoment B raw24936step0 raw24936step0Labels = mixedMoment B raw24936step1 raw24936step1Labels := by
      have ha : raw24936step1 = (fun i j => raw24936step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24936step1 raw24936step0; decide +kernel
      have hl : raw24936step1Labels = raw24936step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24936step0 raw24936step0Labels permutation44 permutation2
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw24937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw24937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24937 raw24937Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw24937 raw24937Labels = mixedMoment B raw24937step0 raw24937step0Labels := by
      have hz : ∀ j, raw24937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24937step0 = (fun i j => raw24937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24937step0 raw24937; decide +kernel
      have hl : raw24937step0Labels = raw24937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24937 raw24937Labels permutation346 hz
    mixedMoment B raw24937step0 raw24937step0Labels = mixedMoment B raw24937step1 raw24937step1Labels := by
      have ha : raw24937step1 = (fun i j => raw24937step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24937step1 raw24937step0; decide +kernel
      have hl : raw24937step1Labels = raw24937step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24937step0 raw24937step0Labels permutation34 permutation2
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw24938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24938 raw24938Labels = mixedMoment B node990 node990Labels := by
  calc
    mixedMoment B raw24938 raw24938Labels = mixedMoment B raw24938step0 raw24938step0Labels := by
      have ha : raw24938step0 = (fun i j => raw24938 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24938step0 raw24938; decide +kernel
      have hl : raw24938step0Labels = raw24938Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24938 raw24938Labels permutation176 permutation2
    _ = mixedMoment B node990 node990Labels := by rfl

def raw24939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24939 raw24939Labels = mixedMoment B node2120 node2120Labels := by
  calc
    _ = mixedMoment B node2120 node2120Labels := by rfl

def raw24940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24940 raw24940Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw24940 raw24940Labels = mixedMoment B raw24940step0 raw24940step0Labels := by
      have ha : raw24940step0 = (fun i j => raw24940 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24940step0 raw24940; decide +kernel
      have hl : raw24940step0Labels = raw24940Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24940 raw24940Labels permutation176 permutation2
    _ = mixedMoment B node1925 node1925Labels := by rfl

def raw24941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw24941step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24941 raw24941Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw24941 raw24941Labels = mixedMoment B raw24941step0 raw24941step0Labels := by
      have ha : raw24941step0 = (fun i j => raw24941 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24941step0 raw24941; decide +kernel
      have hl : raw24941step0Labels = raw24941Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24941 raw24941Labels permutation182 permutation2
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw24942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw24942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24942 raw24942Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw24942 raw24942Labels = mixedMoment B raw24942step0 raw24942step0Labels := by
      have ha : raw24942step0 = (fun i j => raw24942 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24942step0 raw24942; decide +kernel
      have hl : raw24942step0Labels = raw24942Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24942 raw24942Labels permutation188 permutation2
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw24943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24943 raw24943Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw24943 raw24943Labels = mixedMoment B raw24943step0 raw24943step0Labels := by
      have ha : raw24943step0 = (fun i j => raw24943 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24943step0 raw24943; decide +kernel
      have hl : raw24943step0Labels = raw24943Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24943 raw24943Labels permutation180 permutation2
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw24944 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]
def raw24944Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24944step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw24944step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24944step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24944step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24944 raw24944Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24944 raw24944Labels = mixedMoment B raw24944step0 raw24944step0Labels := by
      have hz : ∀ j, raw24944 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw24944step0 = (fun i j => raw24944 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw24944step0 raw24944; decide +kernel
      have hl : raw24944step0Labels = raw24944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24944 raw24944Labels permutation590 hz
    mixedMoment B raw24944step0 raw24944step0Labels = mixedMoment B raw24944step1 raw24944step1Labels := by
      have ha : raw24944step1 = (fun i j => raw24944step0 (permutation41 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24944step1 raw24944step0; decide +kernel
      have hl : raw24944step1Labels = raw24944step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24944step0 raw24944step0Labels permutation41 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw24945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24945 raw24945Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw24945 raw24945Labels = mixedMoment B raw24945step0 raw24945step0Labels := by
      have ha : raw24945step0 = (fun i j => raw24945 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24945step0 raw24945; decide +kernel
      have hl : raw24945step0Labels = raw24945Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24945 raw24945Labels permutation197 permutation2
    _ = mixedMoment B node998 node998Labels := by rfl

def raw24946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24946 raw24946Labels = mixedMoment B node1052 node1052Labels := by
  calc
    mixedMoment B raw24946 raw24946Labels = mixedMoment B raw24946step0 raw24946step0Labels := by
      have ha : raw24946step0 = (fun i j => raw24946 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24946step0 raw24946; decide +kernel
      have hl : raw24946step0Labels = raw24946Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24946 raw24946Labels permutation156 permutation2
    _ = mixedMoment B node1052 node1052Labels := by rfl

def raw24947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24947 raw24947Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw24947 raw24947Labels = mixedMoment B raw24947step0 raw24947step0Labels := by
      have ha : raw24947step0 = (fun i j => raw24947 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24947step0 raw24947; decide +kernel
      have hl : raw24947step0Labels = raw24947Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24947 raw24947Labels permutation181 permutation2
    _ = mixedMoment B node988 node988Labels := by rfl

def raw24948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw24948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24948 raw24948Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw24948 raw24948Labels = mixedMoment B raw24948step0 raw24948step0Labels := by
      have ha : raw24948step0 = (fun i j => raw24948 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24948step0 raw24948; decide +kernel
      have hl : raw24948step0Labels = raw24948Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24948 raw24948Labels permutation180 permutation2
    _ = mixedMoment B node988 node988Labels := by rfl

def raw24949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24949 raw24949Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw24949 raw24949Labels = mixedMoment B raw24949step0 raw24949step0Labels := by
      have ha : raw24949step0 = (fun i j => raw24949 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24949step0 raw24949; decide +kernel
      have hl : raw24949step0Labels = raw24949Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24949 raw24949Labels permutation178 permutation2
    _ = mixedMoment B node988 node988Labels := by rfl

def raw24950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24950 raw24950Labels = mixedMoment B node2118 node2118Labels := by
  calc
    mixedMoment B raw24950 raw24950Labels = mixedMoment B raw24950step0 raw24950step0Labels := by
      have ha : raw24950step0 = (fun i j => raw24950 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24950step0 raw24950; decide +kernel
      have hl : raw24950step0Labels = raw24950Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24950 raw24950Labels permutation154 permutation2
    _ = mixedMoment B node2118 node2118Labels := by rfl

def raw24951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24951 raw24951Labels = mixedMoment B node1922 node1922Labels := by
  calc
    mixedMoment B raw24951 raw24951Labels = mixedMoment B raw24951step0 raw24951step0Labels := by
      have ha : raw24951step0 = (fun i j => raw24951 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24951step0 raw24951; decide +kernel
      have hl : raw24951step0Labels = raw24951Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24951 raw24951Labels permutation178 permutation2
    _ = mixedMoment B node1922 node1922Labels := by rfl

def raw24952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw24952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24952 raw24952Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw24952 raw24952Labels = mixedMoment B raw24952step0 raw24952step0Labels := by
      have ha : raw24952step0 = (fun i j => raw24952 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24952step0 raw24952; decide +kernel
      have hl : raw24952step0Labels = raw24952Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24952 raw24952Labels permutation182 permutation2
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw24953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw24953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24953 raw24953Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw24953 raw24953Labels = mixedMoment B raw24953step0 raw24953step0Labels := by
      have hz : ∀ j, raw24953 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24953step0 = (fun i j => raw24953 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24953step0 raw24953; decide +kernel
      have hl : raw24953step0Labels = raw24953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24953 raw24953Labels permutation520 hz
    mixedMoment B raw24953step0 raw24953step0Labels = mixedMoment B raw24953step1 raw24953step1Labels := by
      have ha : raw24953step1 = (fun i j => raw24953step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24953step1 raw24953step0; decide +kernel
      have hl : raw24953step1Labels = raw24953step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24953step0 raw24953step0Labels permutation38 permutation2
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw24954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw24954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24954 raw24954Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw24954 raw24954Labels = mixedMoment B raw24954step0 raw24954step0Labels := by
      have ha : raw24954step0 = (fun i j => raw24954 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24954step0 raw24954; decide +kernel
      have hl : raw24954step0Labels = raw24954Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24954 raw24954Labels permutation178 permutation2
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw24955 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]
def raw24955Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24955step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw24955step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24955step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24955step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24955 raw24955Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24955 raw24955Labels = mixedMoment B raw24955step0 raw24955step0Labels := by
      have hz : ∀ j, raw24955 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24955step0 = (fun i j => raw24955 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24955step0 raw24955; decide +kernel
      have hl : raw24955step0Labels = raw24955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24955 raw24955Labels permutation520 hz
    mixedMoment B raw24955step0 raw24955step0Labels = mixedMoment B raw24955step1 raw24955step1Labels := by
      have ha : raw24955step1 = (fun i j => raw24955step0 (permutation41 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24955step1 raw24955step0; decide +kernel
      have hl : raw24955step1Labels = raw24955step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24955step0 raw24955step0Labels permutation41 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw24956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24956 raw24956Labels = mixedMoment B node987 node987Labels := by
  calc
    mixedMoment B raw24956 raw24956Labels = mixedMoment B raw24956step0 raw24956step0Labels := by
      have ha : raw24956step0 = (fun i j => raw24956 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24956step0 raw24956; decide +kernel
      have hl : raw24956step0Labels = raw24956Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24956 raw24956Labels permutation176 permutation2
    _ = mixedMoment B node987 node987Labels := by rfl

def raw24957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24957 raw24957Labels = mixedMoment B node2117 node2117Labels := by
  calc
    _ = mixedMoment B node2117 node2117Labels := by rfl

def raw24958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24958 raw24958Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw24958 raw24958Labels = mixedMoment B raw24958step0 raw24958step0Labels := by
      have ha : raw24958step0 = (fun i j => raw24958 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24958step0 raw24958; decide +kernel
      have hl : raw24958step0Labels = raw24958Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24958 raw24958Labels permutation176 permutation2
    _ = mixedMoment B node1921 node1921Labels := by rfl

def raw24959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24959 raw24959Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw24959 raw24959Labels = mixedMoment B raw24959step0 raw24959step0Labels := by
      have hz : ∀ j, raw24959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24959step0 = (fun i j => raw24959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24959step0 raw24959; decide +kernel
      have hl : raw24959step0Labels = raw24959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24959 raw24959Labels permutation434 hz
    mixedMoment B raw24959step0 raw24959step0Labels = mixedMoment B raw24959step1 raw24959step1Labels := by
      have ha : raw24959step1 = (fun i j => raw24959step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24959step1 raw24959step0; decide +kernel
      have hl : raw24959step1Labels = raw24959step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24959step0 raw24959step0Labels permutation38 permutation2
    _ = mixedMoment B node2215 node2215Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
