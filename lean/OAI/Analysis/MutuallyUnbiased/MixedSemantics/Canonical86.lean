import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11008 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11008step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11008step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11008step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11008step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11008 raw11008Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw11008 raw11008Labels = mixedMoment B raw11008step0 raw11008step0Labels := by
      have hz : ∀ j, raw11008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11008step0 = (fun i j => raw11008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11008step0 raw11008; decide +kernel
      have hl : raw11008step0Labels = raw11008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11008 raw11008Labels permutation346 hz
    mixedMoment B raw11008step0 raw11008step0Labels = mixedMoment B raw11008step1 raw11008step1Labels := by
      have ha : raw11008step1 = (fun i j => raw11008step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11008step1 raw11008step0; decide +kernel
      have hl : raw11008step1Labels = raw11008step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11008step0 raw11008step0Labels permutation49 permutation5
    mixedMoment B raw11008step1 raw11008step1Labels = mixedMoment B raw11008step2 raw11008step2Labels := by
      have ha : raw11008step2 = -raw11008step1 := by apply Matrix.ext; change ∀ i j, raw11008step2 i j = -(raw11008step1 i j); unfold raw11008step2 raw11008step1; decide +kernel
      have hl : raw11008step2Labels = raw11008step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11008step2 raw11008step2Labels = mixedMoment B raw11008step3 raw11008step3Labels := by
      have ha : raw11008step3 = raw11008step2 := by apply Matrix.ext; unfold raw11008step3 raw11008step2; decide +kernel
      have hl : raw11008step2Labels = labelEmbedding1 ∘ raw11008step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11008step2 raw11008step2Labels raw11008step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw11009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11009step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11009step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11009step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11009step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11009step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11009 raw11009Labels = mixedMoment B node1442 node1442Labels := by
  calc
    mixedMoment B raw11009 raw11009Labels = mixedMoment B raw11009step0 raw11009step0Labels := by
      have hz : ∀ j, raw11009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11009step0 = (fun i j => raw11009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11009step0 raw11009; decide +kernel
      have hl : raw11009step0Labels = raw11009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11009 raw11009Labels permutation434 hz
    mixedMoment B raw11009step0 raw11009step0Labels = mixedMoment B raw11009step1 raw11009step1Labels := by
      have hz : ∀ j, raw11009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11009step1 = (fun i j => raw11009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11009step1 raw11009step0; decide +kernel
      have hl : raw11009step1Labels = raw11009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11009step0 raw11009step0Labels permutation80 hz
    mixedMoment B raw11009step1 raw11009step1Labels = mixedMoment B raw11009step2 raw11009step2Labels := by
      have ha : raw11009step2 = (fun i j => raw11009step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11009step2 raw11009step1; decide +kernel
      have hl : raw11009step2Labels = raw11009step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11009step1 raw11009step1Labels permutation13 permutation5
    mixedMoment B raw11009step2 raw11009step2Labels = mixedMoment B raw11009step3 raw11009step3Labels := by
      have ha : raw11009step3 = -raw11009step2 := by apply Matrix.ext; change ∀ i j, raw11009step3 i j = -(raw11009step2 i j); unfold raw11009step3 raw11009step2; decide +kernel
      have hl : raw11009step3Labels = raw11009step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11009step3 raw11009step3Labels = mixedMoment B raw11009step4 raw11009step4Labels := by
      have ha : raw11009step4 = raw11009step3 := by apply Matrix.ext; unfold raw11009step4 raw11009step3; decide +kernel
      have hl : raw11009step3Labels = labelEmbedding1 ∘ raw11009step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11009step3 raw11009step3Labels raw11009step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1442 node1442Labels := by rfl

def raw11010 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11010 raw11010Labels = mixedMoment B node3210 node3210Labels := by
  calc
    mixedMoment B raw11010 raw11010Labels = mixedMoment B raw11010step0 raw11010step0Labels := by
      have hz : ∀ j, raw11010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11010step0 = (fun i j => raw11010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11010step0 raw11010; decide +kernel
      have hl : raw11010step0Labels = raw11010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11010 raw11010Labels permutation434 hz
    mixedMoment B raw11010step0 raw11010step0Labels = mixedMoment B raw11010step1 raw11010step1Labels := by
      have ha : raw11010step1 = (fun i j => raw11010step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11010step1 raw11010step0; decide +kernel
      have hl : raw11010step1Labels = raw11010step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11010step0 raw11010step0Labels permutation43 permutation5
    mixedMoment B raw11010step1 raw11010step1Labels = mixedMoment B raw11010step2 raw11010step2Labels := by
      have ha : raw11010step2 = -raw11010step1 := by apply Matrix.ext; change ∀ i j, raw11010step2 i j = -(raw11010step1 i j); unfold raw11010step2 raw11010step1; decide +kernel
      have hl : raw11010step2Labels = raw11010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11010step2 raw11010step2Labels = mixedMoment B raw11010step3 raw11010step3Labels := by
      have ha : raw11010step3 = raw11010step2 := by apply Matrix.ext; unfold raw11010step3 raw11010step2; decide +kernel
      have hl : raw11010step2Labels = labelEmbedding1 ∘ raw11010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11010step2 raw11010step2Labels raw11010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3210 node3210Labels := by rfl

def raw11011 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11011step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw11011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11011step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11011step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11011step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11011 raw11011Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw11011 raw11011Labels = mixedMoment B raw11011step0 raw11011step0Labels := by
      have hz : ∀ j, raw11011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11011step0 = (fun i j => raw11011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11011step0 raw11011; decide +kernel
      have hl : raw11011step0Labels = raw11011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11011 raw11011Labels permutation434 hz
    mixedMoment B raw11011step0 raw11011step0Labels = mixedMoment B raw11011step1 raw11011step1Labels := by
      have hz : ∀ j, raw11011step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11011step1 = (fun i j => raw11011step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11011step1 raw11011step0; decide +kernel
      have hl : raw11011step1Labels = raw11011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11011step0 raw11011step0Labels permutation80 hz
    mixedMoment B raw11011step1 raw11011step1Labels = mixedMoment B raw11011step2 raw11011step2Labels := by
      have ha : raw11011step2 = (fun i j => raw11011step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11011step2 raw11011step1; decide +kernel
      have hl : raw11011step2Labels = raw11011step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11011step1 raw11011step1Labels permutation13 permutation5
    mixedMoment B raw11011step2 raw11011step2Labels = mixedMoment B raw11011step3 raw11011step3Labels := by
      have ha : raw11011step3 = -raw11011step2 := by apply Matrix.ext; change ∀ i j, raw11011step3 i j = -(raw11011step2 i j); unfold raw11011step3 raw11011step2; decide +kernel
      have hl : raw11011step3Labels = raw11011step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11011step3 raw11011step3Labels = mixedMoment B raw11011step4 raw11011step4Labels := by
      have ha : raw11011step4 = raw11011step3 := by apply Matrix.ext; unfold raw11011step4 raw11011step3; decide +kernel
      have hl : raw11011step3Labels = labelEmbedding1 ∘ raw11011step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11011step3 raw11011step3Labels raw11011step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

def raw11012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11012step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11012step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11012step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11012step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11012 raw11012Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw11012 raw11012Labels = mixedMoment B raw11012step0 raw11012step0Labels := by
      have hz : ∀ j, raw11012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11012step0 = (fun i j => raw11012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11012step0 raw11012; decide +kernel
      have hl : raw11012step0Labels = raw11012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11012 raw11012Labels permutation434 hz
    mixedMoment B raw11012step0 raw11012step0Labels = mixedMoment B raw11012step1 raw11012step1Labels := by
      have hz : ∀ j, raw11012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11012step1 = (fun i j => raw11012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11012step1 raw11012step0; decide +kernel
      have hl : raw11012step1Labels = raw11012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11012step0 raw11012step0Labels permutation80 hz
    mixedMoment B raw11012step1 raw11012step1Labels = mixedMoment B raw11012step2 raw11012step2Labels := by
      have ha : raw11012step2 = (fun i j => raw11012step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11012step2 raw11012step1; decide +kernel
      have hl : raw11012step2Labels = raw11012step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11012step1 raw11012step1Labels permutation11 permutation5
    mixedMoment B raw11012step2 raw11012step2Labels = mixedMoment B raw11012step3 raw11012step3Labels := by
      have ha : raw11012step3 = -raw11012step2 := by apply Matrix.ext; change ∀ i j, raw11012step3 i j = -(raw11012step2 i j); unfold raw11012step3 raw11012step2; decide +kernel
      have hl : raw11012step3Labels = raw11012step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11012step3 raw11012step3Labels = mixedMoment B raw11012step4 raw11012step4Labels := by
      have ha : raw11012step4 = raw11012step3 := by apply Matrix.ext; unfold raw11012step4 raw11012step3; decide +kernel
      have hl : raw11012step3Labels = labelEmbedding1 ∘ raw11012step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11012step3 raw11012step3Labels raw11012step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw11013 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11013step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11013step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11013 raw11013Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw11013 raw11013Labels = mixedMoment B raw11013step0 raw11013step0Labels := by
      have hz : ∀ j, raw11013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11013step0 = (fun i j => raw11013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11013step0 raw11013; decide +kernel
      have hl : raw11013step0Labels = raw11013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11013 raw11013Labels permutation434 hz
    mixedMoment B raw11013step0 raw11013step0Labels = mixedMoment B raw11013step1 raw11013step1Labels := by
      have ha : raw11013step1 = (fun i j => raw11013step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11013step1 raw11013step0; decide +kernel
      have hl : raw11013step1Labels = raw11013step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11013step0 raw11013step0Labels permutation41 permutation5
    mixedMoment B raw11013step1 raw11013step1Labels = mixedMoment B raw11013step2 raw11013step2Labels := by
      have ha : raw11013step2 = -raw11013step1 := by apply Matrix.ext; change ∀ i j, raw11013step2 i j = -(raw11013step1 i j); unfold raw11013step2 raw11013step1; decide +kernel
      have hl : raw11013step2Labels = raw11013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11013step2 raw11013step2Labels = mixedMoment B raw11013step3 raw11013step3Labels := by
      have ha : raw11013step3 = raw11013step2 := by apply Matrix.ext; unfold raw11013step3 raw11013step2; decide +kernel
      have hl : raw11013step2Labels = labelEmbedding1 ∘ raw11013step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11013step2 raw11013step2Labels raw11013step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw11014 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11014 raw11014Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw11014 raw11014Labels = mixedMoment B raw11014step0 raw11014step0Labels := by
      have hz : ∀ j, raw11014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11014step0 = (fun i j => raw11014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11014step0 raw11014; decide +kernel
      have hl : raw11014step0Labels = raw11014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11014 raw11014Labels permutation434 hz
    mixedMoment B raw11014step0 raw11014step0Labels = mixedMoment B raw11014step1 raw11014step1Labels := by
      have hz : ∀ j, raw11014step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11014step1 = (fun i j => raw11014step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11014step1 raw11014step0; decide +kernel
      have hl : raw11014step1Labels = raw11014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11014step0 raw11014step0Labels permutation80 hz
    mixedMoment B raw11014step1 raw11014step1Labels = mixedMoment B raw11014step2 raw11014step2Labels := by
      have ha : raw11014step2 = (fun i j => raw11014step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11014step2 raw11014step1; decide +kernel
      have hl : raw11014step2Labels = raw11014step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11014step1 raw11014step1Labels permutation11 permutation4
    mixedMoment B raw11014step2 raw11014step2Labels = mixedMoment B raw11014step3 raw11014step3Labels := by
      have ha : raw11014step3 = -raw11014step2 := by apply Matrix.ext; change ∀ i j, raw11014step3 i j = -(raw11014step2 i j); unfold raw11014step3 raw11014step2; decide +kernel
      have hl : raw11014step3Labels = raw11014step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw11015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw11015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11015 raw11015Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw11015 raw11015Labels = mixedMoment B raw11015step0 raw11015step0Labels := by
      have hz : ∀ j, raw11015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11015step0 = (fun i j => raw11015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11015step0 raw11015; decide +kernel
      have hl : raw11015step0Labels = raw11015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11015 raw11015Labels permutation434 hz
    mixedMoment B raw11015step0 raw11015step0Labels = mixedMoment B raw11015step1 raw11015step1Labels := by
      have hz : ∀ j, raw11015step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11015step1 = (fun i j => raw11015step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11015step1 raw11015step0; decide +kernel
      have hl : raw11015step1Labels = raw11015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11015step0 raw11015step0Labels permutation80 hz
    mixedMoment B raw11015step1 raw11015step1Labels = mixedMoment B raw11015step2 raw11015step2Labels := by
      have ha : raw11015step2 = (fun i j => raw11015step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11015step2 raw11015step1; decide +kernel
      have hl : raw11015step2Labels = raw11015step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11015step1 raw11015step1Labels permutation11 permutation4
    mixedMoment B raw11015step2 raw11015step2Labels = mixedMoment B raw11015step3 raw11015step3Labels := by
      have ha : raw11015step3 = -raw11015step2 := by apply Matrix.ext; change ∀ i j, raw11015step3 i j = -(raw11015step2 i j); unfold raw11015step3 raw11015step2; decide +kernel
      have hl : raw11015step3Labels = raw11015step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw11016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11016 raw11016Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw11016 raw11016Labels = mixedMoment B raw11016step0 raw11016step0Labels := by
      have hz : ∀ j, raw11016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11016step0 = (fun i j => raw11016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11016step0 raw11016; decide +kernel
      have hl : raw11016step0Labels = raw11016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11016 raw11016Labels permutation434 hz
    mixedMoment B raw11016step0 raw11016step0Labels = mixedMoment B raw11016step1 raw11016step1Labels := by
      have ha : raw11016step1 = (fun i j => raw11016step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11016step1 raw11016step0; decide +kernel
      have hl : raw11016step1Labels = raw11016step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11016step0 raw11016step0Labels permutation47 permutation4
    mixedMoment B raw11016step1 raw11016step1Labels = mixedMoment B raw11016step2 raw11016step2Labels := by
      have ha : raw11016step2 = -raw11016step1 := by apply Matrix.ext; change ∀ i j, raw11016step2 i j = -(raw11016step1 i j); unfold raw11016step2 raw11016step1; decide +kernel
      have hl : raw11016step2Labels = raw11016step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw11017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11017 raw11017Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw11017 raw11017Labels = mixedMoment B raw11017step0 raw11017step0Labels := by
      have hz : ∀ j, raw11017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11017step0 = (fun i j => raw11017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11017step0 raw11017; decide +kernel
      have hl : raw11017step0Labels = raw11017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11017 raw11017Labels permutation346 hz
    mixedMoment B raw11017step0 raw11017step0Labels = mixedMoment B raw11017step1 raw11017step1Labels := by
      have ha : raw11017step1 = (fun i j => raw11017step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11017step1 raw11017step0; decide +kernel
      have hl : raw11017step1Labels = raw11017step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11017step0 raw11017step0Labels permutation47 permutation4
    mixedMoment B raw11017step1 raw11017step1Labels = mixedMoment B raw11017step2 raw11017step2Labels := by
      have ha : raw11017step2 = -raw11017step1 := by apply Matrix.ext; change ∀ i j, raw11017step2 i j = -(raw11017step1 i j); unfold raw11017step2 raw11017step1; decide +kernel
      have hl : raw11017step2Labels = raw11017step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw11018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11018step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11018step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11018 raw11018Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw11018 raw11018Labels = mixedMoment B raw11018step0 raw11018step0Labels := by
      have hz : ∀ j, raw11018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11018step0 = (fun i j => raw11018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11018step0 raw11018; decide +kernel
      have hl : raw11018step0Labels = raw11018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11018 raw11018Labels permutation434 hz
    mixedMoment B raw11018step0 raw11018step0Labels = mixedMoment B raw11018step1 raw11018step1Labels := by
      have hz : ∀ j, raw11018step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11018step1 = (fun i j => raw11018step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11018step1 raw11018step0; decide +kernel
      have hl : raw11018step1Labels = raw11018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11018step0 raw11018step0Labels permutation80 hz
    mixedMoment B raw11018step1 raw11018step1Labels = mixedMoment B raw11018step2 raw11018step2Labels := by
      have ha : raw11018step2 = (fun i j => raw11018step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11018step2 raw11018step1; decide +kernel
      have hl : raw11018step2Labels = raw11018step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11018step1 raw11018step1Labels permutation11 permutation4
    mixedMoment B raw11018step2 raw11018step2Labels = mixedMoment B raw11018step3 raw11018step3Labels := by
      have ha : raw11018step3 = -raw11018step2 := by apply Matrix.ext; change ∀ i j, raw11018step3 i j = -(raw11018step2 i j); unfold raw11018step3 raw11018step2; decide +kernel
      have hl : raw11018step3Labels = raw11018step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw11019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11019step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11019 raw11019Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw11019 raw11019Labels = mixedMoment B raw11019step0 raw11019step0Labels := by
      have hz : ∀ j, raw11019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11019step0 = (fun i j => raw11019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11019step0 raw11019; decide +kernel
      have hl : raw11019step0Labels = raw11019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11019 raw11019Labels permutation434 hz
    mixedMoment B raw11019step0 raw11019step0Labels = mixedMoment B raw11019step1 raw11019step1Labels := by
      have hz : ∀ j, raw11019step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11019step1 = (fun i j => raw11019step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11019step1 raw11019step0; decide +kernel
      have hl : raw11019step1Labels = raw11019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11019step0 raw11019step0Labels permutation80 hz
    mixedMoment B raw11019step1 raw11019step1Labels = mixedMoment B raw11019step2 raw11019step2Labels := by
      have ha : raw11019step2 = (fun i j => raw11019step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11019step2 raw11019step1; decide +kernel
      have hl : raw11019step2Labels = raw11019step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11019step1 raw11019step1Labels permutation10 permutation4
    mixedMoment B raw11019step2 raw11019step2Labels = mixedMoment B raw11019step3 raw11019step3Labels := by
      have ha : raw11019step3 = -raw11019step2 := by apply Matrix.ext; change ∀ i j, raw11019step3 i j = -(raw11019step2 i j); unfold raw11019step3 raw11019step2; decide +kernel
      have hl : raw11019step3Labels = raw11019step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw11020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11020step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11020step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11020step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11020step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11020 raw11020Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw11020 raw11020Labels = mixedMoment B raw11020step0 raw11020step0Labels := by
      have hz : ∀ j, raw11020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11020step0 = (fun i j => raw11020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11020step0 raw11020; decide +kernel
      have hl : raw11020step0Labels = raw11020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11020 raw11020Labels permutation434 hz
    mixedMoment B raw11020step0 raw11020step0Labels = mixedMoment B raw11020step1 raw11020step1Labels := by
      have ha : raw11020step1 = (fun i j => raw11020step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11020step1 raw11020step0; decide +kernel
      have hl : raw11020step1Labels = raw11020step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11020step0 raw11020step0Labels permutation50 permutation7
    mixedMoment B raw11020step1 raw11020step1Labels = mixedMoment B raw11020step2 raw11020step2Labels := by
      have ha : raw11020step2 = -raw11020step1 := by apply Matrix.ext; change ∀ i j, raw11020step2 i j = -(raw11020step1 i j); unfold raw11020step2 raw11020step1; decide +kernel
      have hl : raw11020step2Labels = raw11020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11020step2 raw11020step2Labels = mixedMoment B raw11020step3 raw11020step3Labels := by
      have ha : raw11020step3 = raw11020step2 := by apply Matrix.ext; unfold raw11020step3 raw11020step2; decide +kernel
      have hl : raw11020step2Labels = labelEmbedding10 ∘ raw11020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11020step2 raw11020step2Labels raw11020step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw11021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11021step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11021step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11021step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11021 raw11021Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw11021 raw11021Labels = mixedMoment B raw11021step0 raw11021step0Labels := by
      have hz : ∀ j, raw11021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11021step0 = (fun i j => raw11021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11021step0 raw11021; decide +kernel
      have hl : raw11021step0Labels = raw11021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11021 raw11021Labels permutation434 hz
    mixedMoment B raw11021step0 raw11021step0Labels = mixedMoment B raw11021step1 raw11021step1Labels := by
      have ha : raw11021step1 = (fun i j => raw11021step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11021step1 raw11021step0; decide +kernel
      have hl : raw11021step1Labels = raw11021step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11021step0 raw11021step0Labels permutation52 permutation7
    mixedMoment B raw11021step1 raw11021step1Labels = mixedMoment B raw11021step2 raw11021step2Labels := by
      have ha : raw11021step2 = -raw11021step1 := by apply Matrix.ext; change ∀ i j, raw11021step2 i j = -(raw11021step1 i j); unfold raw11021step2 raw11021step1; decide +kernel
      have hl : raw11021step2Labels = raw11021step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11021step2 raw11021step2Labels = mixedMoment B raw11021step3 raw11021step3Labels := by
      have ha : raw11021step3 = raw11021step2 := by apply Matrix.ext; unfold raw11021step3 raw11021step2; decide +kernel
      have hl : raw11021step2Labels = labelEmbedding10 ∘ raw11021step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11021step2 raw11021step2Labels raw11021step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw11022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11022step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11022step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11022step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11022step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11022 raw11022Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw11022 raw11022Labels = mixedMoment B raw11022step0 raw11022step0Labels := by
      have ha : raw11022step0 = (fun i j => raw11022 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11022step0 raw11022; decide +kernel
      have hl : raw11022step0Labels = raw11022Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11022 raw11022Labels permutation218 permutation7
    mixedMoment B raw11022step0 raw11022step0Labels = mixedMoment B raw11022step1 raw11022step1Labels := by
      have ha : raw11022step1 = -raw11022step0 := by apply Matrix.ext; change ∀ i j, raw11022step1 i j = -(raw11022step0 i j); unfold raw11022step1 raw11022step0; decide +kernel
      have hl : raw11022step1Labels = raw11022step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11022step1 raw11022step1Labels = mixedMoment B raw11022step2 raw11022step2Labels := by
      have ha : raw11022step2 = raw11022step1 := by apply Matrix.ext; unfold raw11022step2 raw11022step1; decide +kernel
      have hl : raw11022step1Labels = labelEmbedding10 ∘ raw11022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11022step1 raw11022step1Labels raw11022step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw11023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw11023step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11023step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11023step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11023 raw11023Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw11023 raw11023Labels = mixedMoment B raw11023step0 raw11023step0Labels := by
      have hz : ∀ j, raw11023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11023step0 = (fun i j => raw11023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11023step0 raw11023; decide +kernel
      have hl : raw11023step0Labels = raw11023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11023 raw11023Labels permutation434 hz
    mixedMoment B raw11023step0 raw11023step0Labels = mixedMoment B raw11023step1 raw11023step1Labels := by
      have ha : raw11023step1 = (fun i j => raw11023step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11023step1 raw11023step0; decide +kernel
      have hl : raw11023step1Labels = raw11023step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11023step0 raw11023step0Labels permutation50 permutation7
    mixedMoment B raw11023step1 raw11023step1Labels = mixedMoment B raw11023step2 raw11023step2Labels := by
      have ha : raw11023step2 = -raw11023step1 := by apply Matrix.ext; change ∀ i j, raw11023step2 i j = -(raw11023step1 i j); unfold raw11023step2 raw11023step1; decide +kernel
      have hl : raw11023step2Labels = raw11023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11023step2 raw11023step2Labels = mixedMoment B raw11023step3 raw11023step3Labels := by
      have ha : raw11023step3 = raw11023step2 := by apply Matrix.ext; unfold raw11023step3 raw11023step2; decide +kernel
      have hl : raw11023step2Labels = labelEmbedding10 ∘ raw11023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11023step2 raw11023step2Labels raw11023step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw11024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11024step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11024step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11024step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11024step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11024 raw11024Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw11024 raw11024Labels = mixedMoment B raw11024step0 raw11024step0Labels := by
      have hz : ∀ j, raw11024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11024step0 = (fun i j => raw11024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11024step0 raw11024; decide +kernel
      have hl : raw11024step0Labels = raw11024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11024 raw11024Labels permutation434 hz
    mixedMoment B raw11024step0 raw11024step0Labels = mixedMoment B raw11024step1 raw11024step1Labels := by
      have ha : raw11024step1 = (fun i j => raw11024step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11024step1 raw11024step0; decide +kernel
      have hl : raw11024step1Labels = raw11024step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11024step0 raw11024step0Labels permutation50 permutation7
    mixedMoment B raw11024step1 raw11024step1Labels = mixedMoment B raw11024step2 raw11024step2Labels := by
      have ha : raw11024step2 = -raw11024step1 := by apply Matrix.ext; change ∀ i j, raw11024step2 i j = -(raw11024step1 i j); unfold raw11024step2 raw11024step1; decide +kernel
      have hl : raw11024step2Labels = raw11024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11024step2 raw11024step2Labels = mixedMoment B raw11024step3 raw11024step3Labels := by
      have ha : raw11024step3 = raw11024step2 := by apply Matrix.ext; unfold raw11024step3 raw11024step2; decide +kernel
      have hl : raw11024step2Labels = labelEmbedding10 ∘ raw11024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11024step2 raw11024step2Labels raw11024step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw11025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11025 raw11025Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw11025 raw11025Labels = mixedMoment B raw11025step0 raw11025step0Labels := by
      have hz : ∀ j, raw11025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11025step0 = (fun i j => raw11025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11025step0 raw11025; decide +kernel
      have hl : raw11025step0Labels = raw11025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11025 raw11025Labels permutation434 hz
    mixedMoment B raw11025step0 raw11025step0Labels = mixedMoment B raw11025step1 raw11025step1Labels := by
      have ha : raw11025step1 = (fun i j => raw11025step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11025step1 raw11025step0; decide +kernel
      have hl : raw11025step1Labels = raw11025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11025step0 raw11025step0Labels permutation38 permutation2
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw11026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11026 raw11026Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw11026 raw11026Labels = mixedMoment B raw11026step0 raw11026step0Labels := by
      have hz : ∀ j, raw11026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11026step0 = (fun i j => raw11026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11026step0 raw11026; decide +kernel
      have hl : raw11026step0Labels = raw11026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11026 raw11026Labels permutation434 hz
    mixedMoment B raw11026step0 raw11026step0Labels = mixedMoment B raw11026step1 raw11026step1Labels := by
      have ha : raw11026step1 = (fun i j => raw11026step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11026step1 raw11026step0; decide +kernel
      have hl : raw11026step1Labels = raw11026step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11026step0 raw11026step0Labels permutation38 permutation2
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw11027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11027 raw11027Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw11027 raw11027Labels = mixedMoment B raw11027step0 raw11027step0Labels := by
      have ha : raw11027step0 = (fun i j => raw11027 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11027step0 raw11027; decide +kernel
      have hl : raw11027step0Labels = raw11027Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11027 raw11027Labels permutation206 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw11028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11028step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11028 raw11028Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw11028 raw11028Labels = mixedMoment B raw11028step0 raw11028step0Labels := by
      have hz : ∀ j, raw11028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11028step0 = (fun i j => raw11028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11028step0 raw11028; decide +kernel
      have hl : raw11028step0Labels = raw11028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11028 raw11028Labels permutation434 hz
    mixedMoment B raw11028step0 raw11028step0Labels = mixedMoment B raw11028step1 raw11028step1Labels := by
      have ha : raw11028step1 = (fun i j => raw11028step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11028step1 raw11028step0; decide +kernel
      have hl : raw11028step1Labels = raw11028step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11028step0 raw11028step0Labels permutation40 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw11029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11029 raw11029Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw11029 raw11029Labels = mixedMoment B raw11029step0 raw11029step0Labels := by
      have hz : ∀ j, raw11029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11029step0 = (fun i j => raw11029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11029step0 raw11029; decide +kernel
      have hl : raw11029step0Labels = raw11029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11029 raw11029Labels permutation434 hz
    mixedMoment B raw11029step0 raw11029step0Labels = mixedMoment B raw11029step1 raw11029step1Labels := by
      have ha : raw11029step1 = (fun i j => raw11029step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11029step1 raw11029step0; decide +kernel
      have hl : raw11029step1Labels = raw11029step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11029step0 raw11029step0Labels permutation42 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw11030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11030 raw11030Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw11030 raw11030Labels = mixedMoment B raw11030step0 raw11030step0Labels := by
      have hz : ∀ j, raw11030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11030step0 = (fun i j => raw11030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11030step0 raw11030; decide +kernel
      have hl : raw11030step0Labels = raw11030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11030 raw11030Labels permutation434 hz
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw11031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11031 raw11031Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw11031 raw11031Labels = mixedMoment B raw11031step0 raw11031step0Labels := by
      have hz : ∀ j, raw11031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11031step0 = (fun i j => raw11031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11031step0 raw11031; decide +kernel
      have hl : raw11031step0Labels = raw11031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11031 raw11031Labels permutation434 hz
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw11032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11032 raw11032Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw11032 raw11032Labels = mixedMoment B raw11032step0 raw11032step0Labels := by
      have ha : raw11032step0 = (fun i j => raw11032 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11032step0 raw11032; decide +kernel
      have hl : raw11032step0Labels = raw11032Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11032 raw11032Labels permutation200 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw11033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11033 raw11033Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw11033 raw11033Labels = mixedMoment B raw11033step0 raw11033step0Labels := by
      have hz : ∀ j, raw11033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11033step0 = (fun i j => raw11033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11033step0 raw11033; decide +kernel
      have hl : raw11033step0Labels = raw11033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11033 raw11033Labels permutation434 hz
    mixedMoment B raw11033step0 raw11033step0Labels = mixedMoment B raw11033step1 raw11033step1Labels := by
      have ha : raw11033step1 = (fun i j => raw11033step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11033step1 raw11033step0; decide +kernel
      have hl : raw11033step1Labels = raw11033step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11033step0 raw11033step0Labels permutation34 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw11034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11034 raw11034Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw11034 raw11034Labels = mixedMoment B raw11034step0 raw11034step0Labels := by
      have hz : ∀ j, raw11034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11034step0 = (fun i j => raw11034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11034step0 raw11034; decide +kernel
      have hl : raw11034step0Labels = raw11034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11034 raw11034Labels permutation434 hz
    mixedMoment B raw11034step0 raw11034step0Labels = mixedMoment B raw11034step1 raw11034step1Labels := by
      have ha : raw11034step1 = (fun i j => raw11034step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11034step1 raw11034step0; decide +kernel
      have hl : raw11034step1Labels = raw11034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11034step0 raw11034step0Labels permutation36 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw11035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11035 raw11035Labels = mixedMoment B node4439 node4439Labels := by
  calc
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw11036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11036 raw11036Labels = mixedMoment B node4852 node4852Labels := by
  calc
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw11037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11037 raw11037Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw11037 raw11037Labels = mixedMoment B raw11037step0 raw11037step0Labels := by
      have ha : raw11037step0 = (fun i j => raw11037 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11037step0 raw11037; decide +kernel
      have hl : raw11037step0Labels = raw11037Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11037 raw11037Labels permutation176 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw11038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11038 raw11038Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw11038 raw11038Labels = mixedMoment B raw11038step0 raw11038step0Labels := by
      have ha : raw11038step0 = (fun i j => raw11038 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11038step0 raw11038; decide +kernel
      have hl : raw11038step0Labels = raw11038Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11038 raw11038Labels permutation154 permutation2
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw11039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11039 raw11039Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw11039 raw11039Labels = mixedMoment B raw11039step0 raw11039step0Labels := by
      have ha : raw11039step0 = (fun i j => raw11039 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11039step0 raw11039; decide +kernel
      have hl : raw11039step0Labels = raw11039Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11039 raw11039Labels permutation153 permutation2
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw11040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11040step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11040 raw11040Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw11040 raw11040Labels = mixedMoment B raw11040step0 raw11040step0Labels := by
      have hz : ∀ j, raw11040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11040step0 = (fun i j => raw11040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11040step0 raw11040; decide +kernel
      have hl : raw11040step0Labels = raw11040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11040 raw11040Labels permutation434 hz
    mixedMoment B raw11040step0 raw11040step0Labels = mixedMoment B raw11040step1 raw11040step1Labels := by
      have ha : raw11040step1 = (fun i j => raw11040step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11040step1 raw11040step0; decide +kernel
      have hl : raw11040step1Labels = raw11040step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11040step0 raw11040step0Labels permutation33 permutation2
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw11041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11041 raw11041Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw11041 raw11041Labels = mixedMoment B raw11041step0 raw11041step0Labels := by
      have hz : ∀ j, raw11041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11041step0 = (fun i j => raw11041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11041step0 raw11041; decide +kernel
      have hl : raw11041step0Labels = raw11041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11041 raw11041Labels permutation434 hz
    mixedMoment B raw11041step0 raw11041step0Labels = mixedMoment B raw11041step1 raw11041step1Labels := by
      have ha : raw11041step1 = (fun i j => raw11041step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11041step1 raw11041step0; decide +kernel
      have hl : raw11041step1Labels = raw11041step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11041step0 raw11041step0Labels permutation33 permutation2
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw11042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11042 raw11042Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw11042 raw11042Labels = mixedMoment B raw11042step0 raw11042step0Labels := by
      have hz : ∀ j, raw11042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11042step0 = (fun i j => raw11042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11042step0 raw11042; decide +kernel
      have hl : raw11042step0Labels = raw11042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11042 raw11042Labels permutation434 hz
    mixedMoment B raw11042step0 raw11042step0Labels = mixedMoment B raw11042step1 raw11042step1Labels := by
      have ha : raw11042step1 = (fun i j => raw11042step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11042step1 raw11042step0; decide +kernel
      have hl : raw11042step1Labels = raw11042step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11042step0 raw11042step0Labels permutation39 permutation2
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw11043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11043 raw11043Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw11043 raw11043Labels = mixedMoment B raw11043step0 raw11043step0Labels := by
      have ha : raw11043step0 = (fun i j => raw11043 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11043step0 raw11043; decide +kernel
      have hl : raw11043step0Labels = raw11043Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11043 raw11043Labels permutation201 permutation2
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw11044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw11044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11044 raw11044Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11044 raw11044Labels = mixedMoment B raw11044step0 raw11044step0Labels := by
      have hz : ∀ j, raw11044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11044step0 = (fun i j => raw11044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11044step0 raw11044; decide +kernel
      have hl : raw11044step0Labels = raw11044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11044 raw11044Labels permutation434 hz
    mixedMoment B raw11044step0 raw11044step0Labels = mixedMoment B raw11044step1 raw11044step1Labels := by
      have ha : raw11044step1 = (fun i j => raw11044step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11044step1 raw11044step0; decide +kernel
      have hl : raw11044step1Labels = raw11044step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11044step0 raw11044step0Labels permutation33 permutation2
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw11045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11045 raw11045Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw11045 raw11045Labels = mixedMoment B raw11045step0 raw11045step0Labels := by
      have hz : ∀ j, raw11045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11045step0 = (fun i j => raw11045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11045step0 raw11045; decide +kernel
      have hl : raw11045step0Labels = raw11045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11045 raw11045Labels permutation434 hz
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw11046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw11046step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11046step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11046step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11046step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11046 raw11046Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw11046 raw11046Labels = mixedMoment B raw11046step0 raw11046step0Labels := by
      have hz : ∀ j, raw11046 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11046step0 = (fun i j => raw11046 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11046step0 raw11046; decide +kernel
      have hl : raw11046step0Labels = raw11046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11046 raw11046Labels permutation434 hz
    mixedMoment B raw11046step0 raw11046step0Labels = mixedMoment B raw11046step1 raw11046step1Labels := by
      have ha : raw11046step1 = (fun i j => raw11046step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11046step1 raw11046step0; decide +kernel
      have hl : raw11046step1Labels = raw11046step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11046step0 raw11046step0Labels permutation151 permutation3
    mixedMoment B raw11046step1 raw11046step1Labels = mixedMoment B raw11046step2 raw11046step2Labels := by
      have ha : raw11046step2 = -raw11046step1 := by apply Matrix.ext; change ∀ i j, raw11046step2 i j = -(raw11046step1 i j); unfold raw11046step2 raw11046step1; decide +kernel
      have hl : raw11046step2Labels = raw11046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11046step2 raw11046step2Labels = mixedMoment B raw11046step3 raw11046step3Labels := by
      have ha : raw11046step3 = raw11046step2 := by apply Matrix.ext; unfold raw11046step3 raw11046step2; decide +kernel
      have hl : raw11046step2Labels = labelEmbedding6 ∘ raw11046step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11046step2 raw11046step2Labels raw11046step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw11047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw11047step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11047step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11047step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11047step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11047 raw11047Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw11047 raw11047Labels = mixedMoment B raw11047step0 raw11047step0Labels := by
      have hz : ∀ j, raw11047 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11047step0 = (fun i j => raw11047 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11047step0 raw11047; decide +kernel
      have hl : raw11047step0Labels = raw11047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11047 raw11047Labels permutation434 hz
    mixedMoment B raw11047step0 raw11047step0Labels = mixedMoment B raw11047step1 raw11047step1Labels := by
      have ha : raw11047step1 = (fun i j => raw11047step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11047step1 raw11047step0; decide +kernel
      have hl : raw11047step1Labels = raw11047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11047step0 raw11047step0Labels permutation149 permutation3
    mixedMoment B raw11047step1 raw11047step1Labels = mixedMoment B raw11047step2 raw11047step2Labels := by
      have ha : raw11047step2 = -raw11047step1 := by apply Matrix.ext; change ∀ i j, raw11047step2 i j = -(raw11047step1 i j); unfold raw11047step2 raw11047step1; decide +kernel
      have hl : raw11047step2Labels = raw11047step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11047step2 raw11047step2Labels = mixedMoment B raw11047step3 raw11047step3Labels := by
      have ha : raw11047step3 = raw11047step2 := by apply Matrix.ext; unfold raw11047step3 raw11047step2; decide +kernel
      have hl : raw11047step2Labels = labelEmbedding6 ∘ raw11047step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11047step2 raw11047step2Labels raw11047step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw11048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11048 raw11048Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw11048 raw11048Labels = mixedMoment B raw11048step0 raw11048step0Labels := by
      have ha : raw11048step0 = (fun i j => raw11048 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11048step0 raw11048; decide +kernel
      have hl : raw11048step0Labels = raw11048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11048 raw11048Labels permutation200 permutation2
    _ = mixedMoment B node4793 node4793Labels := by rfl

def raw11049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw11049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw11049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11049 raw11049Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw11049 raw11049Labels = mixedMoment B raw11049step0 raw11049step0Labels := by
      have hz : ∀ j, raw11049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11049step0 = (fun i j => raw11049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11049step0 raw11049; decide +kernel
      have hl : raw11049step0Labels = raw11049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11049 raw11049Labels permutation434 hz
    _ = mixedMoment B node4886 node4886Labels := by rfl

def raw11050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11050step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11050 raw11050Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw11050 raw11050Labels = mixedMoment B raw11050step0 raw11050step0Labels := by
      have hz : ∀ j, raw11050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11050step0 = (fun i j => raw11050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11050step0 raw11050; decide +kernel
      have hl : raw11050step0Labels = raw11050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11050 raw11050Labels permutation434 hz
    mixedMoment B raw11050step0 raw11050step0Labels = mixedMoment B raw11050step1 raw11050step1Labels := by
      have ha : raw11050step1 = (fun i j => raw11050step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11050step1 raw11050step0; decide +kernel
      have hl : raw11050step1Labels = raw11050step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11050step0 raw11050step0Labels permutation50 permutation7
    mixedMoment B raw11050step1 raw11050step1Labels = mixedMoment B raw11050step2 raw11050step2Labels := by
      have ha : raw11050step2 = -raw11050step1 := by apply Matrix.ext; change ∀ i j, raw11050step2 i j = -(raw11050step1 i j); unfold raw11050step2 raw11050step1; decide +kernel
      have hl : raw11050step2Labels = raw11050step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11050step2 raw11050step2Labels = mixedMoment B raw11050step3 raw11050step3Labels := by
      have ha : raw11050step3 = raw11050step2 := by apply Matrix.ext; unfold raw11050step3 raw11050step2; decide +kernel
      have hl : raw11050step2Labels = labelEmbedding1 ∘ raw11050step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11050step2 raw11050step2Labels raw11050step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw11051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11051 raw11051Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw11051 raw11051Labels = mixedMoment B raw11051step0 raw11051step0Labels := by
      have hz : ∀ j, raw11051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11051step0 = (fun i j => raw11051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11051step0 raw11051; decide +kernel
      have hl : raw11051step0Labels = raw11051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11051 raw11051Labels permutation434 hz
    mixedMoment B raw11051step0 raw11051step0Labels = mixedMoment B raw11051step1 raw11051step1Labels := by
      have ha : raw11051step1 = (fun i j => raw11051step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11051step1 raw11051step0; decide +kernel
      have hl : raw11051step1Labels = raw11051step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11051step0 raw11051step0Labels permutation52 permutation7
    mixedMoment B raw11051step1 raw11051step1Labels = mixedMoment B raw11051step2 raw11051step2Labels := by
      have ha : raw11051step2 = -raw11051step1 := by apply Matrix.ext; change ∀ i j, raw11051step2 i j = -(raw11051step1 i j); unfold raw11051step2 raw11051step1; decide +kernel
      have hl : raw11051step2Labels = raw11051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11051step2 raw11051step2Labels = mixedMoment B raw11051step3 raw11051step3Labels := by
      have ha : raw11051step3 = raw11051step2 := by apply Matrix.ext; unfold raw11051step3 raw11051step2; decide +kernel
      have hl : raw11051step2Labels = labelEmbedding1 ∘ raw11051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11051step2 raw11051step2Labels raw11051step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw11052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11052 raw11052Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw11052 raw11052Labels = mixedMoment B raw11052step0 raw11052step0Labels := by
      have ha : raw11052step0 = (fun i j => raw11052 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11052step0 raw11052; decide +kernel
      have hl : raw11052step0Labels = raw11052Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11052 raw11052Labels permutation218 permutation7
    mixedMoment B raw11052step0 raw11052step0Labels = mixedMoment B raw11052step1 raw11052step1Labels := by
      have ha : raw11052step1 = -raw11052step0 := by apply Matrix.ext; change ∀ i j, raw11052step1 i j = -(raw11052step0 i j); unfold raw11052step1 raw11052step0; decide +kernel
      have hl : raw11052step1Labels = raw11052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11052step1 raw11052step1Labels = mixedMoment B raw11052step2 raw11052step2Labels := by
      have ha : raw11052step2 = raw11052step1 := by apply Matrix.ext; unfold raw11052step2 raw11052step1; decide +kernel
      have hl : raw11052step1Labels = labelEmbedding1 ∘ raw11052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11052step1 raw11052step1Labels raw11052step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw11053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11053step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw11053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11053step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11053step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11053 raw11053Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw11053 raw11053Labels = mixedMoment B raw11053step0 raw11053step0Labels := by
      have hz : ∀ j, raw11053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11053step0 = (fun i j => raw11053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11053step0 raw11053; decide +kernel
      have hl : raw11053step0Labels = raw11053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11053 raw11053Labels permutation434 hz
    mixedMoment B raw11053step0 raw11053step0Labels = mixedMoment B raw11053step1 raw11053step1Labels := by
      have ha : raw11053step1 = (fun i j => raw11053step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11053step1 raw11053step0; decide +kernel
      have hl : raw11053step1Labels = raw11053step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11053step0 raw11053step0Labels permutation50 permutation7
    mixedMoment B raw11053step1 raw11053step1Labels = mixedMoment B raw11053step2 raw11053step2Labels := by
      have ha : raw11053step2 = -raw11053step1 := by apply Matrix.ext; change ∀ i j, raw11053step2 i j = -(raw11053step1 i j); unfold raw11053step2 raw11053step1; decide +kernel
      have hl : raw11053step2Labels = raw11053step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11053step2 raw11053step2Labels = mixedMoment B raw11053step3 raw11053step3Labels := by
      have ha : raw11053step3 = raw11053step2 := by apply Matrix.ext; unfold raw11053step3 raw11053step2; decide +kernel
      have hl : raw11053step2Labels = labelEmbedding1 ∘ raw11053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11053step2 raw11053step2Labels raw11053step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

def raw11054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11054 raw11054Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw11054 raw11054Labels = mixedMoment B raw11054step0 raw11054step0Labels := by
      have hz : ∀ j, raw11054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11054step0 = (fun i j => raw11054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11054step0 raw11054; decide +kernel
      have hl : raw11054step0Labels = raw11054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11054 raw11054Labels permutation434 hz
    mixedMoment B raw11054step0 raw11054step0Labels = mixedMoment B raw11054step1 raw11054step1Labels := by
      have ha : raw11054step1 = (fun i j => raw11054step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11054step1 raw11054step0; decide +kernel
      have hl : raw11054step1Labels = raw11054step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11054step0 raw11054step0Labels permutation50 permutation7
    mixedMoment B raw11054step1 raw11054step1Labels = mixedMoment B raw11054step2 raw11054step2Labels := by
      have ha : raw11054step2 = -raw11054step1 := by apply Matrix.ext; change ∀ i j, raw11054step2 i j = -(raw11054step1 i j); unfold raw11054step2 raw11054step1; decide +kernel
      have hl : raw11054step2Labels = raw11054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11054step2 raw11054step2Labels = mixedMoment B raw11054step3 raw11054step3Labels := by
      have ha : raw11054step3 = raw11054step2 := by apply Matrix.ext; unfold raw11054step3 raw11054step2; decide +kernel
      have hl : raw11054step2Labels = labelEmbedding1 ∘ raw11054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11054step2 raw11054step2Labels raw11054step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw11055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11055step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11055step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11055step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11055step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11055 raw11055Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw11055 raw11055Labels = mixedMoment B raw11055step0 raw11055step0Labels := by
      have hz : ∀ j, raw11055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11055step0 = (fun i j => raw11055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11055step0 raw11055; decide +kernel
      have hl : raw11055step0Labels = raw11055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11055 raw11055Labels permutation434 hz
    mixedMoment B raw11055step0 raw11055step0Labels = mixedMoment B raw11055step1 raw11055step1Labels := by
      have ha : raw11055step1 = (fun i j => raw11055step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11055step1 raw11055step0; decide +kernel
      have hl : raw11055step1Labels = raw11055step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11055step0 raw11055step0Labels permutation52 permutation7
    mixedMoment B raw11055step1 raw11055step1Labels = mixedMoment B raw11055step2 raw11055step2Labels := by
      have ha : raw11055step2 = -raw11055step1 := by apply Matrix.ext; change ∀ i j, raw11055step2 i j = -(raw11055step1 i j); unfold raw11055step2 raw11055step1; decide +kernel
      have hl : raw11055step2Labels = raw11055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11055step2 raw11055step2Labels = mixedMoment B raw11055step3 raw11055step3Labels := by
      have ha : raw11055step3 = raw11055step2 := by apply Matrix.ext; unfold raw11055step3 raw11055step2; decide +kernel
      have hl : raw11055step2Labels = labelEmbedding1 ∘ raw11055step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11055step2 raw11055step2Labels raw11055step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw11056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11056step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw11056step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11056step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11056step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11056 raw11056Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw11056 raw11056Labels = mixedMoment B raw11056step0 raw11056step0Labels := by
      have hz : ∀ j, raw11056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11056step0 = (fun i j => raw11056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11056step0 raw11056; decide +kernel
      have hl : raw11056step0Labels = raw11056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11056 raw11056Labels permutation434 hz
    mixedMoment B raw11056step0 raw11056step0Labels = mixedMoment B raw11056step1 raw11056step1Labels := by
      have ha : raw11056step1 = (fun i j => raw11056step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11056step1 raw11056step0; decide +kernel
      have hl : raw11056step1Labels = raw11056step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11056step0 raw11056step0Labels permutation52 permutation7
    mixedMoment B raw11056step1 raw11056step1Labels = mixedMoment B raw11056step2 raw11056step2Labels := by
      have ha : raw11056step2 = -raw11056step1 := by apply Matrix.ext; change ∀ i j, raw11056step2 i j = -(raw11056step1 i j); unfold raw11056step2 raw11056step1; decide +kernel
      have hl : raw11056step2Labels = raw11056step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11056step2 raw11056step2Labels = mixedMoment B raw11056step3 raw11056step3Labels := by
      have ha : raw11056step3 = raw11056step2 := by apply Matrix.ext; unfold raw11056step3 raw11056step2; decide +kernel
      have hl : raw11056step2Labels = labelEmbedding1 ∘ raw11056step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11056step2 raw11056step2Labels raw11056step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw11057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11057step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11057step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11057 raw11057Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw11057 raw11057Labels = mixedMoment B raw11057step0 raw11057step0Labels := by
      have ha : raw11057step0 = (fun i j => raw11057 (permutation220 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11057step0 raw11057; decide +kernel
      have hl : raw11057step0Labels = raw11057Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11057 raw11057Labels permutation220 permutation7
    mixedMoment B raw11057step0 raw11057step0Labels = mixedMoment B raw11057step1 raw11057step1Labels := by
      have ha : raw11057step1 = -raw11057step0 := by apply Matrix.ext; change ∀ i j, raw11057step1 i j = -(raw11057step0 i j); unfold raw11057step1 raw11057step0; decide +kernel
      have hl : raw11057step1Labels = raw11057step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11057step1 raw11057step1Labels = mixedMoment B raw11057step2 raw11057step2Labels := by
      have ha : raw11057step2 = raw11057step1 := by apply Matrix.ext; unfold raw11057step2 raw11057step1; decide +kernel
      have hl : raw11057step1Labels = labelEmbedding1 ∘ raw11057step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11057step1 raw11057step1Labels raw11057step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw11058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11058step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11058step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11058step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11058step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11058 raw11058Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw11058 raw11058Labels = mixedMoment B raw11058step0 raw11058step0Labels := by
      have hz : ∀ j, raw11058 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11058step0 = (fun i j => raw11058 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11058step0 raw11058; decide +kernel
      have hl : raw11058step0Labels = raw11058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11058 raw11058Labels permutation434 hz
    mixedMoment B raw11058step0 raw11058step0Labels = mixedMoment B raw11058step1 raw11058step1Labels := by
      have ha : raw11058step1 = (fun i j => raw11058step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11058step1 raw11058step0; decide +kernel
      have hl : raw11058step1Labels = raw11058step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11058step0 raw11058step0Labels permutation53 permutation7
    mixedMoment B raw11058step1 raw11058step1Labels = mixedMoment B raw11058step2 raw11058step2Labels := by
      have ha : raw11058step2 = -raw11058step1 := by apply Matrix.ext; change ∀ i j, raw11058step2 i j = -(raw11058step1 i j); unfold raw11058step2 raw11058step1; decide +kernel
      have hl : raw11058step2Labels = raw11058step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11058step2 raw11058step2Labels = mixedMoment B raw11058step3 raw11058step3Labels := by
      have ha : raw11058step3 = raw11058step2 := by apply Matrix.ext; unfold raw11058step3 raw11058step2; decide +kernel
      have hl : raw11058step2Labels = labelEmbedding1 ∘ raw11058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11058step2 raw11058step2Labels raw11058step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw11059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11059step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11059step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11059step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11059step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11059 raw11059Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11059 raw11059Labels = mixedMoment B raw11059step0 raw11059step0Labels := by
      have hz : ∀ j, raw11059 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11059step0 = (fun i j => raw11059 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11059step0 raw11059; decide +kernel
      have hl : raw11059step0Labels = raw11059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11059 raw11059Labels permutation434 hz
    mixedMoment B raw11059step0 raw11059step0Labels = mixedMoment B raw11059step1 raw11059step1Labels := by
      have ha : raw11059step1 = (fun i j => raw11059step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11059step1 raw11059step0; decide +kernel
      have hl : raw11059step1Labels = raw11059step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11059step0 raw11059step0Labels permutation52 permutation7
    mixedMoment B raw11059step1 raw11059step1Labels = mixedMoment B raw11059step2 raw11059step2Labels := by
      have ha : raw11059step2 = -raw11059step1 := by apply Matrix.ext; change ∀ i j, raw11059step2 i j = -(raw11059step1 i j); unfold raw11059step2 raw11059step1; decide +kernel
      have hl : raw11059step2Labels = raw11059step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11059step2 raw11059step2Labels = mixedMoment B raw11059step3 raw11059step3Labels := by
      have ha : raw11059step3 = raw11059step2 := by apply Matrix.ext; unfold raw11059step3 raw11059step2; decide +kernel
      have hl : raw11059step2Labels = labelEmbedding1 ∘ raw11059step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11059step2 raw11059step2Labels raw11059step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw11060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11060step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11060step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11060step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11060step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11060 raw11060Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw11060 raw11060Labels = mixedMoment B raw11060step0 raw11060step0Labels := by
      have hz : ∀ j, raw11060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11060step0 = (fun i j => raw11060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11060step0 raw11060; decide +kernel
      have hl : raw11060step0Labels = raw11060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11060 raw11060Labels permutation434 hz
    mixedMoment B raw11060step0 raw11060step0Labels = mixedMoment B raw11060step1 raw11060step1Labels := by
      have ha : raw11060step1 = (fun i j => raw11060step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11060step1 raw11060step0; decide +kernel
      have hl : raw11060step1Labels = raw11060step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11060step0 raw11060step0Labels permutation50 permutation7
    mixedMoment B raw11060step1 raw11060step1Labels = mixedMoment B raw11060step2 raw11060step2Labels := by
      have ha : raw11060step2 = -raw11060step1 := by apply Matrix.ext; change ∀ i j, raw11060step2 i j = -(raw11060step1 i j); unfold raw11060step2 raw11060step1; decide +kernel
      have hl : raw11060step2Labels = raw11060step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11060step2 raw11060step2Labels = mixedMoment B raw11060step3 raw11060step3Labels := by
      have ha : raw11060step3 = raw11060step2 := by apply Matrix.ext; unfold raw11060step3 raw11060step2; decide +kernel
      have hl : raw11060step2Labels = labelEmbedding1 ∘ raw11060step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11060step2 raw11060step2Labels raw11060step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw11061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11061step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw11061step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11061step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11061step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11061step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11061 raw11061Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw11061 raw11061Labels = mixedMoment B raw11061step0 raw11061step0Labels := by
      have hz : ∀ j, raw11061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11061step0 = (fun i j => raw11061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11061step0 raw11061; decide +kernel
      have hl : raw11061step0Labels = raw11061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11061 raw11061Labels permutation434 hz
    mixedMoment B raw11061step0 raw11061step0Labels = mixedMoment B raw11061step1 raw11061step1Labels := by
      have ha : raw11061step1 = (fun i j => raw11061step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11061step1 raw11061step0; decide +kernel
      have hl : raw11061step1Labels = raw11061step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11061step0 raw11061step0Labels permutation50 permutation7
    mixedMoment B raw11061step1 raw11061step1Labels = mixedMoment B raw11061step2 raw11061step2Labels := by
      have ha : raw11061step2 = -raw11061step1 := by apply Matrix.ext; change ∀ i j, raw11061step2 i j = -(raw11061step1 i j); unfold raw11061step2 raw11061step1; decide +kernel
      have hl : raw11061step2Labels = raw11061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11061step2 raw11061step2Labels = mixedMoment B raw11061step3 raw11061step3Labels := by
      have ha : raw11061step3 = raw11061step2 := by apply Matrix.ext; unfold raw11061step3 raw11061step2; decide +kernel
      have hl : raw11061step2Labels = labelEmbedding1 ∘ raw11061step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11061step2 raw11061step2Labels raw11061step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw11062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11062step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11062step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11062step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11062 raw11062Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw11062 raw11062Labels = mixedMoment B raw11062step0 raw11062step0Labels := by
      have ha : raw11062step0 = (fun i j => raw11062 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11062step0 raw11062; decide +kernel
      have hl : raw11062step0Labels = raw11062Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11062 raw11062Labels permutation218 permutation7
    mixedMoment B raw11062step0 raw11062step0Labels = mixedMoment B raw11062step1 raw11062step1Labels := by
      have ha : raw11062step1 = -raw11062step0 := by apply Matrix.ext; change ∀ i j, raw11062step1 i j = -(raw11062step0 i j); unfold raw11062step1 raw11062step0; decide +kernel
      have hl : raw11062step1Labels = raw11062step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11062step1 raw11062step1Labels = mixedMoment B raw11062step2 raw11062step2Labels := by
      have ha : raw11062step2 = raw11062step1 := by apply Matrix.ext; unfold raw11062step2 raw11062step1; decide +kernel
      have hl : raw11062step1Labels = labelEmbedding1 ∘ raw11062step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11062step1 raw11062step1Labels raw11062step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw11063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11063step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11063step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11063step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11063step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11063 raw11063Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw11063 raw11063Labels = mixedMoment B raw11063step0 raw11063step0Labels := by
      have hz : ∀ j, raw11063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11063step0 = (fun i j => raw11063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11063step0 raw11063; decide +kernel
      have hl : raw11063step0Labels = raw11063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11063 raw11063Labels permutation434 hz
    mixedMoment B raw11063step0 raw11063step0Labels = mixedMoment B raw11063step1 raw11063step1Labels := by
      have ha : raw11063step1 = (fun i j => raw11063step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11063step1 raw11063step0; decide +kernel
      have hl : raw11063step1Labels = raw11063step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11063step0 raw11063step0Labels permutation51 permutation7
    mixedMoment B raw11063step1 raw11063step1Labels = mixedMoment B raw11063step2 raw11063step2Labels := by
      have ha : raw11063step2 = -raw11063step1 := by apply Matrix.ext; change ∀ i j, raw11063step2 i j = -(raw11063step1 i j); unfold raw11063step2 raw11063step1; decide +kernel
      have hl : raw11063step2Labels = raw11063step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11063step2 raw11063step2Labels = mixedMoment B raw11063step3 raw11063step3Labels := by
      have ha : raw11063step3 = raw11063step2 := by apply Matrix.ext; unfold raw11063step3 raw11063step2; decide +kernel
      have hl : raw11063step2Labels = labelEmbedding1 ∘ raw11063step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11063step2 raw11063step2Labels raw11063step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw11064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11064Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11064step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11064step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11064step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11064step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11064 raw11064Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11064 raw11064Labels = mixedMoment B raw11064step0 raw11064step0Labels := by
      have hz : ∀ j, raw11064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11064step0 = (fun i j => raw11064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11064step0 raw11064; decide +kernel
      have hl : raw11064step0Labels = raw11064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11064 raw11064Labels permutation434 hz
    mixedMoment B raw11064step0 raw11064step0Labels = mixedMoment B raw11064step1 raw11064step1Labels := by
      have ha : raw11064step1 = (fun i j => raw11064step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11064step1 raw11064step0; decide +kernel
      have hl : raw11064step1Labels = raw11064step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11064step0 raw11064step0Labels permutation50 permutation7
    mixedMoment B raw11064step1 raw11064step1Labels = mixedMoment B raw11064step2 raw11064step2Labels := by
      have ha : raw11064step2 = -raw11064step1 := by apply Matrix.ext; change ∀ i j, raw11064step2 i j = -(raw11064step1 i j); unfold raw11064step2 raw11064step1; decide +kernel
      have hl : raw11064step2Labels = raw11064step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11064step2 raw11064step2Labels = mixedMoment B raw11064step3 raw11064step3Labels := by
      have ha : raw11064step3 = raw11064step2 := by apply Matrix.ext; unfold raw11064step3 raw11064step2; decide +kernel
      have hl : raw11064step2Labels = labelEmbedding1 ∘ raw11064step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11064step2 raw11064step2Labels raw11064step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw11065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11065Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11065step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11065step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11065step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11065 raw11065Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw11065 raw11065Labels = mixedMoment B raw11065step0 raw11065step0Labels := by
      have ha : raw11065step0 = (fun i j => raw11065 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11065step0 raw11065; decide +kernel
      have hl : raw11065step0Labels = raw11065Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11065 raw11065Labels permutation218 permutation7
    mixedMoment B raw11065step0 raw11065step0Labels = mixedMoment B raw11065step1 raw11065step1Labels := by
      have ha : raw11065step1 = -raw11065step0 := by apply Matrix.ext; change ∀ i j, raw11065step1 i j = -(raw11065step0 i j); unfold raw11065step1 raw11065step0; decide +kernel
      have hl : raw11065step1Labels = raw11065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11065step1 raw11065step1Labels = mixedMoment B raw11065step2 raw11065step2Labels := by
      have ha : raw11065step2 = raw11065step1 := by apply Matrix.ext; unfold raw11065step2 raw11065step1; decide +kernel
      have hl : raw11065step1Labels = labelEmbedding1 ∘ raw11065step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11065step1 raw11065step1Labels raw11065step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw11066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11066Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11066 raw11066Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw11066 raw11066Labels = mixedMoment B raw11066step0 raw11066step0Labels := by
      have ha : raw11066step0 = (fun i j => raw11066 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11066step0 raw11066; decide +kernel
      have hl : raw11066step0Labels = raw11066Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11066 raw11066Labels permutation218 permutation7
    mixedMoment B raw11066step0 raw11066step0Labels = mixedMoment B raw11066step1 raw11066step1Labels := by
      have ha : raw11066step1 = -raw11066step0 := by apply Matrix.ext; change ∀ i j, raw11066step1 i j = -(raw11066step0 i j); unfold raw11066step1 raw11066step0; decide +kernel
      have hl : raw11066step1Labels = raw11066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11066step1 raw11066step1Labels = mixedMoment B raw11066step2 raw11066step2Labels := by
      have ha : raw11066step2 = raw11066step1 := by apply Matrix.ext; unfold raw11066step2 raw11066step1; decide +kernel
      have hl : raw11066step1Labels = labelEmbedding1 ∘ raw11066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11066step1 raw11066step1Labels raw11066step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw11067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11067Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw11067step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11067step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11067 raw11067Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw11067 raw11067Labels = mixedMoment B raw11067step0 raw11067step0Labels := by
      have ha : raw11067step0 = (fun i j => raw11067 (permutation220 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11067step0 raw11067; decide +kernel
      have hl : raw11067step0Labels = raw11067Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11067 raw11067Labels permutation220 permutation7
    mixedMoment B raw11067step0 raw11067step0Labels = mixedMoment B raw11067step1 raw11067step1Labels := by
      have ha : raw11067step1 = -raw11067step0 := by apply Matrix.ext; change ∀ i j, raw11067step1 i j = -(raw11067step0 i j); unfold raw11067step1 raw11067step0; decide +kernel
      have hl : raw11067step1Labels = raw11067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11067step1 raw11067step1Labels = mixedMoment B raw11067step2 raw11067step2Labels := by
      have ha : raw11067step2 = raw11067step1 := by apply Matrix.ext; unfold raw11067step2 raw11067step1; decide +kernel
      have hl : raw11067step1Labels = labelEmbedding1 ∘ raw11067step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11067step1 raw11067step1Labels raw11067step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw11068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw11068step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11068 raw11068Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw11068 raw11068Labels = mixedMoment B raw11068step0 raw11068step0Labels := by
      have ha : raw11068step0 = (fun i j => raw11068 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11068step0 raw11068; decide +kernel
      have hl : raw11068step0Labels = raw11068Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11068 raw11068Labels permutation218 permutation7
    mixedMoment B raw11068step0 raw11068step0Labels = mixedMoment B raw11068step1 raw11068step1Labels := by
      have ha : raw11068step1 = -raw11068step0 := by apply Matrix.ext; change ∀ i j, raw11068step1 i j = -(raw11068step0 i j); unfold raw11068step1 raw11068step0; decide +kernel
      have hl : raw11068step1Labels = raw11068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11068step1 raw11068step1Labels = mixedMoment B raw11068step2 raw11068step2Labels := by
      have ha : raw11068step2 = raw11068step1 := by apply Matrix.ext; unfold raw11068step2 raw11068step1; decide +kernel
      have hl : raw11068step1Labels = labelEmbedding1 ∘ raw11068step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11068step1 raw11068step1Labels raw11068step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw11069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11069step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11069step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11069step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11069 raw11069Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw11069 raw11069Labels = mixedMoment B raw11069step0 raw11069step0Labels := by
      have ha : raw11069step0 = (fun i j => raw11069 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11069step0 raw11069; decide +kernel
      have hl : raw11069step0Labels = raw11069Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11069 raw11069Labels permutation218 permutation7
    mixedMoment B raw11069step0 raw11069step0Labels = mixedMoment B raw11069step1 raw11069step1Labels := by
      have ha : raw11069step1 = -raw11069step0 := by apply Matrix.ext; change ∀ i j, raw11069step1 i j = -(raw11069step0 i j); unfold raw11069step1 raw11069step0; decide +kernel
      have hl : raw11069step1Labels = raw11069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11069step1 raw11069step1Labels = mixedMoment B raw11069step2 raw11069step2Labels := by
      have ha : raw11069step2 = raw11069step1 := by apply Matrix.ext; unfold raw11069step2 raw11069step1; decide +kernel
      have hl : raw11069step1Labels = labelEmbedding1 ∘ raw11069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11069step1 raw11069step1Labels raw11069step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw11070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11070step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11070step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11070step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11070 raw11070Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw11070 raw11070Labels = mixedMoment B raw11070step0 raw11070step0Labels := by
      have hz : ∀ j, raw11070 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11070step0 = (fun i j => raw11070 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11070step0 raw11070; decide +kernel
      have hl : raw11070step0Labels = raw11070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11070 raw11070Labels permutation434 hz
    mixedMoment B raw11070step0 raw11070step0Labels = mixedMoment B raw11070step1 raw11070step1Labels := by
      have ha : raw11070step1 = (fun i j => raw11070step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11070step1 raw11070step0; decide +kernel
      have hl : raw11070step1Labels = raw11070step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11070step0 raw11070step0Labels permutation50 permutation7
    mixedMoment B raw11070step1 raw11070step1Labels = mixedMoment B raw11070step2 raw11070step2Labels := by
      have ha : raw11070step2 = -raw11070step1 := by apply Matrix.ext; change ∀ i j, raw11070step2 i j = -(raw11070step1 i j); unfold raw11070step2 raw11070step1; decide +kernel
      have hl : raw11070step2Labels = raw11070step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11070step2 raw11070step2Labels = mixedMoment B raw11070step3 raw11070step3Labels := by
      have ha : raw11070step3 = raw11070step2 := by apply Matrix.ext; unfold raw11070step3 raw11070step2; decide +kernel
      have hl : raw11070step2Labels = labelEmbedding1 ∘ raw11070step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11070step2 raw11070step2Labels raw11070step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw11071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11071step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11071step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11071step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11071step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11071 raw11071Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw11071 raw11071Labels = mixedMoment B raw11071step0 raw11071step0Labels := by
      have hz : ∀ j, raw11071 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11071step0 = (fun i j => raw11071 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11071step0 raw11071; decide +kernel
      have hl : raw11071step0Labels = raw11071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11071 raw11071Labels permutation434 hz
    mixedMoment B raw11071step0 raw11071step0Labels = mixedMoment B raw11071step1 raw11071step1Labels := by
      have ha : raw11071step1 = (fun i j => raw11071step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11071step1 raw11071step0; decide +kernel
      have hl : raw11071step1Labels = raw11071step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11071step0 raw11071step0Labels permutation50 permutation7
    mixedMoment B raw11071step1 raw11071step1Labels = mixedMoment B raw11071step2 raw11071step2Labels := by
      have ha : raw11071step2 = -raw11071step1 := by apply Matrix.ext; change ∀ i j, raw11071step2 i j = -(raw11071step1 i j); unfold raw11071step2 raw11071step1; decide +kernel
      have hl : raw11071step2Labels = raw11071step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11071step2 raw11071step2Labels = mixedMoment B raw11071step3 raw11071step3Labels := by
      have ha : raw11071step3 = raw11071step2 := by apply Matrix.ext; unfold raw11071step3 raw11071step2; decide +kernel
      have hl : raw11071step2Labels = labelEmbedding1 ∘ raw11071step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11071step2 raw11071step2Labels raw11071step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw11072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11072step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11072 raw11072Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw11072 raw11072Labels = mixedMoment B raw11072step0 raw11072step0Labels := by
      have hz : ∀ j, raw11072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11072step0 = (fun i j => raw11072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11072step0 raw11072; decide +kernel
      have hl : raw11072step0Labels = raw11072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11072 raw11072Labels permutation434 hz
    mixedMoment B raw11072step0 raw11072step0Labels = mixedMoment B raw11072step1 raw11072step1Labels := by
      have ha : raw11072step1 = (fun i j => raw11072step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11072step1 raw11072step0; decide +kernel
      have hl : raw11072step1Labels = raw11072step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11072step0 raw11072step0Labels permutation52 permutation7
    mixedMoment B raw11072step1 raw11072step1Labels = mixedMoment B raw11072step2 raw11072step2Labels := by
      have ha : raw11072step2 = -raw11072step1 := by apply Matrix.ext; change ∀ i j, raw11072step2 i j = -(raw11072step1 i j); unfold raw11072step2 raw11072step1; decide +kernel
      have hl : raw11072step2Labels = raw11072step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11072step2 raw11072step2Labels = mixedMoment B raw11072step3 raw11072step3Labels := by
      have ha : raw11072step3 = raw11072step2 := by apply Matrix.ext; unfold raw11072step3 raw11072step2; decide +kernel
      have hl : raw11072step2Labels = labelEmbedding1 ∘ raw11072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11072step2 raw11072step2Labels raw11072step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw11073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11073 raw11073Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw11073 raw11073Labels = mixedMoment B raw11073step0 raw11073step0Labels := by
      have ha : raw11073step0 = (fun i j => raw11073 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11073step0 raw11073; decide +kernel
      have hl : raw11073step0Labels = raw11073Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11073 raw11073Labels permutation218 permutation7
    mixedMoment B raw11073step0 raw11073step0Labels = mixedMoment B raw11073step1 raw11073step1Labels := by
      have ha : raw11073step1 = -raw11073step0 := by apply Matrix.ext; change ∀ i j, raw11073step1 i j = -(raw11073step0 i j); unfold raw11073step1 raw11073step0; decide +kernel
      have hl : raw11073step1Labels = raw11073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11073step1 raw11073step1Labels = mixedMoment B raw11073step2 raw11073step2Labels := by
      have ha : raw11073step2 = raw11073step1 := by apply Matrix.ext; unfold raw11073step2 raw11073step1; decide +kernel
      have hl : raw11073step1Labels = labelEmbedding1 ∘ raw11073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11073step1 raw11073step1Labels raw11073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw11074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw11074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11074step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11074step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11074step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11074step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11074 raw11074Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw11074 raw11074Labels = mixedMoment B raw11074step0 raw11074step0Labels := by
      have hz : ∀ j, raw11074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11074step0 = (fun i j => raw11074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11074step0 raw11074; decide +kernel
      have hl : raw11074step0Labels = raw11074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11074 raw11074Labels permutation434 hz
    mixedMoment B raw11074step0 raw11074step0Labels = mixedMoment B raw11074step1 raw11074step1Labels := by
      have ha : raw11074step1 = (fun i j => raw11074step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11074step1 raw11074step0; decide +kernel
      have hl : raw11074step1Labels = raw11074step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11074step0 raw11074step0Labels permutation50 permutation7
    mixedMoment B raw11074step1 raw11074step1Labels = mixedMoment B raw11074step2 raw11074step2Labels := by
      have ha : raw11074step2 = -raw11074step1 := by apply Matrix.ext; change ∀ i j, raw11074step2 i j = -(raw11074step1 i j); unfold raw11074step2 raw11074step1; decide +kernel
      have hl : raw11074step2Labels = raw11074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11074step2 raw11074step2Labels = mixedMoment B raw11074step3 raw11074step3Labels := by
      have ha : raw11074step3 = raw11074step2 := by apply Matrix.ext; unfold raw11074step3 raw11074step2; decide +kernel
      have hl : raw11074step2Labels = labelEmbedding1 ∘ raw11074step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11074step2 raw11074step2Labels raw11074step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw11075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11075step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11075step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11075step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11075step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11075 raw11075Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw11075 raw11075Labels = mixedMoment B raw11075step0 raw11075step0Labels := by
      have hz : ∀ j, raw11075 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11075step0 = (fun i j => raw11075 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11075step0 raw11075; decide +kernel
      have hl : raw11075step0Labels = raw11075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11075 raw11075Labels permutation434 hz
    mixedMoment B raw11075step0 raw11075step0Labels = mixedMoment B raw11075step1 raw11075step1Labels := by
      have ha : raw11075step1 = (fun i j => raw11075step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11075step1 raw11075step0; decide +kernel
      have hl : raw11075step1Labels = raw11075step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11075step0 raw11075step0Labels permutation50 permutation7
    mixedMoment B raw11075step1 raw11075step1Labels = mixedMoment B raw11075step2 raw11075step2Labels := by
      have ha : raw11075step2 = -raw11075step1 := by apply Matrix.ext; change ∀ i j, raw11075step2 i j = -(raw11075step1 i j); unfold raw11075step2 raw11075step1; decide +kernel
      have hl : raw11075step2Labels = raw11075step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11075step2 raw11075step2Labels = mixedMoment B raw11075step3 raw11075step3Labels := by
      have ha : raw11075step3 = raw11075step2 := by apply Matrix.ext; unfold raw11075step3 raw11075step2; decide +kernel
      have hl : raw11075step2Labels = labelEmbedding1 ∘ raw11075step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11075step2 raw11075step2Labels raw11075step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw11076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11076step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw11076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw11076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11076 raw11076Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw11076 raw11076Labels = mixedMoment B raw11076step0 raw11076step0Labels := by
      have hz : ∀ j, raw11076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11076step0 = (fun i j => raw11076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11076step0 raw11076; decide +kernel
      have hl : raw11076step0Labels = raw11076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11076 raw11076Labels permutation434 hz
    mixedMoment B raw11076step0 raw11076step0Labels = mixedMoment B raw11076step1 raw11076step1Labels := by
      have ha : raw11076step1 = (fun i j => raw11076step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11076step1 raw11076step0; decide +kernel
      have hl : raw11076step1Labels = raw11076step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11076step0 raw11076step0Labels permutation147 permutation5
    mixedMoment B raw11076step1 raw11076step1Labels = mixedMoment B raw11076step2 raw11076step2Labels := by
      have ha : raw11076step2 = raw11076step1 := by apply Matrix.ext; unfold raw11076step2 raw11076step1; decide +kernel
      have hl : raw11076step1Labels = labelEmbedding1 ∘ raw11076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11076step1 raw11076step1Labels raw11076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw11077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw11077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw11077step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11077 raw11077Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw11077 raw11077Labels = mixedMoment B raw11077step0 raw11077step0Labels := by
      have hz : ∀ j, raw11077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11077step0 = (fun i j => raw11077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11077step0 raw11077; decide +kernel
      have hl : raw11077step0Labels = raw11077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11077 raw11077Labels permutation434 hz
    mixedMoment B raw11077step0 raw11077step0Labels = mixedMoment B raw11077step1 raw11077step1Labels := by
      have ha : raw11077step1 = (fun i j => raw11077step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11077step1 raw11077step0; decide +kernel
      have hl : raw11077step1Labels = raw11077step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11077step0 raw11077step0Labels permutation146 permutation5
    mixedMoment B raw11077step1 raw11077step1Labels = mixedMoment B raw11077step2 raw11077step2Labels := by
      have ha : raw11077step2 = raw11077step1 := by apply Matrix.ext; unfold raw11077step2 raw11077step1; decide +kernel
      have hl : raw11077step1Labels = labelEmbedding1 ∘ raw11077step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11077step1 raw11077step1Labels raw11077step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw11078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11078 raw11078Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw11078 raw11078Labels = mixedMoment B raw11078step0 raw11078step0Labels := by
      have ha : raw11078step0 = (fun i j => raw11078 (permutation665 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11078step0 raw11078; decide +kernel
      have hl : raw11078step0Labels = raw11078Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11078 raw11078Labels permutation665 permutation5
    mixedMoment B raw11078step0 raw11078step0Labels = mixedMoment B raw11078step1 raw11078step1Labels := by
      have ha : raw11078step1 = raw11078step0 := by apply Matrix.ext; unfold raw11078step1 raw11078step0; decide +kernel
      have hl : raw11078step0Labels = labelEmbedding1 ∘ raw11078step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11078step0 raw11078step0Labels raw11078step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2219 node2219Labels := by rfl

def raw11079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw11079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw11079step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11079step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11079 raw11079Labels = mixedMoment B node2283 node2283Labels := by
  calc
    mixedMoment B raw11079 raw11079Labels = mixedMoment B raw11079step0 raw11079step0Labels := by
      have hz : ∀ j, raw11079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11079step0 = (fun i j => raw11079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11079step0 raw11079; decide +kernel
      have hl : raw11079step0Labels = raw11079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11079 raw11079Labels permutation434 hz
    mixedMoment B raw11079step0 raw11079step0Labels = mixedMoment B raw11079step1 raw11079step1Labels := by
      have ha : raw11079step1 = (fun i j => raw11079step0 (permutation128 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11079step1 raw11079step0; decide +kernel
      have hl : raw11079step1Labels = raw11079step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11079step0 raw11079step0Labels permutation128 permutation5
    mixedMoment B raw11079step1 raw11079step1Labels = mixedMoment B raw11079step2 raw11079step2Labels := by
      have ha : raw11079step2 = raw11079step1 := by apply Matrix.ext; unfold raw11079step2 raw11079step1; decide +kernel
      have hl : raw11079step1Labels = labelEmbedding1 ∘ raw11079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11079step1 raw11079step1Labels raw11079step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2283 node2283Labels := by rfl

def raw11080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11080 raw11080Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw11080 raw11080Labels = mixedMoment B raw11080step0 raw11080step0Labels := by
      have hz : ∀ j, raw11080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11080step0 = (fun i j => raw11080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11080step0 raw11080; decide +kernel
      have hl : raw11080step0Labels = raw11080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11080 raw11080Labels permutation434 hz
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw11081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11081 raw11081Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw11081 raw11081Labels = mixedMoment B raw11081step0 raw11081step0Labels := by
      have hz : ∀ j, raw11081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11081step0 = (fun i j => raw11081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11081step0 raw11081; decide +kernel
      have hl : raw11081step0Labels = raw11081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11081 raw11081Labels permutation434 hz
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw11082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11082 raw11082Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw11082 raw11082Labels = mixedMoment B raw11082step0 raw11082step0Labels := by
      have hz : ∀ j, raw11082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11082step0 = (fun i j => raw11082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11082step0 raw11082; decide +kernel
      have hl : raw11082step0Labels = raw11082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11082 raw11082Labels permutation434 hz
    mixedMoment B raw11082step0 raw11082step0Labels = mixedMoment B raw11082step1 raw11082step1Labels := by
      have ha : raw11082step1 = (fun i j => raw11082step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11082step1 raw11082step0; decide +kernel
      have hl : raw11082step1Labels = raw11082step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11082step0 raw11082step0Labels permutation38 permutation2
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw11083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11083 raw11083Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11083 raw11083Labels = mixedMoment B raw11083step0 raw11083step0Labels := by
      have ha : raw11083step0 = (fun i j => raw11083 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11083step0 raw11083; decide +kernel
      have hl : raw11083step0Labels = raw11083Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11083 raw11083Labels permutation200 permutation2
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw11084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11084 raw11084Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw11084 raw11084Labels = mixedMoment B raw11084step0 raw11084step0Labels := by
      have hz : ∀ j, raw11084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11084step0 = (fun i j => raw11084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11084step0 raw11084; decide +kernel
      have hl : raw11084step0Labels = raw11084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11084 raw11084Labels permutation434 hz
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw11085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11085 raw11085Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw11085 raw11085Labels = mixedMoment B raw11085step0 raw11085step0Labels := by
      have hz : ∀ j, raw11085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11085step0 = (fun i j => raw11085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11085step0 raw11085; decide +kernel
      have hl : raw11085step0Labels = raw11085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11085 raw11085Labels permutation434 hz
    mixedMoment B raw11085step0 raw11085step0Labels = mixedMoment B raw11085step1 raw11085step1Labels := by
      have ha : raw11085step1 = (fun i j => raw11085step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11085step1 raw11085step0; decide +kernel
      have hl : raw11085step1Labels = raw11085step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11085step0 raw11085step0Labels permutation33 permutation2
    _ = mixedMoment B node3622 node3622Labels := by rfl

def raw11086 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]
def raw11086Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11086step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw11086step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11086step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11086step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11086 raw11086Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11086 raw11086Labels = mixedMoment B raw11086step0 raw11086step0Labels := by
      have hz : ∀ j, raw11086 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11086step0 = (fun i j => raw11086 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11086step0 raw11086; decide +kernel
      have hl : raw11086step0Labels = raw11086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11086 raw11086Labels permutation590 hz
    mixedMoment B raw11086step0 raw11086step0Labels = mixedMoment B raw11086step1 raw11086step1Labels := by
      have hz : ∀ j, raw11086step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11086step1 = (fun i j => raw11086step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11086step1 raw11086step0; decide +kernel
      have hl : raw11086step1Labels = raw11086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11086step0 raw11086step0Labels permutation104 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw11087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11087 raw11087Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw11087 raw11087Labels = mixedMoment B raw11087step0 raw11087step0Labels := by
      have hz : ∀ j, raw11087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11087step0 = (fun i j => raw11087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11087step0 raw11087; decide +kernel
      have hl : raw11087step0Labels = raw11087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11087 raw11087Labels permutation434 hz
    mixedMoment B raw11087step0 raw11087step0Labels = mixedMoment B raw11087step1 raw11087step1Labels := by
      have ha : raw11087step1 = (fun i j => raw11087step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11087step1 raw11087step0; decide +kernel
      have hl : raw11087step1Labels = raw11087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11087step0 raw11087step0Labels permutation38 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw11088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11088 raw11088Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw11088 raw11088Labels = mixedMoment B raw11088step0 raw11088step0Labels := by
      have hz : ∀ j, raw11088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11088step0 = (fun i j => raw11088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11088step0 raw11088; decide +kernel
      have hl : raw11088step0Labels = raw11088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11088 raw11088Labels permutation434 hz
    mixedMoment B raw11088step0 raw11088step0Labels = mixedMoment B raw11088step1 raw11088step1Labels := by
      have ha : raw11088step1 = (fun i j => raw11088step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11088step1 raw11088step0; decide +kernel
      have hl : raw11088step1Labels = raw11088step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11088step0 raw11088step0Labels permutation38 permutation2
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw11089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11089 raw11089Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw11089 raw11089Labels = mixedMoment B raw11089step0 raw11089step0Labels := by
      have ha : raw11089step0 = (fun i j => raw11089 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11089step0 raw11089; decide +kernel
      have hl : raw11089step0Labels = raw11089Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11089 raw11089Labels permutation206 permutation2
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw11090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw11090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11090 raw11090Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw11090 raw11090Labels = mixedMoment B raw11090step0 raw11090step0Labels := by
      have hz : ∀ j, raw11090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11090step0 = (fun i j => raw11090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11090step0 raw11090; decide +kernel
      have hl : raw11090step0Labels = raw11090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11090 raw11090Labels permutation434 hz
    mixedMoment B raw11090step0 raw11090step0Labels = mixedMoment B raw11090step1 raw11090step1Labels := by
      have ha : raw11090step1 = (fun i j => raw11090step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11090step1 raw11090step0; decide +kernel
      have hl : raw11090step1Labels = raw11090step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11090step0 raw11090step0Labels permutation40 permutation2
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw11091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw11091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11091 raw11091Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11091 raw11091Labels = mixedMoment B raw11091step0 raw11091step0Labels := by
      have hz : ∀ j, raw11091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11091step0 = (fun i j => raw11091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11091step0 raw11091; decide +kernel
      have hl : raw11091step0Labels = raw11091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11091 raw11091Labels permutation434 hz
    mixedMoment B raw11091step0 raw11091step0Labels = mixedMoment B raw11091step1 raw11091step1Labels := by
      have ha : raw11091step1 = (fun i j => raw11091step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11091step1 raw11091step0; decide +kernel
      have hl : raw11091step1Labels = raw11091step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11091step0 raw11091step0Labels permutation42 permutation2
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw11092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11092 raw11092Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw11092 raw11092Labels = mixedMoment B raw11092step0 raw11092step0Labels := by
      have hz : ∀ j, raw11092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11092step0 = (fun i j => raw11092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11092step0 raw11092; decide +kernel
      have hl : raw11092step0Labels = raw11092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11092 raw11092Labels permutation434 hz
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw11093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11093 raw11093Labels = mixedMoment B node2089 node2089Labels := by
  calc
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw11094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11094 raw11094Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw11094 raw11094Labels = mixedMoment B raw11094step0 raw11094step0Labels := by
      have hz : ∀ j, raw11094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11094step0 = (fun i j => raw11094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11094step0 raw11094; decide +kernel
      have hl : raw11094step0Labels = raw11094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11094 raw11094Labels permutation434 hz
    mixedMoment B raw11094step0 raw11094step0Labels = mixedMoment B raw11094step1 raw11094step1Labels := by
      have ha : raw11094step1 = (fun i j => raw11094step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11094step1 raw11094step0; decide +kernel
      have hl : raw11094step1Labels = raw11094step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11094step0 raw11094step0Labels permutation33 permutation2
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw11095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11095 raw11095Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw11095 raw11095Labels = mixedMoment B raw11095step0 raw11095step0Labels := by
      have hz : ∀ j, raw11095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11095step0 = (fun i j => raw11095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11095step0 raw11095; decide +kernel
      have hl : raw11095step0Labels = raw11095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11095 raw11095Labels permutation434 hz
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw11096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11096 raw11096Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw11096 raw11096Labels = mixedMoment B raw11096step0 raw11096step0Labels := by
      have ha : raw11096step0 = (fun i j => raw11096 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11096step0 raw11096; decide +kernel
      have hl : raw11096step0Labels = raw11096Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11096 raw11096Labels permutation200 permutation2
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw11097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11097 raw11097Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw11097 raw11097Labels = mixedMoment B raw11097step0 raw11097step0Labels := by
      have ha : raw11097step0 = (fun i j => raw11097 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11097step0 raw11097; decide +kernel
      have hl : raw11097step0Labels = raw11097Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11097 raw11097Labels permutation201 permutation2
    _ = mixedMoment B node2012 node2012Labels := by rfl

def raw11098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw11098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11098 raw11098Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw11098 raw11098Labels = mixedMoment B raw11098step0 raw11098step0Labels := by
      have ha : raw11098step0 = (fun i j => raw11098 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11098step0 raw11098; decide +kernel
      have hl : raw11098step0Labels = raw11098Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11098 raw11098Labels permutation200 permutation2
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw11099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11099 raw11099Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw11099 raw11099Labels = mixedMoment B raw11099step0 raw11099step0Labels := by
      have hz : ∀ j, raw11099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11099step0 = (fun i j => raw11099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11099step0 raw11099; decide +kernel
      have hl : raw11099step0Labels = raw11099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11099 raw11099Labels permutation434 hz
    mixedMoment B raw11099step0 raw11099step0Labels = mixedMoment B raw11099step1 raw11099step1Labels := by
      have ha : raw11099step1 = (fun i j => raw11099step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11099step1 raw11099step0; decide +kernel
      have hl : raw11099step1Labels = raw11099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11099step0 raw11099step0Labels permutation33 permutation2
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw11100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw11100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw11100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11100 raw11100Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw11100 raw11100Labels = mixedMoment B raw11100step0 raw11100step0Labels := by
      have hz : ∀ j, raw11100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11100step0 = (fun i j => raw11100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11100step0 raw11100; decide +kernel
      have hl : raw11100step0Labels = raw11100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11100 raw11100Labels permutation434 hz
    mixedMoment B raw11100step0 raw11100step0Labels = mixedMoment B raw11100step1 raw11100step1Labels := by
      have ha : raw11100step1 = (fun i j => raw11100step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11100step1 raw11100step0; decide +kernel
      have hl : raw11100step1Labels = raw11100step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11100step0 raw11100step0Labels permutation39 permutation2
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw11101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw11101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11101 raw11101Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw11101 raw11101Labels = mixedMoment B raw11101step0 raw11101step0Labels := by
      have hz : ∀ j, raw11101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11101step0 = (fun i j => raw11101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11101step0 raw11101; decide +kernel
      have hl : raw11101step0Labels = raw11101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11101 raw11101Labels permutation434 hz
    mixedMoment B raw11101step0 raw11101step0Labels = mixedMoment B raw11101step1 raw11101step1Labels := by
      have ha : raw11101step1 = (fun i j => raw11101step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11101step1 raw11101step0; decide +kernel
      have hl : raw11101step1Labels = raw11101step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11101step0 raw11101step0Labels permutation33 permutation2
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw11102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11102 raw11102Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw11102 raw11102Labels = mixedMoment B raw11102step0 raw11102step0Labels := by
      have hz : ∀ j, raw11102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11102step0 = (fun i j => raw11102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11102step0 raw11102; decide +kernel
      have hl : raw11102step0Labels = raw11102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11102 raw11102Labels permutation434 hz
    mixedMoment B raw11102step0 raw11102step0Labels = mixedMoment B raw11102step1 raw11102step1Labels := by
      have ha : raw11102step1 = (fun i j => raw11102step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11102step1 raw11102step0; decide +kernel
      have hl : raw11102step1Labels = raw11102step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11102step0 raw11102step0Labels permutation151 permutation2
    mixedMoment B raw11102step1 raw11102step1Labels = mixedMoment B raw11102step2 raw11102step2Labels := by
      have ha : raw11102step2 = -raw11102step1 := by apply Matrix.ext; change ∀ i j, raw11102step2 i j = -(raw11102step1 i j); unfold raw11102step2 raw11102step1; decide +kernel
      have hl : raw11102step2Labels = raw11102step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw11103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11103 raw11103Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw11103 raw11103Labels = mixedMoment B raw11103step0 raw11103step0Labels := by
      have hz : ∀ j, raw11103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11103step0 = (fun i j => raw11103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11103step0 raw11103; decide +kernel
      have hl : raw11103step0Labels = raw11103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11103 raw11103Labels permutation434 hz
    mixedMoment B raw11103step0 raw11103step0Labels = mixedMoment B raw11103step1 raw11103step1Labels := by
      have ha : raw11103step1 = (fun i j => raw11103step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11103step1 raw11103step0; decide +kernel
      have hl : raw11103step1Labels = raw11103step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11103step0 raw11103step0Labels permutation149 permutation2
    mixedMoment B raw11103step1 raw11103step1Labels = mixedMoment B raw11103step2 raw11103step2Labels := by
      have ha : raw11103step2 = -raw11103step1 := by apply Matrix.ext; change ∀ i j, raw11103step2 i j = -(raw11103step1 i j); unfold raw11103step2 raw11103step1; decide +kernel
      have hl : raw11103step2Labels = raw11103step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw11104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11104step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11104 raw11104Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw11104 raw11104Labels = mixedMoment B raw11104step0 raw11104step0Labels := by
      have ha : raw11104step0 = (fun i j => raw11104 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11104step0 raw11104; decide +kernel
      have hl : raw11104step0Labels = raw11104Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11104 raw11104Labels permutation200 permutation3
    mixedMoment B raw11104step0 raw11104step0Labels = mixedMoment B raw11104step1 raw11104step1Labels := by
      have ha : raw11104step1 = raw11104step0 := by apply Matrix.ext; unfold raw11104step1 raw11104step0; decide +kernel
      have hl : raw11104step0Labels = labelEmbedding6 ∘ raw11104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11104step0 raw11104step0Labels raw11104step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw11105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw11105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw11105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11105step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11105 raw11105Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw11105 raw11105Labels = mixedMoment B raw11105step0 raw11105step0Labels := by
      have hz : ∀ j, raw11105 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11105step0 = (fun i j => raw11105 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11105step0 raw11105; decide +kernel
      have hl : raw11105step0Labels = raw11105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11105 raw11105Labels permutation520 hz
    mixedMoment B raw11105step0 raw11105step0Labels = mixedMoment B raw11105step1 raw11105step1Labels := by
      have hz : ∀ j, raw11105step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11105step1 = (fun i j => raw11105step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11105step1 raw11105step0; decide +kernel
      have hl : raw11105step1Labels = raw11105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11105step0 raw11105step0Labels permutation104 hz
    mixedMoment B raw11105step1 raw11105step1Labels = mixedMoment B raw11105step2 raw11105step2Labels := by
      have ha : raw11105step2 = (fun i j => raw11105step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11105step2 raw11105step1; decide +kernel
      have hl : raw11105step2Labels = raw11105step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11105step1 raw11105step1Labels permutation29 permutation2
    mixedMoment B raw11105step2 raw11105step2Labels = mixedMoment B raw11105step3 raw11105step3Labels := by
      have ha : raw11105step3 = -raw11105step2 := by apply Matrix.ext; change ∀ i j, raw11105step3 i j = -(raw11105step2 i j); unfold raw11105step3 raw11105step2; decide +kernel
      have hl : raw11105step3Labels = raw11105step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw11106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11106step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11106step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11106step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11106step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11106 raw11106Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw11106 raw11106Labels = mixedMoment B raw11106step0 raw11106step0Labels := by
      have hz : ∀ j, raw11106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11106step0 = (fun i j => raw11106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11106step0 raw11106; decide +kernel
      have hl : raw11106step0Labels = raw11106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11106 raw11106Labels permutation434 hz
    mixedMoment B raw11106step0 raw11106step0Labels = mixedMoment B raw11106step1 raw11106step1Labels := by
      have ha : raw11106step1 = (fun i j => raw11106step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11106step1 raw11106step0; decide +kernel
      have hl : raw11106step1Labels = raw11106step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11106step0 raw11106step0Labels permutation50 permutation5
    mixedMoment B raw11106step1 raw11106step1Labels = mixedMoment B raw11106step2 raw11106step2Labels := by
      have ha : raw11106step2 = -raw11106step1 := by apply Matrix.ext; change ∀ i j, raw11106step2 i j = -(raw11106step1 i j); unfold raw11106step2 raw11106step1; decide +kernel
      have hl : raw11106step2Labels = raw11106step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11106step2 raw11106step2Labels = mixedMoment B raw11106step3 raw11106step3Labels := by
      have ha : raw11106step3 = raw11106step2 := by apply Matrix.ext; unfold raw11106step3 raw11106step2; decide +kernel
      have hl : raw11106step2Labels = labelEmbedding8 ∘ raw11106step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11106step2 raw11106step2Labels raw11106step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw11107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11107step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11107 raw11107Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw11107 raw11107Labels = mixedMoment B raw11107step0 raw11107step0Labels := by
      have hz : ∀ j, raw11107 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11107step0 = (fun i j => raw11107 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11107step0 raw11107; decide +kernel
      have hl : raw11107step0Labels = raw11107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11107 raw11107Labels permutation434 hz
    mixedMoment B raw11107step0 raw11107step0Labels = mixedMoment B raw11107step1 raw11107step1Labels := by
      have ha : raw11107step1 = (fun i j => raw11107step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11107step1 raw11107step0; decide +kernel
      have hl : raw11107step1Labels = raw11107step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11107step0 raw11107step0Labels permutation40 permutation3
    mixedMoment B raw11107step1 raw11107step1Labels = mixedMoment B raw11107step2 raw11107step2Labels := by
      have ha : raw11107step2 = raw11107step1 := by apply Matrix.ext; unfold raw11107step2 raw11107step1; decide +kernel
      have hl : raw11107step1Labels = labelEmbedding6 ∘ raw11107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11107step1 raw11107step1Labels raw11107step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw11108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11108step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11108 raw11108Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw11108 raw11108Labels = mixedMoment B raw11108step0 raw11108step0Labels := by
      have hz : ∀ j, raw11108 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11108step0 = (fun i j => raw11108 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11108step0 raw11108; decide +kernel
      have hl : raw11108step0Labels = raw11108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11108 raw11108Labels permutation434 hz
    mixedMoment B raw11108step0 raw11108step0Labels = mixedMoment B raw11108step1 raw11108step1Labels := by
      have ha : raw11108step1 = (fun i j => raw11108step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11108step1 raw11108step0; decide +kernel
      have hl : raw11108step1Labels = raw11108step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11108step0 raw11108step0Labels permutation40 permutation3
    mixedMoment B raw11108step1 raw11108step1Labels = mixedMoment B raw11108step2 raw11108step2Labels := by
      have ha : raw11108step2 = raw11108step1 := by apply Matrix.ext; unfold raw11108step2 raw11108step1; decide +kernel
      have hl : raw11108step1Labels = labelEmbedding6 ∘ raw11108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11108step1 raw11108step1Labels raw11108step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw11109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11109step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11109 raw11109Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw11109 raw11109Labels = mixedMoment B raw11109step0 raw11109step0Labels := by
      have ha : raw11109step0 = (fun i j => raw11109 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11109step0 raw11109; decide +kernel
      have hl : raw11109step0Labels = raw11109Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11109 raw11109Labels permutation208 permutation3
    mixedMoment B raw11109step0 raw11109step0Labels = mixedMoment B raw11109step1 raw11109step1Labels := by
      have ha : raw11109step1 = raw11109step0 := by apply Matrix.ext; unfold raw11109step1 raw11109step0; decide +kernel
      have hl : raw11109step0Labels = labelEmbedding6 ∘ raw11109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11109step0 raw11109step0Labels raw11109step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw11110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw11110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11110step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11110step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11110step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11110 raw11110Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw11110 raw11110Labels = mixedMoment B raw11110step0 raw11110step0Labels := by
      have hz : ∀ j, raw11110 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11110step0 = (fun i j => raw11110 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11110step0 raw11110; decide +kernel
      have hl : raw11110step0Labels = raw11110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11110 raw11110Labels permutation520 hz
    mixedMoment B raw11110step0 raw11110step0Labels = mixedMoment B raw11110step1 raw11110step1Labels := by
      have hz : ∀ j, raw11110step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11110step1 = (fun i j => raw11110step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11110step1 raw11110step0; decide +kernel
      have hl : raw11110step1Labels = raw11110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11110step0 raw11110step0Labels permutation104 hz
    mixedMoment B raw11110step1 raw11110step1Labels = mixedMoment B raw11110step2 raw11110step2Labels := by
      have ha : raw11110step2 = (fun i j => raw11110step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11110step2 raw11110step1; decide +kernel
      have hl : raw11110step2Labels = raw11110step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11110step1 raw11110step1Labels permutation10 permutation3
    mixedMoment B raw11110step2 raw11110step2Labels = mixedMoment B raw11110step3 raw11110step3Labels := by
      have ha : raw11110step3 = raw11110step2 := by apply Matrix.ext; unfold raw11110step3 raw11110step2; decide +kernel
      have hl : raw11110step2Labels = labelEmbedding6 ∘ raw11110step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11110step2 raw11110step2Labels raw11110step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw11111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11111step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11111step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11111step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11111step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11111 raw11111Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw11111 raw11111Labels = mixedMoment B raw11111step0 raw11111step0Labels := by
      have hz : ∀ j, raw11111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11111step0 = (fun i j => raw11111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11111step0 raw11111; decide +kernel
      have hl : raw11111step0Labels = raw11111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11111 raw11111Labels permutation434 hz
    mixedMoment B raw11111step0 raw11111step0Labels = mixedMoment B raw11111step1 raw11111step1Labels := by
      have ha : raw11111step1 = (fun i j => raw11111step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11111step1 raw11111step0; decide +kernel
      have hl : raw11111step1Labels = raw11111step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11111step0 raw11111step0Labels permutation53 permutation5
    mixedMoment B raw11111step1 raw11111step1Labels = mixedMoment B raw11111step2 raw11111step2Labels := by
      have ha : raw11111step2 = -raw11111step1 := by apply Matrix.ext; change ∀ i j, raw11111step2 i j = -(raw11111step1 i j); unfold raw11111step2 raw11111step1; decide +kernel
      have hl : raw11111step2Labels = raw11111step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11111step2 raw11111step2Labels = mixedMoment B raw11111step3 raw11111step3Labels := by
      have ha : raw11111step3 = raw11111step2 := by apply Matrix.ext; unfold raw11111step3 raw11111step2; decide +kernel
      have hl : raw11111step2Labels = labelEmbedding8 ∘ raw11111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11111step2 raw11111step2Labels raw11111step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw11112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11112step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11112step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11112 raw11112Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw11112 raw11112Labels = mixedMoment B raw11112step0 raw11112step0Labels := by
      have hz : ∀ j, raw11112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11112step0 = (fun i j => raw11112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11112step0 raw11112; decide +kernel
      have hl : raw11112step0Labels = raw11112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11112 raw11112Labels permutation434 hz
    mixedMoment B raw11112step0 raw11112step0Labels = mixedMoment B raw11112step1 raw11112step1Labels := by
      have ha : raw11112step1 = (fun i j => raw11112step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11112step1 raw11112step0; decide +kernel
      have hl : raw11112step1Labels = raw11112step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11112step0 raw11112step0Labels permutation34 permutation3
    mixedMoment B raw11112step1 raw11112step1Labels = mixedMoment B raw11112step2 raw11112step2Labels := by
      have ha : raw11112step2 = raw11112step1 := by apply Matrix.ext; unfold raw11112step2 raw11112step1; decide +kernel
      have hl : raw11112step1Labels = labelEmbedding6 ∘ raw11112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11112step1 raw11112step1Labels raw11112step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw11113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11113step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11113step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11113 raw11113Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw11113 raw11113Labels = mixedMoment B raw11113step0 raw11113step0Labels := by
      have hz : ∀ j, raw11113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11113step0 = (fun i j => raw11113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11113step0 raw11113; decide +kernel
      have hl : raw11113step0Labels = raw11113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11113 raw11113Labels permutation434 hz
    mixedMoment B raw11113step0 raw11113step0Labels = mixedMoment B raw11113step1 raw11113step1Labels := by
      have ha : raw11113step1 = (fun i j => raw11113step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11113step1 raw11113step0; decide +kernel
      have hl : raw11113step1Labels = raw11113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11113step0 raw11113step0Labels permutation34 permutation3
    mixedMoment B raw11113step1 raw11113step1Labels = mixedMoment B raw11113step2 raw11113step2Labels := by
      have ha : raw11113step2 = raw11113step1 := by apply Matrix.ext; unfold raw11113step2 raw11113step1; decide +kernel
      have hl : raw11113step1Labels = labelEmbedding6 ∘ raw11113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11113step1 raw11113step1Labels raw11113step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw11114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11114step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11114 raw11114Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw11114 raw11114Labels = mixedMoment B raw11114step0 raw11114step0Labels := by
      have ha : raw11114step0 = (fun i j => raw11114 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11114step0 raw11114; decide +kernel
      have hl : raw11114step0Labels = raw11114Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11114 raw11114Labels permutation202 permutation3
    mixedMoment B raw11114step0 raw11114step0Labels = mixedMoment B raw11114step1 raw11114step1Labels := by
      have ha : raw11114step1 = raw11114step0 := by apply Matrix.ext; unfold raw11114step1 raw11114step0; decide +kernel
      have hl : raw11114step0Labels = labelEmbedding6 ∘ raw11114step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11114step0 raw11114step0Labels raw11114step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw11115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw11115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11115step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11115step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11115step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11115 raw11115Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw11115 raw11115Labels = mixedMoment B raw11115step0 raw11115step0Labels := by
      have hz : ∀ j, raw11115 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11115step0 = (fun i j => raw11115 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11115step0 raw11115; decide +kernel
      have hl : raw11115step0Labels = raw11115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11115 raw11115Labels permutation520 hz
    mixedMoment B raw11115step0 raw11115step0Labels = mixedMoment B raw11115step1 raw11115step1Labels := by
      have hz : ∀ j, raw11115step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11115step1 = (fun i j => raw11115step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11115step1 raw11115step0; decide +kernel
      have hl : raw11115step1Labels = raw11115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11115step0 raw11115step0Labels permutation104 hz
    mixedMoment B raw11115step1 raw11115step1Labels = mixedMoment B raw11115step2 raw11115step2Labels := by
      have ha : raw11115step2 = (fun i j => raw11115step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11115step2 raw11115step1; decide +kernel
      have hl : raw11115step2Labels = raw11115step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11115step1 raw11115step1Labels permutation8 permutation3
    mixedMoment B raw11115step2 raw11115step2Labels = mixedMoment B raw11115step3 raw11115step3Labels := by
      have ha : raw11115step3 = raw11115step2 := by apply Matrix.ext; unfold raw11115step3 raw11115step2; decide +kernel
      have hl : raw11115step2Labels = labelEmbedding6 ∘ raw11115step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11115step2 raw11115step2Labels raw11115step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw11116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11116step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11116step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11116step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11116step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11116 raw11116Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw11116 raw11116Labels = mixedMoment B raw11116step0 raw11116step0Labels := by
      have hz : ∀ j, raw11116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11116step0 = (fun i j => raw11116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11116step0 raw11116; decide +kernel
      have hl : raw11116step0Labels = raw11116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11116 raw11116Labels permutation434 hz
    mixedMoment B raw11116step0 raw11116step0Labels = mixedMoment B raw11116step1 raw11116step1Labels := by
      have ha : raw11116step1 = (fun i j => raw11116step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11116step1 raw11116step0; decide +kernel
      have hl : raw11116step1Labels = raw11116step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11116step0 raw11116step0Labels permutation51 permutation5
    mixedMoment B raw11116step1 raw11116step1Labels = mixedMoment B raw11116step2 raw11116step2Labels := by
      have ha : raw11116step2 = -raw11116step1 := by apply Matrix.ext; change ∀ i j, raw11116step2 i j = -(raw11116step1 i j); unfold raw11116step2 raw11116step1; decide +kernel
      have hl : raw11116step2Labels = raw11116step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11116step2 raw11116step2Labels = mixedMoment B raw11116step3 raw11116step3Labels := by
      have ha : raw11116step3 = raw11116step2 := by apply Matrix.ext; unfold raw11116step3 raw11116step2; decide +kernel
      have hl : raw11116step2Labels = labelEmbedding8 ∘ raw11116step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11116step2 raw11116step2Labels raw11116step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw11117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11117step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11117step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11117 raw11117Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw11117 raw11117Labels = mixedMoment B raw11117step0 raw11117step0Labels := by
      have ha : raw11117step0 = (fun i j => raw11117 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11117step0 raw11117; decide +kernel
      have hl : raw11117step0Labels = raw11117Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11117 raw11117Labels permutation152 permutation3
    mixedMoment B raw11117step0 raw11117step0Labels = mixedMoment B raw11117step1 raw11117step1Labels := by
      have ha : raw11117step1 = raw11117step0 := by apply Matrix.ext; unfold raw11117step1 raw11117step0; decide +kernel
      have hl : raw11117step0Labels = labelEmbedding6 ∘ raw11117step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11117step0 raw11117step0Labels raw11117step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

def raw11118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11118step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11118 raw11118Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw11118 raw11118Labels = mixedMoment B raw11118step0 raw11118step0Labels := by
      have ha : raw11118step0 = (fun i j => raw11118 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11118step0 raw11118; decide +kernel
      have hl : raw11118step0Labels = raw11118Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11118 raw11118Labels permutation152 permutation3
    mixedMoment B raw11118step0 raw11118step0Labels = mixedMoment B raw11118step1 raw11118step1Labels := by
      have ha : raw11118step1 = raw11118step0 := by apply Matrix.ext; unfold raw11118step1 raw11118step0; decide +kernel
      have hl : raw11118step0Labels = labelEmbedding6 ∘ raw11118step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11118step0 raw11118step0Labels raw11118step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw11119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11119step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11119step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11119 raw11119Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw11119 raw11119Labels = mixedMoment B raw11119step0 raw11119step0Labels := by
      have ha : raw11119step0 = (fun i j => raw11119 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11119step0 raw11119; decide +kernel
      have hl : raw11119step0Labels = raw11119Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11119 raw11119Labels permutation176 permutation3
    mixedMoment B raw11119step0 raw11119step0Labels = mixedMoment B raw11119step1 raw11119step1Labels := by
      have ha : raw11119step1 = raw11119step0 := by apply Matrix.ext; unfold raw11119step1 raw11119step0; decide +kernel
      have hl : raw11119step0Labels = labelEmbedding6 ∘ raw11119step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11119step0 raw11119step0Labels raw11119step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw11120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11120step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11120step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11120 raw11120Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw11120 raw11120Labels = mixedMoment B raw11120step0 raw11120step0Labels := by
      have hz : ∀ j, raw11120 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11120step0 = (fun i j => raw11120 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11120step0 raw11120; decide +kernel
      have hl : raw11120step0Labels = raw11120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11120 raw11120Labels permutation520 hz
    mixedMoment B raw11120step0 raw11120step0Labels = mixedMoment B raw11120step1 raw11120step1Labels := by
      have ha : raw11120step1 = (fun i j => raw11120step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11120step1 raw11120step0; decide +kernel
      have hl : raw11120step1Labels = raw11120step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11120step0 raw11120step0Labels permutation32 permutation3
    mixedMoment B raw11120step1 raw11120step1Labels = mixedMoment B raw11120step2 raw11120step2Labels := by
      have ha : raw11120step2 = raw11120step1 := by apply Matrix.ext; unfold raw11120step2 raw11120step1; decide +kernel
      have hl : raw11120step1Labels = labelEmbedding6 ∘ raw11120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11120step1 raw11120step1Labels raw11120step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw11121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11121step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11121step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11121step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11121 raw11121Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw11121 raw11121Labels = mixedMoment B raw11121step0 raw11121step0Labels := by
      have ha : raw11121step0 = (fun i j => raw11121 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11121step0 raw11121; decide +kernel
      have hl : raw11121step0Labels = raw11121Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11121 raw11121Labels permutation246 permutation5
    mixedMoment B raw11121step0 raw11121step0Labels = mixedMoment B raw11121step1 raw11121step1Labels := by
      have ha : raw11121step1 = -raw11121step0 := by apply Matrix.ext; change ∀ i j, raw11121step1 i j = -(raw11121step0 i j); unfold raw11121step1 raw11121step0; decide +kernel
      have hl : raw11121step1Labels = raw11121step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11121step1 raw11121step1Labels = mixedMoment B raw11121step2 raw11121step2Labels := by
      have ha : raw11121step2 = raw11121step1 := by apply Matrix.ext; unfold raw11121step2 raw11121step1; decide +kernel
      have hl : raw11121step1Labels = labelEmbedding8 ∘ raw11121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11121step1 raw11121step1Labels raw11121step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw11122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11122 raw11122Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw11122 raw11122Labels = mixedMoment B raw11122step0 raw11122step0Labels := by
      have hz : ∀ j, raw11122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11122step0 = (fun i j => raw11122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11122step0 raw11122; decide +kernel
      have hl : raw11122step0Labels = raw11122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11122 raw11122Labels permutation434 hz
    mixedMoment B raw11122step0 raw11122step0Labels = mixedMoment B raw11122step1 raw11122step1Labels := by
      have ha : raw11122step1 = (fun i j => raw11122step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11122step1 raw11122step0; decide +kernel
      have hl : raw11122step1Labels = raw11122step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11122step0 raw11122step0Labels permutation33 permutation3
    mixedMoment B raw11122step1 raw11122step1Labels = mixedMoment B raw11122step2 raw11122step2Labels := by
      have ha : raw11122step2 = raw11122step1 := by apply Matrix.ext; unfold raw11122step2 raw11122step1; decide +kernel
      have hl : raw11122step1Labels = labelEmbedding6 ∘ raw11122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11122step1 raw11122step1Labels raw11122step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

def raw11123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11123step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11123 raw11123Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw11123 raw11123Labels = mixedMoment B raw11123step0 raw11123step0Labels := by
      have hz : ∀ j, raw11123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11123step0 = (fun i j => raw11123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11123step0 raw11123; decide +kernel
      have hl : raw11123step0Labels = raw11123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11123 raw11123Labels permutation434 hz
    mixedMoment B raw11123step0 raw11123step0Labels = mixedMoment B raw11123step1 raw11123step1Labels := by
      have ha : raw11123step1 = (fun i j => raw11123step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11123step1 raw11123step0; decide +kernel
      have hl : raw11123step1Labels = raw11123step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11123step0 raw11123step0Labels permutation33 permutation3
    mixedMoment B raw11123step1 raw11123step1Labels = mixedMoment B raw11123step2 raw11123step2Labels := by
      have ha : raw11123step2 = raw11123step1 := by apply Matrix.ext; unfold raw11123step2 raw11123step1; decide +kernel
      have hl : raw11123step1Labels = labelEmbedding6 ∘ raw11123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11123step1 raw11123step1Labels raw11123step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw11124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11124 raw11124Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw11124 raw11124Labels = mixedMoment B raw11124step0 raw11124step0Labels := by
      have hz : ∀ j, raw11124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11124step0 = (fun i j => raw11124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11124step0 raw11124; decide +kernel
      have hl : raw11124step0Labels = raw11124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11124 raw11124Labels permutation434 hz
    mixedMoment B raw11124step0 raw11124step0Labels = mixedMoment B raw11124step1 raw11124step1Labels := by
      have ha : raw11124step1 = (fun i j => raw11124step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11124step1 raw11124step0; decide +kernel
      have hl : raw11124step1Labels = raw11124step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11124step0 raw11124step0Labels permutation39 permutation3
    mixedMoment B raw11124step1 raw11124step1Labels = mixedMoment B raw11124step2 raw11124step2Labels := by
      have ha : raw11124step2 = raw11124step1 := by apply Matrix.ext; unfold raw11124step2 raw11124step1; decide +kernel
      have hl : raw11124step1Labels = labelEmbedding6 ∘ raw11124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11124step1 raw11124step1Labels raw11124step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw11125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11125step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11125 raw11125Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw11125 raw11125Labels = mixedMoment B raw11125step0 raw11125step0Labels := by
      have ha : raw11125step0 = (fun i j => raw11125 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11125step0 raw11125; decide +kernel
      have hl : raw11125step0Labels = raw11125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11125 raw11125Labels permutation201 permutation3
    mixedMoment B raw11125step0 raw11125step0Labels = mixedMoment B raw11125step1 raw11125step1Labels := by
      have ha : raw11125step1 = raw11125step0 := by apply Matrix.ext; unfold raw11125step1 raw11125step0; decide +kernel
      have hl : raw11125step0Labels = labelEmbedding6 ∘ raw11125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11125step0 raw11125step0Labels raw11125step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

def raw11126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw11126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw11126step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11126step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11126 raw11126Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw11126 raw11126Labels = mixedMoment B raw11126step0 raw11126step0Labels := by
      have hz : ∀ j, raw11126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11126step0 = (fun i j => raw11126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11126step0 raw11126; decide +kernel
      have hl : raw11126step0Labels = raw11126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11126 raw11126Labels permutation434 hz
    mixedMoment B raw11126step0 raw11126step0Labels = mixedMoment B raw11126step1 raw11126step1Labels := by
      have ha : raw11126step1 = (fun i j => raw11126step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11126step1 raw11126step0; decide +kernel
      have hl : raw11126step1Labels = raw11126step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11126step0 raw11126step0Labels permutation50 permutation5
    mixedMoment B raw11126step1 raw11126step1Labels = mixedMoment B raw11126step2 raw11126step2Labels := by
      have ha : raw11126step2 = -raw11126step1 := by apply Matrix.ext; change ∀ i j, raw11126step2 i j = -(raw11126step1 i j); unfold raw11126step2 raw11126step1; decide +kernel
      have hl : raw11126step2Labels = raw11126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11126step2 raw11126step2Labels = mixedMoment B raw11126step3 raw11126step3Labels := by
      have ha : raw11126step3 = raw11126step2 := by apply Matrix.ext; unfold raw11126step3 raw11126step2; decide +kernel
      have hl : raw11126step2Labels = labelEmbedding8 ∘ raw11126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11126step2 raw11126step2Labels raw11126step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw11127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11127step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11127 raw11127Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw11127 raw11127Labels = mixedMoment B raw11127step0 raw11127step0Labels := by
      have hz : ∀ j, raw11127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11127step0 = (fun i j => raw11127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11127step0 raw11127; decide +kernel
      have hl : raw11127step0Labels = raw11127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11127 raw11127Labels permutation434 hz
    mixedMoment B raw11127step0 raw11127step0Labels = mixedMoment B raw11127step1 raw11127step1Labels := by
      have ha : raw11127step1 = (fun i j => raw11127step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11127step1 raw11127step0; decide +kernel
      have hl : raw11127step1Labels = raw11127step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11127step0 raw11127step0Labels permutation32 permutation3
    mixedMoment B raw11127step1 raw11127step1Labels = mixedMoment B raw11127step2 raw11127step2Labels := by
      have ha : raw11127step2 = raw11127step1 := by apply Matrix.ext; unfold raw11127step2 raw11127step1; decide +kernel
      have hl : raw11127step1Labels = labelEmbedding6 ∘ raw11127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11127step1 raw11127step1Labels raw11127step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

def raw11128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11128step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11128 raw11128Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw11128 raw11128Labels = mixedMoment B raw11128step0 raw11128step0Labels := by
      have hz : ∀ j, raw11128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11128step0 = (fun i j => raw11128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11128step0 raw11128; decide +kernel
      have hl : raw11128step0Labels = raw11128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11128 raw11128Labels permutation434 hz
    mixedMoment B raw11128step0 raw11128step0Labels = mixedMoment B raw11128step1 raw11128step1Labels := by
      have ha : raw11128step1 = (fun i j => raw11128step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11128step1 raw11128step0; decide +kernel
      have hl : raw11128step1Labels = raw11128step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11128step0 raw11128step0Labels permutation32 permutation3
    mixedMoment B raw11128step1 raw11128step1Labels = mixedMoment B raw11128step2 raw11128step2Labels := by
      have ha : raw11128step2 = raw11128step1 := by apply Matrix.ext; unfold raw11128step2 raw11128step1; decide +kernel
      have hl : raw11128step1Labels = labelEmbedding6 ∘ raw11128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11128step1 raw11128step1Labels raw11128step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw11129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11129step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11129 raw11129Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw11129 raw11129Labels = mixedMoment B raw11129step0 raw11129step0Labels := by
      have hz : ∀ j, raw11129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11129step0 = (fun i j => raw11129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11129step0 raw11129; decide +kernel
      have hl : raw11129step0Labels = raw11129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11129 raw11129Labels permutation434 hz
    mixedMoment B raw11129step0 raw11129step0Labels = mixedMoment B raw11129step1 raw11129step1Labels := by
      have ha : raw11129step1 = (fun i j => raw11129step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11129step1 raw11129step0; decide +kernel
      have hl : raw11129step1Labels = raw11129step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11129step0 raw11129step0Labels permutation38 permutation3
    mixedMoment B raw11129step1 raw11129step1Labels = mixedMoment B raw11129step2 raw11129step2Labels := by
      have ha : raw11129step2 = raw11129step1 := by apply Matrix.ext; unfold raw11129step2 raw11129step1; decide +kernel
      have hl : raw11129step1Labels = labelEmbedding6 ∘ raw11129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11129step1 raw11129step1Labels raw11129step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw11130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11130step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11130 raw11130Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw11130 raw11130Labels = mixedMoment B raw11130step0 raw11130step0Labels := by
      have ha : raw11130step0 = (fun i j => raw11130 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11130step0 raw11130; decide +kernel
      have hl : raw11130step0Labels = raw11130Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11130 raw11130Labels permutation200 permutation3
    mixedMoment B raw11130step0 raw11130step0Labels = mixedMoment B raw11130step1 raw11130step1Labels := by
      have ha : raw11130step1 = raw11130step0 := by apply Matrix.ext; unfold raw11130step1 raw11130step0; decide +kernel
      have hl : raw11130step0Labels = labelEmbedding6 ∘ raw11130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11130step0 raw11130step0Labels raw11130step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

def raw11131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw11131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw11131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw11131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11131step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11131step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11131 raw11131Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw11131 raw11131Labels = mixedMoment B raw11131step0 raw11131step0Labels := by
      have hz : ∀ j, raw11131 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11131step0 = (fun i j => raw11131 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11131step0 raw11131; decide +kernel
      have hl : raw11131step0Labels = raw11131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11131 raw11131Labels permutation520 hz
    mixedMoment B raw11131step0 raw11131step0Labels = mixedMoment B raw11131step1 raw11131step1Labels := by
      have hz : ∀ j, raw11131step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11131step1 = (fun i j => raw11131step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11131step1 raw11131step0; decide +kernel
      have hl : raw11131step1Labels = raw11131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11131step0 raw11131step0Labels permutation104 hz
    mixedMoment B raw11131step1 raw11131step1Labels = mixedMoment B raw11131step2 raw11131step2Labels := by
      have ha : raw11131step2 = (fun i j => raw11131step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11131step2 raw11131step1; decide +kernel
      have hl : raw11131step2Labels = raw11131step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11131step1 raw11131step1Labels permutation8 permutation3
    mixedMoment B raw11131step2 raw11131step2Labels = mixedMoment B raw11131step3 raw11131step3Labels := by
      have ha : raw11131step3 = raw11131step2 := by apply Matrix.ext; unfold raw11131step3 raw11131step2; decide +kernel
      have hl : raw11131step2Labels = labelEmbedding6 ∘ raw11131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11131step2 raw11131step2Labels raw11131step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw11132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11132Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11132step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11132 raw11132Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw11132 raw11132Labels = mixedMoment B raw11132step0 raw11132step0Labels := by
      have hz : ∀ j, raw11132 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11132step0 = (fun i j => raw11132 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11132step0 raw11132; decide +kernel
      have hl : raw11132step0Labels = raw11132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11132 raw11132Labels permutation434 hz
    mixedMoment B raw11132step0 raw11132step0Labels = mixedMoment B raw11132step1 raw11132step1Labels := by
      have ha : raw11132step1 = (fun i j => raw11132step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11132step1 raw11132step0; decide +kernel
      have hl : raw11132step1Labels = raw11132step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11132step0 raw11132step0Labels permutation32 permutation3
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw11133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11133step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11133 raw11133Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw11133 raw11133Labels = mixedMoment B raw11133step0 raw11133step0Labels := by
      have hz : ∀ j, raw11133 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11133step0 = (fun i j => raw11133 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11133step0 raw11133; decide +kernel
      have hl : raw11133step0Labels = raw11133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11133 raw11133Labels permutation434 hz
    mixedMoment B raw11133step0 raw11133step0Labels = mixedMoment B raw11133step1 raw11133step1Labels := by
      have ha : raw11133step1 = (fun i j => raw11133step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11133step1 raw11133step0; decide +kernel
      have hl : raw11133step1Labels = raw11133step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11133step0 raw11133step0Labels permutation38 permutation3
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw11134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11134 raw11134Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw11134 raw11134Labels = mixedMoment B raw11134step0 raw11134step0Labels := by
      have ha : raw11134step0 = (fun i j => raw11134 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11134step0 raw11134; decide +kernel
      have hl : raw11134step0Labels = raw11134Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11134 raw11134Labels permutation200 permutation3
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw11135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11135step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw11135step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11135 raw11135Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw11135 raw11135Labels = mixedMoment B raw11135step0 raw11135step0Labels := by
      have hz : ∀ j, raw11135 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11135step0 = (fun i j => raw11135 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11135step0 raw11135; decide +kernel
      have hl : raw11135step0Labels = raw11135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11135 raw11135Labels permutation520 hz
    mixedMoment B raw11135step0 raw11135step0Labels = mixedMoment B raw11135step1 raw11135step1Labels := by
      have hz : ∀ j, raw11135step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11135step1 = (fun i j => raw11135step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11135step1 raw11135step0; decide +kernel
      have hl : raw11135step1Labels = raw11135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11135step0 raw11135step0Labels permutation104 hz
    mixedMoment B raw11135step1 raw11135step1Labels = mixedMoment B raw11135step2 raw11135step2Labels := by
      have ha : raw11135step2 = (fun i j => raw11135step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11135step2 raw11135step1; decide +kernel
      have hl : raw11135step2Labels = raw11135step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11135step1 raw11135step1Labels permutation8 permutation3
    _ = mixedMoment B node3912 node3912Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
