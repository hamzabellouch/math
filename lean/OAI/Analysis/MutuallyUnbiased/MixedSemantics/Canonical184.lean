import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23552step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23552step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23552step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23552step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23552step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23552step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23552step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23552 raw23552Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw23552 raw23552Labels = mixedMoment B raw23552step0 raw23552step0Labels := by
      have hz : ∀ j, raw23552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23552step0 = (fun i j => raw23552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23552step0 raw23552; decide +kernel
      have hl : raw23552step0Labels = raw23552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23552 raw23552Labels permutation434 hz
    mixedMoment B raw23552step0 raw23552step0Labels = mixedMoment B raw23552step1 raw23552step1Labels := by
      have hz : ∀ j, raw23552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23552step1 = (fun i j => raw23552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23552step1 raw23552step0; decide +kernel
      have hl : raw23552step1Labels = raw23552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23552step0 raw23552step0Labels permutation80 hz
    mixedMoment B raw23552step1 raw23552step1Labels = mixedMoment B raw23552step2 raw23552step2Labels := by
      have ha : raw23552step2 = (fun i j => raw23552step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23552step2 raw23552step1; decide +kernel
      have hl : raw23552step2Labels = raw23552step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23552step1 raw23552step1Labels permutation9 permutation7
    mixedMoment B raw23552step2 raw23552step2Labels = mixedMoment B raw23552step3 raw23552step3Labels := by
      have ha : raw23552step3 = -raw23552step2 := by apply Matrix.ext; change ∀ i j, raw23552step3 i j = -(raw23552step2 i j); unfold raw23552step3 raw23552step2; decide +kernel
      have hl : raw23552step3Labels = raw23552step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23552step3 raw23552step3Labels = mixedMoment B raw23552step4 raw23552step4Labels := by
      have ha : raw23552step4 = raw23552step3 := by apply Matrix.ext; unfold raw23552step4 raw23552step3; decide +kernel
      have hl : raw23552step3Labels = labelEmbedding1 ∘ raw23552step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23552step3 raw23552step3Labels raw23552step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw23553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23553step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23553step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23553step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23553step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23553step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23553step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23553 raw23553Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw23553 raw23553Labels = mixedMoment B raw23553step0 raw23553step0Labels := by
      have hz : ∀ j, raw23553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23553step0 = (fun i j => raw23553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23553step0 raw23553; decide +kernel
      have hl : raw23553step0Labels = raw23553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23553 raw23553Labels permutation434 hz
    mixedMoment B raw23553step0 raw23553step0Labels = mixedMoment B raw23553step1 raw23553step1Labels := by
      have hz : ∀ j, raw23553step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23553step1 = (fun i j => raw23553step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23553step1 raw23553step0; decide +kernel
      have hl : raw23553step1Labels = raw23553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23553step0 raw23553step0Labels permutation56 hz
    mixedMoment B raw23553step1 raw23553step1Labels = mixedMoment B raw23553step2 raw23553step2Labels := by
      have ha : raw23553step2 = (fun i j => raw23553step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23553step2 raw23553step1; decide +kernel
      have hl : raw23553step2Labels = raw23553step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23553step1 raw23553step1Labels permutation9 permutation7
    mixedMoment B raw23553step2 raw23553step2Labels = mixedMoment B raw23553step3 raw23553step3Labels := by
      have ha : raw23553step3 = -raw23553step2 := by apply Matrix.ext; change ∀ i j, raw23553step3 i j = -(raw23553step2 i j); unfold raw23553step3 raw23553step2; decide +kernel
      have hl : raw23553step3Labels = raw23553step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23553step3 raw23553step3Labels = mixedMoment B raw23553step4 raw23553step4Labels := by
      have ha : raw23553step4 = raw23553step3 := by apply Matrix.ext; unfold raw23553step4 raw23553step3; decide +kernel
      have hl : raw23553step3Labels = labelEmbedding1 ∘ raw23553step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23553step3 raw23553step3Labels raw23553step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw23554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23554step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23554step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23554step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23554step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23554step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23554step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23554 raw23554Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw23554 raw23554Labels = mixedMoment B raw23554step0 raw23554step0Labels := by
      have hz : ∀ j, raw23554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23554step0 = (fun i j => raw23554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23554step0 raw23554; decide +kernel
      have hl : raw23554step0Labels = raw23554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23554 raw23554Labels permutation346 hz
    mixedMoment B raw23554step0 raw23554step0Labels = mixedMoment B raw23554step1 raw23554step1Labels := by
      have hz : ∀ j, raw23554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23554step1 = (fun i j => raw23554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23554step1 raw23554step0; decide +kernel
      have hl : raw23554step1Labels = raw23554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23554step0 raw23554step0Labels permutation56 hz
    mixedMoment B raw23554step1 raw23554step1Labels = mixedMoment B raw23554step2 raw23554step2Labels := by
      have ha : raw23554step2 = (fun i j => raw23554step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23554step2 raw23554step1; decide +kernel
      have hl : raw23554step2Labels = raw23554step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23554step1 raw23554step1Labels permutation9 permutation7
    mixedMoment B raw23554step2 raw23554step2Labels = mixedMoment B raw23554step3 raw23554step3Labels := by
      have ha : raw23554step3 = -raw23554step2 := by apply Matrix.ext; change ∀ i j, raw23554step3 i j = -(raw23554step2 i j); unfold raw23554step3 raw23554step2; decide +kernel
      have hl : raw23554step3Labels = raw23554step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23554step3 raw23554step3Labels = mixedMoment B raw23554step4 raw23554step4Labels := by
      have ha : raw23554step4 = raw23554step3 := by apply Matrix.ext; unfold raw23554step4 raw23554step3; decide +kernel
      have hl : raw23554step3Labels = labelEmbedding1 ∘ raw23554step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23554step3 raw23554step3Labels raw23554step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw23555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23555step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23555step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw23555step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw23555step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23555step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw23555step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23555step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw23555step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23555 raw23555Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw23555 raw23555Labels = mixedMoment B raw23555step0 raw23555step0Labels := by
      have hz : ∀ j, raw23555 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23555step0 = (fun i j => raw23555 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23555step0 raw23555; decide +kernel
      have hl : raw23555step0Labels = raw23555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23555 raw23555Labels permutation434 hz
    mixedMoment B raw23555step0 raw23555step0Labels = mixedMoment B raw23555step1 raw23555step1Labels := by
      have hz : ∀ j, raw23555step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23555step1 = (fun i j => raw23555step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23555step1 raw23555step0; decide +kernel
      have hl : raw23555step1Labels = raw23555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23555step0 raw23555step0Labels permutation80 hz
    mixedMoment B raw23555step1 raw23555step1Labels = mixedMoment B raw23555step2 raw23555step2Labels := by
      have hz : ∀ j, raw23555step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23555step2 = (fun i j => raw23555step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23555step2 raw23555step1; decide +kernel
      have hl : raw23555step2Labels = raw23555step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23555step1 raw23555step1Labels permutation14 hz
    mixedMoment B raw23555step2 raw23555step2Labels = mixedMoment B raw23555step3 raw23555step3Labels := by
      have ha : raw23555step3 = (fun i j => raw23555step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23555step3 raw23555step2; decide +kernel
      have hl : raw23555step3Labels = raw23555step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23555step2 raw23555step2Labels permutation3 permutation7
    mixedMoment B raw23555step3 raw23555step3Labels = mixedMoment B raw23555step4 raw23555step4Labels := by
      have ha : raw23555step4 = -raw23555step3 := by apply Matrix.ext; change ∀ i j, raw23555step4 i j = -(raw23555step3 i j); unfold raw23555step4 raw23555step3; decide +kernel
      have hl : raw23555step4Labels = raw23555step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23555step4 raw23555step4Labels = mixedMoment B raw23555step5 raw23555step5Labels := by
      have ha : raw23555step5 = raw23555step4 := by apply Matrix.ext; unfold raw23555step5 raw23555step4; decide +kernel
      have hl : raw23555step4Labels = labelEmbedding1 ∘ raw23555step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23555step4 raw23555step4Labels raw23555step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1754 node1754Labels := by rfl

def raw23556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23556step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw23556step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw23556step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23556step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw23556step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23556step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw23556step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23556 raw23556Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw23556 raw23556Labels = mixedMoment B raw23556step0 raw23556step0Labels := by
      have hz : ∀ j, raw23556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23556step0 = (fun i j => raw23556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23556step0 raw23556; decide +kernel
      have hl : raw23556step0Labels = raw23556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23556 raw23556Labels permutation434 hz
    mixedMoment B raw23556step0 raw23556step0Labels = mixedMoment B raw23556step1 raw23556step1Labels := by
      have hz : ∀ j, raw23556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23556step1 = (fun i j => raw23556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23556step1 raw23556step0; decide +kernel
      have hl : raw23556step1Labels = raw23556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23556step0 raw23556step0Labels permutation80 hz
    mixedMoment B raw23556step1 raw23556step1Labels = mixedMoment B raw23556step2 raw23556step2Labels := by
      have hz : ∀ j, raw23556step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23556step2 = (fun i j => raw23556step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23556step2 raw23556step1; decide +kernel
      have hl : raw23556step2Labels = raw23556step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23556step1 raw23556step1Labels permutation14 hz
    mixedMoment B raw23556step2 raw23556step2Labels = mixedMoment B raw23556step3 raw23556step3Labels := by
      have ha : raw23556step3 = (fun i j => raw23556step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23556step3 raw23556step2; decide +kernel
      have hl : raw23556step3Labels = raw23556step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23556step2 raw23556step2Labels permutation3 permutation7
    mixedMoment B raw23556step3 raw23556step3Labels = mixedMoment B raw23556step4 raw23556step4Labels := by
      have ha : raw23556step4 = -raw23556step3 := by apply Matrix.ext; change ∀ i j, raw23556step4 i j = -(raw23556step3 i j); unfold raw23556step4 raw23556step3; decide +kernel
      have hl : raw23556step4Labels = raw23556step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23556step4 raw23556step4Labels = mixedMoment B raw23556step5 raw23556step5Labels := by
      have ha : raw23556step5 = raw23556step4 := by apply Matrix.ext; unfold raw23556step5 raw23556step4; decide +kernel
      have hl : raw23556step4Labels = labelEmbedding1 ∘ raw23556step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23556step4 raw23556step4Labels raw23556step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

def raw23557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw23557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw23557step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23557 raw23557Labels = mixedMoment B node1095 node1095Labels := by
  calc
    mixedMoment B raw23557 raw23557Labels = mixedMoment B raw23557step0 raw23557step0Labels := by
      have hz : ∀ j, raw23557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23557step0 = (fun i j => raw23557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23557step0 raw23557; decide +kernel
      have hl : raw23557step0Labels = raw23557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23557 raw23557Labels permutation434 hz
    mixedMoment B raw23557step0 raw23557step0Labels = mixedMoment B raw23557step1 raw23557step1Labels := by
      have hz : ∀ j, raw23557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23557step1 = (fun i j => raw23557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23557step1 raw23557step0; decide +kernel
      have hl : raw23557step1Labels = raw23557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23557step0 raw23557step0Labels permutation80 hz
    mixedMoment B raw23557step1 raw23557step1Labels = mixedMoment B raw23557step2 raw23557step2Labels := by
      have hz : ∀ j, raw23557step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23557step2 = (fun i j => raw23557step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23557step2 raw23557step1; decide +kernel
      have hl : raw23557step2Labels = raw23557step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23557step1 raw23557step1Labels permutation14 hz
    mixedMoment B raw23557step2 raw23557step2Labels = mixedMoment B raw23557step3 raw23557step3Labels := by
      have ha : raw23557step3 = (fun i j => raw23557step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23557step3 raw23557step2; decide +kernel
      have hl : raw23557step3Labels = raw23557step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23557step2 raw23557step2Labels permutation3 permutation2
    _ = mixedMoment B node1095 node1095Labels := by rfl

def raw23558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23558 raw23558Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw23558 raw23558Labels = mixedMoment B raw23558step0 raw23558step0Labels := by
      have hz : ∀ j, raw23558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23558step0 = (fun i j => raw23558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23558step0 raw23558; decide +kernel
      have hl : raw23558step0Labels = raw23558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23558 raw23558Labels permutation434 hz
    mixedMoment B raw23558step0 raw23558step0Labels = mixedMoment B raw23558step1 raw23558step1Labels := by
      have hz : ∀ j, raw23558step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23558step1 = (fun i j => raw23558step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23558step1 raw23558step0; decide +kernel
      have hl : raw23558step1Labels = raw23558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23558step0 raw23558step0Labels permutation80 hz
    mixedMoment B raw23558step1 raw23558step1Labels = mixedMoment B raw23558step2 raw23558step2Labels := by
      have ha : raw23558step2 = (fun i j => raw23558step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23558step2 raw23558step1; decide +kernel
      have hl : raw23558step2Labels = raw23558step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23558step1 raw23558step1Labels permutation9 permutation2
    _ = mixedMoment B node608 node608Labels := by rfl

def raw23559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23559 raw23559Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw23559 raw23559Labels = mixedMoment B raw23559step0 raw23559step0Labels := by
      have hz : ∀ j, raw23559 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23559step0 = (fun i j => raw23559 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23559step0 raw23559; decide +kernel
      have hl : raw23559step0Labels = raw23559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23559 raw23559Labels permutation434 hz
    mixedMoment B raw23559step0 raw23559step0Labels = mixedMoment B raw23559step1 raw23559step1Labels := by
      have hz : ∀ j, raw23559step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23559step1 = (fun i j => raw23559step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23559step1 raw23559step0; decide +kernel
      have hl : raw23559step1Labels = raw23559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23559step0 raw23559step0Labels permutation56 hz
    mixedMoment B raw23559step1 raw23559step1Labels = mixedMoment B raw23559step2 raw23559step2Labels := by
      have ha : raw23559step2 = (fun i j => raw23559step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23559step2 raw23559step1; decide +kernel
      have hl : raw23559step2Labels = raw23559step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23559step1 raw23559step1Labels permutation9 permutation2
    _ = mixedMoment B node608 node608Labels := by rfl

def raw23560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23560 raw23560Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw23560 raw23560Labels = mixedMoment B raw23560step0 raw23560step0Labels := by
      have hz : ∀ j, raw23560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23560step0 = (fun i j => raw23560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23560step0 raw23560; decide +kernel
      have hl : raw23560step0Labels = raw23560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23560 raw23560Labels permutation346 hz
    mixedMoment B raw23560step0 raw23560step0Labels = mixedMoment B raw23560step1 raw23560step1Labels := by
      have hz : ∀ j, raw23560step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23560step1 = (fun i j => raw23560step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23560step1 raw23560step0; decide +kernel
      have hl : raw23560step1Labels = raw23560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23560step0 raw23560step0Labels permutation56 hz
    mixedMoment B raw23560step1 raw23560step1Labels = mixedMoment B raw23560step2 raw23560step2Labels := by
      have ha : raw23560step2 = (fun i j => raw23560step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23560step2 raw23560step1; decide +kernel
      have hl : raw23560step2Labels = raw23560step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23560step1 raw23560step1Labels permutation9 permutation2
    _ = mixedMoment B node608 node608Labels := by rfl

def raw23561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23561step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, -1, -2], ![2, -1, -1]]
def raw23561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw23561step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23561 raw23561Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw23561 raw23561Labels = mixedMoment B raw23561step0 raw23561step0Labels := by
      have hz : ∀ j, raw23561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23561step0 = (fun i j => raw23561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23561step0 raw23561; decide +kernel
      have hl : raw23561step0Labels = raw23561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23561 raw23561Labels permutation434 hz
    mixedMoment B raw23561step0 raw23561step0Labels = mixedMoment B raw23561step1 raw23561step1Labels := by
      have hz : ∀ j, raw23561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23561step1 = (fun i j => raw23561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23561step1 raw23561step0; decide +kernel
      have hl : raw23561step1Labels = raw23561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23561step0 raw23561step0Labels permutation80 hz
    mixedMoment B raw23561step1 raw23561step1Labels = mixedMoment B raw23561step2 raw23561step2Labels := by
      have hz : ∀ j, raw23561step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23561step2 = (fun i j => raw23561step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23561step2 raw23561step1; decide +kernel
      have hl : raw23561step2Labels = raw23561step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23561step1 raw23561step1Labels permutation14 hz
    mixedMoment B raw23561step2 raw23561step2Labels = mixedMoment B raw23561step3 raw23561step3Labels := by
      have ha : raw23561step3 = (fun i j => raw23561step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23561step3 raw23561step2; decide +kernel
      have hl : raw23561step3Labels = raw23561step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23561step2 raw23561step2Labels permutation3 permutation2
    _ = mixedMoment B node619 node619Labels := by rfl

def raw23562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw23562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23562 raw23562Labels = mixedMoment B node620 node620Labels := by
  calc
    mixedMoment B raw23562 raw23562Labels = mixedMoment B raw23562step0 raw23562step0Labels := by
      have hz : ∀ j, raw23562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23562step0 = (fun i j => raw23562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23562step0 raw23562; decide +kernel
      have hl : raw23562step0Labels = raw23562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23562 raw23562Labels permutation434 hz
    mixedMoment B raw23562step0 raw23562step0Labels = mixedMoment B raw23562step1 raw23562step1Labels := by
      have hz : ∀ j, raw23562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23562step1 = (fun i j => raw23562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23562step1 raw23562step0; decide +kernel
      have hl : raw23562step1Labels = raw23562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23562step0 raw23562step0Labels permutation80 hz
    mixedMoment B raw23562step1 raw23562step1Labels = mixedMoment B raw23562step2 raw23562step2Labels := by
      have hz : ∀ j, raw23562step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23562step2 = (fun i j => raw23562step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23562step2 raw23562step1; decide +kernel
      have hl : raw23562step2Labels = raw23562step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23562step1 raw23562step1Labels permutation14 hz
    _ = mixedMoment B node620 node620Labels := by rfl

def raw23563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23563step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23563step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23563step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23563 raw23563Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw23563 raw23563Labels = mixedMoment B raw23563step0 raw23563step0Labels := by
      have hz : ∀ j, raw23563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23563step0 = (fun i j => raw23563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23563step0 raw23563; decide +kernel
      have hl : raw23563step0Labels = raw23563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23563 raw23563Labels permutation434 hz
    mixedMoment B raw23563step0 raw23563step0Labels = mixedMoment B raw23563step1 raw23563step1Labels := by
      have hz : ∀ j, raw23563step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23563step1 = (fun i j => raw23563step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23563step1 raw23563step0; decide +kernel
      have hl : raw23563step1Labels = raw23563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23563step0 raw23563step0Labels permutation56 hz
    mixedMoment B raw23563step1 raw23563step1Labels = mixedMoment B raw23563step2 raw23563step2Labels := by
      have ha : raw23563step2 = (fun i j => raw23563step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23563step2 raw23563step1; decide +kernel
      have hl : raw23563step2Labels = raw23563step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23563step1 raw23563step1Labels permutation9 permutation6
    mixedMoment B raw23563step2 raw23563step2Labels = mixedMoment B raw23563step3 raw23563step3Labels := by
      have ha : raw23563step3 = raw23563step2 := by apply Matrix.ext; unfold raw23563step3 raw23563step2; decide +kernel
      have hl : raw23563step2Labels = labelEmbedding9 ∘ raw23563step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23563step2 raw23563step2Labels raw23563step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw23564 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23564step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23564 raw23564Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw23564 raw23564Labels = mixedMoment B raw23564step0 raw23564step0Labels := by
      have hz : ∀ j, raw23564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23564step0 = (fun i j => raw23564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23564step0 raw23564; decide +kernel
      have hl : raw23564step0Labels = raw23564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23564 raw23564Labels permutation434 hz
    mixedMoment B raw23564step0 raw23564step0Labels = mixedMoment B raw23564step1 raw23564step1Labels := by
      have ha : raw23564step1 = (fun i j => raw23564step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23564step1 raw23564step0; decide +kernel
      have hl : raw23564step1Labels = raw23564step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23564step0 raw23564step0Labels permutation33 permutation6
    mixedMoment B raw23564step1 raw23564step1Labels = mixedMoment B raw23564step2 raw23564step2Labels := by
      have ha : raw23564step2 = raw23564step1 := by apply Matrix.ext; unfold raw23564step2 raw23564step1; decide +kernel
      have hl : raw23564step1Labels = labelEmbedding9 ∘ raw23564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23564step1 raw23564step1Labels raw23564step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw23565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23565step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23565step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23565 raw23565Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw23565 raw23565Labels = mixedMoment B raw23565step0 raw23565step0Labels := by
      have hz : ∀ j, raw23565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23565step0 = (fun i j => raw23565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23565step0 raw23565; decide +kernel
      have hl : raw23565step0Labels = raw23565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23565 raw23565Labels permutation346 hz
    mixedMoment B raw23565step0 raw23565step0Labels = mixedMoment B raw23565step1 raw23565step1Labels := by
      have hz : ∀ j, raw23565step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23565step1 = (fun i j => raw23565step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23565step1 raw23565step0; decide +kernel
      have hl : raw23565step1Labels = raw23565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23565step0 raw23565step0Labels permutation56 hz
    mixedMoment B raw23565step1 raw23565step1Labels = mixedMoment B raw23565step2 raw23565step2Labels := by
      have ha : raw23565step2 = (fun i j => raw23565step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23565step2 raw23565step1; decide +kernel
      have hl : raw23565step2Labels = raw23565step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23565step1 raw23565step1Labels permutation9 permutation6
    mixedMoment B raw23565step2 raw23565step2Labels = mixedMoment B raw23565step3 raw23565step3Labels := by
      have ha : raw23565step3 = raw23565step2 := by apply Matrix.ext; unfold raw23565step3 raw23565step2; decide +kernel
      have hl : raw23565step2Labels = labelEmbedding9 ∘ raw23565step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23565step2 raw23565step2Labels raw23565step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw23566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23566step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23566step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23566 raw23566Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw23566 raw23566Labels = mixedMoment B raw23566step0 raw23566step0Labels := by
      have hz : ∀ j, raw23566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23566step0 = (fun i j => raw23566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23566step0 raw23566; decide +kernel
      have hl : raw23566step0Labels = raw23566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23566 raw23566Labels permutation346 hz
    mixedMoment B raw23566step0 raw23566step0Labels = mixedMoment B raw23566step1 raw23566step1Labels := by
      have ha : raw23566step1 = (fun i j => raw23566step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23566step1 raw23566step0; decide +kernel
      have hl : raw23566step1Labels = raw23566step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23566step0 raw23566step0Labels permutation33 permutation6
    mixedMoment B raw23566step1 raw23566step1Labels = mixedMoment B raw23566step2 raw23566step2Labels := by
      have ha : raw23566step2 = raw23566step1 := by apply Matrix.ext; unfold raw23566step2 raw23566step1; decide +kernel
      have hl : raw23566step1Labels = labelEmbedding9 ∘ raw23566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23566step1 raw23566step1Labels raw23566step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw23567 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23567step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23567 raw23567Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw23567 raw23567Labels = mixedMoment B raw23567step0 raw23567step0Labels := by
      have hz : ∀ j, raw23567 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23567step0 = (fun i j => raw23567 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23567step0 raw23567; decide +kernel
      have hl : raw23567step0Labels = raw23567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23567 raw23567Labels permutation265 hz
    mixedMoment B raw23567step0 raw23567step0Labels = mixedMoment B raw23567step1 raw23567step1Labels := by
      have ha : raw23567step1 = (fun i j => raw23567step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23567step1 raw23567step0; decide +kernel
      have hl : raw23567step1Labels = raw23567step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23567step0 raw23567step0Labels permutation33 permutation6
    mixedMoment B raw23567step1 raw23567step1Labels = mixedMoment B raw23567step2 raw23567step2Labels := by
      have ha : raw23567step2 = raw23567step1 := by apply Matrix.ext; unfold raw23567step2 raw23567step1; decide +kernel
      have hl : raw23567step1Labels = labelEmbedding9 ∘ raw23567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23567step1 raw23567step1Labels raw23567step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw23568 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![0, -2, 2], ![0, -2, 2]]
def raw23568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-2, 2], ![-2, 2]]
def raw23568step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw23568step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw23568step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw23568step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw23568step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23568 raw23568Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw23568 raw23568Labels = mixedMoment B raw23568step0 raw23568step0Labels := by
      have hz : ∀ j, raw23568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23568step0 = (fun i j => raw23568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23568step0 raw23568; decide +kernel
      have hl : raw23568step0Labels = raw23568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23568 raw23568Labels permutation434 hz
    mixedMoment B raw23568step0 raw23568step0Labels = mixedMoment B raw23568step1 raw23568step1Labels := by
      have hz : ∀ j, raw23568step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23568step1 = (fun i j => raw23568step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23568step1 raw23568step0; decide +kernel
      have hl : raw23568step1Labels = raw23568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23568step0 raw23568step0Labels permutation80 hz
    mixedMoment B raw23568step1 raw23568step1Labels = mixedMoment B raw23568step2 raw23568step2Labels := by
      have hz : ∀ j, raw23568step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23568step2 = (fun i j => raw23568step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23568step2 raw23568step1; decide +kernel
      have hl : raw23568step2Labels = raw23568step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23568step1 raw23568step1Labels permutation14 hz
    mixedMoment B raw23568step2 raw23568step2Labels = mixedMoment B raw23568step3 raw23568step3Labels := by
      have hz : ∀ i, raw23568step2 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw23568step3 = (fun i j => raw23568step2 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw23568step3 raw23568step2; decide +kernel
      have hl : raw23568step3Labels = (fun j => raw23568step2Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23568step2 raw23568step2Labels permutation2 hz
    mixedMoment B raw23568step3 raw23568step3Labels = mixedMoment B raw23568step4 raw23568step4Labels := by
      have ha : raw23568step4 = -raw23568step3 := by apply Matrix.ext; change ∀ i j, raw23568step4 i j = -(raw23568step3 i j); unfold raw23568step4 raw23568step3; decide +kernel
      have hl : raw23568step4Labels = raw23568step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23568step4 raw23568step4Labels = mixedMoment B raw23568step5 raw23568step5Labels := by
      have ha : raw23568step5 = raw23568step4 := by apply Matrix.ext; unfold raw23568step5 raw23568step4; decide +kernel
      have hl : raw23568step4Labels = labelEmbedding3 ∘ raw23568step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23568step4 raw23568step4Labels raw23568step5Labels labelEmbedding3 hl
    _ = mixedMoment B node4071 node4071Labels := by rfl

def raw23569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23569step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23569 raw23569Labels = mixedMoment B node4432 node4432Labels := by
  calc
    mixedMoment B raw23569 raw23569Labels = mixedMoment B raw23569step0 raw23569step0Labels := by
      have hz : ∀ j, raw23569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23569step0 = (fun i j => raw23569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23569step0 raw23569; decide +kernel
      have hl : raw23569step0Labels = raw23569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23569 raw23569Labels permutation434 hz
    mixedMoment B raw23569step0 raw23569step0Labels = mixedMoment B raw23569step1 raw23569step1Labels := by
      have hz : ∀ j, raw23569step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23569step1 = (fun i j => raw23569step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23569step1 raw23569step0; decide +kernel
      have hl : raw23569step1Labels = raw23569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23569step0 raw23569step0Labels permutation80 hz
    mixedMoment B raw23569step1 raw23569step1Labels = mixedMoment B raw23569step2 raw23569step2Labels := by
      have ha : raw23569step2 = (fun i j => raw23569step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23569step2 raw23569step1; decide +kernel
      have hl : raw23569step2Labels = raw23569step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23569step1 raw23569step1Labels permutation8 permutation6
    mixedMoment B raw23569step2 raw23569step2Labels = mixedMoment B raw23569step3 raw23569step3Labels := by
      have ha : raw23569step3 = raw23569step2 := by apply Matrix.ext; unfold raw23569step3 raw23569step2; decide +kernel
      have hl : raw23569step2Labels = labelEmbedding9 ∘ raw23569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23569step2 raw23569step2Labels raw23569step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4432 node4432Labels := by rfl

def raw23570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23570step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23570step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23570 raw23570Labels = mixedMoment B node4432 node4432Labels := by
  calc
    mixedMoment B raw23570 raw23570Labels = mixedMoment B raw23570step0 raw23570step0Labels := by
      have hz : ∀ j, raw23570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23570step0 = (fun i j => raw23570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23570step0 raw23570; decide +kernel
      have hl : raw23570step0Labels = raw23570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23570 raw23570Labels permutation434 hz
    mixedMoment B raw23570step0 raw23570step0Labels = mixedMoment B raw23570step1 raw23570step1Labels := by
      have hz : ∀ j, raw23570step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23570step1 = (fun i j => raw23570step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23570step1 raw23570step0; decide +kernel
      have hl : raw23570step1Labels = raw23570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23570step0 raw23570step0Labels permutation56 hz
    mixedMoment B raw23570step1 raw23570step1Labels = mixedMoment B raw23570step2 raw23570step2Labels := by
      have ha : raw23570step2 = (fun i j => raw23570step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23570step2 raw23570step1; decide +kernel
      have hl : raw23570step2Labels = raw23570step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23570step1 raw23570step1Labels permutation8 permutation6
    mixedMoment B raw23570step2 raw23570step2Labels = mixedMoment B raw23570step3 raw23570step3Labels := by
      have ha : raw23570step3 = raw23570step2 := by apply Matrix.ext; unfold raw23570step3 raw23570step2; decide +kernel
      have hl : raw23570step2Labels = labelEmbedding9 ∘ raw23570step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23570step2 raw23570step2Labels raw23570step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4432 node4432Labels := by rfl

def raw23571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23571 raw23571Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw23571 raw23571Labels = mixedMoment B raw23571step0 raw23571step0Labels := by
      have hz : ∀ j, raw23571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23571step0 = (fun i j => raw23571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23571step0 raw23571; decide +kernel
      have hl : raw23571step0Labels = raw23571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23571 raw23571Labels permutation346 hz
    mixedMoment B raw23571step0 raw23571step0Labels = mixedMoment B raw23571step1 raw23571step1Labels := by
      have ha : raw23571step1 = (fun i j => raw23571step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23571step1 raw23571step0; decide +kernel
      have hl : raw23571step1Labels = raw23571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23571step0 raw23571step0Labels permutation33 permutation2
    _ = mixedMoment B node2006 node2006Labels := by rfl

def raw23572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23572 raw23572Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw23572 raw23572Labels = mixedMoment B raw23572step0 raw23572step0Labels := by
      have hz : ∀ j, raw23572 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23572step0 = (fun i j => raw23572 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23572step0 raw23572; decide +kernel
      have hl : raw23572step0Labels = raw23572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23572 raw23572Labels permutation265 hz
    mixedMoment B raw23572step0 raw23572step0Labels = mixedMoment B raw23572step1 raw23572step1Labels := by
      have ha : raw23572step1 = (fun i j => raw23572step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23572step1 raw23572step0; decide +kernel
      have hl : raw23572step1Labels = raw23572step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23572step0 raw23572step0Labels permutation33 permutation2
    _ = mixedMoment B node2006 node2006Labels := by rfl

def raw23573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23573 raw23573Labels = mixedMoment B node1953 node1953Labels := by
  calc
    mixedMoment B raw23573 raw23573Labels = mixedMoment B raw23573step0 raw23573step0Labels := by
      have hz : ∀ j, raw23573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23573step0 = (fun i j => raw23573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23573step0 raw23573; decide +kernel
      have hl : raw23573step0Labels = raw23573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23573 raw23573Labels permutation346 hz
    mixedMoment B raw23573step0 raw23573step0Labels = mixedMoment B raw23573step1 raw23573step1Labels := by
      have hz : ∀ j, raw23573step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23573step1 = (fun i j => raw23573step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23573step1 raw23573step0; decide +kernel
      have hl : raw23573step1Labels = raw23573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23573step0 raw23573step0Labels permutation56 hz
    mixedMoment B raw23573step1 raw23573step1Labels = mixedMoment B raw23573step2 raw23573step2Labels := by
      have ha : raw23573step2 = (fun i j => raw23573step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23573step2 raw23573step1; decide +kernel
      have hl : raw23573step2Labels = raw23573step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23573step1 raw23573step1Labels permutation9 permutation2
    _ = mixedMoment B node1953 node1953Labels := by rfl

def raw23574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw23574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw23574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw23574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23574 raw23574Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw23574 raw23574Labels = mixedMoment B raw23574step0 raw23574step0Labels := by
      have hz : ∀ j, raw23574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23574step0 = (fun i j => raw23574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23574step0 raw23574; decide +kernel
      have hl : raw23574step0Labels = raw23574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23574 raw23574Labels permutation346 hz
    mixedMoment B raw23574step0 raw23574step0Labels = mixedMoment B raw23574step1 raw23574step1Labels := by
      have hz : ∀ j, raw23574step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23574step1 = (fun i j => raw23574step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23574step1 raw23574step0; decide +kernel
      have hl : raw23574step1Labels = raw23574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23574step0 raw23574step0Labels permutation56 hz
    mixedMoment B raw23574step1 raw23574step1Labels = mixedMoment B raw23574step2 raw23574step2Labels := by
      have ha : raw23574step2 = (fun i j => raw23574step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23574step2 raw23574step1; decide +kernel
      have hl : raw23574step2Labels = raw23574step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23574step1 raw23574step1Labels permutation9 permutation2
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw23575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw23575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23575 raw23575Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw23575 raw23575Labels = mixedMoment B raw23575step0 raw23575step0Labels := by
      have hz : ∀ j, raw23575 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23575step0 = (fun i j => raw23575 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23575step0 raw23575; decide +kernel
      have hl : raw23575step0Labels = raw23575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23575 raw23575Labels permutation346 hz
    mixedMoment B raw23575step0 raw23575step0Labels = mixedMoment B raw23575step1 raw23575step1Labels := by
      have ha : raw23575step1 = (fun i j => raw23575step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23575step1 raw23575step0; decide +kernel
      have hl : raw23575step1Labels = raw23575step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23575step0 raw23575step0Labels permutation39 permutation2
    _ = mixedMoment B node882 node882Labels := by rfl

def raw23576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw23576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23576 raw23576Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw23576 raw23576Labels = mixedMoment B raw23576step0 raw23576step0Labels := by
      have hz : ∀ j, raw23576 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23576step0 = (fun i j => raw23576 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23576step0 raw23576; decide +kernel
      have hl : raw23576step0Labels = raw23576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23576 raw23576Labels permutation265 hz
    mixedMoment B raw23576step0 raw23576step0Labels = mixedMoment B raw23576step1 raw23576step1Labels := by
      have ha : raw23576step1 = (fun i j => raw23576step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23576step1 raw23576step0; decide +kernel
      have hl : raw23576step1Labels = raw23576step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23576step0 raw23576step0Labels permutation39 permutation2
    _ = mixedMoment B node882 node882Labels := by rfl

def raw23577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3], ![2, -1, -1]]
def raw23577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3], ![2, -1, -1]]
def raw23577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![3, 0, -3], ![2, -1, -1]]
def raw23577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw23577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23577 raw23577Labels = mixedMoment B node895 node895Labels := by
  calc
    mixedMoment B raw23577 raw23577Labels = mixedMoment B raw23577step0 raw23577step0Labels := by
      have hz : ∀ j, raw23577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23577step0 = (fun i j => raw23577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23577step0 raw23577; decide +kernel
      have hl : raw23577step0Labels = raw23577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23577 raw23577Labels permutation346 hz
    mixedMoment B raw23577step0 raw23577step0Labels = mixedMoment B raw23577step1 raw23577step1Labels := by
      have hz : ∀ j, raw23577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23577step1 = (fun i j => raw23577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23577step1 raw23577step0; decide +kernel
      have hl : raw23577step1Labels = raw23577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23577step0 raw23577step0Labels permutation56 hz
    mixedMoment B raw23577step1 raw23577step1Labels = mixedMoment B raw23577step2 raw23577step2Labels := by
      have ha : raw23577step2 = (fun i j => raw23577step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23577step2 raw23577step1; decide +kernel
      have hl : raw23577step2Labels = raw23577step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23577step1 raw23577step1Labels permutation9 permutation2
    _ = mixedMoment B node895 node895Labels := by rfl

def raw23578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw23578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw23578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw23578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23578 raw23578Labels = mixedMoment B node897 node897Labels := by
  calc
    mixedMoment B raw23578 raw23578Labels = mixedMoment B raw23578step0 raw23578step0Labels := by
      have hz : ∀ j, raw23578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23578step0 = (fun i j => raw23578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23578step0 raw23578; decide +kernel
      have hl : raw23578step0Labels = raw23578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23578 raw23578Labels permutation346 hz
    mixedMoment B raw23578step0 raw23578step0Labels = mixedMoment B raw23578step1 raw23578step1Labels := by
      have hz : ∀ j, raw23578step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23578step1 = (fun i j => raw23578step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23578step1 raw23578step0; decide +kernel
      have hl : raw23578step1Labels = raw23578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23578step0 raw23578step0Labels permutation56 hz
    _ = mixedMoment B node897 node897Labels := by rfl

def raw23579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23579 raw23579Labels = mixedMoment B node4790 node4790Labels := by
  calc
    mixedMoment B raw23579 raw23579Labels = mixedMoment B raw23579step0 raw23579step0Labels := by
      have hz : ∀ j, raw23579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23579step0 = (fun i j => raw23579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23579step0 raw23579; decide +kernel
      have hl : raw23579step0Labels = raw23579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23579 raw23579Labels permutation346 hz
    _ = mixedMoment B node4790 node4790Labels := by rfl

def raw23580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23580 raw23580Labels = mixedMoment B node4790 node4790Labels := by
  calc
    mixedMoment B raw23580 raw23580Labels = mixedMoment B raw23580step0 raw23580step0Labels := by
      have hz : ∀ j, raw23580 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23580step0 = (fun i j => raw23580 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23580step0 raw23580; decide +kernel
      have hl : raw23580step0Labels = raw23580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23580 raw23580Labels permutation265 hz
    _ = mixedMoment B node4790 node4790Labels := by rfl

def raw23581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw23581step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw23581step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw23581step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23581 raw23581Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw23581 raw23581Labels = mixedMoment B raw23581step0 raw23581step0Labels := by
      have hz : ∀ j, raw23581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23581step0 = (fun i j => raw23581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23581step0 raw23581; decide +kernel
      have hl : raw23581step0Labels = raw23581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23581 raw23581Labels permutation346 hz
    mixedMoment B raw23581step0 raw23581step0Labels = mixedMoment B raw23581step1 raw23581step1Labels := by
      have hz : ∀ j, raw23581step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23581step1 = (fun i j => raw23581step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23581step1 raw23581step0; decide +kernel
      have hl : raw23581step1Labels = raw23581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23581step0 raw23581step0Labels permutation56 hz
    mixedMoment B raw23581step1 raw23581step1Labels = mixedMoment B raw23581step2 raw23581step2Labels := by
      have hz : ∀ i, raw23581step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw23581step2 = (fun i j => raw23581step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw23581step2 raw23581step1; decide +kernel
      have hl : raw23581step2Labels = (fun j => raw23581step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23581step1 raw23581step1Labels permutation4 hz
    mixedMoment B raw23581step2 raw23581step2Labels = mixedMoment B raw23581step3 raw23581step3Labels := by
      have ha : raw23581step3 = raw23581step2 := by apply Matrix.ext; unfold raw23581step3 raw23581step2; decide +kernel
      have hl : raw23581step2Labels = labelEmbedding2 ∘ raw23581step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23581step2 raw23581step2Labels raw23581step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw23582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw23582step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23582step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23582step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23582step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23582 raw23582Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw23582 raw23582Labels = mixedMoment B raw23582step0 raw23582step0Labels := by
      have hz : ∀ j, raw23582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23582step0 = (fun i j => raw23582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23582step0 raw23582; decide +kernel
      have hl : raw23582step0Labels = raw23582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23582 raw23582Labels permutation346 hz
    mixedMoment B raw23582step0 raw23582step0Labels = mixedMoment B raw23582step1 raw23582step1Labels := by
      have hz : ∀ j, raw23582step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23582step1 = (fun i j => raw23582step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23582step1 raw23582step0; decide +kernel
      have hl : raw23582step1Labels = raw23582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23582step0 raw23582step0Labels permutation56 hz
    mixedMoment B raw23582step1 raw23582step1Labels = mixedMoment B raw23582step2 raw23582step2Labels := by
      have ha : raw23582step2 = (fun i j => raw23582step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23582step2 raw23582step1; decide +kernel
      have hl : raw23582step2Labels = raw23582step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23582step1 raw23582step1Labels permutation8 permutation7
    mixedMoment B raw23582step2 raw23582step2Labels = mixedMoment B raw23582step3 raw23582step3Labels := by
      have ha : raw23582step3 = -raw23582step2 := by apply Matrix.ext; change ∀ i j, raw23582step3 i j = -(raw23582step2 i j); unfold raw23582step3 raw23582step2; decide +kernel
      have hl : raw23582step3Labels = raw23582step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23582step3 raw23582step3Labels = mixedMoment B raw23582step4 raw23582step4Labels := by
      have ha : raw23582step4 = raw23582step3 := by apply Matrix.ext; unfold raw23582step4 raw23582step3; decide +kernel
      have hl : raw23582step3Labels = labelEmbedding10 ∘ raw23582step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23582step3 raw23582step3Labels raw23582step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw23583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw23583step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23583step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23583step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23583step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23583 raw23583Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw23583 raw23583Labels = mixedMoment B raw23583step0 raw23583step0Labels := by
      have hz : ∀ j, raw23583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23583step0 = (fun i j => raw23583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23583step0 raw23583; decide +kernel
      have hl : raw23583step0Labels = raw23583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23583 raw23583Labels permutation346 hz
    mixedMoment B raw23583step0 raw23583step0Labels = mixedMoment B raw23583step1 raw23583step1Labels := by
      have hz : ∀ j, raw23583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23583step1 = (fun i j => raw23583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23583step1 raw23583step0; decide +kernel
      have hl : raw23583step1Labels = raw23583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23583step0 raw23583step0Labels permutation56 hz
    mixedMoment B raw23583step1 raw23583step1Labels = mixedMoment B raw23583step2 raw23583step2Labels := by
      have ha : raw23583step2 = (fun i j => raw23583step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23583step2 raw23583step1; decide +kernel
      have hl : raw23583step2Labels = raw23583step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23583step1 raw23583step1Labels permutation9 permutation7
    mixedMoment B raw23583step2 raw23583step2Labels = mixedMoment B raw23583step3 raw23583step3Labels := by
      have ha : raw23583step3 = -raw23583step2 := by apply Matrix.ext; change ∀ i j, raw23583step3 i j = -(raw23583step2 i j); unfold raw23583step3 raw23583step2; decide +kernel
      have hl : raw23583step3Labels = raw23583step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23583step3 raw23583step3Labels = mixedMoment B raw23583step4 raw23583step4Labels := by
      have ha : raw23583step4 = raw23583step3 := by apply Matrix.ext; unfold raw23583step4 raw23583step3; decide +kernel
      have hl : raw23583step3Labels = labelEmbedding10 ∘ raw23583step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23583step3 raw23583step3Labels raw23583step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw23584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23584 raw23584Labels = mixedMoment B node4141 node4141Labels := by
  calc
    mixedMoment B raw23584 raw23584Labels = mixedMoment B raw23584step0 raw23584step0Labels := by
      have hz : ∀ j, raw23584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23584step0 = (fun i j => raw23584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23584step0 raw23584; decide +kernel
      have hl : raw23584step0Labels = raw23584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23584 raw23584Labels permutation346 hz
    mixedMoment B raw23584step0 raw23584step0Labels = mixedMoment B raw23584step1 raw23584step1Labels := by
      have ha : raw23584step1 = (fun i j => raw23584step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23584step1 raw23584step0; decide +kernel
      have hl : raw23584step1Labels = raw23584step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23584step0 raw23584step0Labels permutation38 permutation2
    _ = mixedMoment B node4141 node4141Labels := by rfl

def raw23585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23585 raw23585Labels = mixedMoment B node4321 node4321Labels := by
  calc
    mixedMoment B raw23585 raw23585Labels = mixedMoment B raw23585step0 raw23585step0Labels := by
      have ha : raw23585step0 = (fun i j => raw23585 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23585step0 raw23585; decide +kernel
      have hl : raw23585step0Labels = raw23585Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23585 raw23585Labels permutation182 permutation2
    _ = mixedMoment B node4321 node4321Labels := by rfl

def raw23586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23586 raw23586Labels = mixedMoment B node4305 node4305Labels := by
  calc
    mixedMoment B raw23586 raw23586Labels = mixedMoment B raw23586step0 raw23586step0Labels := by
      have hz : ∀ j, raw23586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23586step0 = (fun i j => raw23586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23586step0 raw23586; decide +kernel
      have hl : raw23586step0Labels = raw23586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23586 raw23586Labels permutation346 hz
    mixedMoment B raw23586step0 raw23586step0Labels = mixedMoment B raw23586step1 raw23586step1Labels := by
      have ha : raw23586step1 = (fun i j => raw23586step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23586step1 raw23586step0; decide +kernel
      have hl : raw23586step1Labels = raw23586step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23586step0 raw23586step0Labels permutation38 permutation2
    _ = mixedMoment B node4305 node4305Labels := by rfl

def raw23587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23587 raw23587Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23587 raw23587Labels = mixedMoment B raw23587step0 raw23587step0Labels := by
      have hz : ∀ j, raw23587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23587step0 = (fun i j => raw23587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23587step0 raw23587; decide +kernel
      have hl : raw23587step0Labels = raw23587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23587 raw23587Labels permutation346 hz
    mixedMoment B raw23587step0 raw23587step0Labels = mixedMoment B raw23587step1 raw23587step1Labels := by
      have ha : raw23587step1 = (fun i j => raw23587step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23587step1 raw23587step0; decide +kernel
      have hl : raw23587step1Labels = raw23587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23587step0 raw23587step0Labels permutation38 permutation2
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw23588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23588 raw23588Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23588 raw23588Labels = mixedMoment B raw23588step0 raw23588step0Labels := by
      have hz : ∀ j, raw23588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23588step0 = (fun i j => raw23588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23588step0 raw23588; decide +kernel
      have hl : raw23588step0Labels = raw23588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23588 raw23588Labels permutation346 hz
    mixedMoment B raw23588step0 raw23588step0Labels = mixedMoment B raw23588step1 raw23588step1Labels := by
      have ha : raw23588step1 = (fun i j => raw23588step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23588step1 raw23588step0; decide +kernel
      have hl : raw23588step1Labels = raw23588step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23588step0 raw23588step0Labels permutation39 permutation2
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw23589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23589 raw23589Labels = mixedMoment B node4141 node4141Labels := by
  calc
    mixedMoment B raw23589 raw23589Labels = mixedMoment B raw23589step0 raw23589step0Labels := by
      have hz : ∀ j, raw23589 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23589step0 = (fun i j => raw23589 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23589step0 raw23589; decide +kernel
      have hl : raw23589step0Labels = raw23589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23589 raw23589Labels permutation265 hz
    mixedMoment B raw23589step0 raw23589step0Labels = mixedMoment B raw23589step1 raw23589step1Labels := by
      have ha : raw23589step1 = (fun i j => raw23589step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23589step1 raw23589step0; decide +kernel
      have hl : raw23589step1Labels = raw23589step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23589step0 raw23589step0Labels permutation38 permutation2
    _ = mixedMoment B node4141 node4141Labels := by rfl

def raw23590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23590 raw23590Labels = mixedMoment B node4321 node4321Labels := by
  calc
    mixedMoment B raw23590 raw23590Labels = mixedMoment B raw23590step0 raw23590step0Labels := by
      have ha : raw23590step0 = (fun i j => raw23590 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23590step0 raw23590; decide +kernel
      have hl : raw23590step0Labels = raw23590Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23590 raw23590Labels permutation158 permutation2
    _ = mixedMoment B node4321 node4321Labels := by rfl

def raw23591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23591 raw23591Labels = mixedMoment B node4305 node4305Labels := by
  calc
    mixedMoment B raw23591 raw23591Labels = mixedMoment B raw23591step0 raw23591step0Labels := by
      have hz : ∀ j, raw23591 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23591step0 = (fun i j => raw23591 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23591step0 raw23591; decide +kernel
      have hl : raw23591step0Labels = raw23591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23591 raw23591Labels permutation265 hz
    mixedMoment B raw23591step0 raw23591step0Labels = mixedMoment B raw23591step1 raw23591step1Labels := by
      have ha : raw23591step1 = (fun i j => raw23591step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23591step1 raw23591step0; decide +kernel
      have hl : raw23591step1Labels = raw23591step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23591step0 raw23591step0Labels permutation38 permutation2
    _ = mixedMoment B node4305 node4305Labels := by rfl

def raw23592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23592 raw23592Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23592 raw23592Labels = mixedMoment B raw23592step0 raw23592step0Labels := by
      have hz : ∀ j, raw23592 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23592step0 = (fun i j => raw23592 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23592step0 raw23592; decide +kernel
      have hl : raw23592step0Labels = raw23592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23592 raw23592Labels permutation265 hz
    mixedMoment B raw23592step0 raw23592step0Labels = mixedMoment B raw23592step1 raw23592step1Labels := by
      have ha : raw23592step1 = (fun i j => raw23592step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23592step1 raw23592step0; decide +kernel
      have hl : raw23592step1Labels = raw23592step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23592step0 raw23592step0Labels permutation38 permutation2
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw23593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23593 raw23593Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23593 raw23593Labels = mixedMoment B raw23593step0 raw23593step0Labels := by
      have hz : ∀ j, raw23593 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23593step0 = (fun i j => raw23593 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23593step0 raw23593; decide +kernel
      have hl : raw23593step0Labels = raw23593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23593 raw23593Labels permutation265 hz
    mixedMoment B raw23593step0 raw23593step0Labels = mixedMoment B raw23593step1 raw23593step1Labels := by
      have ha : raw23593step1 = (fun i j => raw23593step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23593step1 raw23593step0; decide +kernel
      have hl : raw23593step1Labels = raw23593step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23593step0 raw23593step0Labels permutation39 permutation2
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw23594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23594 raw23594Labels = mixedMoment B node4167 node4167Labels := by
  calc
    mixedMoment B raw23594 raw23594Labels = mixedMoment B raw23594step0 raw23594step0Labels := by
      have hz : ∀ j, raw23594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23594step0 = (fun i j => raw23594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23594step0 raw23594; decide +kernel
      have hl : raw23594step0Labels = raw23594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23594 raw23594Labels permutation346 hz
    mixedMoment B raw23594step0 raw23594step0Labels = mixedMoment B raw23594step1 raw23594step1Labels := by
      have hz : ∀ j, raw23594step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23594step1 = (fun i j => raw23594step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23594step1 raw23594step0; decide +kernel
      have hl : raw23594step1Labels = raw23594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23594step0 raw23594step0Labels permutation56 hz
    _ = mixedMoment B node4167 node4167Labels := by rfl

def raw23595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23595 raw23595Labels = mixedMoment B node4339 node4339Labels := by
  calc
    mixedMoment B raw23595 raw23595Labels = mixedMoment B raw23595step0 raw23595step0Labels := by
      have hz : ∀ j, raw23595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23595step0 = (fun i j => raw23595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23595step0 raw23595; decide +kernel
      have hl : raw23595step0Labels = raw23595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23595 raw23595Labels permutation346 hz
    _ = mixedMoment B node4339 node4339Labels := by rfl

def raw23596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23596 raw23596Labels = mixedMoment B node4339 node4339Labels := by
  calc
    mixedMoment B raw23596 raw23596Labels = mixedMoment B raw23596step0 raw23596step0Labels := by
      have hz : ∀ j, raw23596 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23596step0 = (fun i j => raw23596 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23596step0 raw23596; decide +kernel
      have hl : raw23596step0Labels = raw23596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23596 raw23596Labels permutation265 hz
    _ = mixedMoment B node4339 node4339Labels := by rfl

def raw23597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23597 raw23597Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw23597 raw23597Labels = mixedMoment B raw23597step0 raw23597step0Labels := by
      have hz : ∀ j, raw23597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23597step0 = (fun i j => raw23597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23597step0 raw23597; decide +kernel
      have hl : raw23597step0Labels = raw23597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23597 raw23597Labels permutation346 hz
    mixedMoment B raw23597step0 raw23597step0Labels = mixedMoment B raw23597step1 raw23597step1Labels := by
      have hz : ∀ j, raw23597step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23597step1 = (fun i j => raw23597step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23597step1 raw23597step0; decide +kernel
      have hl : raw23597step1Labels = raw23597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23597step0 raw23597step0Labels permutation56 hz
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw23598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23598step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23598 raw23598Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw23598 raw23598Labels = mixedMoment B raw23598step0 raw23598step0Labels := by
      have hz : ∀ j, raw23598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23598step0 = (fun i j => raw23598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23598step0 raw23598; decide +kernel
      have hl : raw23598step0Labels = raw23598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23598 raw23598Labels permutation346 hz
    mixedMoment B raw23598step0 raw23598step0Labels = mixedMoment B raw23598step1 raw23598step1Labels := by
      have hz : ∀ j, raw23598step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23598step1 = (fun i j => raw23598step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23598step1 raw23598step0; decide +kernel
      have hl : raw23598step1Labels = raw23598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23598step0 raw23598step0Labels permutation56 hz
    mixedMoment B raw23598step1 raw23598step1Labels = mixedMoment B raw23598step2 raw23598step2Labels := by
      have ha : raw23598step2 = (fun i j => raw23598step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23598step2 raw23598step1; decide +kernel
      have hl : raw23598step2Labels = raw23598step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23598step1 raw23598step1Labels permutation9 permutation2
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw23599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23599 raw23599Labels = mixedMoment B node4148 node4148Labels := by
  calc
    mixedMoment B raw23599 raw23599Labels = mixedMoment B raw23599step0 raw23599step0Labels := by
      have hz : ∀ j, raw23599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23599step0 = (fun i j => raw23599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23599step0 raw23599; decide +kernel
      have hl : raw23599step0Labels = raw23599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23599 raw23599Labels permutation346 hz
    mixedMoment B raw23599step0 raw23599step0Labels = mixedMoment B raw23599step1 raw23599step1Labels := by
      have hz : ∀ j, raw23599step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23599step1 = (fun i j => raw23599step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23599step1 raw23599step0; decide +kernel
      have hl : raw23599step1Labels = raw23599step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23599step0 raw23599step0Labels permutation56 hz
    mixedMoment B raw23599step1 raw23599step1Labels = mixedMoment B raw23599step2 raw23599step2Labels := by
      have ha : raw23599step2 = (fun i j => raw23599step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23599step2 raw23599step1; decide +kernel
      have hl : raw23599step2Labels = raw23599step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23599step1 raw23599step1Labels permutation9 permutation2
    _ = mixedMoment B node4148 node4148Labels := by rfl

def raw23600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23600 raw23600Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw23600 raw23600Labels = mixedMoment B raw23600step0 raw23600step0Labels := by
      have hz : ∀ j, raw23600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23600step0 = (fun i j => raw23600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23600step0 raw23600; decide +kernel
      have hl : raw23600step0Labels = raw23600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23600 raw23600Labels permutation346 hz
    mixedMoment B raw23600step0 raw23600step0Labels = mixedMoment B raw23600step1 raw23600step1Labels := by
      have ha : raw23600step1 = (fun i j => raw23600step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23600step1 raw23600step0; decide +kernel
      have hl : raw23600step1Labels = raw23600step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23600step0 raw23600step0Labels permutation33 permutation2
    _ = mixedMoment B node4325 node4325Labels := by rfl

def raw23601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23601 raw23601Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw23601 raw23601Labels = mixedMoment B raw23601step0 raw23601step0Labels := by
      have hz : ∀ j, raw23601 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23601step0 = (fun i j => raw23601 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23601step0 raw23601; decide +kernel
      have hl : raw23601step0Labels = raw23601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23601 raw23601Labels permutation265 hz
    mixedMoment B raw23601step0 raw23601step0Labels = mixedMoment B raw23601step1 raw23601step1Labels := by
      have ha : raw23601step1 = (fun i j => raw23601step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23601step1 raw23601step0; decide +kernel
      have hl : raw23601step1Labels = raw23601step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23601step0 raw23601step0Labels permutation33 permutation2
    _ = mixedMoment B node4325 node4325Labels := by rfl

def raw23602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23602 raw23602Labels = mixedMoment B node4318 node4318Labels := by
  calc
    mixedMoment B raw23602 raw23602Labels = mixedMoment B raw23602step0 raw23602step0Labels := by
      have hz : ∀ j, raw23602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23602step0 = (fun i j => raw23602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23602step0 raw23602; decide +kernel
      have hl : raw23602step0Labels = raw23602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23602 raw23602Labels permutation346 hz
    mixedMoment B raw23602step0 raw23602step0Labels = mixedMoment B raw23602step1 raw23602step1Labels := by
      have hz : ∀ j, raw23602step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23602step1 = (fun i j => raw23602step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23602step1 raw23602step0; decide +kernel
      have hl : raw23602step1Labels = raw23602step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23602step0 raw23602step0Labels permutation56 hz
    mixedMoment B raw23602step1 raw23602step1Labels = mixedMoment B raw23602step2 raw23602step2Labels := by
      have ha : raw23602step2 = (fun i j => raw23602step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23602step2 raw23602step1; decide +kernel
      have hl : raw23602step2Labels = raw23602step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23602step1 raw23602step1Labels permutation9 permutation2
    _ = mixedMoment B node4318 node4318Labels := by rfl

def raw23603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23603 raw23603Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw23603 raw23603Labels = mixedMoment B raw23603step0 raw23603step0Labels := by
      have hz : ∀ j, raw23603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23603step0 = (fun i j => raw23603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23603step0 raw23603; decide +kernel
      have hl : raw23603step0Labels = raw23603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23603 raw23603Labels permutation346 hz
    mixedMoment B raw23603step0 raw23603step0Labels = mixedMoment B raw23603step1 raw23603step1Labels := by
      have hz : ∀ j, raw23603step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23603step1 = (fun i j => raw23603step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23603step1 raw23603step0; decide +kernel
      have hl : raw23603step1Labels = raw23603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23603step0 raw23603step0Labels permutation56 hz
    mixedMoment B raw23603step1 raw23603step1Labels = mixedMoment B raw23603step2 raw23603step2Labels := by
      have ha : raw23603step2 = (fun i j => raw23603step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23603step2 raw23603step1; decide +kernel
      have hl : raw23603step2Labels = raw23603step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23603step1 raw23603step1Labels permutation9 permutation2
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw23604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23604 raw23604Labels = mixedMoment B node4148 node4148Labels := by
  calc
    mixedMoment B raw23604 raw23604Labels = mixedMoment B raw23604step0 raw23604step0Labels := by
      have hz : ∀ j, raw23604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23604step0 = (fun i j => raw23604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23604step0 raw23604; decide +kernel
      have hl : raw23604step0Labels = raw23604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23604 raw23604Labels permutation346 hz
    mixedMoment B raw23604step0 raw23604step0Labels = mixedMoment B raw23604step1 raw23604step1Labels := by
      have hz : ∀ j, raw23604step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23604step1 = (fun i j => raw23604step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23604step1 raw23604step0; decide +kernel
      have hl : raw23604step1Labels = raw23604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23604step0 raw23604step0Labels permutation56 hz
    _ = mixedMoment B node4148 node4148Labels := by rfl

def raw23605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23605 raw23605Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw23605 raw23605Labels = mixedMoment B raw23605step0 raw23605step0Labels := by
      have hz : ∀ j, raw23605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23605step0 = (fun i j => raw23605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23605step0 raw23605; decide +kernel
      have hl : raw23605step0Labels = raw23605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23605 raw23605Labels permutation346 hz
    _ = mixedMoment B node4325 node4325Labels := by rfl

def raw23606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23606 raw23606Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw23606 raw23606Labels = mixedMoment B raw23606step0 raw23606step0Labels := by
      have hz : ∀ j, raw23606 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23606step0 = (fun i j => raw23606 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23606step0 raw23606; decide +kernel
      have hl : raw23606step0Labels = raw23606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23606 raw23606Labels permutation265 hz
    _ = mixedMoment B node4325 node4325Labels := by rfl

def raw23607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23607 raw23607Labels = mixedMoment B node4318 node4318Labels := by
  calc
    mixedMoment B raw23607 raw23607Labels = mixedMoment B raw23607step0 raw23607step0Labels := by
      have hz : ∀ j, raw23607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23607step0 = (fun i j => raw23607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23607step0 raw23607; decide +kernel
      have hl : raw23607step0Labels = raw23607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23607 raw23607Labels permutation346 hz
    mixedMoment B raw23607step0 raw23607step0Labels = mixedMoment B raw23607step1 raw23607step1Labels := by
      have hz : ∀ j, raw23607step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23607step1 = (fun i j => raw23607step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23607step1 raw23607step0; decide +kernel
      have hl : raw23607step1Labels = raw23607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23607step0 raw23607step0Labels permutation56 hz
    _ = mixedMoment B node4318 node4318Labels := by rfl

def raw23608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23608 raw23608Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw23608 raw23608Labels = mixedMoment B raw23608step0 raw23608step0Labels := by
      have hz : ∀ j, raw23608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23608step0 = (fun i j => raw23608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23608step0 raw23608; decide +kernel
      have hl : raw23608step0Labels = raw23608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23608 raw23608Labels permutation346 hz
    mixedMoment B raw23608step0 raw23608step0Labels = mixedMoment B raw23608step1 raw23608step1Labels := by
      have hz : ∀ j, raw23608step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23608step1 = (fun i j => raw23608step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23608step1 raw23608step0; decide +kernel
      have hl : raw23608step1Labels = raw23608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23608step0 raw23608step0Labels permutation56 hz
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw23609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23609step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23609step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23609step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23609step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23609 raw23609Labels = mixedMoment B node2007 node2007Labels := by
  calc
    mixedMoment B raw23609 raw23609Labels = mixedMoment B raw23609step0 raw23609step0Labels := by
      have hz : ∀ j, raw23609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23609step0 = (fun i j => raw23609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23609step0 raw23609; decide +kernel
      have hl : raw23609step0Labels = raw23609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23609 raw23609Labels permutation346 hz
    mixedMoment B raw23609step0 raw23609step0Labels = mixedMoment B raw23609step1 raw23609step1Labels := by
      have ha : raw23609step1 = (fun i j => raw23609step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23609step1 raw23609step0; decide +kernel
      have hl : raw23609step1Labels = raw23609step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23609step0 raw23609step0Labels permutation38 permutation7
    mixedMoment B raw23609step1 raw23609step1Labels = mixedMoment B raw23609step2 raw23609step2Labels := by
      have ha : raw23609step2 = -raw23609step1 := by apply Matrix.ext; change ∀ i j, raw23609step2 i j = -(raw23609step1 i j); unfold raw23609step2 raw23609step1; decide +kernel
      have hl : raw23609step2Labels = raw23609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23609step2 raw23609step2Labels = mixedMoment B raw23609step3 raw23609step3Labels := by
      have ha : raw23609step3 = raw23609step2 := by apply Matrix.ext; unfold raw23609step3 raw23609step2; decide +kernel
      have hl : raw23609step2Labels = labelEmbedding1 ∘ raw23609step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23609step2 raw23609step2Labels raw23609step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2007 node2007Labels := by rfl

def raw23610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23610step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23610step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23610step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23610step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23610 raw23610Labels = mixedMoment B node2007 node2007Labels := by
  calc
    mixedMoment B raw23610 raw23610Labels = mixedMoment B raw23610step0 raw23610step0Labels := by
      have hz : ∀ j, raw23610 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23610step0 = (fun i j => raw23610 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23610step0 raw23610; decide +kernel
      have hl : raw23610step0Labels = raw23610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23610 raw23610Labels permutation265 hz
    mixedMoment B raw23610step0 raw23610step0Labels = mixedMoment B raw23610step1 raw23610step1Labels := by
      have ha : raw23610step1 = (fun i j => raw23610step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23610step1 raw23610step0; decide +kernel
      have hl : raw23610step1Labels = raw23610step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23610step0 raw23610step0Labels permutation38 permutation7
    mixedMoment B raw23610step1 raw23610step1Labels = mixedMoment B raw23610step2 raw23610step2Labels := by
      have ha : raw23610step2 = -raw23610step1 := by apply Matrix.ext; change ∀ i j, raw23610step2 i j = -(raw23610step1 i j); unfold raw23610step2 raw23610step1; decide +kernel
      have hl : raw23610step2Labels = raw23610step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23610step2 raw23610step2Labels = mixedMoment B raw23610step3 raw23610step3Labels := by
      have ha : raw23610step3 = raw23610step2 := by apply Matrix.ext; unfold raw23610step3 raw23610step2; decide +kernel
      have hl : raw23610step2Labels = labelEmbedding1 ∘ raw23610step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23610step2 raw23610step2Labels raw23610step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2007 node2007Labels := by rfl

def raw23611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23611step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23611step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw23611step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23611 raw23611Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw23611 raw23611Labels = mixedMoment B raw23611step0 raw23611step0Labels := by
      have hz : ∀ j, raw23611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23611step0 = (fun i j => raw23611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23611step0 raw23611; decide +kernel
      have hl : raw23611step0Labels = raw23611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23611 raw23611Labels permutation346 hz
    mixedMoment B raw23611step0 raw23611step0Labels = mixedMoment B raw23611step1 raw23611step1Labels := by
      have hz : ∀ j, raw23611step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23611step1 = (fun i j => raw23611step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23611step1 raw23611step0; decide +kernel
      have hl : raw23611step1Labels = raw23611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23611step0 raw23611step0Labels permutation56 hz
    mixedMoment B raw23611step1 raw23611step1Labels = mixedMoment B raw23611step2 raw23611step2Labels := by
      have hz : ∀ i, raw23611step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw23611step2 = (fun i j => raw23611step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw23611step2 raw23611step1; decide +kernel
      have hl : raw23611step2Labels = (fun j => raw23611step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23611step1 raw23611step1Labels permutation4 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw23612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23612step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw23612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23612step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23612step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23612step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23612 raw23612Labels = mixedMoment B node2066 node2066Labels := by
  calc
    mixedMoment B raw23612 raw23612Labels = mixedMoment B raw23612step0 raw23612step0Labels := by
      have hz : ∀ j, raw23612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23612step0 = (fun i j => raw23612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23612step0 raw23612; decide +kernel
      have hl : raw23612step0Labels = raw23612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23612 raw23612Labels permutation346 hz
    mixedMoment B raw23612step0 raw23612step0Labels = mixedMoment B raw23612step1 raw23612step1Labels := by
      have hz : ∀ j, raw23612step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23612step1 = (fun i j => raw23612step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23612step1 raw23612step0; decide +kernel
      have hl : raw23612step1Labels = raw23612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23612step0 raw23612step0Labels permutation56 hz
    mixedMoment B raw23612step1 raw23612step1Labels = mixedMoment B raw23612step2 raw23612step2Labels := by
      have ha : raw23612step2 = (fun i j => raw23612step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23612step2 raw23612step1; decide +kernel
      have hl : raw23612step2Labels = raw23612step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23612step1 raw23612step1Labels permutation8 permutation7
    mixedMoment B raw23612step2 raw23612step2Labels = mixedMoment B raw23612step3 raw23612step3Labels := by
      have ha : raw23612step3 = -raw23612step2 := by apply Matrix.ext; change ∀ i j, raw23612step3 i j = -(raw23612step2 i j); unfold raw23612step3 raw23612step2; decide +kernel
      have hl : raw23612step3Labels = raw23612step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23612step3 raw23612step3Labels = mixedMoment B raw23612step4 raw23612step4Labels := by
      have ha : raw23612step4 = raw23612step3 := by apply Matrix.ext; unfold raw23612step4 raw23612step3; decide +kernel
      have hl : raw23612step3Labels = labelEmbedding1 ∘ raw23612step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23612step3 raw23612step3Labels raw23612step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2066 node2066Labels := by rfl

def raw23613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23613step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23613step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw23613step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23613step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23613step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23613step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23613 raw23613Labels = mixedMoment B node2066 node2066Labels := by
  calc
    mixedMoment B raw23613 raw23613Labels = mixedMoment B raw23613step0 raw23613step0Labels := by
      have hz : ∀ j, raw23613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23613step0 = (fun i j => raw23613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23613step0 raw23613; decide +kernel
      have hl : raw23613step0Labels = raw23613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23613 raw23613Labels permutation346 hz
    mixedMoment B raw23613step0 raw23613step0Labels = mixedMoment B raw23613step1 raw23613step1Labels := by
      have hz : ∀ j, raw23613step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23613step1 = (fun i j => raw23613step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23613step1 raw23613step0; decide +kernel
      have hl : raw23613step1Labels = raw23613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23613step0 raw23613step0Labels permutation56 hz
    mixedMoment B raw23613step1 raw23613step1Labels = mixedMoment B raw23613step2 raw23613step2Labels := by
      have ha : raw23613step2 = (fun i j => raw23613step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23613step2 raw23613step1; decide +kernel
      have hl : raw23613step2Labels = raw23613step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23613step1 raw23613step1Labels permutation9 permutation7
    mixedMoment B raw23613step2 raw23613step2Labels = mixedMoment B raw23613step3 raw23613step3Labels := by
      have ha : raw23613step3 = -raw23613step2 := by apply Matrix.ext; change ∀ i j, raw23613step3 i j = -(raw23613step2 i j); unfold raw23613step3 raw23613step2; decide +kernel
      have hl : raw23613step3Labels = raw23613step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23613step3 raw23613step3Labels = mixedMoment B raw23613step4 raw23613step4Labels := by
      have ha : raw23613step4 = raw23613step3 := by apply Matrix.ext; unfold raw23613step4 raw23613step3; decide +kernel
      have hl : raw23613step3Labels = labelEmbedding1 ∘ raw23613step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23613step3 raw23613step3Labels raw23613step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2066 node2066Labels := by rfl

def raw23614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23614step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23614step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23614step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23614step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23614 raw23614Labels = mixedMoment B node1490 node1490Labels := by
  calc
    mixedMoment B raw23614 raw23614Labels = mixedMoment B raw23614step0 raw23614step0Labels := by
      have hz : ∀ j, raw23614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23614step0 = (fun i j => raw23614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23614step0 raw23614; decide +kernel
      have hl : raw23614step0Labels = raw23614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23614 raw23614Labels permutation346 hz
    mixedMoment B raw23614step0 raw23614step0Labels = mixedMoment B raw23614step1 raw23614step1Labels := by
      have ha : raw23614step1 = (fun i j => raw23614step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23614step1 raw23614step0; decide +kernel
      have hl : raw23614step1Labels = raw23614step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23614step0 raw23614step0Labels permutation38 permutation7
    mixedMoment B raw23614step1 raw23614step1Labels = mixedMoment B raw23614step2 raw23614step2Labels := by
      have ha : raw23614step2 = -raw23614step1 := by apply Matrix.ext; change ∀ i j, raw23614step2 i j = -(raw23614step1 i j); unfold raw23614step2 raw23614step1; decide +kernel
      have hl : raw23614step2Labels = raw23614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23614step2 raw23614step2Labels = mixedMoment B raw23614step3 raw23614step3Labels := by
      have ha : raw23614step3 = raw23614step2 := by apply Matrix.ext; unfold raw23614step3 raw23614step2; decide +kernel
      have hl : raw23614step2Labels = labelEmbedding1 ∘ raw23614step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23614step2 raw23614step2Labels raw23614step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1490 node1490Labels := by rfl

def raw23615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23615step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23615 raw23615Labels = mixedMoment B node1587 node1587Labels := by
  calc
    mixedMoment B raw23615 raw23615Labels = mixedMoment B raw23615step0 raw23615step0Labels := by
      have ha : raw23615step0 = (fun i j => raw23615 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23615step0 raw23615; decide +kernel
      have hl : raw23615step0Labels = raw23615Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23615 raw23615Labels permutation206 permutation7
    mixedMoment B raw23615step0 raw23615step0Labels = mixedMoment B raw23615step1 raw23615step1Labels := by
      have ha : raw23615step1 = -raw23615step0 := by apply Matrix.ext; change ∀ i j, raw23615step1 i j = -(raw23615step0 i j); unfold raw23615step1 raw23615step0; decide +kernel
      have hl : raw23615step1Labels = raw23615step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23615step1 raw23615step1Labels = mixedMoment B raw23615step2 raw23615step2Labels := by
      have ha : raw23615step2 = raw23615step1 := by apply Matrix.ext; unfold raw23615step2 raw23615step1; decide +kernel
      have hl : raw23615step1Labels = labelEmbedding1 ∘ raw23615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23615step1 raw23615step1Labels raw23615step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1587 node1587Labels := by rfl

def raw23616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23616step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23616step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23616 raw23616Labels = mixedMoment B node1560 node1560Labels := by
  calc
    mixedMoment B raw23616 raw23616Labels = mixedMoment B raw23616step0 raw23616step0Labels := by
      have hz : ∀ j, raw23616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23616step0 = (fun i j => raw23616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23616step0 raw23616; decide +kernel
      have hl : raw23616step0Labels = raw23616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23616 raw23616Labels permutation346 hz
    mixedMoment B raw23616step0 raw23616step0Labels = mixedMoment B raw23616step1 raw23616step1Labels := by
      have ha : raw23616step1 = (fun i j => raw23616step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23616step1 raw23616step0; decide +kernel
      have hl : raw23616step1Labels = raw23616step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23616step0 raw23616step0Labels permutation38 permutation7
    mixedMoment B raw23616step1 raw23616step1Labels = mixedMoment B raw23616step2 raw23616step2Labels := by
      have ha : raw23616step2 = -raw23616step1 := by apply Matrix.ext; change ∀ i j, raw23616step2 i j = -(raw23616step1 i j); unfold raw23616step2 raw23616step1; decide +kernel
      have hl : raw23616step2Labels = raw23616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23616step2 raw23616step2Labels = mixedMoment B raw23616step3 raw23616step3Labels := by
      have ha : raw23616step3 = raw23616step2 := by apply Matrix.ext; unfold raw23616step3 raw23616step2; decide +kernel
      have hl : raw23616step2Labels = labelEmbedding1 ∘ raw23616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23616step2 raw23616step2Labels raw23616step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1560 node1560Labels := by rfl

def raw23617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23617step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23617 raw23617Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw23617 raw23617Labels = mixedMoment B raw23617step0 raw23617step0Labels := by
      have hz : ∀ j, raw23617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23617step0 = (fun i j => raw23617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23617step0 raw23617; decide +kernel
      have hl : raw23617step0Labels = raw23617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23617 raw23617Labels permutation346 hz
    mixedMoment B raw23617step0 raw23617step0Labels = mixedMoment B raw23617step1 raw23617step1Labels := by
      have ha : raw23617step1 = (fun i j => raw23617step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23617step1 raw23617step0; decide +kernel
      have hl : raw23617step1Labels = raw23617step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23617step0 raw23617step0Labels permutation38 permutation7
    mixedMoment B raw23617step1 raw23617step1Labels = mixedMoment B raw23617step2 raw23617step2Labels := by
      have ha : raw23617step2 = -raw23617step1 := by apply Matrix.ext; change ∀ i j, raw23617step2 i j = -(raw23617step1 i j); unfold raw23617step2 raw23617step1; decide +kernel
      have hl : raw23617step2Labels = raw23617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23617step2 raw23617step2Labels = mixedMoment B raw23617step3 raw23617step3Labels := by
      have ha : raw23617step3 = raw23617step2 := by apply Matrix.ext; unfold raw23617step3 raw23617step2; decide +kernel
      have hl : raw23617step2Labels = labelEmbedding1 ∘ raw23617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23617step2 raw23617step2Labels raw23617step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1605 node1605Labels := by rfl

def raw23618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23618step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23618step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23618step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23618step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23618 raw23618Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw23618 raw23618Labels = mixedMoment B raw23618step0 raw23618step0Labels := by
      have hz : ∀ j, raw23618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23618step0 = (fun i j => raw23618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23618step0 raw23618; decide +kernel
      have hl : raw23618step0Labels = raw23618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23618 raw23618Labels permutation346 hz
    mixedMoment B raw23618step0 raw23618step0Labels = mixedMoment B raw23618step1 raw23618step1Labels := by
      have ha : raw23618step1 = (fun i j => raw23618step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23618step1 raw23618step0; decide +kernel
      have hl : raw23618step1Labels = raw23618step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23618step0 raw23618step0Labels permutation39 permutation7
    mixedMoment B raw23618step1 raw23618step1Labels = mixedMoment B raw23618step2 raw23618step2Labels := by
      have ha : raw23618step2 = -raw23618step1 := by apply Matrix.ext; change ∀ i j, raw23618step2 i j = -(raw23618step1 i j); unfold raw23618step2 raw23618step1; decide +kernel
      have hl : raw23618step2Labels = raw23618step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23618step2 raw23618step2Labels = mixedMoment B raw23618step3 raw23618step3Labels := by
      have ha : raw23618step3 = raw23618step2 := by apply Matrix.ext; unfold raw23618step3 raw23618step2; decide +kernel
      have hl : raw23618step2Labels = labelEmbedding1 ∘ raw23618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23618step2 raw23618step2Labels raw23618step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1605 node1605Labels := by rfl

def raw23619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23619step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23619step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23619step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23619step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23619 raw23619Labels = mixedMoment B node1490 node1490Labels := by
  calc
    mixedMoment B raw23619 raw23619Labels = mixedMoment B raw23619step0 raw23619step0Labels := by
      have hz : ∀ j, raw23619 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23619step0 = (fun i j => raw23619 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23619step0 raw23619; decide +kernel
      have hl : raw23619step0Labels = raw23619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23619 raw23619Labels permutation265 hz
    mixedMoment B raw23619step0 raw23619step0Labels = mixedMoment B raw23619step1 raw23619step1Labels := by
      have ha : raw23619step1 = (fun i j => raw23619step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23619step1 raw23619step0; decide +kernel
      have hl : raw23619step1Labels = raw23619step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23619step0 raw23619step0Labels permutation38 permutation7
    mixedMoment B raw23619step1 raw23619step1Labels = mixedMoment B raw23619step2 raw23619step2Labels := by
      have ha : raw23619step2 = -raw23619step1 := by apply Matrix.ext; change ∀ i j, raw23619step2 i j = -(raw23619step1 i j); unfold raw23619step2 raw23619step1; decide +kernel
      have hl : raw23619step2Labels = raw23619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23619step2 raw23619step2Labels = mixedMoment B raw23619step3 raw23619step3Labels := by
      have ha : raw23619step3 = raw23619step2 := by apply Matrix.ext; unfold raw23619step3 raw23619step2; decide +kernel
      have hl : raw23619step2Labels = labelEmbedding1 ∘ raw23619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23619step2 raw23619step2Labels raw23619step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1490 node1490Labels := by rfl

def raw23620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23620step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23620 raw23620Labels = mixedMoment B node1587 node1587Labels := by
  calc
    mixedMoment B raw23620 raw23620Labels = mixedMoment B raw23620step0 raw23620step0Labels := by
      have ha : raw23620step0 = (fun i j => raw23620 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23620step0 raw23620; decide +kernel
      have hl : raw23620step0Labels = raw23620Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23620 raw23620Labels permutation200 permutation7
    mixedMoment B raw23620step0 raw23620step0Labels = mixedMoment B raw23620step1 raw23620step1Labels := by
      have ha : raw23620step1 = -raw23620step0 := by apply Matrix.ext; change ∀ i j, raw23620step1 i j = -(raw23620step0 i j); unfold raw23620step1 raw23620step0; decide +kernel
      have hl : raw23620step1Labels = raw23620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23620step1 raw23620step1Labels = mixedMoment B raw23620step2 raw23620step2Labels := by
      have ha : raw23620step2 = raw23620step1 := by apply Matrix.ext; unfold raw23620step2 raw23620step1; decide +kernel
      have hl : raw23620step1Labels = labelEmbedding1 ∘ raw23620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23620step1 raw23620step1Labels raw23620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1587 node1587Labels := by rfl

def raw23621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23621 raw23621Labels = mixedMoment B node1560 node1560Labels := by
  calc
    mixedMoment B raw23621 raw23621Labels = mixedMoment B raw23621step0 raw23621step0Labels := by
      have hz : ∀ j, raw23621 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23621step0 = (fun i j => raw23621 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23621step0 raw23621; decide +kernel
      have hl : raw23621step0Labels = raw23621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23621 raw23621Labels permutation265 hz
    mixedMoment B raw23621step0 raw23621step0Labels = mixedMoment B raw23621step1 raw23621step1Labels := by
      have ha : raw23621step1 = (fun i j => raw23621step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23621step1 raw23621step0; decide +kernel
      have hl : raw23621step1Labels = raw23621step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23621step0 raw23621step0Labels permutation38 permutation7
    mixedMoment B raw23621step1 raw23621step1Labels = mixedMoment B raw23621step2 raw23621step2Labels := by
      have ha : raw23621step2 = -raw23621step1 := by apply Matrix.ext; change ∀ i j, raw23621step2 i j = -(raw23621step1 i j); unfold raw23621step2 raw23621step1; decide +kernel
      have hl : raw23621step2Labels = raw23621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23621step2 raw23621step2Labels = mixedMoment B raw23621step3 raw23621step3Labels := by
      have ha : raw23621step3 = raw23621step2 := by apply Matrix.ext; unfold raw23621step3 raw23621step2; decide +kernel
      have hl : raw23621step2Labels = labelEmbedding1 ∘ raw23621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23621step2 raw23621step2Labels raw23621step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1560 node1560Labels := by rfl

def raw23622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23622 raw23622Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw23622 raw23622Labels = mixedMoment B raw23622step0 raw23622step0Labels := by
      have hz : ∀ j, raw23622 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23622step0 = (fun i j => raw23622 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23622step0 raw23622; decide +kernel
      have hl : raw23622step0Labels = raw23622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23622 raw23622Labels permutation265 hz
    mixedMoment B raw23622step0 raw23622step0Labels = mixedMoment B raw23622step1 raw23622step1Labels := by
      have ha : raw23622step1 = (fun i j => raw23622step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23622step1 raw23622step0; decide +kernel
      have hl : raw23622step1Labels = raw23622step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23622step0 raw23622step0Labels permutation38 permutation7
    mixedMoment B raw23622step1 raw23622step1Labels = mixedMoment B raw23622step2 raw23622step2Labels := by
      have ha : raw23622step2 = -raw23622step1 := by apply Matrix.ext; change ∀ i j, raw23622step2 i j = -(raw23622step1 i j); unfold raw23622step2 raw23622step1; decide +kernel
      have hl : raw23622step2Labels = raw23622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23622step2 raw23622step2Labels = mixedMoment B raw23622step3 raw23622step3Labels := by
      have ha : raw23622step3 = raw23622step2 := by apply Matrix.ext; unfold raw23622step3 raw23622step2; decide +kernel
      have hl : raw23622step2Labels = labelEmbedding1 ∘ raw23622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23622step2 raw23622step2Labels raw23622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1605 node1605Labels := by rfl

def raw23623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23623step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23623 raw23623Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw23623 raw23623Labels = mixedMoment B raw23623step0 raw23623step0Labels := by
      have hz : ∀ j, raw23623 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23623step0 = (fun i j => raw23623 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23623step0 raw23623; decide +kernel
      have hl : raw23623step0Labels = raw23623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23623 raw23623Labels permutation265 hz
    mixedMoment B raw23623step0 raw23623step0Labels = mixedMoment B raw23623step1 raw23623step1Labels := by
      have ha : raw23623step1 = (fun i j => raw23623step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23623step1 raw23623step0; decide +kernel
      have hl : raw23623step1Labels = raw23623step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23623step0 raw23623step0Labels permutation39 permutation7
    mixedMoment B raw23623step1 raw23623step1Labels = mixedMoment B raw23623step2 raw23623step2Labels := by
      have ha : raw23623step2 = -raw23623step1 := by apply Matrix.ext; change ∀ i j, raw23623step2 i j = -(raw23623step1 i j); unfold raw23623step2 raw23623step1; decide +kernel
      have hl : raw23623step2Labels = raw23623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23623step2 raw23623step2Labels = mixedMoment B raw23623step3 raw23623step3Labels := by
      have ha : raw23623step3 = raw23623step2 := by apply Matrix.ext; unfold raw23623step3 raw23623step2; decide +kernel
      have hl : raw23623step2Labels = labelEmbedding1 ∘ raw23623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23623step2 raw23623step2Labels raw23623step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1605 node1605Labels := by rfl

def raw23624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23624step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23624step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23624step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23624step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23624step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23624step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23624 raw23624Labels = mixedMoment B node1500 node1500Labels := by
  calc
    mixedMoment B raw23624 raw23624Labels = mixedMoment B raw23624step0 raw23624step0Labels := by
      have hz : ∀ j, raw23624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23624step0 = (fun i j => raw23624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23624step0 raw23624; decide +kernel
      have hl : raw23624step0Labels = raw23624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23624 raw23624Labels permutation346 hz
    mixedMoment B raw23624step0 raw23624step0Labels = mixedMoment B raw23624step1 raw23624step1Labels := by
      have hz : ∀ j, raw23624step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23624step1 = (fun i j => raw23624step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23624step1 raw23624step0; decide +kernel
      have hl : raw23624step1Labels = raw23624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23624step0 raw23624step0Labels permutation56 hz
    mixedMoment B raw23624step1 raw23624step1Labels = mixedMoment B raw23624step2 raw23624step2Labels := by
      have ha : raw23624step2 = (fun i j => raw23624step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23624step2 raw23624step1; decide +kernel
      have hl : raw23624step2Labels = raw23624step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23624step1 raw23624step1Labels permutation8 permutation7
    mixedMoment B raw23624step2 raw23624step2Labels = mixedMoment B raw23624step3 raw23624step3Labels := by
      have ha : raw23624step3 = -raw23624step2 := by apply Matrix.ext; change ∀ i j, raw23624step3 i j = -(raw23624step2 i j); unfold raw23624step3 raw23624step2; decide +kernel
      have hl : raw23624step3Labels = raw23624step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23624step3 raw23624step3Labels = mixedMoment B raw23624step4 raw23624step4Labels := by
      have ha : raw23624step4 = raw23624step3 := by apply Matrix.ext; unfold raw23624step4 raw23624step3; decide +kernel
      have hl : raw23624step3Labels = labelEmbedding1 ∘ raw23624step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23624step3 raw23624step3Labels raw23624step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1500 node1500Labels := by rfl

def raw23625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23625step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23625step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23625step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23625 raw23625Labels = mixedMoment B node1634 node1634Labels := by
  calc
    mixedMoment B raw23625 raw23625Labels = mixedMoment B raw23625step0 raw23625step0Labels := by
      have hz : ∀ j, raw23625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23625step0 = (fun i j => raw23625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23625step0 raw23625; decide +kernel
      have hl : raw23625step0Labels = raw23625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23625 raw23625Labels permutation346 hz
    mixedMoment B raw23625step0 raw23625step0Labels = mixedMoment B raw23625step1 raw23625step1Labels := by
      have ha : raw23625step1 = (fun i j => raw23625step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23625step1 raw23625step0; decide +kernel
      have hl : raw23625step1Labels = raw23625step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23625step0 raw23625step0Labels permutation38 permutation7
    mixedMoment B raw23625step1 raw23625step1Labels = mixedMoment B raw23625step2 raw23625step2Labels := by
      have ha : raw23625step2 = -raw23625step1 := by apply Matrix.ext; change ∀ i j, raw23625step2 i j = -(raw23625step1 i j); unfold raw23625step2 raw23625step1; decide +kernel
      have hl : raw23625step2Labels = raw23625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23625step2 raw23625step2Labels = mixedMoment B raw23625step3 raw23625step3Labels := by
      have ha : raw23625step3 = raw23625step2 := by apply Matrix.ext; unfold raw23625step3 raw23625step2; decide +kernel
      have hl : raw23625step2Labels = labelEmbedding1 ∘ raw23625step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23625step2 raw23625step2Labels raw23625step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1634 node1634Labels := by rfl

def raw23626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw23626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23626 raw23626Labels = mixedMoment B node1634 node1634Labels := by
  calc
    mixedMoment B raw23626 raw23626Labels = mixedMoment B raw23626step0 raw23626step0Labels := by
      have hz : ∀ j, raw23626 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23626step0 = (fun i j => raw23626 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23626step0 raw23626; decide +kernel
      have hl : raw23626step0Labels = raw23626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23626 raw23626Labels permutation265 hz
    mixedMoment B raw23626step0 raw23626step0Labels = mixedMoment B raw23626step1 raw23626step1Labels := by
      have ha : raw23626step1 = (fun i j => raw23626step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23626step1 raw23626step0; decide +kernel
      have hl : raw23626step1Labels = raw23626step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23626step0 raw23626step0Labels permutation38 permutation7
    mixedMoment B raw23626step1 raw23626step1Labels = mixedMoment B raw23626step2 raw23626step2Labels := by
      have ha : raw23626step2 = -raw23626step1 := by apply Matrix.ext; change ∀ i j, raw23626step2 i j = -(raw23626step1 i j); unfold raw23626step2 raw23626step1; decide +kernel
      have hl : raw23626step2Labels = raw23626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23626step2 raw23626step2Labels = mixedMoment B raw23626step3 raw23626step3Labels := by
      have ha : raw23626step3 = raw23626step2 := by apply Matrix.ext; unfold raw23626step3 raw23626step2; decide +kernel
      have hl : raw23626step2Labels = labelEmbedding1 ∘ raw23626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23626step2 raw23626step2Labels raw23626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1634 node1634Labels := by rfl

def raw23627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23627step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23627step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23627step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23627step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23627step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23627 raw23627Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw23627 raw23627Labels = mixedMoment B raw23627step0 raw23627step0Labels := by
      have hz : ∀ j, raw23627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23627step0 = (fun i j => raw23627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23627step0 raw23627; decide +kernel
      have hl : raw23627step0Labels = raw23627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23627 raw23627Labels permutation346 hz
    mixedMoment B raw23627step0 raw23627step0Labels = mixedMoment B raw23627step1 raw23627step1Labels := by
      have hz : ∀ j, raw23627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23627step1 = (fun i j => raw23627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23627step1 raw23627step0; decide +kernel
      have hl : raw23627step1Labels = raw23627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23627step0 raw23627step0Labels permutation56 hz
    mixedMoment B raw23627step1 raw23627step1Labels = mixedMoment B raw23627step2 raw23627step2Labels := by
      have ha : raw23627step2 = (fun i j => raw23627step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23627step2 raw23627step1; decide +kernel
      have hl : raw23627step2Labels = raw23627step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23627step1 raw23627step1Labels permutation8 permutation7
    mixedMoment B raw23627step2 raw23627step2Labels = mixedMoment B raw23627step3 raw23627step3Labels := by
      have ha : raw23627step3 = -raw23627step2 := by apply Matrix.ext; change ∀ i j, raw23627step3 i j = -(raw23627step2 i j); unfold raw23627step3 raw23627step2; decide +kernel
      have hl : raw23627step3Labels = raw23627step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23627step3 raw23627step3Labels = mixedMoment B raw23627step4 raw23627step4Labels := by
      have ha : raw23627step4 = raw23627step3 := by apply Matrix.ext; unfold raw23627step4 raw23627step3; decide +kernel
      have hl : raw23627step3Labels = labelEmbedding1 ∘ raw23627step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23627step3 raw23627step3Labels raw23627step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1653 node1653Labels := by rfl

def raw23628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23628step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23628step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23628step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23628step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23628step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23628step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23628 raw23628Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw23628 raw23628Labels = mixedMoment B raw23628step0 raw23628step0Labels := by
      have hz : ∀ j, raw23628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23628step0 = (fun i j => raw23628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23628step0 raw23628; decide +kernel
      have hl : raw23628step0Labels = raw23628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23628 raw23628Labels permutation346 hz
    mixedMoment B raw23628step0 raw23628step0Labels = mixedMoment B raw23628step1 raw23628step1Labels := by
      have hz : ∀ j, raw23628step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23628step1 = (fun i j => raw23628step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23628step1 raw23628step0; decide +kernel
      have hl : raw23628step1Labels = raw23628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23628step0 raw23628step0Labels permutation56 hz
    mixedMoment B raw23628step1 raw23628step1Labels = mixedMoment B raw23628step2 raw23628step2Labels := by
      have ha : raw23628step2 = (fun i j => raw23628step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23628step2 raw23628step1; decide +kernel
      have hl : raw23628step2Labels = raw23628step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23628step1 raw23628step1Labels permutation9 permutation7
    mixedMoment B raw23628step2 raw23628step2Labels = mixedMoment B raw23628step3 raw23628step3Labels := by
      have ha : raw23628step3 = -raw23628step2 := by apply Matrix.ext; change ∀ i j, raw23628step3 i j = -(raw23628step2 i j); unfold raw23628step3 raw23628step2; decide +kernel
      have hl : raw23628step3Labels = raw23628step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23628step3 raw23628step3Labels = mixedMoment B raw23628step4 raw23628step4Labels := by
      have ha : raw23628step4 = raw23628step3 := by apply Matrix.ext; unfold raw23628step4 raw23628step3; decide +kernel
      have hl : raw23628step3Labels = labelEmbedding1 ∘ raw23628step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23628step3 raw23628step3Labels raw23628step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1653 node1653Labels := by rfl

def raw23629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23629step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23629step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw23629step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23629step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw23629step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23629step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw23629step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23629 raw23629Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw23629 raw23629Labels = mixedMoment B raw23629step0 raw23629step0Labels := by
      have hz : ∀ j, raw23629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23629step0 = (fun i j => raw23629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23629step0 raw23629; decide +kernel
      have hl : raw23629step0Labels = raw23629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23629 raw23629Labels permutation346 hz
    mixedMoment B raw23629step0 raw23629step0Labels = mixedMoment B raw23629step1 raw23629step1Labels := by
      have hz : ∀ j, raw23629step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23629step1 = (fun i j => raw23629step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23629step1 raw23629step0; decide +kernel
      have hl : raw23629step1Labels = raw23629step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23629step0 raw23629step0Labels permutation56 hz
    mixedMoment B raw23629step1 raw23629step1Labels = mixedMoment B raw23629step2 raw23629step2Labels := by
      have ha : raw23629step2 = (fun i j => raw23629step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23629step2 raw23629step1; decide +kernel
      have hl : raw23629step2Labels = raw23629step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23629step1 raw23629step1Labels permutation9 permutation7
    mixedMoment B raw23629step2 raw23629step2Labels = mixedMoment B raw23629step3 raw23629step3Labels := by
      have ha : raw23629step3 = -raw23629step2 := by apply Matrix.ext; change ∀ i j, raw23629step3 i j = -(raw23629step2 i j); unfold raw23629step3 raw23629step2; decide +kernel
      have hl : raw23629step3Labels = raw23629step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23629step3 raw23629step3Labels = mixedMoment B raw23629step4 raw23629step4Labels := by
      have ha : raw23629step4 = raw23629step3 := by apply Matrix.ext; unfold raw23629step4 raw23629step3; decide +kernel
      have hl : raw23629step3Labels = labelEmbedding1 ∘ raw23629step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23629step3 raw23629step3Labels raw23629step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1496 node1496Labels := by rfl

def raw23630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23630step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw23630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23630step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23630step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23630 raw23630Labels = mixedMoment B node1591 node1591Labels := by
  calc
    mixedMoment B raw23630 raw23630Labels = mixedMoment B raw23630step0 raw23630step0Labels := by
      have hz : ∀ j, raw23630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23630step0 = (fun i j => raw23630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23630step0 raw23630; decide +kernel
      have hl : raw23630step0Labels = raw23630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23630 raw23630Labels permutation346 hz
    mixedMoment B raw23630step0 raw23630step0Labels = mixedMoment B raw23630step1 raw23630step1Labels := by
      have ha : raw23630step1 = (fun i j => raw23630step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23630step1 raw23630step0; decide +kernel
      have hl : raw23630step1Labels = raw23630step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23630step0 raw23630step0Labels permutation39 permutation7
    mixedMoment B raw23630step1 raw23630step1Labels = mixedMoment B raw23630step2 raw23630step2Labels := by
      have ha : raw23630step2 = -raw23630step1 := by apply Matrix.ext; change ∀ i j, raw23630step2 i j = -(raw23630step1 i j); unfold raw23630step2 raw23630step1; decide +kernel
      have hl : raw23630step2Labels = raw23630step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23630step2 raw23630step2Labels = mixedMoment B raw23630step3 raw23630step3Labels := by
      have ha : raw23630step3 = raw23630step2 := by apply Matrix.ext; unfold raw23630step3 raw23630step2; decide +kernel
      have hl : raw23630step2Labels = labelEmbedding1 ∘ raw23630step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23630step2 raw23630step2Labels raw23630step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1591 node1591Labels := by rfl

def raw23631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23631step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw23631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23631step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23631step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23631step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23631 raw23631Labels = mixedMoment B node1591 node1591Labels := by
  calc
    mixedMoment B raw23631 raw23631Labels = mixedMoment B raw23631step0 raw23631step0Labels := by
      have hz : ∀ j, raw23631 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23631step0 = (fun i j => raw23631 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23631step0 raw23631; decide +kernel
      have hl : raw23631step0Labels = raw23631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23631 raw23631Labels permutation265 hz
    mixedMoment B raw23631step0 raw23631step0Labels = mixedMoment B raw23631step1 raw23631step1Labels := by
      have ha : raw23631step1 = (fun i j => raw23631step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23631step1 raw23631step0; decide +kernel
      have hl : raw23631step1Labels = raw23631step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23631step0 raw23631step0Labels permutation39 permutation7
    mixedMoment B raw23631step1 raw23631step1Labels = mixedMoment B raw23631step2 raw23631step2Labels := by
      have ha : raw23631step2 = -raw23631step1 := by apply Matrix.ext; change ∀ i j, raw23631step2 i j = -(raw23631step1 i j); unfold raw23631step2 raw23631step1; decide +kernel
      have hl : raw23631step2Labels = raw23631step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23631step2 raw23631step2Labels = mixedMoment B raw23631step3 raw23631step3Labels := by
      have ha : raw23631step3 = raw23631step2 := by apply Matrix.ext; unfold raw23631step3 raw23631step2; decide +kernel
      have hl : raw23631step2Labels = labelEmbedding1 ∘ raw23631step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23631step2 raw23631step2Labels raw23631step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1591 node1591Labels := by rfl

def raw23632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23632step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw23632step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23632step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23632step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23632step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23632 raw23632Labels = mixedMoment B node1579 node1579Labels := by
  calc
    mixedMoment B raw23632 raw23632Labels = mixedMoment B raw23632step0 raw23632step0Labels := by
      have hz : ∀ j, raw23632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23632step0 = (fun i j => raw23632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23632step0 raw23632; decide +kernel
      have hl : raw23632step0Labels = raw23632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23632 raw23632Labels permutation346 hz
    mixedMoment B raw23632step0 raw23632step0Labels = mixedMoment B raw23632step1 raw23632step1Labels := by
      have hz : ∀ j, raw23632step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23632step1 = (fun i j => raw23632step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23632step1 raw23632step0; decide +kernel
      have hl : raw23632step1Labels = raw23632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23632step0 raw23632step0Labels permutation56 hz
    mixedMoment B raw23632step1 raw23632step1Labels = mixedMoment B raw23632step2 raw23632step2Labels := by
      have ha : raw23632step2 = (fun i j => raw23632step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23632step2 raw23632step1; decide +kernel
      have hl : raw23632step2Labels = raw23632step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23632step1 raw23632step1Labels permutation9 permutation7
    mixedMoment B raw23632step2 raw23632step2Labels = mixedMoment B raw23632step3 raw23632step3Labels := by
      have ha : raw23632step3 = -raw23632step2 := by apply Matrix.ext; change ∀ i j, raw23632step3 i j = -(raw23632step2 i j); unfold raw23632step3 raw23632step2; decide +kernel
      have hl : raw23632step3Labels = raw23632step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23632step3 raw23632step3Labels = mixedMoment B raw23632step4 raw23632step4Labels := by
      have ha : raw23632step4 = raw23632step3 := by apply Matrix.ext; unfold raw23632step4 raw23632step3; decide +kernel
      have hl : raw23632step3Labels = labelEmbedding1 ∘ raw23632step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23632step3 raw23632step3Labels raw23632step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1579 node1579Labels := by rfl

def raw23633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23633step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw23633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23633step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw23633step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23633step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw23633step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23633 raw23633Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw23633 raw23633Labels = mixedMoment B raw23633step0 raw23633step0Labels := by
      have hz : ∀ j, raw23633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23633step0 = (fun i j => raw23633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23633step0 raw23633; decide +kernel
      have hl : raw23633step0Labels = raw23633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23633 raw23633Labels permutation346 hz
    mixedMoment B raw23633step0 raw23633step0Labels = mixedMoment B raw23633step1 raw23633step1Labels := by
      have hz : ∀ j, raw23633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23633step1 = (fun i j => raw23633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23633step1 raw23633step0; decide +kernel
      have hl : raw23633step1Labels = raw23633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23633step0 raw23633step0Labels permutation56 hz
    mixedMoment B raw23633step1 raw23633step1Labels = mixedMoment B raw23633step2 raw23633step2Labels := by
      have ha : raw23633step2 = (fun i j => raw23633step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23633step2 raw23633step1; decide +kernel
      have hl : raw23633step2Labels = raw23633step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23633step1 raw23633step1Labels permutation9 permutation7
    mixedMoment B raw23633step2 raw23633step2Labels = mixedMoment B raw23633step3 raw23633step3Labels := by
      have ha : raw23633step3 = -raw23633step2 := by apply Matrix.ext; change ∀ i j, raw23633step3 i j = -(raw23633step2 i j); unfold raw23633step3 raw23633step2; decide +kernel
      have hl : raw23633step3Labels = raw23633step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23633step3 raw23633step3Labels = mixedMoment B raw23633step4 raw23633step4Labels := by
      have ha : raw23633step4 = raw23633step3 := by apply Matrix.ext; unfold raw23633step4 raw23633step3; decide +kernel
      have hl : raw23633step3Labels = labelEmbedding1 ∘ raw23633step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23633step3 raw23633step3Labels raw23633step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1630 node1630Labels := by rfl

def raw23634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23634step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23634step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23634step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw23634step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23634step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw23634step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23634step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw23634step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23634 raw23634Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw23634 raw23634Labels = mixedMoment B raw23634step0 raw23634step0Labels := by
      have hz : ∀ j, raw23634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23634step0 = (fun i j => raw23634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23634step0 raw23634; decide +kernel
      have hl : raw23634step0Labels = raw23634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23634 raw23634Labels permutation346 hz
    mixedMoment B raw23634step0 raw23634step0Labels = mixedMoment B raw23634step1 raw23634step1Labels := by
      have hz : ∀ j, raw23634step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23634step1 = (fun i j => raw23634step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23634step1 raw23634step0; decide +kernel
      have hl : raw23634step1Labels = raw23634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23634step0 raw23634step0Labels permutation56 hz
    mixedMoment B raw23634step1 raw23634step1Labels = mixedMoment B raw23634step2 raw23634step2Labels := by
      have ha : raw23634step2 = (fun i j => raw23634step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23634step2 raw23634step1; decide +kernel
      have hl : raw23634step2Labels = raw23634step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23634step1 raw23634step1Labels permutation8 permutation7
    mixedMoment B raw23634step2 raw23634step2Labels = mixedMoment B raw23634step3 raw23634step3Labels := by
      have ha : raw23634step3 = -raw23634step2 := by apply Matrix.ext; change ∀ i j, raw23634step3 i j = -(raw23634step2 i j); unfold raw23634step3 raw23634step2; decide +kernel
      have hl : raw23634step3Labels = raw23634step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23634step3 raw23634step3Labels = mixedMoment B raw23634step4 raw23634step4Labels := by
      have ha : raw23634step4 = raw23634step3 := by apply Matrix.ext; unfold raw23634step4 raw23634step3; decide +kernel
      have hl : raw23634step3Labels = labelEmbedding1 ∘ raw23634step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23634step3 raw23634step3Labels raw23634step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1496 node1496Labels := by rfl

def raw23635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw23635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23635 raw23635Labels = mixedMoment B node1591 node1591Labels := by
  calc
    mixedMoment B raw23635 raw23635Labels = mixedMoment B raw23635step0 raw23635step0Labels := by
      have hz : ∀ j, raw23635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23635step0 = (fun i j => raw23635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23635step0 raw23635; decide +kernel
      have hl : raw23635step0Labels = raw23635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23635 raw23635Labels permutation346 hz
    mixedMoment B raw23635step0 raw23635step0Labels = mixedMoment B raw23635step1 raw23635step1Labels := by
      have ha : raw23635step1 = (fun i j => raw23635step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23635step1 raw23635step0; decide +kernel
      have hl : raw23635step1Labels = raw23635step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23635step0 raw23635step0Labels permutation38 permutation7
    mixedMoment B raw23635step1 raw23635step1Labels = mixedMoment B raw23635step2 raw23635step2Labels := by
      have ha : raw23635step2 = -raw23635step1 := by apply Matrix.ext; change ∀ i j, raw23635step2 i j = -(raw23635step1 i j); unfold raw23635step2 raw23635step1; decide +kernel
      have hl : raw23635step2Labels = raw23635step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23635step2 raw23635step2Labels = mixedMoment B raw23635step3 raw23635step3Labels := by
      have ha : raw23635step3 = raw23635step2 := by apply Matrix.ext; unfold raw23635step3 raw23635step2; decide +kernel
      have hl : raw23635step2Labels = labelEmbedding1 ∘ raw23635step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23635step2 raw23635step2Labels raw23635step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1591 node1591Labels := by rfl

def raw23636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw23636step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23636step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23636step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23636step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23636 raw23636Labels = mixedMoment B node1591 node1591Labels := by
  calc
    mixedMoment B raw23636 raw23636Labels = mixedMoment B raw23636step0 raw23636step0Labels := by
      have hz : ∀ j, raw23636 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23636step0 = (fun i j => raw23636 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23636step0 raw23636; decide +kernel
      have hl : raw23636step0Labels = raw23636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23636 raw23636Labels permutation265 hz
    mixedMoment B raw23636step0 raw23636step0Labels = mixedMoment B raw23636step1 raw23636step1Labels := by
      have ha : raw23636step1 = (fun i j => raw23636step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23636step1 raw23636step0; decide +kernel
      have hl : raw23636step1Labels = raw23636step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23636step0 raw23636step0Labels permutation38 permutation7
    mixedMoment B raw23636step1 raw23636step1Labels = mixedMoment B raw23636step2 raw23636step2Labels := by
      have ha : raw23636step2 = -raw23636step1 := by apply Matrix.ext; change ∀ i j, raw23636step2 i j = -(raw23636step1 i j); unfold raw23636step2 raw23636step1; decide +kernel
      have hl : raw23636step2Labels = raw23636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23636step2 raw23636step2Labels = mixedMoment B raw23636step3 raw23636step3Labels := by
      have ha : raw23636step3 = raw23636step2 := by apply Matrix.ext; unfold raw23636step3 raw23636step2; decide +kernel
      have hl : raw23636step2Labels = labelEmbedding1 ∘ raw23636step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23636step2 raw23636step2Labels raw23636step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1591 node1591Labels := by rfl

def raw23637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23637step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw23637step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23637step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23637step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23637step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23637 raw23637Labels = mixedMoment B node1579 node1579Labels := by
  calc
    mixedMoment B raw23637 raw23637Labels = mixedMoment B raw23637step0 raw23637step0Labels := by
      have hz : ∀ j, raw23637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23637step0 = (fun i j => raw23637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23637step0 raw23637; decide +kernel
      have hl : raw23637step0Labels = raw23637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23637 raw23637Labels permutation346 hz
    mixedMoment B raw23637step0 raw23637step0Labels = mixedMoment B raw23637step1 raw23637step1Labels := by
      have hz : ∀ j, raw23637step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23637step1 = (fun i j => raw23637step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23637step1 raw23637step0; decide +kernel
      have hl : raw23637step1Labels = raw23637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23637step0 raw23637step0Labels permutation56 hz
    mixedMoment B raw23637step1 raw23637step1Labels = mixedMoment B raw23637step2 raw23637step2Labels := by
      have ha : raw23637step2 = (fun i j => raw23637step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23637step2 raw23637step1; decide +kernel
      have hl : raw23637step2Labels = raw23637step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23637step1 raw23637step1Labels permutation8 permutation7
    mixedMoment B raw23637step2 raw23637step2Labels = mixedMoment B raw23637step3 raw23637step3Labels := by
      have ha : raw23637step3 = -raw23637step2 := by apply Matrix.ext; change ∀ i j, raw23637step3 i j = -(raw23637step2 i j); unfold raw23637step3 raw23637step2; decide +kernel
      have hl : raw23637step3Labels = raw23637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23637step3 raw23637step3Labels = mixedMoment B raw23637step4 raw23637step4Labels := by
      have ha : raw23637step4 = raw23637step3 := by apply Matrix.ext; unfold raw23637step4 raw23637step3; decide +kernel
      have hl : raw23637step3Labels = labelEmbedding1 ∘ raw23637step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23637step3 raw23637step3Labels raw23637step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1579 node1579Labels := by rfl

def raw23638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23638step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw23638step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw23638step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23638step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw23638step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23638 raw23638Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw23638 raw23638Labels = mixedMoment B raw23638step0 raw23638step0Labels := by
      have hz : ∀ j, raw23638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23638step0 = (fun i j => raw23638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23638step0 raw23638; decide +kernel
      have hl : raw23638step0Labels = raw23638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23638 raw23638Labels permutation346 hz
    mixedMoment B raw23638step0 raw23638step0Labels = mixedMoment B raw23638step1 raw23638step1Labels := by
      have hz : ∀ j, raw23638step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23638step1 = (fun i j => raw23638step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23638step1 raw23638step0; decide +kernel
      have hl : raw23638step1Labels = raw23638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23638step0 raw23638step0Labels permutation56 hz
    mixedMoment B raw23638step1 raw23638step1Labels = mixedMoment B raw23638step2 raw23638step2Labels := by
      have ha : raw23638step2 = (fun i j => raw23638step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23638step2 raw23638step1; decide +kernel
      have hl : raw23638step2Labels = raw23638step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23638step1 raw23638step1Labels permutation8 permutation7
    mixedMoment B raw23638step2 raw23638step2Labels = mixedMoment B raw23638step3 raw23638step3Labels := by
      have ha : raw23638step3 = -raw23638step2 := by apply Matrix.ext; change ∀ i j, raw23638step3 i j = -(raw23638step2 i j); unfold raw23638step3 raw23638step2; decide +kernel
      have hl : raw23638step3Labels = raw23638step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23638step3 raw23638step3Labels = mixedMoment B raw23638step4 raw23638step4Labels := by
      have ha : raw23638step4 = raw23638step3 := by apply Matrix.ext; unfold raw23638step4 raw23638step3; decide +kernel
      have hl : raw23638step3Labels = labelEmbedding1 ∘ raw23638step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23638step3 raw23638step3Labels raw23638step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1630 node1630Labels := by rfl

def raw23639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23639 raw23639Labels = mixedMoment B node569 node569Labels := by
  calc
    mixedMoment B raw23639 raw23639Labels = mixedMoment B raw23639step0 raw23639step0Labels := by
      have hz : ∀ j, raw23639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23639step0 = (fun i j => raw23639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23639step0 raw23639; decide +kernel
      have hl : raw23639step0Labels = raw23639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23639 raw23639Labels permutation346 hz
    mixedMoment B raw23639step0 raw23639step0Labels = mixedMoment B raw23639step1 raw23639step1Labels := by
      have ha : raw23639step1 = (fun i j => raw23639step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23639step1 raw23639step0; decide +kernel
      have hl : raw23639step1Labels = raw23639step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23639step0 raw23639step0Labels permutation38 permutation2
    _ = mixedMoment B node569 node569Labels := by rfl

def raw23640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23640 raw23640Labels = mixedMoment B node569 node569Labels := by
  calc
    mixedMoment B raw23640 raw23640Labels = mixedMoment B raw23640step0 raw23640step0Labels := by
      have hz : ∀ j, raw23640 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23640step0 = (fun i j => raw23640 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23640step0 raw23640; decide +kernel
      have hl : raw23640step0Labels = raw23640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23640 raw23640Labels permutation265 hz
    mixedMoment B raw23640step0 raw23640step0Labels = mixedMoment B raw23640step1 raw23640step1Labels := by
      have ha : raw23640step1 = (fun i j => raw23640step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23640step1 raw23640step0; decide +kernel
      have hl : raw23640step1Labels = raw23640step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23640step0 raw23640step0Labels permutation38 permutation2
    _ = mixedMoment B node569 node569Labels := by rfl

def raw23641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23641 raw23641Labels = mixedMoment B node595 node595Labels := by
  calc
    mixedMoment B raw23641 raw23641Labels = mixedMoment B raw23641step0 raw23641step0Labels := by
      have hz : ∀ j, raw23641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23641step0 = (fun i j => raw23641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23641step0 raw23641; decide +kernel
      have hl : raw23641step0Labels = raw23641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23641 raw23641Labels permutation346 hz
    mixedMoment B raw23641step0 raw23641step0Labels = mixedMoment B raw23641step1 raw23641step1Labels := by
      have hz : ∀ j, raw23641step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23641step1 = (fun i j => raw23641step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23641step1 raw23641step0; decide +kernel
      have hl : raw23641step1Labels = raw23641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23641step0 raw23641step0Labels permutation56 hz
    _ = mixedMoment B node595 node595Labels := by rfl

def raw23642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23642 raw23642Labels = mixedMoment B node576 node576Labels := by
  calc
    mixedMoment B raw23642 raw23642Labels = mixedMoment B raw23642step0 raw23642step0Labels := by
      have hz : ∀ j, raw23642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23642step0 = (fun i j => raw23642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23642step0 raw23642; decide +kernel
      have hl : raw23642step0Labels = raw23642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23642 raw23642Labels permutation346 hz
    mixedMoment B raw23642step0 raw23642step0Labels = mixedMoment B raw23642step1 raw23642step1Labels := by
      have hz : ∀ j, raw23642step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23642step1 = (fun i j => raw23642step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23642step1 raw23642step0; decide +kernel
      have hl : raw23642step1Labels = raw23642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23642step0 raw23642step0Labels permutation56 hz
    mixedMoment B raw23642step1 raw23642step1Labels = mixedMoment B raw23642step2 raw23642step2Labels := by
      have ha : raw23642step2 = (fun i j => raw23642step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23642step2 raw23642step1; decide +kernel
      have hl : raw23642step2Labels = raw23642step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23642step1 raw23642step1Labels permutation9 permutation2
    _ = mixedMoment B node576 node576Labels := by rfl

def raw23643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23643 raw23643Labels = mixedMoment B node899 node899Labels := by
  calc
    mixedMoment B raw23643 raw23643Labels = mixedMoment B raw23643step0 raw23643step0Labels := by
      have ha : raw23643step0 = (fun i j => raw23643 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23643step0 raw23643; decide +kernel
      have hl : raw23643step0Labels = raw23643Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23643 raw23643Labels permutation182 permutation2
    _ = mixedMoment B node899 node899Labels := by rfl

def raw23644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23644 raw23644Labels = mixedMoment B node883 node883Labels := by
  calc
    mixedMoment B raw23644 raw23644Labels = mixedMoment B raw23644step0 raw23644step0Labels := by
      have hz : ∀ j, raw23644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23644step0 = (fun i j => raw23644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23644step0 raw23644; decide +kernel
      have hl : raw23644step0Labels = raw23644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23644 raw23644Labels permutation346 hz
    mixedMoment B raw23644step0 raw23644step0Labels = mixedMoment B raw23644step1 raw23644step1Labels := by
      have ha : raw23644step1 = (fun i j => raw23644step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23644step1 raw23644step0; decide +kernel
      have hl : raw23644step1Labels = raw23644step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23644step0 raw23644step0Labels permutation38 permutation2
    _ = mixedMoment B node883 node883Labels := by rfl

def raw23645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23645 raw23645Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw23645 raw23645Labels = mixedMoment B raw23645step0 raw23645step0Labels := by
      have hz : ∀ j, raw23645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23645step0 = (fun i j => raw23645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23645step0 raw23645; decide +kernel
      have hl : raw23645step0Labels = raw23645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23645 raw23645Labels permutation346 hz
    mixedMoment B raw23645step0 raw23645step0Labels = mixedMoment B raw23645step1 raw23645step1Labels := by
      have ha : raw23645step1 = (fun i j => raw23645step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23645step1 raw23645step0; decide +kernel
      have hl : raw23645step1Labels = raw23645step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23645step0 raw23645step0Labels permutation39 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw23646 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23646step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23646step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23646step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23646step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23646 raw23646Labels = mixedMoment B node4214 node4214Labels := by
  calc
    mixedMoment B raw23646 raw23646Labels = mixedMoment B raw23646step0 raw23646step0Labels := by
      have hz : ∀ j, raw23646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23646step0 = (fun i j => raw23646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23646step0 raw23646; decide +kernel
      have hl : raw23646step0Labels = raw23646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23646 raw23646Labels permutation346 hz
    mixedMoment B raw23646step0 raw23646step0Labels = mixedMoment B raw23646step1 raw23646step1Labels := by
      have ha : raw23646step1 = (fun i j => raw23646step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23646step1 raw23646step0; decide +kernel
      have hl : raw23646step1Labels = raw23646step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23646step0 raw23646step0Labels permutation38 permutation4
    mixedMoment B raw23646step1 raw23646step1Labels = mixedMoment B raw23646step2 raw23646step2Labels := by
      have ha : raw23646step2 = -raw23646step1 := by apply Matrix.ext; change ∀ i j, raw23646step2 i j = -(raw23646step1 i j); unfold raw23646step2 raw23646step1; decide +kernel
      have hl : raw23646step2Labels = raw23646step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23646step2 raw23646step2Labels = mixedMoment B raw23646step3 raw23646step3Labels := by
      have ha : raw23646step3 = raw23646step2 := by apply Matrix.ext; unfold raw23646step3 raw23646step2; decide +kernel
      have hl : raw23646step2Labels = labelEmbedding7 ∘ raw23646step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23646step2 raw23646step2Labels raw23646step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4214 node4214Labels := by rfl

def raw23647 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23647step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23647 raw23647Labels = mixedMoment B node4385 node4385Labels := by
  calc
    mixedMoment B raw23647 raw23647Labels = mixedMoment B raw23647step0 raw23647step0Labels := by
      have ha : raw23647step0 = (fun i j => raw23647 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23647step0 raw23647; decide +kernel
      have hl : raw23647step0Labels = raw23647Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23647 raw23647Labels permutation182 permutation6
    mixedMoment B raw23647step0 raw23647step0Labels = mixedMoment B raw23647step1 raw23647step1Labels := by
      have ha : raw23647step1 = raw23647step0 := by apply Matrix.ext; unfold raw23647step1 raw23647step0; decide +kernel
      have hl : raw23647step0Labels = labelEmbedding9 ∘ raw23647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23647step0 raw23647step0Labels raw23647step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4385 node4385Labels := by rfl

def raw23648 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23648step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23648step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23648 raw23648Labels = mixedMoment B node4378 node4378Labels := by
  calc
    mixedMoment B raw23648 raw23648Labels = mixedMoment B raw23648step0 raw23648step0Labels := by
      have hz : ∀ j, raw23648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23648step0 = (fun i j => raw23648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23648step0 raw23648; decide +kernel
      have hl : raw23648step0Labels = raw23648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23648 raw23648Labels permutation346 hz
    mixedMoment B raw23648step0 raw23648step0Labels = mixedMoment B raw23648step1 raw23648step1Labels := by
      have ha : raw23648step1 = (fun i j => raw23648step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23648step1 raw23648step0; decide +kernel
      have hl : raw23648step1Labels = raw23648step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23648step0 raw23648step0Labels permutation38 permutation6
    mixedMoment B raw23648step1 raw23648step1Labels = mixedMoment B raw23648step2 raw23648step2Labels := by
      have ha : raw23648step2 = raw23648step1 := by apply Matrix.ext; unfold raw23648step2 raw23648step1; decide +kernel
      have hl : raw23648step1Labels = labelEmbedding9 ∘ raw23648step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23648step1 raw23648step1Labels raw23648step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4378 node4378Labels := by rfl

def raw23649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23649step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23649step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23649step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23649step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23649 raw23649Labels = mixedMoment B node4214 node4214Labels := by
  calc
    mixedMoment B raw23649 raw23649Labels = mixedMoment B raw23649step0 raw23649step0Labels := by
      have hz : ∀ j, raw23649 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23649step0 = (fun i j => raw23649 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23649step0 raw23649; decide +kernel
      have hl : raw23649step0Labels = raw23649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23649 raw23649Labels permutation265 hz
    mixedMoment B raw23649step0 raw23649step0Labels = mixedMoment B raw23649step1 raw23649step1Labels := by
      have ha : raw23649step1 = (fun i j => raw23649step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23649step1 raw23649step0; decide +kernel
      have hl : raw23649step1Labels = raw23649step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23649step0 raw23649step0Labels permutation38 permutation4
    mixedMoment B raw23649step1 raw23649step1Labels = mixedMoment B raw23649step2 raw23649step2Labels := by
      have ha : raw23649step2 = -raw23649step1 := by apply Matrix.ext; change ∀ i j, raw23649step2 i j = -(raw23649step1 i j); unfold raw23649step2 raw23649step1; decide +kernel
      have hl : raw23649step2Labels = raw23649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23649step2 raw23649step2Labels = mixedMoment B raw23649step3 raw23649step3Labels := by
      have ha : raw23649step3 = raw23649step2 := by apply Matrix.ext; unfold raw23649step3 raw23649step2; decide +kernel
      have hl : raw23649step2Labels = labelEmbedding7 ∘ raw23649step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23649step2 raw23649step2Labels raw23649step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4214 node4214Labels := by rfl

def raw23650 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23650step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23650 raw23650Labels = mixedMoment B node4385 node4385Labels := by
  calc
    mixedMoment B raw23650 raw23650Labels = mixedMoment B raw23650step0 raw23650step0Labels := by
      have ha : raw23650step0 = (fun i j => raw23650 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23650step0 raw23650; decide +kernel
      have hl : raw23650step0Labels = raw23650Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23650 raw23650Labels permutation158 permutation6
    mixedMoment B raw23650step0 raw23650step0Labels = mixedMoment B raw23650step1 raw23650step1Labels := by
      have ha : raw23650step1 = raw23650step0 := by apply Matrix.ext; unfold raw23650step1 raw23650step0; decide +kernel
      have hl : raw23650step0Labels = labelEmbedding9 ∘ raw23650step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23650step0 raw23650step0Labels raw23650step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4385 node4385Labels := by rfl

def raw23651 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23651step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw23651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23651 raw23651Labels = mixedMoment B node4378 node4378Labels := by
  calc
    mixedMoment B raw23651 raw23651Labels = mixedMoment B raw23651step0 raw23651step0Labels := by
      have hz : ∀ j, raw23651 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23651step0 = (fun i j => raw23651 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23651step0 raw23651; decide +kernel
      have hl : raw23651step0Labels = raw23651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23651 raw23651Labels permutation265 hz
    mixedMoment B raw23651step0 raw23651step0Labels = mixedMoment B raw23651step1 raw23651step1Labels := by
      have ha : raw23651step1 = (fun i j => raw23651step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23651step1 raw23651step0; decide +kernel
      have hl : raw23651step1Labels = raw23651step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23651step0 raw23651step0Labels permutation38 permutation6
    mixedMoment B raw23651step1 raw23651step1Labels = mixedMoment B raw23651step2 raw23651step2Labels := by
      have ha : raw23651step2 = raw23651step1 := by apply Matrix.ext; unfold raw23651step2 raw23651step1; decide +kernel
      have hl : raw23651step1Labels = labelEmbedding9 ∘ raw23651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23651step1 raw23651step1Labels raw23651step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4378 node4378Labels := by rfl

def raw23652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23652step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23652 raw23652Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw23652 raw23652Labels = mixedMoment B raw23652step0 raw23652step0Labels := by
      have hz : ∀ j, raw23652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23652step0 = (fun i j => raw23652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23652step0 raw23652; decide +kernel
      have hl : raw23652step0Labels = raw23652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23652 raw23652Labels permutation265 hz
    mixedMoment B raw23652step0 raw23652step0Labels = mixedMoment B raw23652step1 raw23652step1Labels := by
      have ha : raw23652step1 = (fun i j => raw23652step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23652step1 raw23652step0; decide +kernel
      have hl : raw23652step1Labels = raw23652step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23652step0 raw23652step0Labels permutation38 permutation6
    mixedMoment B raw23652step1 raw23652step1Labels = mixedMoment B raw23652step2 raw23652step2Labels := by
      have ha : raw23652step2 = raw23652step1 := by apply Matrix.ext; unfold raw23652step2 raw23652step1; decide +kernel
      have hl : raw23652step1Labels = labelEmbedding9 ∘ raw23652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23652step1 raw23652step1Labels raw23652step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw23653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw23653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw23653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw23653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23653step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw23653step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23653step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw23653step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23653step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw23653step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23653 raw23653Labels = mixedMoment B node4228 node4228Labels := by
  calc
    mixedMoment B raw23653 raw23653Labels = mixedMoment B raw23653step0 raw23653step0Labels := by
      have hz : ∀ j, raw23653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23653step0 = (fun i j => raw23653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23653step0 raw23653; decide +kernel
      have hl : raw23653step0Labels = raw23653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23653 raw23653Labels permutation346 hz
    mixedMoment B raw23653step0 raw23653step0Labels = mixedMoment B raw23653step1 raw23653step1Labels := by
      have hz : ∀ j, raw23653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23653step1 = (fun i j => raw23653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23653step1 raw23653step0; decide +kernel
      have hl : raw23653step1Labels = raw23653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23653step0 raw23653step0Labels permutation56 hz
    mixedMoment B raw23653step1 raw23653step1Labels = mixedMoment B raw23653step2 raw23653step2Labels := by
      have ha : raw23653step2 = (fun i j => raw23653step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23653step2 raw23653step1; decide +kernel
      have hl : raw23653step2Labels = raw23653step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23653step1 raw23653step1Labels permutation9 permutation4
    mixedMoment B raw23653step2 raw23653step2Labels = mixedMoment B raw23653step3 raw23653step3Labels := by
      have ha : raw23653step3 = -raw23653step2 := by apply Matrix.ext; change ∀ i j, raw23653step3 i j = -(raw23653step2 i j); unfold raw23653step3 raw23653step2; decide +kernel
      have hl : raw23653step3Labels = raw23653step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23653step3 raw23653step3Labels = mixedMoment B raw23653step4 raw23653step4Labels := by
      have ha : raw23653step4 = raw23653step3 := by apply Matrix.ext; unfold raw23653step4 raw23653step3; decide +kernel
      have hl : raw23653step3Labels = labelEmbedding7 ∘ raw23653step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23653step3 raw23653step3Labels raw23653step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4228 node4228Labels := by rfl

def raw23654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw23654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw23654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23654step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23654step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23654 raw23654Labels = mixedMoment B node4389 node4389Labels := by
  calc
    mixedMoment B raw23654 raw23654Labels = mixedMoment B raw23654step0 raw23654step0Labels := by
      have hz : ∀ j, raw23654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23654step0 = (fun i j => raw23654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23654step0 raw23654; decide +kernel
      have hl : raw23654step0Labels = raw23654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23654 raw23654Labels permutation346 hz
    mixedMoment B raw23654step0 raw23654step0Labels = mixedMoment B raw23654step1 raw23654step1Labels := by
      have ha : raw23654step1 = (fun i j => raw23654step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23654step1 raw23654step0; decide +kernel
      have hl : raw23654step1Labels = raw23654step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23654step0 raw23654step0Labels permutation33 permutation6
    mixedMoment B raw23654step1 raw23654step1Labels = mixedMoment B raw23654step2 raw23654step2Labels := by
      have ha : raw23654step2 = raw23654step1 := by apply Matrix.ext; unfold raw23654step2 raw23654step1; decide +kernel
      have hl : raw23654step1Labels = labelEmbedding9 ∘ raw23654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23654step1 raw23654step1Labels raw23654step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4389 node4389Labels := by rfl

def raw23655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw23655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw23655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23655step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23655 raw23655Labels = mixedMoment B node4389 node4389Labels := by
  calc
    mixedMoment B raw23655 raw23655Labels = mixedMoment B raw23655step0 raw23655step0Labels := by
      have hz : ∀ j, raw23655 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23655step0 = (fun i j => raw23655 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23655step0 raw23655; decide +kernel
      have hl : raw23655step0Labels = raw23655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23655 raw23655Labels permutation265 hz
    mixedMoment B raw23655step0 raw23655step0Labels = mixedMoment B raw23655step1 raw23655step1Labels := by
      have ha : raw23655step1 = (fun i j => raw23655step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23655step1 raw23655step0; decide +kernel
      have hl : raw23655step1Labels = raw23655step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23655step0 raw23655step0Labels permutation33 permutation6
    mixedMoment B raw23655step1 raw23655step1Labels = mixedMoment B raw23655step2 raw23655step2Labels := by
      have ha : raw23655step2 = raw23655step1 := by apply Matrix.ext; unfold raw23655step2 raw23655step1; decide +kernel
      have hl : raw23655step1Labels = labelEmbedding9 ∘ raw23655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23655step1 raw23655step1Labels raw23655step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4389 node4389Labels := by rfl

def raw23656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw23656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw23656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw23656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw23656step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw23656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23656 raw23656Labels = mixedMoment B node4383 node4383Labels := by
  calc
    mixedMoment B raw23656 raw23656Labels = mixedMoment B raw23656step0 raw23656step0Labels := by
      have hz : ∀ j, raw23656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23656step0 = (fun i j => raw23656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23656step0 raw23656; decide +kernel
      have hl : raw23656step0Labels = raw23656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23656 raw23656Labels permutation346 hz
    mixedMoment B raw23656step0 raw23656step0Labels = mixedMoment B raw23656step1 raw23656step1Labels := by
      have hz : ∀ j, raw23656step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23656step1 = (fun i j => raw23656step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23656step1 raw23656step0; decide +kernel
      have hl : raw23656step1Labels = raw23656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23656step0 raw23656step0Labels permutation56 hz
    mixedMoment B raw23656step1 raw23656step1Labels = mixedMoment B raw23656step2 raw23656step2Labels := by
      have ha : raw23656step2 = (fun i j => raw23656step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23656step2 raw23656step1; decide +kernel
      have hl : raw23656step2Labels = raw23656step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23656step1 raw23656step1Labels permutation9 permutation6
    mixedMoment B raw23656step2 raw23656step2Labels = mixedMoment B raw23656step3 raw23656step3Labels := by
      have ha : raw23656step3 = raw23656step2 := by apply Matrix.ext; unfold raw23656step3 raw23656step2; decide +kernel
      have hl : raw23656step2Labels = labelEmbedding9 ∘ raw23656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23656step2 raw23656step2Labels raw23656step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4383 node4383Labels := by rfl

def raw23657 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw23657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw23657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw23657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw23657step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw23657step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23657step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw23657step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23657 raw23657Labels = mixedMoment B node4228 node4228Labels := by
  calc
    mixedMoment B raw23657 raw23657Labels = mixedMoment B raw23657step0 raw23657step0Labels := by
      have hz : ∀ j, raw23657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23657step0 = (fun i j => raw23657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23657step0 raw23657; decide +kernel
      have hl : raw23657step0Labels = raw23657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23657 raw23657Labels permutation346 hz
    mixedMoment B raw23657step0 raw23657step0Labels = mixedMoment B raw23657step1 raw23657step1Labels := by
      have hz : ∀ j, raw23657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23657step1 = (fun i j => raw23657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23657step1 raw23657step0; decide +kernel
      have hl : raw23657step1Labels = raw23657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23657step0 raw23657step0Labels permutation56 hz
    mixedMoment B raw23657step1 raw23657step1Labels = mixedMoment B raw23657step2 raw23657step2Labels := by
      have ha : raw23657step2 = (fun i j => raw23657step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23657step2 raw23657step1; decide +kernel
      have hl : raw23657step2Labels = raw23657step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23657step1 raw23657step1Labels permutation8 permutation4
    mixedMoment B raw23657step2 raw23657step2Labels = mixedMoment B raw23657step3 raw23657step3Labels := by
      have ha : raw23657step3 = -raw23657step2 := by apply Matrix.ext; change ∀ i j, raw23657step3 i j = -(raw23657step2 i j); unfold raw23657step3 raw23657step2; decide +kernel
      have hl : raw23657step3Labels = raw23657step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23657step3 raw23657step3Labels = mixedMoment B raw23657step4 raw23657step4Labels := by
      have ha : raw23657step4 = raw23657step3 := by apply Matrix.ext; unfold raw23657step4 raw23657step3; decide +kernel
      have hl : raw23657step3Labels = labelEmbedding7 ∘ raw23657step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23657step3 raw23657step3Labels raw23657step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4228 node4228Labels := by rfl

def raw23658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw23658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw23658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23658step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23658 raw23658Labels = mixedMoment B node4389 node4389Labels := by
  calc
    mixedMoment B raw23658 raw23658Labels = mixedMoment B raw23658step0 raw23658step0Labels := by
      have hz : ∀ j, raw23658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23658step0 = (fun i j => raw23658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23658step0 raw23658; decide +kernel
      have hl : raw23658step0Labels = raw23658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23658 raw23658Labels permutation346 hz
    mixedMoment B raw23658step0 raw23658step0Labels = mixedMoment B raw23658step1 raw23658step1Labels := by
      have ha : raw23658step1 = (fun i j => raw23658step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23658step1 raw23658step0; decide +kernel
      have hl : raw23658step1Labels = raw23658step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23658step0 raw23658step0Labels permutation32 permutation6
    mixedMoment B raw23658step1 raw23658step1Labels = mixedMoment B raw23658step2 raw23658step2Labels := by
      have ha : raw23658step2 = raw23658step1 := by apply Matrix.ext; unfold raw23658step2 raw23658step1; decide +kernel
      have hl : raw23658step1Labels = labelEmbedding9 ∘ raw23658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23658step1 raw23658step1Labels raw23658step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4389 node4389Labels := by rfl

def raw23659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw23659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw23659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23659step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw23659step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23659 raw23659Labels = mixedMoment B node4389 node4389Labels := by
  calc
    mixedMoment B raw23659 raw23659Labels = mixedMoment B raw23659step0 raw23659step0Labels := by
      have hz : ∀ j, raw23659 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23659step0 = (fun i j => raw23659 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23659step0 raw23659; decide +kernel
      have hl : raw23659step0Labels = raw23659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23659 raw23659Labels permutation265 hz
    mixedMoment B raw23659step0 raw23659step0Labels = mixedMoment B raw23659step1 raw23659step1Labels := by
      have ha : raw23659step1 = (fun i j => raw23659step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23659step1 raw23659step0; decide +kernel
      have hl : raw23659step1Labels = raw23659step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23659step0 raw23659step0Labels permutation32 permutation6
    mixedMoment B raw23659step1 raw23659step1Labels = mixedMoment B raw23659step2 raw23659step2Labels := by
      have ha : raw23659step2 = raw23659step1 := by apply Matrix.ext; unfold raw23659step2 raw23659step1; decide +kernel
      have hl : raw23659step1Labels = labelEmbedding9 ∘ raw23659step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23659step1 raw23659step1Labels raw23659step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4389 node4389Labels := by rfl

def raw23660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw23660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw23660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw23660step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw23660step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23660step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw23660step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23660 raw23660Labels = mixedMoment B node4383 node4383Labels := by
  calc
    mixedMoment B raw23660 raw23660Labels = mixedMoment B raw23660step0 raw23660step0Labels := by
      have hz : ∀ j, raw23660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23660step0 = (fun i j => raw23660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23660step0 raw23660; decide +kernel
      have hl : raw23660step0Labels = raw23660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23660 raw23660Labels permutation346 hz
    mixedMoment B raw23660step0 raw23660step0Labels = mixedMoment B raw23660step1 raw23660step1Labels := by
      have hz : ∀ j, raw23660step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23660step1 = (fun i j => raw23660step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23660step1 raw23660step0; decide +kernel
      have hl : raw23660step1Labels = raw23660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23660step0 raw23660step0Labels permutation56 hz
    mixedMoment B raw23660step1 raw23660step1Labels = mixedMoment B raw23660step2 raw23660step2Labels := by
      have ha : raw23660step2 = (fun i j => raw23660step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23660step2 raw23660step1; decide +kernel
      have hl : raw23660step2Labels = raw23660step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23660step1 raw23660step1Labels permutation8 permutation6
    mixedMoment B raw23660step2 raw23660step2Labels = mixedMoment B raw23660step3 raw23660step3Labels := by
      have ha : raw23660step3 = raw23660step2 := by apply Matrix.ext; unfold raw23660step3 raw23660step2; decide +kernel
      have hl : raw23660step2Labels = labelEmbedding9 ∘ raw23660step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23660step2 raw23660step2Labels raw23660step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4383 node4383Labels := by rfl

def raw23661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw23661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw23661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw23661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23661step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23661step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23661 raw23661Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw23661 raw23661Labels = mixedMoment B raw23661step0 raw23661step0Labels := by
      have hz : ∀ j, raw23661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23661step0 = (fun i j => raw23661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23661step0 raw23661; decide +kernel
      have hl : raw23661step0Labels = raw23661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23661 raw23661Labels permutation346 hz
    mixedMoment B raw23661step0 raw23661step0Labels = mixedMoment B raw23661step1 raw23661step1Labels := by
      have hz : ∀ j, raw23661step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23661step1 = (fun i j => raw23661step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23661step1 raw23661step0; decide +kernel
      have hl : raw23661step1Labels = raw23661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23661step0 raw23661step0Labels permutation56 hz
    mixedMoment B raw23661step1 raw23661step1Labels = mixedMoment B raw23661step2 raw23661step2Labels := by
      have ha : raw23661step2 = (fun i j => raw23661step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23661step2 raw23661step1; decide +kernel
      have hl : raw23661step2Labels = raw23661step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23661step1 raw23661step1Labels permutation8 permutation6
    mixedMoment B raw23661step2 raw23661step2Labels = mixedMoment B raw23661step3 raw23661step3Labels := by
      have ha : raw23661step3 = raw23661step2 := by apply Matrix.ext; unfold raw23661step3 raw23661step2; decide +kernel
      have hl : raw23661step2Labels = labelEmbedding9 ∘ raw23661step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23661step2 raw23661step2Labels raw23661step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw23662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, 0, -2], ![2, -2, 0]]
def raw23662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23662 raw23662Labels = mixedMoment B node562 node562Labels := by
  calc
    mixedMoment B raw23662 raw23662Labels = mixedMoment B raw23662step0 raw23662step0Labels := by
      have hz : ∀ j, raw23662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23662step0 = (fun i j => raw23662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23662step0 raw23662; decide +kernel
      have hl : raw23662step0Labels = raw23662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23662 raw23662Labels permutation434 hz
    mixedMoment B raw23662step0 raw23662step0Labels = mixedMoment B raw23662step1 raw23662step1Labels := by
      have hz : ∀ j, raw23662step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23662step1 = (fun i j => raw23662step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23662step1 raw23662step0; decide +kernel
      have hl : raw23662step1Labels = raw23662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23662step0 raw23662step0Labels permutation80 hz
    mixedMoment B raw23662step1 raw23662step1Labels = mixedMoment B raw23662step2 raw23662step2Labels := by
      have ha : raw23662step2 = (fun i j => raw23662step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23662step2 raw23662step1; decide +kernel
      have hl : raw23662step2Labels = raw23662step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23662step1 raw23662step1Labels permutation9 permutation2
    _ = mixedMoment B node562 node562Labels := by rfl

def raw23663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23663 raw23663Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw23663 raw23663Labels = mixedMoment B raw23663step0 raw23663step0Labels := by
      have hz : ∀ j, raw23663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23663step0 = (fun i j => raw23663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23663step0 raw23663; decide +kernel
      have hl : raw23663step0Labels = raw23663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23663 raw23663Labels permutation434 hz
    mixedMoment B raw23663step0 raw23663step0Labels = mixedMoment B raw23663step1 raw23663step1Labels := by
      have ha : raw23663step1 = (fun i j => raw23663step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23663step1 raw23663step0; decide +kernel
      have hl : raw23663step1Labels = raw23663step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23663step0 raw23663step0Labels permutation39 permutation2
    _ = mixedMoment B node724 node724Labels := by rfl

def raw23664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23664step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23664 raw23664Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw23664 raw23664Labels = mixedMoment B raw23664step0 raw23664step0Labels := by
      have hz : ∀ j, raw23664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23664step0 = (fun i j => raw23664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23664step0 raw23664; decide +kernel
      have hl : raw23664step0Labels = raw23664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23664 raw23664Labels permutation346 hz
    mixedMoment B raw23664step0 raw23664step0Labels = mixedMoment B raw23664step1 raw23664step1Labels := by
      have ha : raw23664step1 = (fun i j => raw23664step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23664step1 raw23664step0; decide +kernel
      have hl : raw23664step1Labels = raw23664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23664step0 raw23664step0Labels permutation39 permutation2
    _ = mixedMoment B node724 node724Labels := by rfl

def raw23665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![2, 0, -2], ![1, -1, 0]]
def raw23665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23665 raw23665Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw23665 raw23665Labels = mixedMoment B raw23665step0 raw23665step0Labels := by
      have hz : ∀ j, raw23665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23665step0 = (fun i j => raw23665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23665step0 raw23665; decide +kernel
      have hl : raw23665step0Labels = raw23665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23665 raw23665Labels permutation434 hz
    mixedMoment B raw23665step0 raw23665step0Labels = mixedMoment B raw23665step1 raw23665step1Labels := by
      have hz : ∀ j, raw23665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23665step1 = (fun i j => raw23665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23665step1 raw23665step0; decide +kernel
      have hl : raw23665step1Labels = raw23665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23665step0 raw23665step0Labels permutation80 hz
    mixedMoment B raw23665step1 raw23665step1Labels = mixedMoment B raw23665step2 raw23665step2Labels := by
      have ha : raw23665step2 = (fun i j => raw23665step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23665step2 raw23665step1; decide +kernel
      have hl : raw23665step2Labels = raw23665step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23665step1 raw23665step1Labels permutation12 permutation2
    _ = mixedMoment B node852 node852Labels := by rfl

def raw23666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23666 raw23666Labels = mixedMoment B node1661 node1661Labels := by
  calc
    mixedMoment B raw23666 raw23666Labels = mixedMoment B raw23666step0 raw23666step0Labels := by
      have hz : ∀ j, raw23666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23666step0 = (fun i j => raw23666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23666step0 raw23666; decide +kernel
      have hl : raw23666step0Labels = raw23666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23666 raw23666Labels permutation434 hz
    mixedMoment B raw23666step0 raw23666step0Labels = mixedMoment B raw23666step1 raw23666step1Labels := by
      have hz : ∀ j, raw23666step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23666step1 = (fun i j => raw23666step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23666step1 raw23666step0; decide +kernel
      have hl : raw23666step1Labels = raw23666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23666step0 raw23666step0Labels permutation80 hz
    _ = mixedMoment B node1661 node1661Labels := by rfl

def raw23667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23667step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23667 raw23667Labels = mixedMoment B node1612 node1612Labels := by
  calc
    mixedMoment B raw23667 raw23667Labels = mixedMoment B raw23667step0 raw23667step0Labels := by
      have hz : ∀ j, raw23667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23667step0 = (fun i j => raw23667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23667step0 raw23667; decide +kernel
      have hl : raw23667step0Labels = raw23667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23667 raw23667Labels permutation434 hz
    mixedMoment B raw23667step0 raw23667step0Labels = mixedMoment B raw23667step1 raw23667step1Labels := by
      have ha : raw23667step1 = (fun i j => raw23667step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23667step1 raw23667step0; decide +kernel
      have hl : raw23667step1Labels = raw23667step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23667step0 raw23667step0Labels permutation38 permutation2
    _ = mixedMoment B node1612 node1612Labels := by rfl

def raw23668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23668 raw23668Labels = mixedMoment B node1612 node1612Labels := by
  calc
    mixedMoment B raw23668 raw23668Labels = mixedMoment B raw23668step0 raw23668step0Labels := by
      have hz : ∀ j, raw23668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23668step0 = (fun i j => raw23668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23668step0 raw23668; decide +kernel
      have hl : raw23668step0Labels = raw23668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23668 raw23668Labels permutation346 hz
    mixedMoment B raw23668step0 raw23668step0Labels = mixedMoment B raw23668step1 raw23668step1Labels := by
      have ha : raw23668step1 = (fun i j => raw23668step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23668step1 raw23668step0; decide +kernel
      have hl : raw23668step1Labels = raw23668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23668step0 raw23668step0Labels permutation38 permutation2
    _ = mixedMoment B node1612 node1612Labels := by rfl

def raw23669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, -1, -1], ![1, 0, -1]]
def raw23669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw23669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23669 raw23669Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw23669 raw23669Labels = mixedMoment B raw23669step0 raw23669step0Labels := by
      have hz : ∀ j, raw23669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23669step0 = (fun i j => raw23669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23669step0 raw23669; decide +kernel
      have hl : raw23669step0Labels = raw23669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23669 raw23669Labels permutation434 hz
    mixedMoment B raw23669step0 raw23669step0Labels = mixedMoment B raw23669step1 raw23669step1Labels := by
      have hz : ∀ j, raw23669step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23669step1 = (fun i j => raw23669step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23669step1 raw23669step0; decide +kernel
      have hl : raw23669step1Labels = raw23669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23669step0 raw23669step0Labels permutation80 hz
    mixedMoment B raw23669step1 raw23669step1Labels = mixedMoment B raw23669step2 raw23669step2Labels := by
      have ha : raw23669step2 = (fun i j => raw23669step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23669step2 raw23669step1; decide +kernel
      have hl : raw23669step2Labels = raw23669step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23669step1 raw23669step1Labels permutation9 permutation2
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw23670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23670 raw23670Labels = mixedMoment B node563 node563Labels := by
  calc
    mixedMoment B raw23670 raw23670Labels = mixedMoment B raw23670step0 raw23670step0Labels := by
      have hz : ∀ j, raw23670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23670step0 = (fun i j => raw23670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23670step0 raw23670; decide +kernel
      have hl : raw23670step0Labels = raw23670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23670 raw23670Labels permutation434 hz
    mixedMoment B raw23670step0 raw23670step0Labels = mixedMoment B raw23670step1 raw23670step1Labels := by
      have hz : ∀ j, raw23670step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23670step1 = (fun i j => raw23670step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23670step1 raw23670step0; decide +kernel
      have hl : raw23670step1Labels = raw23670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23670step0 raw23670step0Labels permutation80 hz
    _ = mixedMoment B node563 node563Labels := by rfl

def raw23671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23671step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23671 raw23671Labels = mixedMoment B node725 node725Labels := by
  calc
    mixedMoment B raw23671 raw23671Labels = mixedMoment B raw23671step0 raw23671step0Labels := by
      have hz : ∀ j, raw23671 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23671step0 = (fun i j => raw23671 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23671step0 raw23671; decide +kernel
      have hl : raw23671step0Labels = raw23671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23671 raw23671Labels permutation434 hz
    mixedMoment B raw23671step0 raw23671step0Labels = mixedMoment B raw23671step1 raw23671step1Labels := by
      have ha : raw23671step1 = (fun i j => raw23671step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23671step1 raw23671step0; decide +kernel
      have hl : raw23671step1Labels = raw23671step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23671step0 raw23671step0Labels permutation38 permutation2
    _ = mixedMoment B node725 node725Labels := by rfl

def raw23672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23672 raw23672Labels = mixedMoment B node725 node725Labels := by
  calc
    mixedMoment B raw23672 raw23672Labels = mixedMoment B raw23672step0 raw23672step0Labels := by
      have hz : ∀ j, raw23672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23672step0 = (fun i j => raw23672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23672step0 raw23672; decide +kernel
      have hl : raw23672step0Labels = raw23672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23672 raw23672Labels permutation346 hz
    mixedMoment B raw23672step0 raw23672step0Labels = mixedMoment B raw23672step1 raw23672step1Labels := by
      have ha : raw23672step1 = (fun i j => raw23672step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23672step1 raw23672step0; decide +kernel
      have hl : raw23672step1Labels = raw23672step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23672step0 raw23672step0Labels permutation38 permutation2
    _ = mixedMoment B node725 node725Labels := by rfl

def raw23673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw23673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23673 raw23673Labels = mixedMoment B node856 node856Labels := by
  calc
    mixedMoment B raw23673 raw23673Labels = mixedMoment B raw23673step0 raw23673step0Labels := by
      have hz : ∀ j, raw23673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23673step0 = (fun i j => raw23673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23673step0 raw23673; decide +kernel
      have hl : raw23673step0Labels = raw23673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23673 raw23673Labels permutation434 hz
    mixedMoment B raw23673step0 raw23673step0Labels = mixedMoment B raw23673step1 raw23673step1Labels := by
      have hz : ∀ j, raw23673step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23673step1 = (fun i j => raw23673step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23673step1 raw23673step0; decide +kernel
      have hl : raw23673step1Labels = raw23673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23673step0 raw23673step0Labels permutation80 hz
    mixedMoment B raw23673step1 raw23673step1Labels = mixedMoment B raw23673step2 raw23673step2Labels := by
      have ha : raw23673step2 = (fun i j => raw23673step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23673step2 raw23673step1; decide +kernel
      have hl : raw23673step2Labels = raw23673step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23673step1 raw23673step1Labels permutation12 permutation2
    _ = mixedMoment B node856 node856Labels := by rfl

def raw23674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23674step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23674step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23674 raw23674Labels = mixedMoment B node1640 node1640Labels := by
  calc
    mixedMoment B raw23674 raw23674Labels = mixedMoment B raw23674step0 raw23674step0Labels := by
      have hz : ∀ j, raw23674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23674step0 = (fun i j => raw23674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23674step0 raw23674; decide +kernel
      have hl : raw23674step0Labels = raw23674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23674 raw23674Labels permutation434 hz
    mixedMoment B raw23674step0 raw23674step0Labels = mixedMoment B raw23674step1 raw23674step1Labels := by
      have ha : raw23674step1 = (fun i j => raw23674step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23674step1 raw23674step0; decide +kernel
      have hl : raw23674step1Labels = raw23674step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23674step0 raw23674step0Labels permutation33 permutation2
    _ = mixedMoment B node1640 node1640Labels := by rfl

def raw23675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23675 raw23675Labels = mixedMoment B node1640 node1640Labels := by
  calc
    mixedMoment B raw23675 raw23675Labels = mixedMoment B raw23675step0 raw23675step0Labels := by
      have hz : ∀ j, raw23675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23675step0 = (fun i j => raw23675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23675step0 raw23675; decide +kernel
      have hl : raw23675step0Labels = raw23675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23675 raw23675Labels permutation434 hz
    mixedMoment B raw23675step0 raw23675step0Labels = mixedMoment B raw23675step1 raw23675step1Labels := by
      have ha : raw23675step1 = (fun i j => raw23675step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23675step1 raw23675step0; decide +kernel
      have hl : raw23675step1Labels = raw23675step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23675step0 raw23675step0Labels permutation39 permutation2
    _ = mixedMoment B node1640 node1640Labels := by rfl

def raw23676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23676 raw23676Labels = mixedMoment B node1594 node1594Labels := by
  calc
    mixedMoment B raw23676 raw23676Labels = mixedMoment B raw23676step0 raw23676step0Labels := by
      have ha : raw23676step0 = (fun i j => raw23676 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23676step0 raw23676; decide +kernel
      have hl : raw23676step0Labels = raw23676Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23676 raw23676Labels permutation201 permutation2
    _ = mixedMoment B node1594 node1594Labels := by rfl

def raw23677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw23677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23677 raw23677Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw23677 raw23677Labels = mixedMoment B raw23677step0 raw23677step0Labels := by
      have hz : ∀ j, raw23677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23677step0 = (fun i j => raw23677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23677step0 raw23677; decide +kernel
      have hl : raw23677step0Labels = raw23677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23677 raw23677Labels permutation434 hz
    mixedMoment B raw23677step0 raw23677step0Labels = mixedMoment B raw23677step1 raw23677step1Labels := by
      have ha : raw23677step1 = (fun i j => raw23677step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23677step1 raw23677step0; decide +kernel
      have hl : raw23677step1Labels = raw23677step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23677step0 raw23677step0Labels permutation33 permutation2
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw23678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23678 raw23678Labels = mixedMoment B node543 node543Labels := by
  calc
    mixedMoment B raw23678 raw23678Labels = mixedMoment B raw23678step0 raw23678step0Labels := by
      have hz : ∀ j, raw23678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23678step0 = (fun i j => raw23678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23678step0 raw23678; decide +kernel
      have hl : raw23678step0Labels = raw23678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23678 raw23678Labels permutation434 hz
    mixedMoment B raw23678step0 raw23678step0Labels = mixedMoment B raw23678step1 raw23678step1Labels := by
      have ha : raw23678step1 = (fun i j => raw23678step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23678step1 raw23678step0; decide +kernel
      have hl : raw23678step1Labels = raw23678step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23678step0 raw23678step0Labels permutation39 permutation2
    _ = mixedMoment B node543 node543Labels := by rfl

def raw23679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23679 raw23679Labels = mixedMoment B node738 node738Labels := by
  calc
    mixedMoment B raw23679 raw23679Labels = mixedMoment B raw23679step0 raw23679step0Labels := by
      have hz : ∀ j, raw23679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23679step0 = (fun i j => raw23679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23679step0 raw23679; decide +kernel
      have hl : raw23679step0Labels = raw23679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23679 raw23679Labels permutation434 hz
    mixedMoment B raw23679step0 raw23679step0Labels = mixedMoment B raw23679step1 raw23679step1Labels := by
      have ha : raw23679step1 = (fun i j => raw23679step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23679step1 raw23679step0; decide +kernel
      have hl : raw23679step1Labels = raw23679step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23679step0 raw23679step0Labels permutation39 permutation2
    _ = mixedMoment B node738 node738Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
