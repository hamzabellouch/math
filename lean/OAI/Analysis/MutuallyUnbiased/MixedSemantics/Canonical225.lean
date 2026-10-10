import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28800 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28800step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28800step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28800step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28800step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28800 raw28800Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw28800 raw28800Labels = mixedMoment B raw28800step0 raw28800step0Labels := by
      have hz : ∀ j, raw28800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28800step0 = (fun i j => raw28800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28800step0 raw28800; decide +kernel
      have hl : raw28800step0Labels = raw28800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28800 raw28800Labels permutation346 hz
    mixedMoment B raw28800step0 raw28800step0Labels = mixedMoment B raw28800step1 raw28800step1Labels := by
      have ha : raw28800step1 = (fun i j => raw28800step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28800step1 raw28800step0; decide +kernel
      have hl : raw28800step1Labels = raw28800step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28800step0 raw28800step0Labels permutation151 permutation6
    mixedMoment B raw28800step1 raw28800step1Labels = mixedMoment B raw28800step2 raw28800step2Labels := by
      have ha : raw28800step2 = -raw28800step1 := by apply Matrix.ext; change ∀ i j, raw28800step2 i j = -(raw28800step1 i j); unfold raw28800step2 raw28800step1; decide +kernel
      have hl : raw28800step2Labels = raw28800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28800step2 raw28800step2Labels = mixedMoment B raw28800step3 raw28800step3Labels := by
      have ha : raw28800step3 = raw28800step2 := by apply Matrix.ext; unfold raw28800step3 raw28800step2; decide +kernel
      have hl : raw28800step2Labels = labelEmbedding9 ∘ raw28800step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28800step2 raw28800step2Labels raw28800step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw28801 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw28801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw28801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28801step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28801step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28801 raw28801Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw28801 raw28801Labels = mixedMoment B raw28801step0 raw28801step0Labels := by
      have hz : ∀ j, raw28801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28801step0 = (fun i j => raw28801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28801step0 raw28801; decide +kernel
      have hl : raw28801step0Labels = raw28801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28801 raw28801Labels permutation346 hz
    mixedMoment B raw28801step0 raw28801step0Labels = mixedMoment B raw28801step1 raw28801step1Labels := by
      have ha : raw28801step1 = (fun i j => raw28801step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28801step1 raw28801step0; decide +kernel
      have hl : raw28801step1Labels = raw28801step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28801step0 raw28801step0Labels permutation32 permutation7
    mixedMoment B raw28801step1 raw28801step1Labels = mixedMoment B raw28801step2 raw28801step2Labels := by
      have ha : raw28801step2 = raw28801step1 := by apply Matrix.ext; unfold raw28801step2 raw28801step1; decide +kernel
      have hl : raw28801step1Labels = labelEmbedding10 ∘ raw28801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28801step1 raw28801step1Labels raw28801step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw28802 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw28802step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28802step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28802step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28802step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28802 raw28802Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw28802 raw28802Labels = mixedMoment B raw28802step0 raw28802step0Labels := by
      have hz : ∀ j, raw28802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28802step0 = (fun i j => raw28802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28802step0 raw28802; decide +kernel
      have hl : raw28802step0Labels = raw28802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28802 raw28802Labels permutation346 hz
    mixedMoment B raw28802step0 raw28802step0Labels = mixedMoment B raw28802step1 raw28802step1Labels := by
      have ha : raw28802step1 = (fun i j => raw28802step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28802step1 raw28802step0; decide +kernel
      have hl : raw28802step1Labels = raw28802step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28802step0 raw28802step0Labels permutation38 permutation4
    mixedMoment B raw28802step1 raw28802step1Labels = mixedMoment B raw28802step2 raw28802step2Labels := by
      have ha : raw28802step2 = -raw28802step1 := by apply Matrix.ext; change ∀ i j, raw28802step2 i j = -(raw28802step1 i j); unfold raw28802step2 raw28802step1; decide +kernel
      have hl : raw28802step2Labels = raw28802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28802step2 raw28802step2Labels = mixedMoment B raw28802step3 raw28802step3Labels := by
      have ha : raw28802step3 = raw28802step2 := by apply Matrix.ext; unfold raw28802step3 raw28802step2; decide +kernel
      have hl : raw28802step2Labels = labelEmbedding7 ∘ raw28802step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28802step2 raw28802step2Labels raw28802step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw28803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw28803step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28803step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28803step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28803 raw28803Labels = mixedMoment B node5064 node5064Labels := by
  calc
    mixedMoment B raw28803 raw28803Labels = mixedMoment B raw28803step0 raw28803step0Labels := by
      have ha : raw28803step0 = (fun i j => raw28803 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28803step0 raw28803; decide +kernel
      have hl : raw28803step0Labels = raw28803Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28803 raw28803Labels permutation682 permutation6
    mixedMoment B raw28803step0 raw28803step0Labels = mixedMoment B raw28803step1 raw28803step1Labels := by
      have ha : raw28803step1 = -raw28803step0 := by apply Matrix.ext; change ∀ i j, raw28803step1 i j = -(raw28803step0 i j); unfold raw28803step1 raw28803step0; decide +kernel
      have hl : raw28803step1Labels = raw28803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28803step1 raw28803step1Labels = mixedMoment B raw28803step2 raw28803step2Labels := by
      have ha : raw28803step2 = raw28803step1 := by apply Matrix.ext; unfold raw28803step2 raw28803step1; decide +kernel
      have hl : raw28803step1Labels = labelEmbedding9 ∘ raw28803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28803step1 raw28803step1Labels raw28803step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5064 node5064Labels := by rfl

def raw28804 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw28804step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw28804step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28804step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw28804step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28804 raw28804Labels = mixedMoment B node5084 node5084Labels := by
  calc
    mixedMoment B raw28804 raw28804Labels = mixedMoment B raw28804step0 raw28804step0Labels := by
      have hz : ∀ j, raw28804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28804step0 = (fun i j => raw28804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28804step0 raw28804; decide +kernel
      have hl : raw28804step0Labels = raw28804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28804 raw28804Labels permutation346 hz
    mixedMoment B raw28804step0 raw28804step0Labels = mixedMoment B raw28804step1 raw28804step1Labels := by
      have ha : raw28804step1 = (fun i j => raw28804step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28804step1 raw28804step0; decide +kernel
      have hl : raw28804step1Labels = raw28804step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28804step0 raw28804step0Labels permutation151 permutation6
    mixedMoment B raw28804step1 raw28804step1Labels = mixedMoment B raw28804step2 raw28804step2Labels := by
      have ha : raw28804step2 = -raw28804step1 := by apply Matrix.ext; change ∀ i j, raw28804step2 i j = -(raw28804step1 i j); unfold raw28804step2 raw28804step1; decide +kernel
      have hl : raw28804step2Labels = raw28804step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28804step2 raw28804step2Labels = mixedMoment B raw28804step3 raw28804step3Labels := by
      have ha : raw28804step3 = raw28804step2 := by apply Matrix.ext; unfold raw28804step3 raw28804step2; decide +kernel
      have hl : raw28804step2Labels = labelEmbedding9 ∘ raw28804step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28804step2 raw28804step2Labels raw28804step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5084 node5084Labels := by rfl

def raw28805 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw28805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw28805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw28805step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28805step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28805step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28805step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28805 raw28805Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw28805 raw28805Labels = mixedMoment B raw28805step0 raw28805step0Labels := by
      have hz : ∀ j, raw28805 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28805step0 = (fun i j => raw28805 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28805step0 raw28805; decide +kernel
      have hl : raw28805step0Labels = raw28805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28805 raw28805Labels permutation346 hz
    mixedMoment B raw28805step0 raw28805step0Labels = mixedMoment B raw28805step1 raw28805step1Labels := by
      have ha : raw28805step1 = (fun i j => raw28805step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28805step1 raw28805step0; decide +kernel
      have hl : raw28805step1Labels = raw28805step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28805step0 raw28805step0Labels permutation151 permutation6
    mixedMoment B raw28805step1 raw28805step1Labels = mixedMoment B raw28805step2 raw28805step2Labels := by
      have ha : raw28805step2 = -raw28805step1 := by apply Matrix.ext; change ∀ i j, raw28805step2 i j = -(raw28805step1 i j); unfold raw28805step2 raw28805step1; decide +kernel
      have hl : raw28805step2Labels = raw28805step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28805step2 raw28805step2Labels = mixedMoment B raw28805step3 raw28805step3Labels := by
      have ha : raw28805step3 = raw28805step2 := by apply Matrix.ext; unfold raw28805step3 raw28805step2; decide +kernel
      have hl : raw28805step2Labels = labelEmbedding9 ∘ raw28805step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28805step2 raw28805step2Labels raw28805step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw28806 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28806step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28806 raw28806Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw28806 raw28806Labels = mixedMoment B raw28806step0 raw28806step0Labels := by
      have ha : raw28806step0 = (fun i j => raw28806 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28806step0 raw28806; decide +kernel
      have hl : raw28806step0Labels = raw28806Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28806 raw28806Labels permutation158 permutation6
    mixedMoment B raw28806step0 raw28806step0Labels = mixedMoment B raw28806step1 raw28806step1Labels := by
      have ha : raw28806step1 = raw28806step0 := by apply Matrix.ext; unfold raw28806step1 raw28806step0; decide +kernel
      have hl : raw28806step0Labels = labelEmbedding9 ∘ raw28806step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28806step0 raw28806step0Labels raw28806step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw28807 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28807step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28807 raw28807Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw28807 raw28807Labels = mixedMoment B raw28807step0 raw28807step0Labels := by
      have ha : raw28807step0 = (fun i j => raw28807 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28807step0 raw28807; decide +kernel
      have hl : raw28807step0Labels = raw28807Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28807 raw28807Labels permutation158 permutation6
    mixedMoment B raw28807step0 raw28807step0Labels = mixedMoment B raw28807step1 raw28807step1Labels := by
      have ha : raw28807step1 = raw28807step0 := by apply Matrix.ext; unfold raw28807step1 raw28807step0; decide +kernel
      have hl : raw28807step0Labels = labelEmbedding9 ∘ raw28807step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28807step0 raw28807step0Labels raw28807step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5047 node5047Labels := by rfl

def raw28808 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28808step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28808step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28808step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28808step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28808 raw28808Labels = mixedMoment B node5051 node5051Labels := by
  calc
    mixedMoment B raw28808 raw28808Labels = mixedMoment B raw28808step0 raw28808step0Labels := by
      have ha : raw28808step0 = (fun i j => raw28808 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28808step0 raw28808; decide +kernel
      have hl : raw28808step0Labels = raw28808Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28808 raw28808Labels permutation682 permutation6
    mixedMoment B raw28808step0 raw28808step0Labels = mixedMoment B raw28808step1 raw28808step1Labels := by
      have ha : raw28808step1 = -raw28808step0 := by apply Matrix.ext; change ∀ i j, raw28808step1 i j = -(raw28808step0 i j); unfold raw28808step1 raw28808step0; decide +kernel
      have hl : raw28808step1Labels = raw28808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28808step1 raw28808step1Labels = mixedMoment B raw28808step2 raw28808step2Labels := by
      have ha : raw28808step2 = raw28808step1 := by apply Matrix.ext; unfold raw28808step2 raw28808step1; decide +kernel
      have hl : raw28808step1Labels = labelEmbedding9 ∘ raw28808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28808step1 raw28808step1Labels raw28808step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5051 node5051Labels := by rfl

def raw28809 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw28809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28809step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28809 raw28809Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw28809 raw28809Labels = mixedMoment B raw28809step0 raw28809step0Labels := by
      have ha : raw28809step0 = (fun i j => raw28809 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28809step0 raw28809; decide +kernel
      have hl : raw28809step0Labels = raw28809Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28809 raw28809Labels permutation158 permutation6
    mixedMoment B raw28809step0 raw28809step0Labels = mixedMoment B raw28809step1 raw28809step1Labels := by
      have ha : raw28809step1 = raw28809step0 := by apply Matrix.ext; unfold raw28809step1 raw28809step0; decide +kernel
      have hl : raw28809step0Labels = labelEmbedding9 ∘ raw28809step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28809step0 raw28809step0Labels raw28809step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5127 node5127Labels := by rfl

def raw28810 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw28810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw28810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28810step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28810step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28810 raw28810Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw28810 raw28810Labels = mixedMoment B raw28810step0 raw28810step0Labels := by
      have hz : ∀ j, raw28810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28810step0 = (fun i j => raw28810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28810step0 raw28810; decide +kernel
      have hl : raw28810step0Labels = raw28810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28810 raw28810Labels permutation346 hz
    mixedMoment B raw28810step0 raw28810step0Labels = mixedMoment B raw28810step1 raw28810step1Labels := by
      have ha : raw28810step1 = (fun i j => raw28810step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28810step1 raw28810step0; decide +kernel
      have hl : raw28810step1Labels = raw28810step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28810step0 raw28810step0Labels permutation32 permutation6
    mixedMoment B raw28810step1 raw28810step1Labels = mixedMoment B raw28810step2 raw28810step2Labels := by
      have ha : raw28810step2 = raw28810step1 := by apply Matrix.ext; unfold raw28810step2 raw28810step1; decide +kernel
      have hl : raw28810step1Labels = labelEmbedding9 ∘ raw28810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28810step1 raw28810step1Labels raw28810step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw28811 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw28811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw28811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw28811step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28811step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28811step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28811step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28811 raw28811Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw28811 raw28811Labels = mixedMoment B raw28811step0 raw28811step0Labels := by
      have hz : ∀ j, raw28811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28811step0 = (fun i j => raw28811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28811step0 raw28811; decide +kernel
      have hl : raw28811step0Labels = raw28811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28811 raw28811Labels permutation346 hz
    mixedMoment B raw28811step0 raw28811step0Labels = mixedMoment B raw28811step1 raw28811step1Labels := by
      have ha : raw28811step1 = (fun i j => raw28811step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28811step1 raw28811step0; decide +kernel
      have hl : raw28811step1Labels = raw28811step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28811step0 raw28811step0Labels permutation151 permutation6
    mixedMoment B raw28811step1 raw28811step1Labels = mixedMoment B raw28811step2 raw28811step2Labels := by
      have ha : raw28811step2 = -raw28811step1 := by apply Matrix.ext; change ∀ i j, raw28811step2 i j = -(raw28811step1 i j); unfold raw28811step2 raw28811step1; decide +kernel
      have hl : raw28811step2Labels = raw28811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28811step2 raw28811step2Labels = mixedMoment B raw28811step3 raw28811step3Labels := by
      have ha : raw28811step3 = raw28811step2 := by apply Matrix.ext; unfold raw28811step3 raw28811step2; decide +kernel
      have hl : raw28811step2Labels = labelEmbedding9 ∘ raw28811step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28811step2 raw28811step2Labels raw28811step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw28812 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw28812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28812step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28812step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28812 raw28812Labels = mixedMoment B node4991 node4991Labels := by
  calc
    mixedMoment B raw28812 raw28812Labels = mixedMoment B raw28812step0 raw28812step0Labels := by
      have ha : raw28812step0 = (fun i j => raw28812 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28812step0 raw28812; decide +kernel
      have hl : raw28812step0Labels = raw28812Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28812 raw28812Labels permutation682 permutation6
    mixedMoment B raw28812step0 raw28812step0Labels = mixedMoment B raw28812step1 raw28812step1Labels := by
      have ha : raw28812step1 = -raw28812step0 := by apply Matrix.ext; change ∀ i j, raw28812step1 i j = -(raw28812step0 i j); unfold raw28812step1 raw28812step0; decide +kernel
      have hl : raw28812step1Labels = raw28812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28812step1 raw28812step1Labels = mixedMoment B raw28812step2 raw28812step2Labels := by
      have ha : raw28812step2 = raw28812step1 := by apply Matrix.ext; unfold raw28812step2 raw28812step1; decide +kernel
      have hl : raw28812step1Labels = labelEmbedding9 ∘ raw28812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28812step1 raw28812step1Labels raw28812step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4991 node4991Labels := by rfl

def raw28813 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw28813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw28813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28813step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28813step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28813 raw28813Labels = mixedMoment B node5006 node5006Labels := by
  calc
    mixedMoment B raw28813 raw28813Labels = mixedMoment B raw28813step0 raw28813step0Labels := by
      have hz : ∀ j, raw28813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28813step0 = (fun i j => raw28813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28813step0 raw28813; decide +kernel
      have hl : raw28813step0Labels = raw28813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28813 raw28813Labels permutation346 hz
    mixedMoment B raw28813step0 raw28813step0Labels = mixedMoment B raw28813step1 raw28813step1Labels := by
      have ha : raw28813step1 = (fun i j => raw28813step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28813step1 raw28813step0; decide +kernel
      have hl : raw28813step1Labels = raw28813step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28813step0 raw28813step0Labels permutation151 permutation6
    mixedMoment B raw28813step1 raw28813step1Labels = mixedMoment B raw28813step2 raw28813step2Labels := by
      have ha : raw28813step2 = -raw28813step1 := by apply Matrix.ext; change ∀ i j, raw28813step2 i j = -(raw28813step1 i j); unfold raw28813step2 raw28813step1; decide +kernel
      have hl : raw28813step2Labels = raw28813step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28813step2 raw28813step2Labels = mixedMoment B raw28813step3 raw28813step3Labels := by
      have ha : raw28813step3 = raw28813step2 := by apply Matrix.ext; unfold raw28813step3 raw28813step2; decide +kernel
      have hl : raw28813step2Labels = labelEmbedding9 ∘ raw28813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28813step2 raw28813step2Labels raw28813step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5006 node5006Labels := by rfl

def raw28814 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw28814step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw28814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28814 raw28814Labels = mixedMoment B node4738 node4738Labels := by
  calc
    mixedMoment B raw28814 raw28814Labels = mixedMoment B raw28814step0 raw28814step0Labels := by
      have hz : ∀ j, raw28814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28814step0 = (fun i j => raw28814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28814step0 raw28814; decide +kernel
      have hl : raw28814step0Labels = raw28814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28814 raw28814Labels permutation346 hz
    mixedMoment B raw28814step0 raw28814step0Labels = mixedMoment B raw28814step1 raw28814step1Labels := by
      have ha : raw28814step1 = (fun i j => raw28814step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28814step1 raw28814step0; decide +kernel
      have hl : raw28814step1Labels = raw28814step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28814step0 raw28814step0Labels permutation149 permutation4
    mixedMoment B raw28814step1 raw28814step1Labels = mixedMoment B raw28814step2 raw28814step2Labels := by
      have ha : raw28814step2 = raw28814step1 := by apply Matrix.ext; unfold raw28814step2 raw28814step1; decide +kernel
      have hl : raw28814step1Labels = labelEmbedding7 ∘ raw28814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28814step1 raw28814step1Labels raw28814step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4738 node4738Labels := by rfl

def raw28815 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw28815step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28815step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28815step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28815step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28815 raw28815Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw28815 raw28815Labels = mixedMoment B raw28815step0 raw28815step0Labels := by
      have hz : ∀ j, raw28815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28815step0 = (fun i j => raw28815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28815step0 raw28815; decide +kernel
      have hl : raw28815step0Labels = raw28815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28815 raw28815Labels permutation346 hz
    mixedMoment B raw28815step0 raw28815step0Labels = mixedMoment B raw28815step1 raw28815step1Labels := by
      have ha : raw28815step1 = (fun i j => raw28815step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28815step1 raw28815step0; decide +kernel
      have hl : raw28815step1Labels = raw28815step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28815step0 raw28815step0Labels permutation151 permutation6
    mixedMoment B raw28815step1 raw28815step1Labels = mixedMoment B raw28815step2 raw28815step2Labels := by
      have ha : raw28815step2 = -raw28815step1 := by apply Matrix.ext; change ∀ i j, raw28815step2 i j = -(raw28815step1 i j); unfold raw28815step2 raw28815step1; decide +kernel
      have hl : raw28815step2Labels = raw28815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28815step2 raw28815step2Labels = mixedMoment B raw28815step3 raw28815step3Labels := by
      have ha : raw28815step3 = raw28815step2 := by apply Matrix.ext; unfold raw28815step3 raw28815step2; decide +kernel
      have hl : raw28815step2Labels = labelEmbedding9 ∘ raw28815step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28815step2 raw28815step2Labels raw28815step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4741 node4741Labels := by rfl

def raw28816 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28816step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28816step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28816step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28816 raw28816Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw28816 raw28816Labels = mixedMoment B raw28816step0 raw28816step0Labels := by
      have ha : raw28816step0 = (fun i j => raw28816 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28816step0 raw28816; decide +kernel
      have hl : raw28816step0Labels = raw28816Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28816 raw28816Labels permutation682 permutation6
    mixedMoment B raw28816step0 raw28816step0Labels = mixedMoment B raw28816step1 raw28816step1Labels := by
      have ha : raw28816step1 = -raw28816step0 := by apply Matrix.ext; change ∀ i j, raw28816step1 i j = -(raw28816step0 i j); unfold raw28816step1 raw28816step0; decide +kernel
      have hl : raw28816step1Labels = raw28816step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28816step1 raw28816step1Labels = mixedMoment B raw28816step2 raw28816step2Labels := by
      have ha : raw28816step2 = raw28816step1 := by apply Matrix.ext; unfold raw28816step2 raw28816step1; decide +kernel
      have hl : raw28816step1Labels = labelEmbedding9 ∘ raw28816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28816step1 raw28816step1Labels raw28816step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

def raw28817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28817step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28817 raw28817Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw28817 raw28817Labels = mixedMoment B raw28817step0 raw28817step0Labels := by
      have hz : ∀ j, raw28817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28817step0 = (fun i j => raw28817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28817step0 raw28817; decide +kernel
      have hl : raw28817step0Labels = raw28817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28817 raw28817Labels permutation346 hz
    mixedMoment B raw28817step0 raw28817step0Labels = mixedMoment B raw28817step1 raw28817step1Labels := by
      have ha : raw28817step1 = (fun i j => raw28817step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28817step1 raw28817step0; decide +kernel
      have hl : raw28817step1Labels = raw28817step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28817step0 raw28817step0Labels permutation149 permutation4
    mixedMoment B raw28817step1 raw28817step1Labels = mixedMoment B raw28817step2 raw28817step2Labels := by
      have ha : raw28817step2 = raw28817step1 := by apply Matrix.ext; unfold raw28817step2 raw28817step1; decide +kernel
      have hl : raw28817step1Labels = labelEmbedding7 ∘ raw28817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28817step1 raw28817step1Labels raw28817step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw28818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28818 raw28818Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw28818 raw28818Labels = mixedMoment B raw28818step0 raw28818step0Labels := by
      have hz : ∀ j, raw28818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28818step0 = (fun i j => raw28818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28818step0 raw28818; decide +kernel
      have hl : raw28818step0Labels = raw28818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28818 raw28818Labels permutation346 hz
    mixedMoment B raw28818step0 raw28818step0Labels = mixedMoment B raw28818step1 raw28818step1Labels := by
      have ha : raw28818step1 = (fun i j => raw28818step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28818step1 raw28818step0; decide +kernel
      have hl : raw28818step1Labels = raw28818step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28818step0 raw28818step0Labels permutation151 permutation2
    mixedMoment B raw28818step1 raw28818step1Labels = mixedMoment B raw28818step2 raw28818step2Labels := by
      have ha : raw28818step2 = -raw28818step1 := by apply Matrix.ext; change ∀ i j, raw28818step2 i j = -(raw28818step1 i j); unfold raw28818step2 raw28818step1; decide +kernel
      have hl : raw28818step2Labels = raw28818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw28819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28819 raw28819Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw28819 raw28819Labels = mixedMoment B raw28819step0 raw28819step0Labels := by
      have ha : raw28819step0 = (fun i j => raw28819 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28819step0 raw28819; decide +kernel
      have hl : raw28819step0Labels = raw28819Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28819 raw28819Labels permutation686 permutation2
    mixedMoment B raw28819step0 raw28819step0Labels = mixedMoment B raw28819step1 raw28819step1Labels := by
      have ha : raw28819step1 = -raw28819step0 := by apply Matrix.ext; change ∀ i j, raw28819step1 i j = -(raw28819step0 i j); unfold raw28819step1 raw28819step0; decide +kernel
      have hl : raw28819step1Labels = raw28819step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw28820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28820 raw28820Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw28820 raw28820Labels = mixedMoment B raw28820step0 raw28820step0Labels := by
      have hz : ∀ j, raw28820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28820step0 = (fun i j => raw28820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28820step0 raw28820; decide +kernel
      have hl : raw28820step0Labels = raw28820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28820 raw28820Labels permutation346 hz
    mixedMoment B raw28820step0 raw28820step0Labels = mixedMoment B raw28820step1 raw28820step1Labels := by
      have ha : raw28820step1 = (fun i j => raw28820step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28820step1 raw28820step0; decide +kernel
      have hl : raw28820step1Labels = raw28820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28820step0 raw28820step0Labels permutation149 permutation2
    mixedMoment B raw28820step1 raw28820step1Labels = mixedMoment B raw28820step2 raw28820step2Labels := by
      have ha : raw28820step2 = -raw28820step1 := by apply Matrix.ext; change ∀ i j, raw28820step2 i j = -(raw28820step1 i j); unfold raw28820step2 raw28820step1; decide +kernel
      have hl : raw28820step2Labels = raw28820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw28821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28821step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28821 raw28821Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw28821 raw28821Labels = mixedMoment B raw28821step0 raw28821step0Labels := by
      have hz : ∀ j, raw28821 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28821step0 = (fun i j => raw28821 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28821step0 raw28821; decide +kernel
      have hl : raw28821step0Labels = raw28821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28821 raw28821Labels permutation520 hz
    mixedMoment B raw28821step0 raw28821step0Labels = mixedMoment B raw28821step1 raw28821step1Labels := by
      have hz : ∀ j, raw28821step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28821step1 = (fun i j => raw28821step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28821step1 raw28821step0; decide +kernel
      have hl : raw28821step1Labels = raw28821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28821step0 raw28821step0Labels permutation80 hz
    mixedMoment B raw28821step1 raw28821step1Labels = mixedMoment B raw28821step2 raw28821step2Labels := by
      have ha : raw28821step2 = (fun i j => raw28821step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28821step2 raw28821step1; decide +kernel
      have hl : raw28821step2Labels = raw28821step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28821step1 raw28821step1Labels permutation31 permutation2
    mixedMoment B raw28821step2 raw28821step2Labels = mixedMoment B raw28821step3 raw28821step3Labels := by
      have ha : raw28821step3 = -raw28821step2 := by apply Matrix.ext; change ∀ i j, raw28821step3 i j = -(raw28821step2 i j); unfold raw28821step3 raw28821step2; decide +kernel
      have hl : raw28821step3Labels = raw28821step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw28822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28822 raw28822Labels = mixedMoment B node4756 node4756Labels := by
  calc
    mixedMoment B raw28822 raw28822Labels = mixedMoment B raw28822step0 raw28822step0Labels := by
      have ha : raw28822step0 = (fun i j => raw28822 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28822step0 raw28822; decide +kernel
      have hl : raw28822step0Labels = raw28822Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28822 raw28822Labels permutation646 permutation2
    mixedMoment B raw28822step0 raw28822step0Labels = mixedMoment B raw28822step1 raw28822step1Labels := by
      have ha : raw28822step1 = -raw28822step0 := by apply Matrix.ext; change ∀ i j, raw28822step1 i j = -(raw28822step0 i j); unfold raw28822step1 raw28822step0; decide +kernel
      have hl : raw28822step1Labels = raw28822step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4756 node4756Labels := by rfl

def raw28823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28823 raw28823Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw28823 raw28823Labels = mixedMoment B raw28823step0 raw28823step0Labels := by
      have ha : raw28823step0 = (fun i j => raw28823 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28823step0 raw28823; decide +kernel
      have hl : raw28823step0Labels = raw28823Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28823 raw28823Labels permutation644 permutation2
    mixedMoment B raw28823step0 raw28823step0Labels = mixedMoment B raw28823step1 raw28823step1Labels := by
      have ha : raw28823step1 = -raw28823step0 := by apply Matrix.ext; change ∀ i j, raw28823step1 i j = -(raw28823step0 i j); unfold raw28823step1 raw28823step0; decide +kernel
      have hl : raw28823step1Labels = raw28823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4760 node4760Labels := by rfl

def raw28824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28824 raw28824Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw28824 raw28824Labels = mixedMoment B raw28824step0 raw28824step0Labels := by
      have hz : ∀ j, raw28824 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28824step0 = (fun i j => raw28824 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28824step0 raw28824; decide +kernel
      have hl : raw28824step0Labels = raw28824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28824 raw28824Labels permutation520 hz
    mixedMoment B raw28824step0 raw28824step0Labels = mixedMoment B raw28824step1 raw28824step1Labels := by
      have ha : raw28824step1 = (fun i j => raw28824step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28824step1 raw28824step0; decide +kernel
      have hl : raw28824step1Labels = raw28824step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28824step0 raw28824step0Labels permutation145 permutation2
    mixedMoment B raw28824step1 raw28824step1Labels = mixedMoment B raw28824step2 raw28824step2Labels := by
      have ha : raw28824step2 = -raw28824step1 := by apply Matrix.ext; change ∀ i j, raw28824step2 i j = -(raw28824step1 i j); unfold raw28824step2 raw28824step1; decide +kernel
      have hl : raw28824step2Labels = raw28824step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw28825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28825 raw28825Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw28825 raw28825Labels = mixedMoment B raw28825step0 raw28825step0Labels := by
      have hz : ∀ j, raw28825 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28825step0 = (fun i j => raw28825 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28825step0 raw28825; decide +kernel
      have hl : raw28825step0Labels = raw28825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28825 raw28825Labels permutation346 hz
    mixedMoment B raw28825step0 raw28825step0Labels = mixedMoment B raw28825step1 raw28825step1Labels := by
      have ha : raw28825step1 = (fun i j => raw28825step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28825step1 raw28825step0; decide +kernel
      have hl : raw28825step1Labels = raw28825step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28825step0 raw28825step0Labels permutation151 permutation2
    mixedMoment B raw28825step1 raw28825step1Labels = mixedMoment B raw28825step2 raw28825step2Labels := by
      have ha : raw28825step2 = -raw28825step1 := by apply Matrix.ext; change ∀ i j, raw28825step2 i j = -(raw28825step1 i j); unfold raw28825step2 raw28825step1; decide +kernel
      have hl : raw28825step2Labels = raw28825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4776 node4776Labels := by rfl

def raw28826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28826 raw28826Labels = mixedMoment B node4771 node4771Labels := by
  calc
    mixedMoment B raw28826 raw28826Labels = mixedMoment B raw28826step0 raw28826step0Labels := by
      have ha : raw28826step0 = (fun i j => raw28826 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28826step0 raw28826; decide +kernel
      have hl : raw28826step0Labels = raw28826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28826 raw28826Labels permutation686 permutation2
    mixedMoment B raw28826step0 raw28826step0Labels = mixedMoment B raw28826step1 raw28826step1Labels := by
      have ha : raw28826step1 = -raw28826step0 := by apply Matrix.ext; change ∀ i j, raw28826step1 i j = -(raw28826step0 i j); unfold raw28826step1 raw28826step0; decide +kernel
      have hl : raw28826step1Labels = raw28826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4771 node4771Labels := by rfl

def raw28827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28827step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28827step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28827 raw28827Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw28827 raw28827Labels = mixedMoment B raw28827step0 raw28827step0Labels := by
      have hz : ∀ j, raw28827 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28827step0 = (fun i j => raw28827 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28827step0 raw28827; decide +kernel
      have hl : raw28827step0Labels = raw28827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28827 raw28827Labels permutation520 hz
    mixedMoment B raw28827step0 raw28827step0Labels = mixedMoment B raw28827step1 raw28827step1Labels := by
      have hz : ∀ j, raw28827step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28827step1 = (fun i j => raw28827step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28827step1 raw28827step0; decide +kernel
      have hl : raw28827step1Labels = raw28827step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28827step0 raw28827step0Labels permutation80 hz
    mixedMoment B raw28827step1 raw28827step1Labels = mixedMoment B raw28827step2 raw28827step2Labels := by
      have ha : raw28827step2 = (fun i j => raw28827step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28827step2 raw28827step1; decide +kernel
      have hl : raw28827step2Labels = raw28827step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28827step1 raw28827step1Labels permutation31 permutation2
    mixedMoment B raw28827step2 raw28827step2Labels = mixedMoment B raw28827step3 raw28827step3Labels := by
      have ha : raw28827step3 = -raw28827step2 := by apply Matrix.ext; change ∀ i j, raw28827step3 i j = -(raw28827step2 i j); unfold raw28827step3 raw28827step2; decide +kernel
      have hl : raw28827step3Labels = raw28827step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw28828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28828 raw28828Labels = mixedMoment B node4669 node4669Labels := by
  calc
    mixedMoment B raw28828 raw28828Labels = mixedMoment B raw28828step0 raw28828step0Labels := by
      have hz : ∀ j, raw28828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28828step0 = (fun i j => raw28828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28828step0 raw28828; decide +kernel
      have hl : raw28828step0Labels = raw28828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28828 raw28828Labels permutation346 hz
    mixedMoment B raw28828step0 raw28828step0Labels = mixedMoment B raw28828step1 raw28828step1Labels := by
      have ha : raw28828step1 = (fun i j => raw28828step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28828step1 raw28828step0; decide +kernel
      have hl : raw28828step1Labels = raw28828step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28828step0 raw28828step0Labels permutation151 permutation2
    mixedMoment B raw28828step1 raw28828step1Labels = mixedMoment B raw28828step2 raw28828step2Labels := by
      have ha : raw28828step2 = -raw28828step1 := by apply Matrix.ext; change ∀ i j, raw28828step2 i j = -(raw28828step1 i j); unfold raw28828step2 raw28828step1; decide +kernel
      have hl : raw28828step2Labels = raw28828step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4669 node4669Labels := by rfl

def raw28829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28829 raw28829Labels = mixedMoment B node4663 node4663Labels := by
  calc
    mixedMoment B raw28829 raw28829Labels = mixedMoment B raw28829step0 raw28829step0Labels := by
      have ha : raw28829step0 = (fun i j => raw28829 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28829step0 raw28829; decide +kernel
      have hl : raw28829step0Labels = raw28829Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28829 raw28829Labels permutation686 permutation2
    mixedMoment B raw28829step0 raw28829step0Labels = mixedMoment B raw28829step1 raw28829step1Labels := by
      have ha : raw28829step1 = -raw28829step0 := by apply Matrix.ext; change ∀ i j, raw28829step1 i j = -(raw28829step0 i j); unfold raw28829step1 raw28829step0; decide +kernel
      have hl : raw28829step1Labels = raw28829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4663 node4663Labels := by rfl

def raw28830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28830step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28830 raw28830Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw28830 raw28830Labels = mixedMoment B raw28830step0 raw28830step0Labels := by
      have hz : ∀ j, raw28830 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28830step0 = (fun i j => raw28830 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28830step0 raw28830; decide +kernel
      have hl : raw28830step0Labels = raw28830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28830 raw28830Labels permutation346 hz
    mixedMoment B raw28830step0 raw28830step0Labels = mixedMoment B raw28830step1 raw28830step1Labels := by
      have ha : raw28830step1 = (fun i j => raw28830step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28830step1 raw28830step0; decide +kernel
      have hl : raw28830step1Labels = raw28830step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28830step0 raw28830step0Labels permutation149 permutation2
    mixedMoment B raw28830step1 raw28830step1Labels = mixedMoment B raw28830step2 raw28830step2Labels := by
      have ha : raw28830step2 = -raw28830step1 := by apply Matrix.ext; change ∀ i j, raw28830step2 i j = -(raw28830step1 i j); unfold raw28830step2 raw28830step1; decide +kernel
      have hl : raw28830step2Labels = raw28830step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw28831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28831 raw28831Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw28831 raw28831Labels = mixedMoment B raw28831step0 raw28831step0Labels := by
      have hz : ∀ j, raw28831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28831step0 = (fun i j => raw28831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28831step0 raw28831; decide +kernel
      have hl : raw28831step0Labels = raw28831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28831 raw28831Labels permutation346 hz
    mixedMoment B raw28831step0 raw28831step0Labels = mixedMoment B raw28831step1 raw28831step1Labels := by
      have ha : raw28831step1 = (fun i j => raw28831step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28831step1 raw28831step0; decide +kernel
      have hl : raw28831step1Labels = raw28831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28831step0 raw28831step0Labels permutation151 permutation2
    mixedMoment B raw28831step1 raw28831step1Labels = mixedMoment B raw28831step2 raw28831step2Labels := by
      have ha : raw28831step2 = -raw28831step1 := by apply Matrix.ext; change ∀ i j, raw28831step2 i j = -(raw28831step1 i j); unfold raw28831step2 raw28831step1; decide +kernel
      have hl : raw28831step2Labels = raw28831step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4334 node4334Labels := by rfl

def raw28832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28832 raw28832Labels = mixedMoment B node4326 node4326Labels := by
  calc
    mixedMoment B raw28832 raw28832Labels = mixedMoment B raw28832step0 raw28832step0Labels := by
      have ha : raw28832step0 = (fun i j => raw28832 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28832step0 raw28832; decide +kernel
      have hl : raw28832step0Labels = raw28832Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28832 raw28832Labels permutation686 permutation2
    mixedMoment B raw28832step0 raw28832step0Labels = mixedMoment B raw28832step1 raw28832step1Labels := by
      have ha : raw28832step1 = -raw28832step0 := by apply Matrix.ext; change ∀ i j, raw28832step1 i j = -(raw28832step0 i j); unfold raw28832step1 raw28832step0; decide +kernel
      have hl : raw28832step1Labels = raw28832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4326 node4326Labels := by rfl

def raw28833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28833 raw28833Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw28833 raw28833Labels = mixedMoment B raw28833step0 raw28833step0Labels := by
      have hz : ∀ j, raw28833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28833step0 = (fun i j => raw28833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28833step0 raw28833; decide +kernel
      have hl : raw28833step0Labels = raw28833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28833 raw28833Labels permutation346 hz
    mixedMoment B raw28833step0 raw28833step0Labels = mixedMoment B raw28833step1 raw28833step1Labels := by
      have ha : raw28833step1 = (fun i j => raw28833step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28833step1 raw28833step0; decide +kernel
      have hl : raw28833step1Labels = raw28833step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28833step0 raw28833step0Labels permutation149 permutation2
    mixedMoment B raw28833step1 raw28833step1Labels = mixedMoment B raw28833step2 raw28833step2Labels := by
      have ha : raw28833step2 = -raw28833step1 := by apply Matrix.ext; change ∀ i j, raw28833step2 i j = -(raw28833step1 i j); unfold raw28833step2 raw28833step1; decide +kernel
      have hl : raw28833step2Labels = raw28833step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw28834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28834step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28834 raw28834Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw28834 raw28834Labels = mixedMoment B raw28834step0 raw28834step0Labels := by
      have hz : ∀ j, raw28834 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28834step0 = (fun i j => raw28834 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28834step0 raw28834; decide +kernel
      have hl : raw28834step0Labels = raw28834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28834 raw28834Labels permutation520 hz
    mixedMoment B raw28834step0 raw28834step0Labels = mixedMoment B raw28834step1 raw28834step1Labels := by
      have hz : ∀ j, raw28834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28834step1 = (fun i j => raw28834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28834step1 raw28834step0; decide +kernel
      have hl : raw28834step1Labels = raw28834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28834step0 raw28834step0Labels permutation80 hz
    mixedMoment B raw28834step1 raw28834step1Labels = mixedMoment B raw28834step2 raw28834step2Labels := by
      have ha : raw28834step2 = (fun i j => raw28834step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28834step2 raw28834step1; decide +kernel
      have hl : raw28834step2Labels = raw28834step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28834step1 raw28834step1Labels permutation31 permutation2
    mixedMoment B raw28834step2 raw28834step2Labels = mixedMoment B raw28834step3 raw28834step3Labels := by
      have ha : raw28834step3 = -raw28834step2 := by apply Matrix.ext; change ∀ i j, raw28834step3 i j = -(raw28834step2 i j); unfold raw28834step3 raw28834step2; decide +kernel
      have hl : raw28834step3Labels = raw28834step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw28835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw28835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28835 raw28835Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw28835 raw28835Labels = mixedMoment B raw28835step0 raw28835step0Labels := by
      have hz : ∀ j, raw28835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28835step0 = (fun i j => raw28835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28835step0 raw28835; decide +kernel
      have hl : raw28835step0Labels = raw28835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28835 raw28835Labels permutation346 hz
    mixedMoment B raw28835step0 raw28835step0Labels = mixedMoment B raw28835step1 raw28835step1Labels := by
      have ha : raw28835step1 = (fun i j => raw28835step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28835step1 raw28835step0; decide +kernel
      have hl : raw28835step1Labels = raw28835step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28835step0 raw28835step0Labels permutation150 permutation3
    mixedMoment B raw28835step1 raw28835step1Labels = mixedMoment B raw28835step2 raw28835step2Labels := by
      have ha : raw28835step2 = -raw28835step1 := by apply Matrix.ext; change ∀ i j, raw28835step2 i j = -(raw28835step1 i j); unfold raw28835step2 raw28835step1; decide +kernel
      have hl : raw28835step2Labels = raw28835step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw28836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28836 raw28836Labels = mixedMoment B node3205 node3205Labels := by
  calc
    mixedMoment B raw28836 raw28836Labels = mixedMoment B raw28836step0 raw28836step0Labels := by
      have ha : raw28836step0 = (fun i j => raw28836 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28836step0 raw28836; decide +kernel
      have hl : raw28836step0Labels = raw28836Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28836 raw28836Labels permutation686 permutation3
    mixedMoment B raw28836step0 raw28836step0Labels = mixedMoment B raw28836step1 raw28836step1Labels := by
      have ha : raw28836step1 = -raw28836step0 := by apply Matrix.ext; change ∀ i j, raw28836step1 i j = -(raw28836step0 i j); unfold raw28836step1 raw28836step0; decide +kernel
      have hl : raw28836step1Labels = raw28836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3205 node3205Labels := by rfl

def raw28837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw28837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28837 raw28837Labels = mixedMoment B node3214 node3214Labels := by
  calc
    mixedMoment B raw28837 raw28837Labels = mixedMoment B raw28837step0 raw28837step0Labels := by
      have hz : ∀ j, raw28837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28837step0 = (fun i j => raw28837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28837step0 raw28837; decide +kernel
      have hl : raw28837step0Labels = raw28837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28837 raw28837Labels permutation346 hz
    mixedMoment B raw28837step0 raw28837step0Labels = mixedMoment B raw28837step1 raw28837step1Labels := by
      have ha : raw28837step1 = (fun i j => raw28837step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28837step1 raw28837step0; decide +kernel
      have hl : raw28837step1Labels = raw28837step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28837step0 raw28837step0Labels permutation151 permutation3
    mixedMoment B raw28837step1 raw28837step1Labels = mixedMoment B raw28837step2 raw28837step2Labels := by
      have ha : raw28837step2 = -raw28837step1 := by apply Matrix.ext; change ∀ i j, raw28837step2 i j = -(raw28837step1 i j); unfold raw28837step2 raw28837step1; decide +kernel
      have hl : raw28837step2Labels = raw28837step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3214 node3214Labels := by rfl

def raw28838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28838step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28838step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw28838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28838 raw28838Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw28838 raw28838Labels = mixedMoment B raw28838step0 raw28838step0Labels := by
      have hz : ∀ j, raw28838 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28838step0 = (fun i j => raw28838 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28838step0 raw28838; decide +kernel
      have hl : raw28838step0Labels = raw28838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28838 raw28838Labels permutation520 hz
    mixedMoment B raw28838step0 raw28838step0Labels = mixedMoment B raw28838step1 raw28838step1Labels := by
      have hz : ∀ j, raw28838step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28838step1 = (fun i j => raw28838step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28838step1 raw28838step0; decide +kernel
      have hl : raw28838step1Labels = raw28838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28838step0 raw28838step0Labels permutation80 hz
    mixedMoment B raw28838step1 raw28838step1Labels = mixedMoment B raw28838step2 raw28838step2Labels := by
      have ha : raw28838step2 = (fun i j => raw28838step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28838step2 raw28838step1; decide +kernel
      have hl : raw28838step2Labels = raw28838step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28838step1 raw28838step1Labels permutation31 permutation3
    mixedMoment B raw28838step2 raw28838step2Labels = mixedMoment B raw28838step3 raw28838step3Labels := by
      have ha : raw28838step3 = -raw28838step2 := by apply Matrix.ext; change ∀ i j, raw28838step3 i j = -(raw28838step2 i j); unfold raw28838step3 raw28838step2; decide +kernel
      have hl : raw28838step3Labels = raw28838step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw28839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28839 raw28839Labels = mixedMoment B node2800 node2800Labels := by
  calc
    mixedMoment B raw28839 raw28839Labels = mixedMoment B raw28839step0 raw28839step0Labels := by
      have ha : raw28839step0 = (fun i j => raw28839 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28839step0 raw28839; decide +kernel
      have hl : raw28839step0Labels = raw28839Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28839 raw28839Labels permutation158 permutation3
    _ = mixedMoment B node2800 node2800Labels := by rfl

def raw28840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28840 raw28840Labels = mixedMoment B node2901 node2901Labels := by
  calc
    mixedMoment B raw28840 raw28840Labels = mixedMoment B raw28840step0 raw28840step0Labels := by
      have ha : raw28840step0 = (fun i j => raw28840 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28840step0 raw28840; decide +kernel
      have hl : raw28840step0Labels = raw28840Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28840 raw28840Labels permutation158 permutation3
    _ = mixedMoment B node2901 node2901Labels := by rfl

def raw28841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28841 raw28841Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw28841 raw28841Labels = mixedMoment B raw28841step0 raw28841step0Labels := by
      have hz : ∀ j, raw28841 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28841step0 = (fun i j => raw28841 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28841step0 raw28841; decide +kernel
      have hl : raw28841step0Labels = raw28841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28841 raw28841Labels permutation520 hz
    mixedMoment B raw28841step0 raw28841step0Labels = mixedMoment B raw28841step1 raw28841step1Labels := by
      have ha : raw28841step1 = (fun i j => raw28841step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28841step1 raw28841step0; decide +kernel
      have hl : raw28841step1Labels = raw28841step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28841step0 raw28841step0Labels permutation34 permutation3
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw28842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28842 raw28842Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw28842 raw28842Labels = mixedMoment B raw28842step0 raw28842step0Labels := by
      have hz : ∀ j, raw28842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28842step0 = (fun i j => raw28842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28842step0 raw28842; decide +kernel
      have hl : raw28842step0Labels = raw28842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28842 raw28842Labels permutation346 hz
    mixedMoment B raw28842step0 raw28842step0Labels = mixedMoment B raw28842step1 raw28842step1Labels := by
      have ha : raw28842step1 = (fun i j => raw28842step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28842step1 raw28842step0; decide +kernel
      have hl : raw28842step1Labels = raw28842step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28842step0 raw28842step0Labels permutation34 permutation3
    _ = mixedMoment B node2816 node2816Labels := by rfl

def raw28843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28843 raw28843Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw28843 raw28843Labels = mixedMoment B raw28843step0 raw28843step0Labels := by
      have ha : raw28843step0 = (fun i j => raw28843 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28843step0 raw28843; decide +kernel
      have hl : raw28843step0Labels = raw28843Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28843 raw28843Labels permutation154 permutation3
    _ = mixedMoment B node2895 node2895Labels := by rfl

def raw28844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28844step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28844 raw28844Labels = mixedMoment B node2966 node2966Labels := by
  calc
    mixedMoment B raw28844 raw28844Labels = mixedMoment B raw28844step0 raw28844step0Labels := by
      have hz : ∀ j, raw28844 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28844step0 = (fun i j => raw28844 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28844step0 raw28844; decide +kernel
      have hl : raw28844step0Labels = raw28844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28844 raw28844Labels permutation520 hz
    mixedMoment B raw28844step0 raw28844step0Labels = mixedMoment B raw28844step1 raw28844step1Labels := by
      have hz : ∀ j, raw28844step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28844step1 = (fun i j => raw28844step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28844step1 raw28844step0; decide +kernel
      have hl : raw28844step1Labels = raw28844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28844step0 raw28844step0Labels permutation80 hz
    mixedMoment B raw28844step1 raw28844step1Labels = mixedMoment B raw28844step2 raw28844step2Labels := by
      have ha : raw28844step2 = (fun i j => raw28844step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28844step2 raw28844step1; decide +kernel
      have hl : raw28844step2Labels = raw28844step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28844step1 raw28844step1Labels permutation8 permutation3
    _ = mixedMoment B node2966 node2966Labels := by rfl

def raw28845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28845 raw28845Labels = mixedMoment B node2803 node2803Labels := by
  calc
    mixedMoment B raw28845 raw28845Labels = mixedMoment B raw28845step0 raw28845step0Labels := by
      have hz : ∀ j, raw28845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28845step0 = (fun i j => raw28845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28845step0 raw28845; decide +kernel
      have hl : raw28845step0Labels = raw28845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28845 raw28845Labels permutation346 hz
    mixedMoment B raw28845step0 raw28845step0Labels = mixedMoment B raw28845step1 raw28845step1Labels := by
      have ha : raw28845step1 = (fun i j => raw28845step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28845step1 raw28845step0; decide +kernel
      have hl : raw28845step1Labels = raw28845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28845step0 raw28845step0Labels permutation32 permutation3
    _ = mixedMoment B node2803 node2803Labels := by rfl

def raw28846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28846 raw28846Labels = mixedMoment B node2890 node2890Labels := by
  calc
    mixedMoment B raw28846 raw28846Labels = mixedMoment B raw28846step0 raw28846step0Labels := by
      have ha : raw28846step0 = (fun i j => raw28846 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28846step0 raw28846; decide +kernel
      have hl : raw28846step0Labels = raw28846Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28846 raw28846Labels permutation152 permutation3
    _ = mixedMoment B node2890 node2890Labels := by rfl

def raw28847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28847 raw28847Labels = mixedMoment B node2904 node2904Labels := by
  calc
    mixedMoment B raw28847 raw28847Labels = mixedMoment B raw28847step0 raw28847step0Labels := by
      have hz : ∀ j, raw28847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28847step0 = (fun i j => raw28847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28847step0 raw28847; decide +kernel
      have hl : raw28847step0Labels = raw28847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28847 raw28847Labels permutation346 hz
    mixedMoment B raw28847step0 raw28847step0Labels = mixedMoment B raw28847step1 raw28847step1Labels := by
      have ha : raw28847step1 = (fun i j => raw28847step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28847step1 raw28847step0; decide +kernel
      have hl : raw28847step1Labels = raw28847step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28847step0 raw28847step0Labels permutation32 permutation3
    _ = mixedMoment B node2904 node2904Labels := by rfl

def raw28848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw28848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28848 raw28848Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw28848 raw28848Labels = mixedMoment B raw28848step0 raw28848step0Labels := by
      have hz : ∀ j, raw28848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28848step0 = (fun i j => raw28848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28848step0 raw28848; decide +kernel
      have hl : raw28848step0Labels = raw28848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28848 raw28848Labels permutation346 hz
    mixedMoment B raw28848step0 raw28848step0Labels = mixedMoment B raw28848step1 raw28848step1Labels := by
      have ha : raw28848step1 = (fun i j => raw28848step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28848step1 raw28848step0; decide +kernel
      have hl : raw28848step1Labels = raw28848step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28848step0 raw28848step0Labels permutation151 permutation3
    mixedMoment B raw28848step1 raw28848step1Labels = mixedMoment B raw28848step2 raw28848step2Labels := by
      have ha : raw28848step2 = -raw28848step1 := by apply Matrix.ext; change ∀ i j, raw28848step2 i j = -(raw28848step1 i j); unfold raw28848step2 raw28848step1; decide +kernel
      have hl : raw28848step2Labels = raw28848step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1334 node1334Labels := by rfl

def raw28849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28849 raw28849Labels = mixedMoment B node1329 node1329Labels := by
  calc
    mixedMoment B raw28849 raw28849Labels = mixedMoment B raw28849step0 raw28849step0Labels := by
      have ha : raw28849step0 = (fun i j => raw28849 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28849step0 raw28849; decide +kernel
      have hl : raw28849step0Labels = raw28849Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28849 raw28849Labels permutation686 permutation3
    mixedMoment B raw28849step0 raw28849step0Labels = mixedMoment B raw28849step1 raw28849step1Labels := by
      have ha : raw28849step1 = -raw28849step0 := by apply Matrix.ext; change ∀ i j, raw28849step1 i j = -(raw28849step0 i j); unfold raw28849step1 raw28849step0; decide +kernel
      have hl : raw28849step1Labels = raw28849step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1329 node1329Labels := by rfl

def raw28850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw28850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28850 raw28850Labels = mixedMoment B node1342 node1342Labels := by
  calc
    mixedMoment B raw28850 raw28850Labels = mixedMoment B raw28850step0 raw28850step0Labels := by
      have hz : ∀ j, raw28850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28850step0 = (fun i j => raw28850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28850step0 raw28850; decide +kernel
      have hl : raw28850step0Labels = raw28850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28850 raw28850Labels permutation346 hz
    mixedMoment B raw28850step0 raw28850step0Labels = mixedMoment B raw28850step1 raw28850step1Labels := by
      have ha : raw28850step1 = (fun i j => raw28850step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28850step1 raw28850step0; decide +kernel
      have hl : raw28850step1Labels = raw28850step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28850step0 raw28850step0Labels permutation151 permutation3
    mixedMoment B raw28850step1 raw28850step1Labels = mixedMoment B raw28850step2 raw28850step2Labels := by
      have ha : raw28850step2 = -raw28850step1 := by apply Matrix.ext; change ∀ i j, raw28850step2 i j = -(raw28850step1 i j); unfold raw28850step2 raw28850step1; decide +kernel
      have hl : raw28850step2Labels = raw28850step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1342 node1342Labels := by rfl

def raw28851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28851step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw28851step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28851 raw28851Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw28851 raw28851Labels = mixedMoment B raw28851step0 raw28851step0Labels := by
      have hz : ∀ j, raw28851 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28851step0 = (fun i j => raw28851 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28851step0 raw28851; decide +kernel
      have hl : raw28851step0Labels = raw28851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28851 raw28851Labels permutation520 hz
    mixedMoment B raw28851step0 raw28851step0Labels = mixedMoment B raw28851step1 raw28851step1Labels := by
      have hz : ∀ j, raw28851step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28851step1 = (fun i j => raw28851step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28851step1 raw28851step0; decide +kernel
      have hl : raw28851step1Labels = raw28851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28851step0 raw28851step0Labels permutation80 hz
    mixedMoment B raw28851step1 raw28851step1Labels = mixedMoment B raw28851step2 raw28851step2Labels := by
      have ha : raw28851step2 = (fun i j => raw28851step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28851step2 raw28851step1; decide +kernel
      have hl : raw28851step2Labels = raw28851step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28851step1 raw28851step1Labels permutation31 permutation3
    mixedMoment B raw28851step2 raw28851step2Labels = mixedMoment B raw28851step3 raw28851step3Labels := by
      have ha : raw28851step3 = -raw28851step2 := by apply Matrix.ext; change ∀ i j, raw28851step3 i j = -(raw28851step2 i j); unfold raw28851step3 raw28851step2; decide +kernel
      have hl : raw28851step3Labels = raw28851step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw28852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28852step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28852step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28852 raw28852Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw28852 raw28852Labels = mixedMoment B raw28852step0 raw28852step0Labels := by
      have hz : ∀ j, raw28852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28852step0 = (fun i j => raw28852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28852step0 raw28852; decide +kernel
      have hl : raw28852step0Labels = raw28852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28852 raw28852Labels permutation346 hz
    mixedMoment B raw28852step0 raw28852step0Labels = mixedMoment B raw28852step1 raw28852step1Labels := by
      have ha : raw28852step1 = (fun i j => raw28852step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28852step1 raw28852step0; decide +kernel
      have hl : raw28852step1Labels = raw28852step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28852step0 raw28852step0Labels permutation149 permutation7
    mixedMoment B raw28852step1 raw28852step1Labels = mixedMoment B raw28852step2 raw28852step2Labels := by
      have ha : raw28852step2 = raw28852step1 := by apply Matrix.ext; unfold raw28852step2 raw28852step1; decide +kernel
      have hl : raw28852step1Labels = labelEmbedding1 ∘ raw28852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28852step1 raw28852step1Labels raw28852step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw28853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28853step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28853 raw28853Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw28853 raw28853Labels = mixedMoment B raw28853step0 raw28853step0Labels := by
      have ha : raw28853step0 = (fun i j => raw28853 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28853step0 raw28853; decide +kernel
      have hl : raw28853step0Labels = raw28853Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28853 raw28853Labels permutation674 permutation7
    mixedMoment B raw28853step0 raw28853step0Labels = mixedMoment B raw28853step1 raw28853step1Labels := by
      have ha : raw28853step1 = raw28853step0 := by apply Matrix.ext; unfold raw28853step1 raw28853step0; decide +kernel
      have hl : raw28853step0Labels = labelEmbedding1 ∘ raw28853step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28853step0 raw28853step0Labels raw28853step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw28854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28854 raw28854Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw28854 raw28854Labels = mixedMoment B raw28854step0 raw28854step0Labels := by
      have hz : ∀ j, raw28854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28854step0 = (fun i j => raw28854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28854step0 raw28854; decide +kernel
      have hl : raw28854step0Labels = raw28854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28854 raw28854Labels permutation346 hz
    mixedMoment B raw28854step0 raw28854step0Labels = mixedMoment B raw28854step1 raw28854step1Labels := by
      have ha : raw28854step1 = (fun i j => raw28854step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28854step1 raw28854step0; decide +kernel
      have hl : raw28854step1Labels = raw28854step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28854step0 raw28854step0Labels permutation149 permutation7
    mixedMoment B raw28854step1 raw28854step1Labels = mixedMoment B raw28854step2 raw28854step2Labels := by
      have ha : raw28854step2 = raw28854step1 := by apply Matrix.ext; unfold raw28854step2 raw28854step1; decide +kernel
      have hl : raw28854step1Labels = labelEmbedding1 ∘ raw28854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28854step1 raw28854step1Labels raw28854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw28855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28855step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28855step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28855 raw28855Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw28855 raw28855Labels = mixedMoment B raw28855step0 raw28855step0Labels := by
      have hz : ∀ j, raw28855 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28855step0 = (fun i j => raw28855 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28855step0 raw28855; decide +kernel
      have hl : raw28855step0Labels = raw28855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28855 raw28855Labels permutation520 hz
    mixedMoment B raw28855step0 raw28855step0Labels = mixedMoment B raw28855step1 raw28855step1Labels := by
      have hz : ∀ j, raw28855step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28855step1 = (fun i j => raw28855step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28855step1 raw28855step0; decide +kernel
      have hl : raw28855step1Labels = raw28855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28855step0 raw28855step0Labels permutation80 hz
    mixedMoment B raw28855step1 raw28855step1Labels = mixedMoment B raw28855step2 raw28855step2Labels := by
      have ha : raw28855step2 = (fun i j => raw28855step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28855step2 raw28855step1; decide +kernel
      have hl : raw28855step2Labels = raw28855step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28855step1 raw28855step1Labels permutation29 permutation7
    mixedMoment B raw28855step2 raw28855step2Labels = mixedMoment B raw28855step3 raw28855step3Labels := by
      have ha : raw28855step3 = raw28855step2 := by apply Matrix.ext; unfold raw28855step3 raw28855step2; decide +kernel
      have hl : raw28855step2Labels = labelEmbedding1 ∘ raw28855step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28855step2 raw28855step2Labels raw28855step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw28856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28856 raw28856Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw28856 raw28856Labels = mixedMoment B raw28856step0 raw28856step0Labels := by
      have ha : raw28856step0 = (fun i j => raw28856 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28856step0 raw28856; decide +kernel
      have hl : raw28856step0Labels = raw28856Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28856 raw28856Labels permutation644 permutation7
    mixedMoment B raw28856step0 raw28856step0Labels = mixedMoment B raw28856step1 raw28856step1Labels := by
      have ha : raw28856step1 = raw28856step0 := by apply Matrix.ext; unfold raw28856step1 raw28856step0; decide +kernel
      have hl : raw28856step0Labels = labelEmbedding1 ∘ raw28856step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28856step0 raw28856step0Labels raw28856step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2176 node2176Labels := by rfl

def raw28857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28857 raw28857Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw28857 raw28857Labels = mixedMoment B raw28857step0 raw28857step0Labels := by
      have ha : raw28857step0 = (fun i j => raw28857 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28857step0 raw28857; decide +kernel
      have hl : raw28857step0Labels = raw28857Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28857 raw28857Labels permutation644 permutation7
    mixedMoment B raw28857step0 raw28857step0Labels = mixedMoment B raw28857step1 raw28857step1Labels := by
      have ha : raw28857step1 = raw28857step0 := by apply Matrix.ext; unfold raw28857step1 raw28857step0; decide +kernel
      have hl : raw28857step0Labels = labelEmbedding1 ∘ raw28857step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28857step0 raw28857step0Labels raw28857step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

def raw28858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28858step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28858 raw28858Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw28858 raw28858Labels = mixedMoment B raw28858step0 raw28858step0Labels := by
      have hz : ∀ j, raw28858 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28858step0 = (fun i j => raw28858 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28858step0 raw28858; decide +kernel
      have hl : raw28858step0Labels = raw28858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28858 raw28858Labels permutation520 hz
    mixedMoment B raw28858step0 raw28858step0Labels = mixedMoment B raw28858step1 raw28858step1Labels := by
      have ha : raw28858step1 = (fun i j => raw28858step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28858step1 raw28858step0; decide +kernel
      have hl : raw28858step1Labels = raw28858step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28858step0 raw28858step0Labels permutation143 permutation7
    mixedMoment B raw28858step1 raw28858step1Labels = mixedMoment B raw28858step2 raw28858step2Labels := by
      have ha : raw28858step2 = raw28858step1 := by apply Matrix.ext; unfold raw28858step2 raw28858step1; decide +kernel
      have hl : raw28858step1Labels = labelEmbedding1 ∘ raw28858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28858step1 raw28858step1Labels raw28858step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw28859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28859 raw28859Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw28859 raw28859Labels = mixedMoment B raw28859step0 raw28859step0Labels := by
      have hz : ∀ j, raw28859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28859step0 = (fun i j => raw28859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28859step0 raw28859; decide +kernel
      have hl : raw28859step0Labels = raw28859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28859 raw28859Labels permutation346 hz
    mixedMoment B raw28859step0 raw28859step0Labels = mixedMoment B raw28859step1 raw28859step1Labels := by
      have ha : raw28859step1 = (fun i j => raw28859step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28859step1 raw28859step0; decide +kernel
      have hl : raw28859step1Labels = raw28859step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28859step0 raw28859step0Labels permutation149 permutation7
    mixedMoment B raw28859step1 raw28859step1Labels = mixedMoment B raw28859step2 raw28859step2Labels := by
      have ha : raw28859step2 = raw28859step1 := by apply Matrix.ext; unfold raw28859step2 raw28859step1; decide +kernel
      have hl : raw28859step1Labels = labelEmbedding1 ∘ raw28859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28859step1 raw28859step1Labels raw28859step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

def raw28860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28860 raw28860Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw28860 raw28860Labels = mixedMoment B raw28860step0 raw28860step0Labels := by
      have ha : raw28860step0 = (fun i j => raw28860 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28860step0 raw28860; decide +kernel
      have hl : raw28860step0Labels = raw28860Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28860 raw28860Labels permutation674 permutation7
    mixedMoment B raw28860step0 raw28860step0Labels = mixedMoment B raw28860step1 raw28860step1Labels := by
      have ha : raw28860step1 = raw28860step0 := by apply Matrix.ext; unfold raw28860step1 raw28860step0; decide +kernel
      have hl : raw28860step0Labels = labelEmbedding1 ∘ raw28860step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28860step0 raw28860step0Labels raw28860step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

def raw28861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28861step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28861 raw28861Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw28861 raw28861Labels = mixedMoment B raw28861step0 raw28861step0Labels := by
      have hz : ∀ j, raw28861 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28861step0 = (fun i j => raw28861 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28861step0 raw28861; decide +kernel
      have hl : raw28861step0Labels = raw28861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28861 raw28861Labels permutation520 hz
    mixedMoment B raw28861step0 raw28861step0Labels = mixedMoment B raw28861step1 raw28861step1Labels := by
      have hz : ∀ j, raw28861step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28861step1 = (fun i j => raw28861step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28861step1 raw28861step0; decide +kernel
      have hl : raw28861step1Labels = raw28861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28861step0 raw28861step0Labels permutation80 hz
    mixedMoment B raw28861step1 raw28861step1Labels = mixedMoment B raw28861step2 raw28861step2Labels := by
      have ha : raw28861step2 = (fun i j => raw28861step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28861step2 raw28861step1; decide +kernel
      have hl : raw28861step2Labels = raw28861step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28861step1 raw28861step1Labels permutation29 permutation7
    mixedMoment B raw28861step2 raw28861step2Labels = mixedMoment B raw28861step3 raw28861step3Labels := by
      have ha : raw28861step3 = raw28861step2 := by apply Matrix.ext; unfold raw28861step3 raw28861step2; decide +kernel
      have hl : raw28861step2Labels = labelEmbedding1 ∘ raw28861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28861step2 raw28861step2Labels raw28861step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw28862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28862step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28862 raw28862Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw28862 raw28862Labels = mixedMoment B raw28862step0 raw28862step0Labels := by
      have hz : ∀ j, raw28862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28862step0 = (fun i j => raw28862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28862step0 raw28862; decide +kernel
      have hl : raw28862step0Labels = raw28862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28862 raw28862Labels permutation346 hz
    mixedMoment B raw28862step0 raw28862step0Labels = mixedMoment B raw28862step1 raw28862step1Labels := by
      have ha : raw28862step1 = (fun i j => raw28862step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28862step1 raw28862step0; decide +kernel
      have hl : raw28862step1Labels = raw28862step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28862step0 raw28862step0Labels permutation149 permutation7
    mixedMoment B raw28862step1 raw28862step1Labels = mixedMoment B raw28862step2 raw28862step2Labels := by
      have ha : raw28862step2 = raw28862step1 := by apply Matrix.ext; unfold raw28862step2 raw28862step1; decide +kernel
      have hl : raw28862step1Labels = labelEmbedding1 ∘ raw28862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28862step1 raw28862step1Labels raw28862step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2155 node2155Labels := by rfl

def raw28863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28863step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28863 raw28863Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw28863 raw28863Labels = mixedMoment B raw28863step0 raw28863step0Labels := by
      have ha : raw28863step0 = (fun i j => raw28863 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28863step0 raw28863; decide +kernel
      have hl : raw28863step0Labels = raw28863Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28863 raw28863Labels permutation674 permutation7
    mixedMoment B raw28863step0 raw28863step0Labels = mixedMoment B raw28863step1 raw28863step1Labels := by
      have ha : raw28863step1 = raw28863step0 := by apply Matrix.ext; unfold raw28863step1 raw28863step0; decide +kernel
      have hl : raw28863step0Labels = labelEmbedding1 ∘ raw28863step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28863step0 raw28863step0Labels raw28863step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2140 node2140Labels := by rfl

def raw28864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28864step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28864 raw28864Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw28864 raw28864Labels = mixedMoment B raw28864step0 raw28864step0Labels := by
      have hz : ∀ j, raw28864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28864step0 = (fun i j => raw28864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28864step0 raw28864; decide +kernel
      have hl : raw28864step0Labels = raw28864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28864 raw28864Labels permutation346 hz
    mixedMoment B raw28864step0 raw28864step0Labels = mixedMoment B raw28864step1 raw28864step1Labels := by
      have ha : raw28864step1 = (fun i j => raw28864step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28864step1 raw28864step0; decide +kernel
      have hl : raw28864step1Labels = raw28864step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28864step0 raw28864step0Labels permutation149 permutation7
    mixedMoment B raw28864step1 raw28864step1Labels = mixedMoment B raw28864step2 raw28864step2Labels := by
      have ha : raw28864step2 = raw28864step1 := by apply Matrix.ext; unfold raw28864step2 raw28864step1; decide +kernel
      have hl : raw28864step1Labels = labelEmbedding1 ∘ raw28864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28864step1 raw28864step1Labels raw28864step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

def raw28865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28865step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28865 raw28865Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw28865 raw28865Labels = mixedMoment B raw28865step0 raw28865step0Labels := by
      have hz : ∀ j, raw28865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28865step0 = (fun i j => raw28865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28865step0 raw28865; decide +kernel
      have hl : raw28865step0Labels = raw28865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28865 raw28865Labels permutation346 hz
    mixedMoment B raw28865step0 raw28865step0Labels = mixedMoment B raw28865step1 raw28865step1Labels := by
      have ha : raw28865step1 = (fun i j => raw28865step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28865step1 raw28865step0; decide +kernel
      have hl : raw28865step1Labels = raw28865step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28865step0 raw28865step0Labels permutation149 permutation7
    mixedMoment B raw28865step1 raw28865step1Labels = mixedMoment B raw28865step2 raw28865step2Labels := by
      have ha : raw28865step2 = raw28865step1 := by apply Matrix.ext; unfold raw28865step2 raw28865step1; decide +kernel
      have hl : raw28865step1Labels = labelEmbedding1 ∘ raw28865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28865step1 raw28865step1Labels raw28865step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw28866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28866 raw28866Labels = mixedMoment B node1663 node1663Labels := by
  calc
    mixedMoment B raw28866 raw28866Labels = mixedMoment B raw28866step0 raw28866step0Labels := by
      have ha : raw28866step0 = (fun i j => raw28866 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28866step0 raw28866; decide +kernel
      have hl : raw28866step0Labels = raw28866Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28866 raw28866Labels permutation674 permutation7
    mixedMoment B raw28866step0 raw28866step0Labels = mixedMoment B raw28866step1 raw28866step1Labels := by
      have ha : raw28866step1 = raw28866step0 := by apply Matrix.ext; unfold raw28866step1 raw28866step0; decide +kernel
      have hl : raw28866step0Labels = labelEmbedding1 ∘ raw28866step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28866step0 raw28866step0Labels raw28866step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1663 node1663Labels := by rfl

def raw28867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28867step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28867step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28867step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28867 raw28867Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw28867 raw28867Labels = mixedMoment B raw28867step0 raw28867step0Labels := by
      have hz : ∀ j, raw28867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28867step0 = (fun i j => raw28867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28867step0 raw28867; decide +kernel
      have hl : raw28867step0Labels = raw28867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28867 raw28867Labels permutation346 hz
    mixedMoment B raw28867step0 raw28867step0Labels = mixedMoment B raw28867step1 raw28867step1Labels := by
      have ha : raw28867step1 = (fun i j => raw28867step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28867step1 raw28867step0; decide +kernel
      have hl : raw28867step1Labels = raw28867step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28867step0 raw28867step0Labels permutation149 permutation7
    mixedMoment B raw28867step1 raw28867step1Labels = mixedMoment B raw28867step2 raw28867step2Labels := by
      have ha : raw28867step2 = raw28867step1 := by apply Matrix.ext; unfold raw28867step2 raw28867step1; decide +kernel
      have hl : raw28867step1Labels = labelEmbedding1 ∘ raw28867step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28867step1 raw28867step1Labels raw28867step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw28868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28868step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28868step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28868step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28868step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28868 raw28868Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw28868 raw28868Labels = mixedMoment B raw28868step0 raw28868step0Labels := by
      have hz : ∀ j, raw28868 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28868step0 = (fun i j => raw28868 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28868step0 raw28868; decide +kernel
      have hl : raw28868step0Labels = raw28868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28868 raw28868Labels permutation520 hz
    mixedMoment B raw28868step0 raw28868step0Labels = mixedMoment B raw28868step1 raw28868step1Labels := by
      have hz : ∀ j, raw28868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28868step1 = (fun i j => raw28868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28868step1 raw28868step0; decide +kernel
      have hl : raw28868step1Labels = raw28868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28868step0 raw28868step0Labels permutation80 hz
    mixedMoment B raw28868step1 raw28868step1Labels = mixedMoment B raw28868step2 raw28868step2Labels := by
      have ha : raw28868step2 = (fun i j => raw28868step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28868step2 raw28868step1; decide +kernel
      have hl : raw28868step2Labels = raw28868step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28868step1 raw28868step1Labels permutation29 permutation7
    mixedMoment B raw28868step2 raw28868step2Labels = mixedMoment B raw28868step3 raw28868step3Labels := by
      have ha : raw28868step3 = raw28868step2 := by apply Matrix.ext; unfold raw28868step3 raw28868step2; decide +kernel
      have hl : raw28868step2Labels = labelEmbedding1 ∘ raw28868step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28868step2 raw28868step2Labels raw28868step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw28869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28869 raw28869Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw28869 raw28869Labels = mixedMoment B raw28869step0 raw28869step0Labels := by
      have hz : ∀ j, raw28869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28869step0 = (fun i j => raw28869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28869step0 raw28869; decide +kernel
      have hl : raw28869step0Labels = raw28869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28869 raw28869Labels permutation346 hz
    mixedMoment B raw28869step0 raw28869step0Labels = mixedMoment B raw28869step1 raw28869step1Labels := by
      have ha : raw28869step1 = (fun i j => raw28869step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28869step1 raw28869step0; decide +kernel
      have hl : raw28869step1Labels = raw28869step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28869step0 raw28869step0Labels permutation151 permutation2
    mixedMoment B raw28869step1 raw28869step1Labels = mixedMoment B raw28869step2 raw28869step2Labels := by
      have ha : raw28869step2 = -raw28869step1 := by apply Matrix.ext; change ∀ i j, raw28869step2 i j = -(raw28869step1 i j); unfold raw28869step2 raw28869step1; decide +kernel
      have hl : raw28869step2Labels = raw28869step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw28870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28870 raw28870Labels = mixedMoment B node1955 node1955Labels := by
  calc
    mixedMoment B raw28870 raw28870Labels = mixedMoment B raw28870step0 raw28870step0Labels := by
      have ha : raw28870step0 = (fun i j => raw28870 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28870step0 raw28870; decide +kernel
      have hl : raw28870step0Labels = raw28870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28870 raw28870Labels permutation646 permutation2
    mixedMoment B raw28870step0 raw28870step0Labels = mixedMoment B raw28870step1 raw28870step1Labels := by
      have ha : raw28870step1 = -raw28870step0 := by apply Matrix.ext; change ∀ i j, raw28870step1 i j = -(raw28870step0 i j); unfold raw28870step1 raw28870step0; decide +kernel
      have hl : raw28870step1Labels = raw28870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1955 node1955Labels := by rfl

def raw28871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28871 raw28871Labels = mixedMoment B node1978 node1978Labels := by
  calc
    mixedMoment B raw28871 raw28871Labels = mixedMoment B raw28871step0 raw28871step0Labels := by
      have hz : ∀ j, raw28871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28871step0 = (fun i j => raw28871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28871step0 raw28871; decide +kernel
      have hl : raw28871step0Labels = raw28871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28871 raw28871Labels permutation346 hz
    mixedMoment B raw28871step0 raw28871step0Labels = mixedMoment B raw28871step1 raw28871step1Labels := by
      have ha : raw28871step1 = (fun i j => raw28871step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28871step1 raw28871step0; decide +kernel
      have hl : raw28871step1Labels = raw28871step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28871step0 raw28871step0Labels permutation151 permutation2
    mixedMoment B raw28871step1 raw28871step1Labels = mixedMoment B raw28871step2 raw28871step2Labels := by
      have ha : raw28871step2 = -raw28871step1 := by apply Matrix.ext; change ∀ i j, raw28871step2 i j = -(raw28871step1 i j); unfold raw28871step2 raw28871step1; decide +kernel
      have hl : raw28871step2Labels = raw28871step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1978 node1978Labels := by rfl

def raw28872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28872 raw28872Labels = mixedMoment B node1795 node1795Labels := by
  calc
    mixedMoment B raw28872 raw28872Labels = mixedMoment B raw28872step0 raw28872step0Labels := by
      have hz : ∀ j, raw28872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28872step0 = (fun i j => raw28872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28872step0 raw28872; decide +kernel
      have hl : raw28872step0Labels = raw28872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28872 raw28872Labels permutation346 hz
    mixedMoment B raw28872step0 raw28872step0Labels = mixedMoment B raw28872step1 raw28872step1Labels := by
      have ha : raw28872step1 = (fun i j => raw28872step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28872step1 raw28872step0; decide +kernel
      have hl : raw28872step1Labels = raw28872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28872step0 raw28872step0Labels permutation151 permutation2
    mixedMoment B raw28872step1 raw28872step1Labels = mixedMoment B raw28872step2 raw28872step2Labels := by
      have ha : raw28872step2 = -raw28872step1 := by apply Matrix.ext; change ∀ i j, raw28872step2 i j = -(raw28872step1 i j); unfold raw28872step2 raw28872step1; decide +kernel
      have hl : raw28872step2Labels = raw28872step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1795 node1795Labels := by rfl

def raw28873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28873 raw28873Labels = mixedMoment B node912 node912Labels := by
  calc
    mixedMoment B raw28873 raw28873Labels = mixedMoment B raw28873step0 raw28873step0Labels := by
      have hz : ∀ j, raw28873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28873step0 = (fun i j => raw28873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28873step0 raw28873; decide +kernel
      have hl : raw28873step0Labels = raw28873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28873 raw28873Labels permutation346 hz
    mixedMoment B raw28873step0 raw28873step0Labels = mixedMoment B raw28873step1 raw28873step1Labels := by
      have ha : raw28873step1 = (fun i j => raw28873step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28873step1 raw28873step0; decide +kernel
      have hl : raw28873step1Labels = raw28873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28873step0 raw28873step0Labels permutation151 permutation2
    mixedMoment B raw28873step1 raw28873step1Labels = mixedMoment B raw28873step2 raw28873step2Labels := by
      have ha : raw28873step2 = -raw28873step1 := by apply Matrix.ext; change ∀ i j, raw28873step2 i j = -(raw28873step1 i j); unfold raw28873step2 raw28873step1; decide +kernel
      have hl : raw28873step2Labels = raw28873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node912 node912Labels := by rfl

def raw28874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28874 raw28874Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw28874 raw28874Labels = mixedMoment B raw28874step0 raw28874step0Labels := by
      have ha : raw28874step0 = (fun i j => raw28874 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28874step0 raw28874; decide +kernel
      have hl : raw28874step0Labels = raw28874Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28874 raw28874Labels permutation644 permutation2
    mixedMoment B raw28874step0 raw28874step0Labels = mixedMoment B raw28874step1 raw28874step1Labels := by
      have ha : raw28874step1 = -raw28874step0 := by apply Matrix.ext; change ∀ i j, raw28874step1 i j = -(raw28874step0 i j); unfold raw28874step1 raw28874step0; decide +kernel
      have hl : raw28874step1Labels = raw28874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1960 node1960Labels := by rfl

def raw28875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28875 raw28875Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw28875 raw28875Labels = mixedMoment B raw28875step0 raw28875step0Labels := by
      have hz : ∀ j, raw28875 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28875step0 = (fun i j => raw28875 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28875step0 raw28875; decide +kernel
      have hl : raw28875step0Labels = raw28875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28875 raw28875Labels permutation520 hz
    mixedMoment B raw28875step0 raw28875step0Labels = mixedMoment B raw28875step1 raw28875step1Labels := by
      have ha : raw28875step1 = (fun i j => raw28875step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28875step1 raw28875step0; decide +kernel
      have hl : raw28875step1Labels = raw28875step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28875step0 raw28875step0Labels permutation145 permutation2
    mixedMoment B raw28875step1 raw28875step1Labels = mixedMoment B raw28875step2 raw28875step2Labels := by
      have ha : raw28875step2 = -raw28875step1 := by apply Matrix.ext; change ∀ i j, raw28875step2 i j = -(raw28875step1 i j); unfold raw28875step2 raw28875step1; decide +kernel
      have hl : raw28875step2Labels = raw28875step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw28876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28876 raw28876Labels = mixedMoment B node2552 node2552Labels := by
  calc
    mixedMoment B raw28876 raw28876Labels = mixedMoment B raw28876step0 raw28876step0Labels := by
      have ha : raw28876step0 = (fun i j => raw28876 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28876step0 raw28876; decide +kernel
      have hl : raw28876step0Labels = raw28876Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28876 raw28876Labels permutation158 permutation2
    _ = mixedMoment B node2552 node2552Labels := by rfl

def raw28877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28877 raw28877Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw28877 raw28877Labels = mixedMoment B raw28877step0 raw28877step0Labels := by
      have ha : raw28877step0 = (fun i j => raw28877 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28877step0 raw28877; decide +kernel
      have hl : raw28877step0Labels = raw28877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28877 raw28877Labels permutation686 permutation2
    mixedMoment B raw28877step0 raw28877step0Labels = mixedMoment B raw28877step1 raw28877step1Labels := by
      have ha : raw28877step1 = -raw28877step0 := by apply Matrix.ext; change ∀ i j, raw28877step1 i j = -(raw28877step0 i j); unfold raw28877step1 raw28877step0; decide +kernel
      have hl : raw28877step1Labels = raw28877step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2019 node2019Labels := by rfl

def raw28878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28878 raw28878Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw28878 raw28878Labels = mixedMoment B raw28878step0 raw28878step0Labels := by
      have hz : ∀ j, raw28878 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw28878step0 = (fun i j => raw28878 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw28878step0 raw28878; decide +kernel
      have hl : raw28878step0Labels = raw28878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28878 raw28878Labels permutation265 hz
    mixedMoment B raw28878step0 raw28878step0Labels = mixedMoment B raw28878step1 raw28878step1Labels := by
      have ha : raw28878step1 = (fun i j => raw28878step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28878step1 raw28878step0; decide +kernel
      have hl : raw28878step1Labels = raw28878step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28878step0 raw28878step0Labels permutation151 permutation2
    mixedMoment B raw28878step1 raw28878step1Labels = mixedMoment B raw28878step2 raw28878step2Labels := by
      have ha : raw28878step2 = -raw28878step1 := by apply Matrix.ext; change ∀ i j, raw28878step2 i j = -(raw28878step1 i j); unfold raw28878step2 raw28878step1; decide +kernel
      have hl : raw28878step2Labels = raw28878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw28879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28879 raw28879Labels = mixedMoment B node1972 node1972Labels := by
  calc
    mixedMoment B raw28879 raw28879Labels = mixedMoment B raw28879step0 raw28879step0Labels := by
      have ha : raw28879step0 = (fun i j => raw28879 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28879step0 raw28879; decide +kernel
      have hl : raw28879step0Labels = raw28879Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28879 raw28879Labels permutation686 permutation2
    mixedMoment B raw28879step0 raw28879step0Labels = mixedMoment B raw28879step1 raw28879step1Labels := by
      have ha : raw28879step1 = -raw28879step0 := by apply Matrix.ext; change ∀ i j, raw28879step1 i j = -(raw28879step0 i j); unfold raw28879step1 raw28879step0; decide +kernel
      have hl : raw28879step1Labels = raw28879step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1972 node1972Labels := by rfl

def raw28880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28880 raw28880Labels = mixedMoment B node1789 node1789Labels := by
  calc
    mixedMoment B raw28880 raw28880Labels = mixedMoment B raw28880step0 raw28880step0Labels := by
      have ha : raw28880step0 = (fun i j => raw28880 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28880step0 raw28880; decide +kernel
      have hl : raw28880step0Labels = raw28880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28880 raw28880Labels permutation686 permutation2
    mixedMoment B raw28880step0 raw28880step0Labels = mixedMoment B raw28880step1 raw28880step1Labels := by
      have ha : raw28880step1 = -raw28880step0 := by apply Matrix.ext; change ∀ i j, raw28880step1 i j = -(raw28880step0 i j); unfold raw28880step1 raw28880step0; decide +kernel
      have hl : raw28880step1Labels = raw28880step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1789 node1789Labels := by rfl

def raw28881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28881 raw28881Labels = mixedMoment B node904 node904Labels := by
  calc
    mixedMoment B raw28881 raw28881Labels = mixedMoment B raw28881step0 raw28881step0Labels := by
      have ha : raw28881step0 = (fun i j => raw28881 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28881step0 raw28881; decide +kernel
      have hl : raw28881step0Labels = raw28881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28881 raw28881Labels permutation686 permutation2
    mixedMoment B raw28881step0 raw28881step0Labels = mixedMoment B raw28881step1 raw28881step1Labels := by
      have ha : raw28881step1 = -raw28881step0 := by apply Matrix.ext; change ∀ i j, raw28881step1 i j = -(raw28881step0 i j); unfold raw28881step1 raw28881step0; decide +kernel
      have hl : raw28881step1Labels = raw28881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node904 node904Labels := by rfl

def raw28882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28882 raw28882Labels = mixedMoment B node2053 node2053Labels := by
  calc
    mixedMoment B raw28882 raw28882Labels = mixedMoment B raw28882step0 raw28882step0Labels := by
      have hz : ∀ j, raw28882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28882step0 = (fun i j => raw28882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28882step0 raw28882; decide +kernel
      have hl : raw28882step0Labels = raw28882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28882 raw28882Labels permutation346 hz
    mixedMoment B raw28882step0 raw28882step0Labels = mixedMoment B raw28882step1 raw28882step1Labels := by
      have ha : raw28882step1 = (fun i j => raw28882step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28882step1 raw28882step0; decide +kernel
      have hl : raw28882step1Labels = raw28882step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28882step0 raw28882step0Labels permutation149 permutation2
    mixedMoment B raw28882step1 raw28882step1Labels = mixedMoment B raw28882step2 raw28882step2Labels := by
      have ha : raw28882step2 = -raw28882step1 := by apply Matrix.ext; change ∀ i j, raw28882step2 i j = -(raw28882step1 i j); unfold raw28882step2 raw28882step1; decide +kernel
      have hl : raw28882step2Labels = raw28882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2053 node2053Labels := by rfl

def raw28883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28883 raw28883Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw28883 raw28883Labels = mixedMoment B raw28883step0 raw28883step0Labels := by
      have hz : ∀ j, raw28883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28883step0 = (fun i j => raw28883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28883step0 raw28883; decide +kernel
      have hl : raw28883step0Labels = raw28883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28883 raw28883Labels permutation346 hz
    mixedMoment B raw28883step0 raw28883step0Labels = mixedMoment B raw28883step1 raw28883step1Labels := by
      have ha : raw28883step1 = (fun i j => raw28883step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28883step1 raw28883step0; decide +kernel
      have hl : raw28883step1Labels = raw28883step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28883step0 raw28883step0Labels permutation149 permutation2
    mixedMoment B raw28883step1 raw28883step1Labels = mixedMoment B raw28883step2 raw28883step2Labels := by
      have ha : raw28883step2 = -raw28883step1 := by apply Matrix.ext; change ∀ i j, raw28883step2 i j = -(raw28883step1 i j); unfold raw28883step2 raw28883step1; decide +kernel
      have hl : raw28883step2Labels = raw28883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1807 node1807Labels := by rfl

def raw28884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28884 raw28884Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw28884 raw28884Labels = mixedMoment B raw28884step0 raw28884step0Labels := by
      have hz : ∀ j, raw28884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28884step0 = (fun i j => raw28884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28884step0 raw28884; decide +kernel
      have hl : raw28884step0Labels = raw28884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28884 raw28884Labels permutation346 hz
    mixedMoment B raw28884step0 raw28884step0Labels = mixedMoment B raw28884step1 raw28884step1Labels := by
      have ha : raw28884step1 = (fun i j => raw28884step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28884step1 raw28884step0; decide +kernel
      have hl : raw28884step1Labels = raw28884step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28884step0 raw28884step0Labels permutation149 permutation2
    mixedMoment B raw28884step1 raw28884step1Labels = mixedMoment B raw28884step2 raw28884step2Labels := by
      have ha : raw28884step2 = -raw28884step1 := by apply Matrix.ext; change ∀ i j, raw28884step2 i j = -(raw28884step1 i j); unfold raw28884step2 raw28884step1; decide +kernel
      have hl : raw28884step2Labels = raw28884step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node924 node924Labels := by rfl

def raw28885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28885step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28885step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28885step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28885step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28885 raw28885Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw28885 raw28885Labels = mixedMoment B raw28885step0 raw28885step0Labels := by
      have hz : ∀ j, raw28885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28885step0 = (fun i j => raw28885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28885step0 raw28885; decide +kernel
      have hl : raw28885step0Labels = raw28885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28885 raw28885Labels permutation346 hz
    mixedMoment B raw28885step0 raw28885step0Labels = mixedMoment B raw28885step1 raw28885step1Labels := by
      have ha : raw28885step1 = (fun i j => raw28885step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28885step1 raw28885step0; decide +kernel
      have hl : raw28885step1Labels = raw28885step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28885step0 raw28885step0Labels permutation150 permutation3
    mixedMoment B raw28885step1 raw28885step1Labels = mixedMoment B raw28885step2 raw28885step2Labels := by
      have ha : raw28885step2 = -raw28885step1 := by apply Matrix.ext; change ∀ i j, raw28885step2 i j = -(raw28885step1 i j); unfold raw28885step2 raw28885step1; decide +kernel
      have hl : raw28885step2Labels = raw28885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28885step2 raw28885step2Labels = mixedMoment B raw28885step3 raw28885step3Labels := by
      have ha : raw28885step3 = raw28885step2 := by apply Matrix.ext; unfold raw28885step3 raw28885step2; decide +kernel
      have hl : raw28885step2Labels = labelEmbedding6 ∘ raw28885step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28885step2 raw28885step2Labels raw28885step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw28886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28886step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28886step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28886step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28886step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28886 raw28886Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw28886 raw28886Labels = mixedMoment B raw28886step0 raw28886step0Labels := by
      have ha : raw28886step0 = (fun i j => raw28886 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28886step0 raw28886; decide +kernel
      have hl : raw28886step0Labels = raw28886Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28886 raw28886Labels permutation686 permutation3
    mixedMoment B raw28886step0 raw28886step0Labels = mixedMoment B raw28886step1 raw28886step1Labels := by
      have ha : raw28886step1 = -raw28886step0 := by apply Matrix.ext; change ∀ i j, raw28886step1 i j = -(raw28886step0 i j); unfold raw28886step1 raw28886step0; decide +kernel
      have hl : raw28886step1Labels = raw28886step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28886step1 raw28886step1Labels = mixedMoment B raw28886step2 raw28886step2Labels := by
      have ha : raw28886step2 = raw28886step1 := by apply Matrix.ext; unfold raw28886step2 raw28886step1; decide +kernel
      have hl : raw28886step1Labels = labelEmbedding6 ∘ raw28886step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28886step1 raw28886step1Labels raw28886step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw28887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28887step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28887step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28887step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28887step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28887 raw28887Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw28887 raw28887Labels = mixedMoment B raw28887step0 raw28887step0Labels := by
      have hz : ∀ j, raw28887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28887step0 = (fun i j => raw28887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28887step0 raw28887; decide +kernel
      have hl : raw28887step0Labels = raw28887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28887 raw28887Labels permutation346 hz
    mixedMoment B raw28887step0 raw28887step0Labels = mixedMoment B raw28887step1 raw28887step1Labels := by
      have ha : raw28887step1 = (fun i j => raw28887step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28887step1 raw28887step0; decide +kernel
      have hl : raw28887step1Labels = raw28887step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28887step0 raw28887step0Labels permutation149 permutation3
    mixedMoment B raw28887step1 raw28887step1Labels = mixedMoment B raw28887step2 raw28887step2Labels := by
      have ha : raw28887step2 = -raw28887step1 := by apply Matrix.ext; change ∀ i j, raw28887step2 i j = -(raw28887step1 i j); unfold raw28887step2 raw28887step1; decide +kernel
      have hl : raw28887step2Labels = raw28887step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28887step2 raw28887step2Labels = mixedMoment B raw28887step3 raw28887step3Labels := by
      have ha : raw28887step3 = raw28887step2 := by apply Matrix.ext; unfold raw28887step3 raw28887step2; decide +kernel
      have hl : raw28887step2Labels = labelEmbedding6 ∘ raw28887step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28887step2 raw28887step2Labels raw28887step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw28888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw28888step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw28888step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28888step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw28888step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28888 raw28888Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw28888 raw28888Labels = mixedMoment B raw28888step0 raw28888step0Labels := by
      have hz : ∀ j, raw28888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28888step0 = (fun i j => raw28888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28888step0 raw28888; decide +kernel
      have hl : raw28888step0Labels = raw28888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28888 raw28888Labels permutation346 hz
    mixedMoment B raw28888step0 raw28888step0Labels = mixedMoment B raw28888step1 raw28888step1Labels := by
      have ha : raw28888step1 = (fun i j => raw28888step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28888step1 raw28888step0; decide +kernel
      have hl : raw28888step1Labels = raw28888step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28888step0 raw28888step0Labels permutation145 permutation3
    mixedMoment B raw28888step1 raw28888step1Labels = mixedMoment B raw28888step2 raw28888step2Labels := by
      have ha : raw28888step2 = -raw28888step1 := by apply Matrix.ext; change ∀ i j, raw28888step2 i j = -(raw28888step1 i j); unfold raw28888step2 raw28888step1; decide +kernel
      have hl : raw28888step2Labels = raw28888step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28888step2 raw28888step2Labels = mixedMoment B raw28888step3 raw28888step3Labels := by
      have ha : raw28888step3 = raw28888step2 := by apply Matrix.ext; unfold raw28888step3 raw28888step2; decide +kernel
      have hl : raw28888step2Labels = labelEmbedding6 ∘ raw28888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28888step2 raw28888step2Labels raw28888step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw28889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28889step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28889 raw28889Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw28889 raw28889Labels = mixedMoment B raw28889step0 raw28889step0Labels := by
      have ha : raw28889step0 = (fun i j => raw28889 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28889step0 raw28889; decide +kernel
      have hl : raw28889step0Labels = raw28889Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28889 raw28889Labels permutation160 permutation3
    mixedMoment B raw28889step0 raw28889step0Labels = mixedMoment B raw28889step1 raw28889step1Labels := by
      have ha : raw28889step1 = raw28889step0 := by apply Matrix.ext; unfold raw28889step1 raw28889step0; decide +kernel
      have hl : raw28889step0Labels = labelEmbedding6 ∘ raw28889step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28889step0 raw28889step0Labels raw28889step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4320 node4320Labels := by rfl

def raw28890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28890step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28890step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28890step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28890 raw28890Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw28890 raw28890Labels = mixedMoment B raw28890step0 raw28890step0Labels := by
      have ha : raw28890step0 = (fun i j => raw28890 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28890step0 raw28890; decide +kernel
      have hl : raw28890step0Labels = raw28890Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28890 raw28890Labels permutation646 permutation3
    mixedMoment B raw28890step0 raw28890step0Labels = mixedMoment B raw28890step1 raw28890step1Labels := by
      have ha : raw28890step1 = -raw28890step0 := by apply Matrix.ext; change ∀ i j, raw28890step1 i j = -(raw28890step0 i j); unfold raw28890step1 raw28890step0; decide +kernel
      have hl : raw28890step1Labels = raw28890step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28890step1 raw28890step1Labels = mixedMoment B raw28890step2 raw28890step2Labels := by
      have ha : raw28890step2 = raw28890step1 := by apply Matrix.ext; unfold raw28890step2 raw28890step1; decide +kernel
      have hl : raw28890step1Labels = labelEmbedding6 ∘ raw28890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28890step1 raw28890step1Labels raw28890step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

def raw28891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28891step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28891step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28891 raw28891Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw28891 raw28891Labels = mixedMoment B raw28891step0 raw28891step0Labels := by
      have ha : raw28891step0 = (fun i j => raw28891 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28891step0 raw28891; decide +kernel
      have hl : raw28891step0Labels = raw28891Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28891 raw28891Labels permutation644 permutation3
    mixedMoment B raw28891step0 raw28891step0Labels = mixedMoment B raw28891step1 raw28891step1Labels := by
      have ha : raw28891step1 = -raw28891step0 := by apply Matrix.ext; change ∀ i j, raw28891step1 i j = -(raw28891step0 i j); unfold raw28891step1 raw28891step0; decide +kernel
      have hl : raw28891step1Labels = raw28891step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28891step1 raw28891step1Labels = mixedMoment B raw28891step2 raw28891step2Labels := by
      have ha : raw28891step2 = raw28891step1 := by apply Matrix.ext; unfold raw28891step2 raw28891step1; decide +kernel
      have hl : raw28891step1Labels = labelEmbedding6 ∘ raw28891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28891step1 raw28891step1Labels raw28891step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

def raw28892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28892step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28892step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28892step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28892 raw28892Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw28892 raw28892Labels = mixedMoment B raw28892step0 raw28892step0Labels := by
      have ha : raw28892step0 = (fun i j => raw28892 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28892step0 raw28892; decide +kernel
      have hl : raw28892step0Labels = raw28892Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28892 raw28892Labels permutation640 permutation3
    mixedMoment B raw28892step0 raw28892step0Labels = mixedMoment B raw28892step1 raw28892step1Labels := by
      have ha : raw28892step1 = -raw28892step0 := by apply Matrix.ext; change ∀ i j, raw28892step1 i j = -(raw28892step0 i j); unfold raw28892step1 raw28892step0; decide +kernel
      have hl : raw28892step1Labels = raw28892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28892step1 raw28892step1Labels = mixedMoment B raw28892step2 raw28892step2Labels := by
      have ha : raw28892step2 = raw28892step1 := by apply Matrix.ext; unfold raw28892step2 raw28892step1; decide +kernel
      have hl : raw28892step1Labels = labelEmbedding6 ∘ raw28892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28892step1 raw28892step1Labels raw28892step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

def raw28893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28893step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28893step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28893step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28893 raw28893Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw28893 raw28893Labels = mixedMoment B raw28893step0 raw28893step0Labels := by
      have hz : ∀ j, raw28893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28893step0 = (fun i j => raw28893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28893step0 raw28893; decide +kernel
      have hl : raw28893step0Labels = raw28893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28893 raw28893Labels permutation346 hz
    mixedMoment B raw28893step0 raw28893step0Labels = mixedMoment B raw28893step1 raw28893step1Labels := by
      have ha : raw28893step1 = (fun i j => raw28893step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28893step1 raw28893step0; decide +kernel
      have hl : raw28893step1Labels = raw28893step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28893step0 raw28893step0Labels permutation145 permutation3
    mixedMoment B raw28893step1 raw28893step1Labels = mixedMoment B raw28893step2 raw28893step2Labels := by
      have ha : raw28893step2 = -raw28893step1 := by apply Matrix.ext; change ∀ i j, raw28893step2 i j = -(raw28893step1 i j); unfold raw28893step2 raw28893step1; decide +kernel
      have hl : raw28893step2Labels = raw28893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28893step2 raw28893step2Labels = mixedMoment B raw28893step3 raw28893step3Labels := by
      have ha : raw28893step3 = raw28893step2 := by apply Matrix.ext; unfold raw28893step3 raw28893step2; decide +kernel
      have hl : raw28893step2Labels = labelEmbedding6 ∘ raw28893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28893step2 raw28893step2Labels raw28893step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

def raw28894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28894step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28894step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28894step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28894 raw28894Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw28894 raw28894Labels = mixedMoment B raw28894step0 raw28894step0Labels := by
      have ha : raw28894step0 = (fun i j => raw28894 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28894step0 raw28894; decide +kernel
      have hl : raw28894step0Labels = raw28894Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28894 raw28894Labels permutation662 permutation3
    mixedMoment B raw28894step0 raw28894step0Labels = mixedMoment B raw28894step1 raw28894step1Labels := by
      have ha : raw28894step1 = -raw28894step0 := by apply Matrix.ext; change ∀ i j, raw28894step1 i j = -(raw28894step0 i j); unfold raw28894step1 raw28894step0; decide +kernel
      have hl : raw28894step1Labels = raw28894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28894step1 raw28894step1Labels = mixedMoment B raw28894step2 raw28894step2Labels := by
      have ha : raw28894step2 = raw28894step1 := by apply Matrix.ext; unfold raw28894step2 raw28894step1; decide +kernel
      have hl : raw28894step1Labels = labelEmbedding6 ∘ raw28894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28894step1 raw28894step1Labels raw28894step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4760 node4760Labels := by rfl

def raw28895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28895step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28895step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28895step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28895step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28895 raw28895Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw28895 raw28895Labels = mixedMoment B raw28895step0 raw28895step0Labels := by
      have hz : ∀ j, raw28895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28895step0 = (fun i j => raw28895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28895step0 raw28895; decide +kernel
      have hl : raw28895step0Labels = raw28895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28895 raw28895Labels permutation346 hz
    mixedMoment B raw28895step0 raw28895step0Labels = mixedMoment B raw28895step1 raw28895step1Labels := by
      have ha : raw28895step1 = (fun i j => raw28895step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28895step1 raw28895step0; decide +kernel
      have hl : raw28895step1Labels = raw28895step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28895step0 raw28895step0Labels permutation145 permutation3
    mixedMoment B raw28895step1 raw28895step1Labels = mixedMoment B raw28895step2 raw28895step2Labels := by
      have ha : raw28895step2 = -raw28895step1 := by apply Matrix.ext; change ∀ i j, raw28895step2 i j = -(raw28895step1 i j); unfold raw28895step2 raw28895step1; decide +kernel
      have hl : raw28895step2Labels = raw28895step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28895step2 raw28895step2Labels = mixedMoment B raw28895step3 raw28895step3Labels := by
      have ha : raw28895step3 = raw28895step2 := by apply Matrix.ext; unfold raw28895step3 raw28895step2; decide +kernel
      have hl : raw28895step2Labels = labelEmbedding6 ∘ raw28895step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28895step2 raw28895step2Labels raw28895step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw28896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw28896step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw28896step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28896 raw28896Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw28896 raw28896Labels = mixedMoment B raw28896step0 raw28896step0Labels := by
      have hz : ∀ j, raw28896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28896step0 = (fun i j => raw28896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28896step0 raw28896; decide +kernel
      have hl : raw28896step0Labels = raw28896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28896 raw28896Labels permutation346 hz
    mixedMoment B raw28896step0 raw28896step0Labels = mixedMoment B raw28896step1 raw28896step1Labels := by
      have ha : raw28896step1 = (fun i j => raw28896step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28896step1 raw28896step0; decide +kernel
      have hl : raw28896step1Labels = raw28896step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28896step0 raw28896step0Labels permutation32 permutation3
    mixedMoment B raw28896step1 raw28896step1Labels = mixedMoment B raw28896step2 raw28896step2Labels := by
      have ha : raw28896step2 = raw28896step1 := by apply Matrix.ext; unfold raw28896step2 raw28896step1; decide +kernel
      have hl : raw28896step1Labels = labelEmbedding6 ∘ raw28896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28896step1 raw28896step1Labels raw28896step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4324 node4324Labels := by rfl

def raw28897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28897step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28897step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28897 raw28897Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw28897 raw28897Labels = mixedMoment B raw28897step0 raw28897step0Labels := by
      have hz : ∀ j, raw28897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28897step0 = (fun i j => raw28897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28897step0 raw28897; decide +kernel
      have hl : raw28897step0Labels = raw28897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28897 raw28897Labels permutation346 hz
    mixedMoment B raw28897step0 raw28897step0Labels = mixedMoment B raw28897step1 raw28897step1Labels := by
      have ha : raw28897step1 = (fun i j => raw28897step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28897step1 raw28897step0; decide +kernel
      have hl : raw28897step1Labels = raw28897step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28897step0 raw28897step0Labels permutation151 permutation3
    mixedMoment B raw28897step1 raw28897step1Labels = mixedMoment B raw28897step2 raw28897step2Labels := by
      have ha : raw28897step2 = -raw28897step1 := by apply Matrix.ext; change ∀ i j, raw28897step2 i j = -(raw28897step1 i j); unfold raw28897step2 raw28897step1; decide +kernel
      have hl : raw28897step2Labels = raw28897step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28897step2 raw28897step2Labels = mixedMoment B raw28897step3 raw28897step3Labels := by
      have ha : raw28897step3 = raw28897step2 := by apply Matrix.ext; unfold raw28897step3 raw28897step2; decide +kernel
      have hl : raw28897step2Labels = labelEmbedding6 ∘ raw28897step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28897step2 raw28897step2Labels raw28897step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

def raw28898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28898step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28898step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28898 raw28898Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw28898 raw28898Labels = mixedMoment B raw28898step0 raw28898step0Labels := by
      have ha : raw28898step0 = (fun i j => raw28898 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28898step0 raw28898; decide +kernel
      have hl : raw28898step0Labels = raw28898Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28898 raw28898Labels permutation686 permutation3
    mixedMoment B raw28898step0 raw28898step0Labels = mixedMoment B raw28898step1 raw28898step1Labels := by
      have ha : raw28898step1 = -raw28898step0 := by apply Matrix.ext; change ∀ i j, raw28898step1 i j = -(raw28898step0 i j); unfold raw28898step1 raw28898step0; decide +kernel
      have hl : raw28898step1Labels = raw28898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28898step1 raw28898step1Labels = mixedMoment B raw28898step2 raw28898step2Labels := by
      have ha : raw28898step2 = raw28898step1 := by apply Matrix.ext; unfold raw28898step2 raw28898step1; decide +kernel
      have hl : raw28898step1Labels = labelEmbedding6 ∘ raw28898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28898step1 raw28898step1Labels raw28898step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4631 node4631Labels := by rfl

def raw28899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28899step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28899step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28899step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28899step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28899 raw28899Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw28899 raw28899Labels = mixedMoment B raw28899step0 raw28899step0Labels := by
      have hz : ∀ j, raw28899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28899step0 = (fun i j => raw28899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28899step0 raw28899; decide +kernel
      have hl : raw28899step0Labels = raw28899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28899 raw28899Labels permutation346 hz
    mixedMoment B raw28899step0 raw28899step0Labels = mixedMoment B raw28899step1 raw28899step1Labels := by
      have ha : raw28899step1 = (fun i j => raw28899step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28899step1 raw28899step0; decide +kernel
      have hl : raw28899step1Labels = raw28899step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28899step0 raw28899step0Labels permutation149 permutation3
    mixedMoment B raw28899step1 raw28899step1Labels = mixedMoment B raw28899step2 raw28899step2Labels := by
      have ha : raw28899step2 = -raw28899step1 := by apply Matrix.ext; change ∀ i j, raw28899step2 i j = -(raw28899step1 i j); unfold raw28899step2 raw28899step1; decide +kernel
      have hl : raw28899step2Labels = raw28899step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28899step2 raw28899step2Labels = mixedMoment B raw28899step3 raw28899step3Labels := by
      have ha : raw28899step3 = raw28899step2 := by apply Matrix.ext; unfold raw28899step3 raw28899step2; decide +kernel
      have hl : raw28899step2Labels = labelEmbedding6 ∘ raw28899step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28899step2 raw28899step2Labels raw28899step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

def raw28900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28900step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28900step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28900step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28900 raw28900Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw28900 raw28900Labels = mixedMoment B raw28900step0 raw28900step0Labels := by
      have hz : ∀ j, raw28900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28900step0 = (fun i j => raw28900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28900step0 raw28900; decide +kernel
      have hl : raw28900step0Labels = raw28900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28900 raw28900Labels permutation346 hz
    mixedMoment B raw28900step0 raw28900step0Labels = mixedMoment B raw28900step1 raw28900step1Labels := by
      have ha : raw28900step1 = (fun i j => raw28900step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28900step1 raw28900step0; decide +kernel
      have hl : raw28900step1Labels = raw28900step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28900step0 raw28900step0Labels permutation151 permutation3
    mixedMoment B raw28900step1 raw28900step1Labels = mixedMoment B raw28900step2 raw28900step2Labels := by
      have ha : raw28900step2 = -raw28900step1 := by apply Matrix.ext; change ∀ i j, raw28900step2 i j = -(raw28900step1 i j); unfold raw28900step2 raw28900step1; decide +kernel
      have hl : raw28900step2Labels = raw28900step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28900step2 raw28900step2Labels = mixedMoment B raw28900step3 raw28900step3Labels := by
      have ha : raw28900step3 = raw28900step2 := by apply Matrix.ext; unfold raw28900step3 raw28900step2; decide +kernel
      have hl : raw28900step2Labels = labelEmbedding6 ∘ raw28900step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28900step2 raw28900step2Labels raw28900step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4198 node4198Labels := by rfl

def raw28901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28901step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28901step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28901step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28901 raw28901Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw28901 raw28901Labels = mixedMoment B raw28901step0 raw28901step0Labels := by
      have hz : ∀ j, raw28901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28901step0 = (fun i j => raw28901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28901step0 raw28901; decide +kernel
      have hl : raw28901step0Labels = raw28901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28901 raw28901Labels permutation346 hz
    mixedMoment B raw28901step0 raw28901step0Labels = mixedMoment B raw28901step1 raw28901step1Labels := by
      have ha : raw28901step1 = (fun i j => raw28901step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28901step1 raw28901step0; decide +kernel
      have hl : raw28901step1Labels = raw28901step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28901step0 raw28901step0Labels permutation151 permutation3
    mixedMoment B raw28901step1 raw28901step1Labels = mixedMoment B raw28901step2 raw28901step2Labels := by
      have ha : raw28901step2 = -raw28901step1 := by apply Matrix.ext; change ∀ i j, raw28901step2 i j = -(raw28901step1 i j); unfold raw28901step2 raw28901step1; decide +kernel
      have hl : raw28901step2Labels = raw28901step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28901step2 raw28901step2Labels = mixedMoment B raw28901step3 raw28901step3Labels := by
      have ha : raw28901step3 = raw28901step2 := by apply Matrix.ext; unfold raw28901step3 raw28901step2; decide +kernel
      have hl : raw28901step2Labels = labelEmbedding6 ∘ raw28901step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28901step2 raw28901step2Labels raw28901step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4204 node4204Labels := by rfl

def raw28902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28902step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28902step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28902step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28902 raw28902Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw28902 raw28902Labels = mixedMoment B raw28902step0 raw28902step0Labels := by
      have ha : raw28902step0 = (fun i j => raw28902 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28902step0 raw28902; decide +kernel
      have hl : raw28902step0Labels = raw28902Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28902 raw28902Labels permutation686 permutation3
    mixedMoment B raw28902step0 raw28902step0Labels = mixedMoment B raw28902step1 raw28902step1Labels := by
      have ha : raw28902step1 = -raw28902step0 := by apply Matrix.ext; change ∀ i j, raw28902step1 i j = -(raw28902step0 i j); unfold raw28902step1 raw28902step0; decide +kernel
      have hl : raw28902step1Labels = raw28902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28902step1 raw28902step1Labels = mixedMoment B raw28902step2 raw28902step2Labels := by
      have ha : raw28902step2 = raw28902step1 := by apply Matrix.ext; unfold raw28902step2 raw28902step1; decide +kernel
      have hl : raw28902step1Labels = labelEmbedding6 ∘ raw28902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28902step1 raw28902step1Labels raw28902step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4196 node4196Labels := by rfl

def raw28903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28903step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28903step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28903step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28903step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28903 raw28903Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw28903 raw28903Labels = mixedMoment B raw28903step0 raw28903step0Labels := by
      have hz : ∀ j, raw28903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28903step0 = (fun i j => raw28903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28903step0 raw28903; decide +kernel
      have hl : raw28903step0Labels = raw28903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28903 raw28903Labels permutation346 hz
    mixedMoment B raw28903step0 raw28903step0Labels = mixedMoment B raw28903step1 raw28903step1Labels := by
      have ha : raw28903step1 = (fun i j => raw28903step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28903step1 raw28903step0; decide +kernel
      have hl : raw28903step1Labels = raw28903step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28903step0 raw28903step0Labels permutation149 permutation3
    mixedMoment B raw28903step1 raw28903step1Labels = mixedMoment B raw28903step2 raw28903step2Labels := by
      have ha : raw28903step2 = -raw28903step1 := by apply Matrix.ext; change ∀ i j, raw28903step2 i j = -(raw28903step1 i j); unfold raw28903step2 raw28903step1; decide +kernel
      have hl : raw28903step2Labels = raw28903step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28903step2 raw28903step2Labels = mixedMoment B raw28903step3 raw28903step3Labels := by
      have ha : raw28903step3 = raw28903step2 := by apply Matrix.ext; unfold raw28903step3 raw28903step2; decide +kernel
      have hl : raw28903step2Labels = labelEmbedding6 ∘ raw28903step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28903step2 raw28903step2Labels raw28903step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw28904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28904step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28904step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28904step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28904step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28904 raw28904Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw28904 raw28904Labels = mixedMoment B raw28904step0 raw28904step0Labels := by
      have hz : ∀ j, raw28904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28904step0 = (fun i j => raw28904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28904step0 raw28904; decide +kernel
      have hl : raw28904step0Labels = raw28904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28904 raw28904Labels permutation346 hz
    mixedMoment B raw28904step0 raw28904step0Labels = mixedMoment B raw28904step1 raw28904step1Labels := by
      have ha : raw28904step1 = (fun i j => raw28904step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28904step1 raw28904step0; decide +kernel
      have hl : raw28904step1Labels = raw28904step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28904step0 raw28904step0Labels permutation145 permutation3
    mixedMoment B raw28904step1 raw28904step1Labels = mixedMoment B raw28904step2 raw28904step2Labels := by
      have ha : raw28904step2 = -raw28904step1 := by apply Matrix.ext; change ∀ i j, raw28904step2 i j = -(raw28904step1 i j); unfold raw28904step2 raw28904step1; decide +kernel
      have hl : raw28904step2Labels = raw28904step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28904step2 raw28904step2Labels = mixedMoment B raw28904step3 raw28904step3Labels := by
      have ha : raw28904step3 = raw28904step2 := by apply Matrix.ext; unfold raw28904step3 raw28904step2; decide +kernel
      have hl : raw28904step2Labels = labelEmbedding6 ∘ raw28904step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28904step2 raw28904step2Labels raw28904step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw28905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28905step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28905 raw28905Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw28905 raw28905Labels = mixedMoment B raw28905step0 raw28905step0Labels := by
      have hz : ∀ j, raw28905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28905step0 = (fun i j => raw28905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28905step0 raw28905; decide +kernel
      have hl : raw28905step0Labels = raw28905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28905 raw28905Labels permutation346 hz
    mixedMoment B raw28905step0 raw28905step0Labels = mixedMoment B raw28905step1 raw28905step1Labels := by
      have ha : raw28905step1 = (fun i j => raw28905step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28905step1 raw28905step0; decide +kernel
      have hl : raw28905step1Labels = raw28905step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28905step0 raw28905step0Labels permutation150 permutation3
    mixedMoment B raw28905step1 raw28905step1Labels = mixedMoment B raw28905step2 raw28905step2Labels := by
      have ha : raw28905step2 = -raw28905step1 := by apply Matrix.ext; change ∀ i j, raw28905step2 i j = -(raw28905step1 i j); unfold raw28905step2 raw28905step1; decide +kernel
      have hl : raw28905step2Labels = raw28905step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw28906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28906 raw28906Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw28906 raw28906Labels = mixedMoment B raw28906step0 raw28906step0Labels := by
      have ha : raw28906step0 = (fun i j => raw28906 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28906step0 raw28906; decide +kernel
      have hl : raw28906step0Labels = raw28906Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28906 raw28906Labels permutation686 permutation3
    mixedMoment B raw28906step0 raw28906step0Labels = mixedMoment B raw28906step1 raw28906step1Labels := by
      have ha : raw28906step1 = -raw28906step0 := by apply Matrix.ext; change ∀ i j, raw28906step1 i j = -(raw28906step0 i j); unfold raw28906step1 raw28906step0; decide +kernel
      have hl : raw28906step1Labels = raw28906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw28907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28907 raw28907Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw28907 raw28907Labels = mixedMoment B raw28907step0 raw28907step0Labels := by
      have hz : ∀ j, raw28907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28907step0 = (fun i j => raw28907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28907step0 raw28907; decide +kernel
      have hl : raw28907step0Labels = raw28907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28907 raw28907Labels permutation346 hz
    mixedMoment B raw28907step0 raw28907step0Labels = mixedMoment B raw28907step1 raw28907step1Labels := by
      have ha : raw28907step1 = (fun i j => raw28907step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28907step1 raw28907step0; decide +kernel
      have hl : raw28907step1Labels = raw28907step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28907step0 raw28907step0Labels permutation149 permutation3
    mixedMoment B raw28907step1 raw28907step1Labels = mixedMoment B raw28907step2 raw28907step2Labels := by
      have ha : raw28907step2 = -raw28907step1 := by apply Matrix.ext; change ∀ i j, raw28907step2 i j = -(raw28907step1 i j); unfold raw28907step2 raw28907step1; decide +kernel
      have hl : raw28907step2Labels = raw28907step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw28908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw28908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw28908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28908 raw28908Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw28908 raw28908Labels = mixedMoment B raw28908step0 raw28908step0Labels := by
      have hz : ∀ j, raw28908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28908step0 = (fun i j => raw28908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28908step0 raw28908; decide +kernel
      have hl : raw28908step0Labels = raw28908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28908 raw28908Labels permutation346 hz
    mixedMoment B raw28908step0 raw28908step0Labels = mixedMoment B raw28908step1 raw28908step1Labels := by
      have ha : raw28908step1 = (fun i j => raw28908step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28908step1 raw28908step0; decide +kernel
      have hl : raw28908step1Labels = raw28908step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28908step0 raw28908step0Labels permutation145 permutation3
    mixedMoment B raw28908step1 raw28908step1Labels = mixedMoment B raw28908step2 raw28908step2Labels := by
      have ha : raw28908step2 = -raw28908step1 := by apply Matrix.ext; change ∀ i j, raw28908step2 i j = -(raw28908step1 i j); unfold raw28908step2 raw28908step1; decide +kernel
      have hl : raw28908step2Labels = raw28908step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw28909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28909 raw28909Labels = mixedMoment B node898 node898Labels := by
  calc
    mixedMoment B raw28909 raw28909Labels = mixedMoment B raw28909step0 raw28909step0Labels := by
      have ha : raw28909step0 = (fun i j => raw28909 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28909step0 raw28909; decide +kernel
      have hl : raw28909step0Labels = raw28909Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28909 raw28909Labels permutation160 permutation3
    _ = mixedMoment B node898 node898Labels := by rfl

def raw28910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28910step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28910 raw28910Labels = mixedMoment B node1860 node1860Labels := by
  calc
    mixedMoment B raw28910 raw28910Labels = mixedMoment B raw28910step0 raw28910step0Labels := by
      have ha : raw28910step0 = (fun i j => raw28910 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28910step0 raw28910; decide +kernel
      have hl : raw28910step0Labels = raw28910Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28910 raw28910Labels permutation646 permutation3
    mixedMoment B raw28910step0 raw28910step0Labels = mixedMoment B raw28910step1 raw28910step1Labels := by
      have ha : raw28910step1 = -raw28910step0 := by apply Matrix.ext; change ∀ i j, raw28910step1 i j = -(raw28910step0 i j); unfold raw28910step1 raw28910step0; decide +kernel
      have hl : raw28910step1Labels = raw28910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1860 node1860Labels := by rfl

def raw28911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28911 raw28911Labels = mixedMoment B node1863 node1863Labels := by
  calc
    mixedMoment B raw28911 raw28911Labels = mixedMoment B raw28911step0 raw28911step0Labels := by
      have ha : raw28911step0 = (fun i j => raw28911 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28911step0 raw28911; decide +kernel
      have hl : raw28911step0Labels = raw28911Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28911 raw28911Labels permutation644 permutation3
    mixedMoment B raw28911step0 raw28911step0Labels = mixedMoment B raw28911step1 raw28911step1Labels := by
      have ha : raw28911step1 = -raw28911step0 := by apply Matrix.ext; change ∀ i j, raw28911step1 i j = -(raw28911step0 i j); unfold raw28911step1 raw28911step0; decide +kernel
      have hl : raw28911step1Labels = raw28911step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1863 node1863Labels := by rfl

def raw28912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28912 raw28912Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw28912 raw28912Labels = mixedMoment B raw28912step0 raw28912step0Labels := by
      have ha : raw28912step0 = (fun i j => raw28912 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28912step0 raw28912; decide +kernel
      have hl : raw28912step0Labels = raw28912Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28912 raw28912Labels permutation640 permutation3
    mixedMoment B raw28912step0 raw28912step0Labels = mixedMoment B raw28912step1 raw28912step1Labels := by
      have ha : raw28912step1 = -raw28912step0 := by apply Matrix.ext; change ∀ i j, raw28912step1 i j = -(raw28912step0 i j); unfold raw28912step1 raw28912step0; decide +kernel
      have hl : raw28912step1Labels = raw28912step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1897 node1897Labels := by rfl

def raw28913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28913 raw28913Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw28913 raw28913Labels = mixedMoment B raw28913step0 raw28913step0Labels := by
      have hz : ∀ j, raw28913 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28913step0 = (fun i j => raw28913 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28913step0 raw28913; decide +kernel
      have hl : raw28913step0Labels = raw28913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28913 raw28913Labels permutation346 hz
    mixedMoment B raw28913step0 raw28913step0Labels = mixedMoment B raw28913step1 raw28913step1Labels := by
      have ha : raw28913step1 = (fun i j => raw28913step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28913step1 raw28913step0; decide +kernel
      have hl : raw28913step1Labels = raw28913step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28913step0 raw28913step0Labels permutation145 permutation3
    mixedMoment B raw28913step1 raw28913step1Labels = mixedMoment B raw28913step2 raw28913step2Labels := by
      have ha : raw28913step2 = -raw28913step1 := by apply Matrix.ext; change ∀ i j, raw28913step2 i j = -(raw28913step1 i j); unfold raw28913step2 raw28913step1; decide +kernel
      have hl : raw28913step2Labels = raw28913step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1969 node1969Labels := by rfl

def raw28914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28914 raw28914Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw28914 raw28914Labels = mixedMoment B raw28914step0 raw28914step0Labels := by
      have ha : raw28914step0 = (fun i j => raw28914 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28914step0 raw28914; decide +kernel
      have hl : raw28914step0Labels = raw28914Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28914 raw28914Labels permutation662 permutation3
    mixedMoment B raw28914step0 raw28914step0Labels = mixedMoment B raw28914step1 raw28914step1Labels := by
      have ha : raw28914step1 = -raw28914step0 := by apply Matrix.ext; change ∀ i j, raw28914step1 i j = -(raw28914step0 i j); unfold raw28914step1 raw28914step0; decide +kernel
      have hl : raw28914step1Labels = raw28914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1960 node1960Labels := by rfl

def raw28915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28915 raw28915Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw28915 raw28915Labels = mixedMoment B raw28915step0 raw28915step0Labels := by
      have hz : ∀ j, raw28915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28915step0 = (fun i j => raw28915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28915step0 raw28915; decide +kernel
      have hl : raw28915step0Labels = raw28915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28915 raw28915Labels permutation346 hz
    mixedMoment B raw28915step0 raw28915step0Labels = mixedMoment B raw28915step1 raw28915step1Labels := by
      have ha : raw28915step1 = (fun i j => raw28915step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28915step1 raw28915step0; decide +kernel
      have hl : raw28915step1Labels = raw28915step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28915step0 raw28915step0Labels permutation145 permutation3
    mixedMoment B raw28915step1 raw28915step1Labels = mixedMoment B raw28915step2 raw28915step2Labels := by
      have ha : raw28915step2 = -raw28915step1 := by apply Matrix.ext; change ∀ i j, raw28915step2 i j = -(raw28915step1 i j); unfold raw28915step2 raw28915step1; decide +kernel
      have hl : raw28915step2Labels = raw28915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw28916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw28916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28916 raw28916Labels = mixedMoment B node902 node902Labels := by
  calc
    mixedMoment B raw28916 raw28916Labels = mixedMoment B raw28916step0 raw28916step0Labels := by
      have hz : ∀ j, raw28916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28916step0 = (fun i j => raw28916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28916step0 raw28916; decide +kernel
      have hl : raw28916step0Labels = raw28916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28916 raw28916Labels permutation346 hz
    mixedMoment B raw28916step0 raw28916step0Labels = mixedMoment B raw28916step1 raw28916step1Labels := by
      have ha : raw28916step1 = (fun i j => raw28916step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28916step1 raw28916step0; decide +kernel
      have hl : raw28916step1Labels = raw28916step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28916step0 raw28916step0Labels permutation32 permutation3
    _ = mixedMoment B node902 node902Labels := by rfl

def raw28917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28917step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28917 raw28917Labels = mixedMoment B node1766 node1766Labels := by
  calc
    mixedMoment B raw28917 raw28917Labels = mixedMoment B raw28917step0 raw28917step0Labels := by
      have hz : ∀ j, raw28917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28917step0 = (fun i j => raw28917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28917step0 raw28917; decide +kernel
      have hl : raw28917step0Labels = raw28917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28917 raw28917Labels permutation346 hz
    mixedMoment B raw28917step0 raw28917step0Labels = mixedMoment B raw28917step1 raw28917step1Labels := by
      have ha : raw28917step1 = (fun i j => raw28917step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28917step1 raw28917step0; decide +kernel
      have hl : raw28917step1Labels = raw28917step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28917step0 raw28917step0Labels permutation151 permutation3
    mixedMoment B raw28917step1 raw28917step1Labels = mixedMoment B raw28917step2 raw28917step2Labels := by
      have ha : raw28917step2 = -raw28917step1 := by apply Matrix.ext; change ∀ i j, raw28917step2 i j = -(raw28917step1 i j); unfold raw28917step2 raw28917step1; decide +kernel
      have hl : raw28917step2Labels = raw28917step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1766 node1766Labels := by rfl

def raw28918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28918 raw28918Labels = mixedMoment B node1760 node1760Labels := by
  calc
    mixedMoment B raw28918 raw28918Labels = mixedMoment B raw28918step0 raw28918step0Labels := by
      have ha : raw28918step0 = (fun i j => raw28918 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28918step0 raw28918; decide +kernel
      have hl : raw28918step0Labels = raw28918Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28918 raw28918Labels permutation686 permutation3
    mixedMoment B raw28918step0 raw28918step0Labels = mixedMoment B raw28918step1 raw28918step1Labels := by
      have ha : raw28918step1 = -raw28918step0 := by apply Matrix.ext; change ∀ i j, raw28918step1 i j = -(raw28918step0 i j); unfold raw28918step1 raw28918step0; decide +kernel
      have hl : raw28918step1Labels = raw28918step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1760 node1760Labels := by rfl

def raw28919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28919 raw28919Labels = mixedMoment B node1773 node1773Labels := by
  calc
    mixedMoment B raw28919 raw28919Labels = mixedMoment B raw28919step0 raw28919step0Labels := by
      have hz : ∀ j, raw28919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28919step0 = (fun i j => raw28919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28919step0 raw28919; decide +kernel
      have hl : raw28919step0Labels = raw28919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28919 raw28919Labels permutation346 hz
    mixedMoment B raw28919step0 raw28919step0Labels = mixedMoment B raw28919step1 raw28919step1Labels := by
      have ha : raw28919step1 = (fun i j => raw28919step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28919step1 raw28919step0; decide +kernel
      have hl : raw28919step1Labels = raw28919step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28919step0 raw28919step0Labels permutation149 permutation3
    mixedMoment B raw28919step1 raw28919step1Labels = mixedMoment B raw28919step2 raw28919step2Labels := by
      have ha : raw28919step2 = -raw28919step1 := by apply Matrix.ext; change ∀ i j, raw28919step2 i j = -(raw28919step1 i j); unfold raw28919step2 raw28919step1; decide +kernel
      have hl : raw28919step2Labels = raw28919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1773 node1773Labels := by rfl

def raw28920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28920 raw28920Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw28920 raw28920Labels = mixedMoment B raw28920step0 raw28920step0Labels := by
      have hz : ∀ j, raw28920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28920step0 = (fun i j => raw28920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28920step0 raw28920; decide +kernel
      have hl : raw28920step0Labels = raw28920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28920 raw28920Labels permutation346 hz
    mixedMoment B raw28920step0 raw28920step0Labels = mixedMoment B raw28920step1 raw28920step1Labels := by
      have ha : raw28920step1 = (fun i j => raw28920step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28920step1 raw28920step0; decide +kernel
      have hl : raw28920step1Labels = raw28920step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28920step0 raw28920step0Labels permutation151 permutation3
    mixedMoment B raw28920step1 raw28920step1Labels = mixedMoment B raw28920step2 raw28920step2Labels := by
      have ha : raw28920step2 = -raw28920step1 := by apply Matrix.ext; change ∀ i j, raw28920step2 i j = -(raw28920step1 i j); unfold raw28920step2 raw28920step1; decide +kernel
      have hl : raw28920step2Labels = raw28920step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node701 node701Labels := by rfl

def raw28921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28921step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28921step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28921 raw28921Labels = mixedMoment B node707 node707Labels := by
  calc
    mixedMoment B raw28921 raw28921Labels = mixedMoment B raw28921step0 raw28921step0Labels := by
      have hz : ∀ j, raw28921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28921step0 = (fun i j => raw28921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28921step0 raw28921; decide +kernel
      have hl : raw28921step0Labels = raw28921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28921 raw28921Labels permutation346 hz
    mixedMoment B raw28921step0 raw28921step0Labels = mixedMoment B raw28921step1 raw28921step1Labels := by
      have ha : raw28921step1 = (fun i j => raw28921step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28921step1 raw28921step0; decide +kernel
      have hl : raw28921step1Labels = raw28921step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28921step0 raw28921step0Labels permutation151 permutation3
    mixedMoment B raw28921step1 raw28921step1Labels = mixedMoment B raw28921step2 raw28921step2Labels := by
      have ha : raw28921step2 = -raw28921step1 := by apply Matrix.ext; change ∀ i j, raw28921step2 i j = -(raw28921step1 i j); unfold raw28921step2 raw28921step1; decide +kernel
      have hl : raw28921step2Labels = raw28921step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node707 node707Labels := by rfl

def raw28922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28922 raw28922Labels = mixedMoment B node699 node699Labels := by
  calc
    mixedMoment B raw28922 raw28922Labels = mixedMoment B raw28922step0 raw28922step0Labels := by
      have ha : raw28922step0 = (fun i j => raw28922 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28922step0 raw28922; decide +kernel
      have hl : raw28922step0Labels = raw28922Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28922 raw28922Labels permutation686 permutation3
    mixedMoment B raw28922step0 raw28922step0Labels = mixedMoment B raw28922step1 raw28922step1Labels := by
      have ha : raw28922step1 = -raw28922step0 := by apply Matrix.ext; change ∀ i j, raw28922step1 i j = -(raw28922step0 i j); unfold raw28922step1 raw28922step0; decide +kernel
      have hl : raw28922step1Labels = raw28922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node699 node699Labels := by rfl

def raw28923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28923step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28923 raw28923Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw28923 raw28923Labels = mixedMoment B raw28923step0 raw28923step0Labels := by
      have hz : ∀ j, raw28923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28923step0 = (fun i j => raw28923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28923step0 raw28923; decide +kernel
      have hl : raw28923step0Labels = raw28923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28923 raw28923Labels permutation346 hz
    mixedMoment B raw28923step0 raw28923step0Labels = mixedMoment B raw28923step1 raw28923step1Labels := by
      have ha : raw28923step1 = (fun i j => raw28923step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28923step1 raw28923step0; decide +kernel
      have hl : raw28923step1Labels = raw28923step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28923step0 raw28923step0Labels permutation149 permutation3
    mixedMoment B raw28923step1 raw28923step1Labels = mixedMoment B raw28923step2 raw28923step2Labels := by
      have ha : raw28923step2 = -raw28923step1 := by apply Matrix.ext; change ∀ i j, raw28923step2 i j = -(raw28923step1 i j); unfold raw28923step2 raw28923step1; decide +kernel
      have hl : raw28923step2Labels = raw28923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node715 node715Labels := by rfl

def raw28924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28924 raw28924Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw28924 raw28924Labels = mixedMoment B raw28924step0 raw28924step0Labels := by
      have hz : ∀ j, raw28924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28924step0 = (fun i j => raw28924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28924step0 raw28924; decide +kernel
      have hl : raw28924step0Labels = raw28924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28924 raw28924Labels permutation346 hz
    mixedMoment B raw28924step0 raw28924step0Labels = mixedMoment B raw28924step1 raw28924step1Labels := by
      have ha : raw28924step1 = (fun i j => raw28924step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28924step1 raw28924step0; decide +kernel
      have hl : raw28924step1Labels = raw28924step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28924step0 raw28924step0Labels permutation145 permutation3
    mixedMoment B raw28924step1 raw28924step1Labels = mixedMoment B raw28924step2 raw28924step2Labels := by
      have ha : raw28924step2 = -raw28924step1 := by apply Matrix.ext; change ∀ i j, raw28924step2 i j = -(raw28924step1 i j); unfold raw28924step2 raw28924step1; decide +kernel
      have hl : raw28924step2Labels = raw28924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node785 node785Labels := by rfl

def raw28925 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28925step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28925step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28925step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28925step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28925 raw28925Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw28925 raw28925Labels = mixedMoment B raw28925step0 raw28925step0Labels := by
      have hz : ∀ j, raw28925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28925step0 = (fun i j => raw28925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28925step0 raw28925; decide +kernel
      have hl : raw28925step0Labels = raw28925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28925 raw28925Labels permutation346 hz
    mixedMoment B raw28925step0 raw28925step0Labels = mixedMoment B raw28925step1 raw28925step1Labels := by
      have ha : raw28925step1 = (fun i j => raw28925step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28925step1 raw28925step0; decide +kernel
      have hl : raw28925step1Labels = raw28925step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28925step0 raw28925step0Labels permutation151 permutation6
    mixedMoment B raw28925step1 raw28925step1Labels = mixedMoment B raw28925step2 raw28925step2Labels := by
      have ha : raw28925step2 = -raw28925step1 := by apply Matrix.ext; change ∀ i j, raw28925step2 i j = -(raw28925step1 i j); unfold raw28925step2 raw28925step1; decide +kernel
      have hl : raw28925step2Labels = raw28925step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28925step2 raw28925step2Labels = mixedMoment B raw28925step3 raw28925step3Labels := by
      have ha : raw28925step3 = raw28925step2 := by apply Matrix.ext; unfold raw28925step3 raw28925step2; decide +kernel
      have hl : raw28925step2Labels = labelEmbedding9 ∘ raw28925step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28925step2 raw28925step2Labels raw28925step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw28926 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw28926step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28926step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28926step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28926step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28926 raw28926Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw28926 raw28926Labels = mixedMoment B raw28926step0 raw28926step0Labels := by
      have ha : raw28926step0 = (fun i j => raw28926 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28926step0 raw28926; decide +kernel
      have hl : raw28926step0Labels = raw28926Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28926 raw28926Labels permutation682 permutation6
    mixedMoment B raw28926step0 raw28926step0Labels = mixedMoment B raw28926step1 raw28926step1Labels := by
      have ha : raw28926step1 = -raw28926step0 := by apply Matrix.ext; change ∀ i j, raw28926step1 i j = -(raw28926step0 i j); unfold raw28926step1 raw28926step0; decide +kernel
      have hl : raw28926step1Labels = raw28926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28926step1 raw28926step1Labels = mixedMoment B raw28926step2 raw28926step2Labels := by
      have ha : raw28926step2 = raw28926step1 := by apply Matrix.ext; unfold raw28926step2 raw28926step1; decide +kernel
      have hl : raw28926step1Labels = labelEmbedding9 ∘ raw28926step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28926step1 raw28926step1Labels raw28926step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw28927 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28927step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28927step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28927step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28927step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28927 raw28927Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw28927 raw28927Labels = mixedMoment B raw28927step0 raw28927step0Labels := by
      have hz : ∀ j, raw28927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28927step0 = (fun i j => raw28927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28927step0 raw28927; decide +kernel
      have hl : raw28927step0Labels = raw28927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28927 raw28927Labels permutation346 hz
    mixedMoment B raw28927step0 raw28927step0Labels = mixedMoment B raw28927step1 raw28927step1Labels := by
      have ha : raw28927step1 = (fun i j => raw28927step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28927step1 raw28927step0; decide +kernel
      have hl : raw28927step1Labels = raw28927step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28927step0 raw28927step0Labels permutation151 permutation6
    mixedMoment B raw28927step1 raw28927step1Labels = mixedMoment B raw28927step2 raw28927step2Labels := by
      have ha : raw28927step2 = -raw28927step1 := by apply Matrix.ext; change ∀ i j, raw28927step2 i j = -(raw28927step1 i j); unfold raw28927step2 raw28927step1; decide +kernel
      have hl : raw28927step2Labels = raw28927step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28927step2 raw28927step2Labels = mixedMoment B raw28927step3 raw28927step3Labels := by
      have ha : raw28927step3 = raw28927step2 := by apply Matrix.ext; unfold raw28927step3 raw28927step2; decide +kernel
      have hl : raw28927step2Labels = labelEmbedding9 ∘ raw28927step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28927step2 raw28927step2Labels raw28927step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
