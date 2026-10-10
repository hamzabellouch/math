import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![2, -2, 0]]
def raw9600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw9600step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9600step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw9600step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9600 raw9600Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw9600 raw9600Labels = mixedMoment B raw9600step0 raw9600step0Labels := by
      have hz : ∀ j, raw9600 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9600step0 = (fun i j => raw9600 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9600step0 raw9600; decide +kernel
      have hl : raw9600step0Labels = raw9600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9600 raw9600Labels permutation434 hz
    mixedMoment B raw9600step0 raw9600step0Labels = mixedMoment B raw9600step1 raw9600step1Labels := by
      have hz : ∀ j, raw9600step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9600step1 = (fun i j => raw9600step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9600step1 raw9600step0; decide +kernel
      have hl : raw9600step1Labels = raw9600step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9600step0 raw9600step0Labels permutation80 hz
    mixedMoment B raw9600step1 raw9600step1Labels = mixedMoment B raw9600step2 raw9600step2Labels := by
      have ha : raw9600step2 = (fun i j => raw9600step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9600step2 raw9600step1; decide +kernel
      have hl : raw9600step2Labels = raw9600step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9600step1 raw9600step1Labels permutation10 permutation3
    mixedMoment B raw9600step2 raw9600step2Labels = mixedMoment B raw9600step3 raw9600step3Labels := by
      have ha : raw9600step3 = raw9600step2 := by apply Matrix.ext; unfold raw9600step3 raw9600step2; decide +kernel
      have hl : raw9600step2Labels = labelEmbedding6 ∘ raw9600step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9600step2 raw9600step2Labels raw9600step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw9601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]
def raw9601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9601step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9601step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9601 raw9601Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw9601 raw9601Labels = mixedMoment B raw9601step0 raw9601step0Labels := by
      have hz : ∀ j, raw9601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9601step0 = (fun i j => raw9601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9601step0 raw9601; decide +kernel
      have hl : raw9601step0Labels = raw9601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9601 raw9601Labels permutation434 hz
    mixedMoment B raw9601step0 raw9601step0Labels = mixedMoment B raw9601step1 raw9601step1Labels := by
      have hz : ∀ j, raw9601step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9601step1 = (fun i j => raw9601step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9601step1 raw9601step0; decide +kernel
      have hl : raw9601step1Labels = raw9601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9601step0 raw9601step0Labels permutation80 hz
    mixedMoment B raw9601step1 raw9601step1Labels = mixedMoment B raw9601step2 raw9601step2Labels := by
      have ha : raw9601step2 = (fun i j => raw9601step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9601step2 raw9601step1; decide +kernel
      have hl : raw9601step2Labels = raw9601step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9601step1 raw9601step1Labels permutation11 permutation3
    mixedMoment B raw9601step2 raw9601step2Labels = mixedMoment B raw9601step3 raw9601step3Labels := by
      have ha : raw9601step3 = raw9601step2 := by apply Matrix.ext; unfold raw9601step3 raw9601step2; decide +kernel
      have hl : raw9601step2Labels = labelEmbedding6 ∘ raw9601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9601step2 raw9601step2Labels raw9601step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw9602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9602 raw9602Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw9602 raw9602Labels = mixedMoment B raw9602step0 raw9602step0Labels := by
      have hz : ∀ j, raw9602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9602step0 = (fun i j => raw9602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9602step0 raw9602; decide +kernel
      have hl : raw9602step0Labels = raw9602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9602 raw9602Labels permutation434 hz
    mixedMoment B raw9602step0 raw9602step0Labels = mixedMoment B raw9602step1 raw9602step1Labels := by
      have ha : raw9602step1 = (fun i j => raw9602step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9602step1 raw9602step0; decide +kernel
      have hl : raw9602step1Labels = raw9602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9602step0 raw9602step0Labels permutation34 permutation3
    mixedMoment B raw9602step1 raw9602step1Labels = mixedMoment B raw9602step2 raw9602step2Labels := by
      have ha : raw9602step2 = raw9602step1 := by apply Matrix.ext; unfold raw9602step2 raw9602step1; decide +kernel
      have hl : raw9602step1Labels = labelEmbedding6 ∘ raw9602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9602step1 raw9602step1Labels raw9602step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw9603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9603step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9603 raw9603Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw9603 raw9603Labels = mixedMoment B raw9603step0 raw9603step0Labels := by
      have hz : ∀ j, raw9603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9603step0 = (fun i j => raw9603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9603step0 raw9603; decide +kernel
      have hl : raw9603step0Labels = raw9603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9603 raw9603Labels permutation434 hz
    mixedMoment B raw9603step0 raw9603step0Labels = mixedMoment B raw9603step1 raw9603step1Labels := by
      have ha : raw9603step1 = (fun i j => raw9603step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9603step1 raw9603step0; decide +kernel
      have hl : raw9603step1Labels = raw9603step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9603step0 raw9603step0Labels permutation34 permutation3
    mixedMoment B raw9603step1 raw9603step1Labels = mixedMoment B raw9603step2 raw9603step2Labels := by
      have ha : raw9603step2 = raw9603step1 := by apply Matrix.ext; unfold raw9603step2 raw9603step1; decide +kernel
      have hl : raw9603step1Labels = labelEmbedding6 ∘ raw9603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9603step1 raw9603step1Labels raw9603step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw9604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9604step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9604 raw9604Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw9604 raw9604Labels = mixedMoment B raw9604step0 raw9604step0Labels := by
      have ha : raw9604step0 = (fun i j => raw9604 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9604step0 raw9604; decide +kernel
      have hl : raw9604step0Labels = raw9604Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9604 raw9604Labels permutation202 permutation3
    mixedMoment B raw9604step0 raw9604step0Labels = mixedMoment B raw9604step1 raw9604step1Labels := by
      have ha : raw9604step1 = raw9604step0 := by apply Matrix.ext; unfold raw9604step1 raw9604step0; decide +kernel
      have hl : raw9604step0Labels = labelEmbedding6 ∘ raw9604step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9604step0 raw9604step0Labels raw9604step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw9605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9605 raw9605Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw9605 raw9605Labels = mixedMoment B raw9605step0 raw9605step0Labels := by
      have hz : ∀ j, raw9605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9605step0 = (fun i j => raw9605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9605step0 raw9605; decide +kernel
      have hl : raw9605step0Labels = raw9605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9605 raw9605Labels permutation434 hz
    mixedMoment B raw9605step0 raw9605step0Labels = mixedMoment B raw9605step1 raw9605step1Labels := by
      have ha : raw9605step1 = (fun i j => raw9605step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9605step1 raw9605step0; decide +kernel
      have hl : raw9605step1Labels = raw9605step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9605step0 raw9605step0Labels permutation44 permutation3
    mixedMoment B raw9605step1 raw9605step1Labels = mixedMoment B raw9605step2 raw9605step2Labels := by
      have ha : raw9605step2 = raw9605step1 := by apply Matrix.ext; unfold raw9605step2 raw9605step1; decide +kernel
      have hl : raw9605step1Labels = labelEmbedding6 ∘ raw9605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9605step1 raw9605step1Labels raw9605step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw9606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9606step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9606 raw9606Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw9606 raw9606Labels = mixedMoment B raw9606step0 raw9606step0Labels := by
      have hz : ∀ j, raw9606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9606step0 = (fun i j => raw9606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9606step0 raw9606; decide +kernel
      have hl : raw9606step0Labels = raw9606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9606 raw9606Labels permutation434 hz
    mixedMoment B raw9606step0 raw9606step0Labels = mixedMoment B raw9606step1 raw9606step1Labels := by
      have ha : raw9606step1 = (fun i j => raw9606step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9606step1 raw9606step0; decide +kernel
      have hl : raw9606step1Labels = raw9606step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9606step0 raw9606step0Labels permutation34 permutation3
    mixedMoment B raw9606step1 raw9606step1Labels = mixedMoment B raw9606step2 raw9606step2Labels := by
      have ha : raw9606step2 = raw9606step1 := by apply Matrix.ext; unfold raw9606step2 raw9606step1; decide +kernel
      have hl : raw9606step1Labels = labelEmbedding6 ∘ raw9606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9606step1 raw9606step1Labels raw9606step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw9607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9607step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9607step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9607 raw9607Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw9607 raw9607Labels = mixedMoment B raw9607step0 raw9607step0Labels := by
      have hz : ∀ j, raw9607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9607step0 = (fun i j => raw9607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9607step0 raw9607; decide +kernel
      have hl : raw9607step0Labels = raw9607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9607 raw9607Labels permutation346 hz
    mixedMoment B raw9607step0 raw9607step0Labels = mixedMoment B raw9607step1 raw9607step1Labels := by
      have ha : raw9607step1 = (fun i j => raw9607step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9607step1 raw9607step0; decide +kernel
      have hl : raw9607step1Labels = raw9607step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9607step0 raw9607step0Labels permutation34 permutation3
    mixedMoment B raw9607step1 raw9607step1Labels = mixedMoment B raw9607step2 raw9607step2Labels := by
      have ha : raw9607step2 = raw9607step1 := by apply Matrix.ext; unfold raw9607step2 raw9607step1; decide +kernel
      have hl : raw9607step1Labels = labelEmbedding6 ∘ raw9607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9607step1 raw9607step1Labels raw9607step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw9608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9608 raw9608Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw9608 raw9608Labels = mixedMoment B raw9608step0 raw9608step0Labels := by
      have hz : ∀ j, raw9608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9608step0 = (fun i j => raw9608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9608step0 raw9608; decide +kernel
      have hl : raw9608step0Labels = raw9608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9608 raw9608Labels permutation346 hz
    mixedMoment B raw9608step0 raw9608step0Labels = mixedMoment B raw9608step1 raw9608step1Labels := by
      have ha : raw9608step1 = (fun i j => raw9608step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9608step1 raw9608step0; decide +kernel
      have hl : raw9608step1Labels = raw9608step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9608step0 raw9608step0Labels permutation34 permutation3
    mixedMoment B raw9608step1 raw9608step1Labels = mixedMoment B raw9608step2 raw9608step2Labels := by
      have ha : raw9608step2 = raw9608step1 := by apply Matrix.ext; unfold raw9608step2 raw9608step1; decide +kernel
      have hl : raw9608step1Labels = labelEmbedding6 ∘ raw9608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9608step1 raw9608step1Labels raw9608step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw9609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9609step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9609 raw9609Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw9609 raw9609Labels = mixedMoment B raw9609step0 raw9609step0Labels := by
      have ha : raw9609step0 = (fun i j => raw9609 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9609step0 raw9609; decide +kernel
      have hl : raw9609step0Labels = raw9609Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9609 raw9609Labels permutation178 permutation3
    mixedMoment B raw9609step0 raw9609step0Labels = mixedMoment B raw9609step1 raw9609step1Labels := by
      have ha : raw9609step1 = raw9609step0 := by apply Matrix.ext; unfold raw9609step1 raw9609step0; decide +kernel
      have hl : raw9609step0Labels = labelEmbedding6 ∘ raw9609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9609step0 raw9609step0Labels raw9609step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw9610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9610step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9610 raw9610Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw9610 raw9610Labels = mixedMoment B raw9610step0 raw9610step0Labels := by
      have hz : ∀ j, raw9610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9610step0 = (fun i j => raw9610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9610step0 raw9610; decide +kernel
      have hl : raw9610step0Labels = raw9610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9610 raw9610Labels permutation346 hz
    mixedMoment B raw9610step0 raw9610step0Labels = mixedMoment B raw9610step1 raw9610step1Labels := by
      have ha : raw9610step1 = (fun i j => raw9610step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9610step1 raw9610step0; decide +kernel
      have hl : raw9610step1Labels = raw9610step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9610step0 raw9610step0Labels permutation44 permutation3
    mixedMoment B raw9610step1 raw9610step1Labels = mixedMoment B raw9610step2 raw9610step2Labels := by
      have ha : raw9610step2 = raw9610step1 := by apply Matrix.ext; unfold raw9610step2 raw9610step1; decide +kernel
      have hl : raw9610step1Labels = labelEmbedding6 ∘ raw9610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9610step1 raw9610step1Labels raw9610step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw9611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9611 raw9611Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw9611 raw9611Labels = mixedMoment B raw9611step0 raw9611step0Labels := by
      have hz : ∀ j, raw9611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9611step0 = (fun i j => raw9611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9611step0 raw9611; decide +kernel
      have hl : raw9611step0Labels = raw9611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9611 raw9611Labels permutation346 hz
    mixedMoment B raw9611step0 raw9611step0Labels = mixedMoment B raw9611step1 raw9611step1Labels := by
      have ha : raw9611step1 = (fun i j => raw9611step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9611step1 raw9611step0; decide +kernel
      have hl : raw9611step1Labels = raw9611step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9611step0 raw9611step0Labels permutation34 permutation3
    mixedMoment B raw9611step1 raw9611step1Labels = mixedMoment B raw9611step2 raw9611step2Labels := by
      have ha : raw9611step2 = raw9611step1 := by apply Matrix.ext; unfold raw9611step2 raw9611step1; decide +kernel
      have hl : raw9611step1Labels = labelEmbedding6 ∘ raw9611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9611step1 raw9611step1Labels raw9611step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw9612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw9612step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9612step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9612step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9612 raw9612Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw9612 raw9612Labels = mixedMoment B raw9612step0 raw9612step0Labels := by
      have hz : ∀ j, raw9612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9612step0 = (fun i j => raw9612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9612step0 raw9612; decide +kernel
      have hl : raw9612step0Labels = raw9612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9612 raw9612Labels permutation434 hz
    mixedMoment B raw9612step0 raw9612step0Labels = mixedMoment B raw9612step1 raw9612step1Labels := by
      have hz : ∀ j, raw9612step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9612step1 = (fun i j => raw9612step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9612step1 raw9612step0; decide +kernel
      have hl : raw9612step1Labels = raw9612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9612step0 raw9612step0Labels permutation80 hz
    mixedMoment B raw9612step1 raw9612step1Labels = mixedMoment B raw9612step2 raw9612step2Labels := by
      have ha : raw9612step2 = (fun i j => raw9612step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9612step2 raw9612step1; decide +kernel
      have hl : raw9612step2Labels = raw9612step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9612step1 raw9612step1Labels permutation8 permutation3
    mixedMoment B raw9612step2 raw9612step2Labels = mixedMoment B raw9612step3 raw9612step3Labels := by
      have ha : raw9612step3 = raw9612step2 := by apply Matrix.ext; unfold raw9612step3 raw9612step2; decide +kernel
      have hl : raw9612step2Labels = labelEmbedding6 ∘ raw9612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9612step2 raw9612step2Labels raw9612step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw9613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw9613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw9613step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw9613step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9613 raw9613Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw9613 raw9613Labels = mixedMoment B raw9613step0 raw9613step0Labels := by
      have hz : ∀ j, raw9613 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9613step0 = (fun i j => raw9613 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9613step0 raw9613; decide +kernel
      have hl : raw9613step0Labels = raw9613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9613 raw9613Labels permutation434 hz
    mixedMoment B raw9613step0 raw9613step0Labels = mixedMoment B raw9613step1 raw9613step1Labels := by
      have hz : ∀ j, raw9613step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9613step1 = (fun i j => raw9613step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9613step1 raw9613step0; decide +kernel
      have hl : raw9613step1Labels = raw9613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9613step0 raw9613step0Labels permutation80 hz
    mixedMoment B raw9613step1 raw9613step1Labels = mixedMoment B raw9613step2 raw9613step2Labels := by
      have ha : raw9613step2 = (fun i j => raw9613step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9613step2 raw9613step1; decide +kernel
      have hl : raw9613step2Labels = raw9613step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9613step1 raw9613step1Labels permutation8 permutation3
    mixedMoment B raw9613step2 raw9613step2Labels = mixedMoment B raw9613step3 raw9613step3Labels := by
      have ha : raw9613step3 = raw9613step2 := by apply Matrix.ext; unfold raw9613step3 raw9613step2; decide +kernel
      have hl : raw9613step2Labels = labelEmbedding6 ∘ raw9613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9613step2 raw9613step2Labels raw9613step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw9614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9614 raw9614Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw9614 raw9614Labels = mixedMoment B raw9614step0 raw9614step0Labels := by
      have hz : ∀ j, raw9614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9614step0 = (fun i j => raw9614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9614step0 raw9614; decide +kernel
      have hl : raw9614step0Labels = raw9614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9614 raw9614Labels permutation434 hz
    mixedMoment B raw9614step0 raw9614step0Labels = mixedMoment B raw9614step1 raw9614step1Labels := by
      have ha : raw9614step1 = (fun i j => raw9614step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9614step1 raw9614step0; decide +kernel
      have hl : raw9614step1Labels = raw9614step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9614step0 raw9614step0Labels permutation38 permutation3
    mixedMoment B raw9614step1 raw9614step1Labels = mixedMoment B raw9614step2 raw9614step2Labels := by
      have ha : raw9614step2 = raw9614step1 := by apply Matrix.ext; unfold raw9614step2 raw9614step1; decide +kernel
      have hl : raw9614step1Labels = labelEmbedding6 ∘ raw9614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9614step1 raw9614step1Labels raw9614step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw9615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9615step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9615 raw9615Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw9615 raw9615Labels = mixedMoment B raw9615step0 raw9615step0Labels := by
      have hz : ∀ j, raw9615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9615step0 = (fun i j => raw9615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9615step0 raw9615; decide +kernel
      have hl : raw9615step0Labels = raw9615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9615 raw9615Labels permutation346 hz
    mixedMoment B raw9615step0 raw9615step0Labels = mixedMoment B raw9615step1 raw9615step1Labels := by
      have ha : raw9615step1 = (fun i j => raw9615step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9615step1 raw9615step0; decide +kernel
      have hl : raw9615step1Labels = raw9615step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9615step0 raw9615step0Labels permutation38 permutation3
    mixedMoment B raw9615step1 raw9615step1Labels = mixedMoment B raw9615step2 raw9615step2Labels := by
      have ha : raw9615step2 = raw9615step1 := by apply Matrix.ext; unfold raw9615step2 raw9615step1; decide +kernel
      have hl : raw9615step1Labels = labelEmbedding6 ∘ raw9615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9615step1 raw9615step1Labels raw9615step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw9616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw9616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw9616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw9616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9616step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9616step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9616step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9616 raw9616Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw9616 raw9616Labels = mixedMoment B raw9616step0 raw9616step0Labels := by
      have hz : ∀ j, raw9616 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9616step0 = (fun i j => raw9616 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9616step0 raw9616; decide +kernel
      have hl : raw9616step0Labels = raw9616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9616 raw9616Labels permutation434 hz
    mixedMoment B raw9616step0 raw9616step0Labels = mixedMoment B raw9616step1 raw9616step1Labels := by
      have hz : ∀ j, raw9616step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9616step1 = (fun i j => raw9616step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9616step1 raw9616step0; decide +kernel
      have hl : raw9616step1Labels = raw9616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9616step0 raw9616step0Labels permutation80 hz
    mixedMoment B raw9616step1 raw9616step1Labels = mixedMoment B raw9616step2 raw9616step2Labels := by
      have ha : raw9616step2 = (fun i j => raw9616step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9616step2 raw9616step1; decide +kernel
      have hl : raw9616step2Labels = raw9616step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9616step1 raw9616step1Labels permutation9 permutation3
    mixedMoment B raw9616step2 raw9616step2Labels = mixedMoment B raw9616step3 raw9616step3Labels := by
      have ha : raw9616step3 = raw9616step2 := by apply Matrix.ext; unfold raw9616step3 raw9616step2; decide +kernel
      have hl : raw9616step2Labels = labelEmbedding6 ∘ raw9616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9616step2 raw9616step2Labels raw9616step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw9617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw9617step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw9617step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9617 raw9617Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw9617 raw9617Labels = mixedMoment B raw9617step0 raw9617step0Labels := by
      have hz : ∀ j, raw9617 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9617step0 = (fun i j => raw9617 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9617step0 raw9617; decide +kernel
      have hl : raw9617step0Labels = raw9617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9617 raw9617Labels permutation434 hz
    mixedMoment B raw9617step0 raw9617step0Labels = mixedMoment B raw9617step1 raw9617step1Labels := by
      have hz : ∀ j, raw9617step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9617step1 = (fun i j => raw9617step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9617step1 raw9617step0; decide +kernel
      have hl : raw9617step1Labels = raw9617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9617step0 raw9617step0Labels permutation80 hz
    mixedMoment B raw9617step1 raw9617step1Labels = mixedMoment B raw9617step2 raw9617step2Labels := by
      have ha : raw9617step2 = (fun i j => raw9617step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9617step2 raw9617step1; decide +kernel
      have hl : raw9617step2Labels = raw9617step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9617step1 raw9617step1Labels permutation8 permutation3
    mixedMoment B raw9617step2 raw9617step2Labels = mixedMoment B raw9617step3 raw9617step3Labels := by
      have ha : raw9617step3 = raw9617step2 := by apply Matrix.ext; unfold raw9617step3 raw9617step2; decide +kernel
      have hl : raw9617step2Labels = labelEmbedding6 ∘ raw9617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9617step2 raw9617step2Labels raw9617step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

def raw9618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9618step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9618step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9618step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9618step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9618 raw9618Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw9618 raw9618Labels = mixedMoment B raw9618step0 raw9618step0Labels := by
      have hz : ∀ j, raw9618 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9618step0 = (fun i j => raw9618 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9618step0 raw9618; decide +kernel
      have hl : raw9618step0Labels = raw9618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9618 raw9618Labels permutation434 hz
    mixedMoment B raw9618step0 raw9618step0Labels = mixedMoment B raw9618step1 raw9618step1Labels := by
      have hz : ∀ j, raw9618step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9618step1 = (fun i j => raw9618step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9618step1 raw9618step0; decide +kernel
      have hl : raw9618step1Labels = raw9618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9618step0 raw9618step0Labels permutation80 hz
    mixedMoment B raw9618step1 raw9618step1Labels = mixedMoment B raw9618step2 raw9618step2Labels := by
      have ha : raw9618step2 = (fun i j => raw9618step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9618step2 raw9618step1; decide +kernel
      have hl : raw9618step2Labels = raw9618step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9618step1 raw9618step1Labels permutation31 permutation3
    mixedMoment B raw9618step2 raw9618step2Labels = mixedMoment B raw9618step3 raw9618step3Labels := by
      have ha : raw9618step3 = -raw9618step2 := by apply Matrix.ext; change ∀ i j, raw9618step3 i j = -(raw9618step2 i j); unfold raw9618step3 raw9618step2; decide +kernel
      have hl : raw9618step3Labels = raw9618step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9618step3 raw9618step3Labels = mixedMoment B raw9618step4 raw9618step4Labels := by
      have ha : raw9618step4 = raw9618step3 := by apply Matrix.ext; unfold raw9618step4 raw9618step3; decide +kernel
      have hl : raw9618step3Labels = labelEmbedding6 ∘ raw9618step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9618step3 raw9618step3Labels raw9618step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw9619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9619step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9619 raw9619Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw9619 raw9619Labels = mixedMoment B raw9619step0 raw9619step0Labels := by
      have hz : ∀ j, raw9619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9619step0 = (fun i j => raw9619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9619step0 raw9619; decide +kernel
      have hl : raw9619step0Labels = raw9619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9619 raw9619Labels permutation434 hz
    mixedMoment B raw9619step0 raw9619step0Labels = mixedMoment B raw9619step1 raw9619step1Labels := by
      have ha : raw9619step1 = (fun i j => raw9619step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9619step1 raw9619step0; decide +kernel
      have hl : raw9619step1Labels = raw9619step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9619step0 raw9619step0Labels permutation139 permutation5
    mixedMoment B raw9619step1 raw9619step1Labels = mixedMoment B raw9619step2 raw9619step2Labels := by
      have ha : raw9619step2 = raw9619step1 := by apply Matrix.ext; unfold raw9619step2 raw9619step1; decide +kernel
      have hl : raw9619step1Labels = labelEmbedding8 ∘ raw9619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9619step1 raw9619step1Labels raw9619step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw9620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9620step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9620 raw9620Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw9620 raw9620Labels = mixedMoment B raw9620step0 raw9620step0Labels := by
      have hz : ∀ j, raw9620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9620step0 = (fun i j => raw9620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9620step0 raw9620; decide +kernel
      have hl : raw9620step0Labels = raw9620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9620 raw9620Labels permutation346 hz
    mixedMoment B raw9620step0 raw9620step0Labels = mixedMoment B raw9620step1 raw9620step1Labels := by
      have ha : raw9620step1 = (fun i j => raw9620step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9620step1 raw9620step0; decide +kernel
      have hl : raw9620step1Labels = raw9620step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9620step0 raw9620step0Labels permutation139 permutation5
    mixedMoment B raw9620step1 raw9620step1Labels = mixedMoment B raw9620step2 raw9620step2Labels := by
      have ha : raw9620step2 = raw9620step1 := by apply Matrix.ext; unfold raw9620step2 raw9620step1; decide +kernel
      have hl : raw9620step1Labels = labelEmbedding8 ∘ raw9620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9620step1 raw9620step1Labels raw9620step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw9621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw9621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw9621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw9621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw9621step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9621step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw9621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9621 raw9621Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw9621 raw9621Labels = mixedMoment B raw9621step0 raw9621step0Labels := by
      have hz : ∀ j, raw9621 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9621step0 = (fun i j => raw9621 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9621step0 raw9621; decide +kernel
      have hl : raw9621step0Labels = raw9621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9621 raw9621Labels permutation434 hz
    mixedMoment B raw9621step0 raw9621step0Labels = mixedMoment B raw9621step1 raw9621step1Labels := by
      have hz : ∀ j, raw9621step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9621step1 = (fun i j => raw9621step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9621step1 raw9621step0; decide +kernel
      have hl : raw9621step1Labels = raw9621step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9621step0 raw9621step0Labels permutation80 hz
    mixedMoment B raw9621step1 raw9621step1Labels = mixedMoment B raw9621step2 raw9621step2Labels := by
      have ha : raw9621step2 = (fun i j => raw9621step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9621step2 raw9621step1; decide +kernel
      have hl : raw9621step2Labels = raw9621step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9621step1 raw9621step1Labels permutation29 permutation5
    mixedMoment B raw9621step2 raw9621step2Labels = mixedMoment B raw9621step3 raw9621step3Labels := by
      have ha : raw9621step3 = raw9621step2 := by apply Matrix.ext; unfold raw9621step3 raw9621step2; decide +kernel
      have hl : raw9621step2Labels = labelEmbedding8 ∘ raw9621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9621step2 raw9621step2Labels raw9621step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw9622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9622step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9622step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9622 raw9622Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw9622 raw9622Labels = mixedMoment B raw9622step0 raw9622step0Labels := by
      have hz : ∀ j, raw9622 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9622step0 = (fun i j => raw9622 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9622step0 raw9622; decide +kernel
      have hl : raw9622step0Labels = raw9622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9622 raw9622Labels permutation434 hz
    mixedMoment B raw9622step0 raw9622step0Labels = mixedMoment B raw9622step1 raw9622step1Labels := by
      have hz : ∀ j, raw9622step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9622step1 = (fun i j => raw9622step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9622step1 raw9622step0; decide +kernel
      have hl : raw9622step1Labels = raw9622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9622step0 raw9622step0Labels permutation80 hz
    mixedMoment B raw9622step1 raw9622step1Labels = mixedMoment B raw9622step2 raw9622step2Labels := by
      have ha : raw9622step2 = (fun i j => raw9622step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9622step2 raw9622step1; decide +kernel
      have hl : raw9622step2Labels = raw9622step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9622step1 raw9622step1Labels permutation31 permutation3
    mixedMoment B raw9622step2 raw9622step2Labels = mixedMoment B raw9622step3 raw9622step3Labels := by
      have ha : raw9622step3 = -raw9622step2 := by apply Matrix.ext; change ∀ i j, raw9622step3 i j = -(raw9622step2 i j); unfold raw9622step3 raw9622step2; decide +kernel
      have hl : raw9622step3Labels = raw9622step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw9623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9623 raw9623Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw9623 raw9623Labels = mixedMoment B raw9623step0 raw9623step0Labels := by
      have hz : ∀ j, raw9623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9623step0 = (fun i j => raw9623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9623step0 raw9623; decide +kernel
      have hl : raw9623step0Labels = raw9623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9623 raw9623Labels permutation434 hz
    mixedMoment B raw9623step0 raw9623step0Labels = mixedMoment B raw9623step1 raw9623step1Labels := by
      have ha : raw9623step1 = (fun i j => raw9623step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9623step1 raw9623step0; decide +kernel
      have hl : raw9623step1Labels = raw9623step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9623step0 raw9623step0Labels permutation149 permutation3
    mixedMoment B raw9623step1 raw9623step1Labels = mixedMoment B raw9623step2 raw9623step2Labels := by
      have ha : raw9623step2 = -raw9623step1 := by apply Matrix.ext; change ∀ i j, raw9623step2 i j = -(raw9623step1 i j); unfold raw9623step2 raw9623step1; decide +kernel
      have hl : raw9623step2Labels = raw9623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw9624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9624 raw9624Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw9624 raw9624Labels = mixedMoment B raw9624step0 raw9624step0Labels := by
      have hz : ∀ j, raw9624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9624step0 = (fun i j => raw9624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9624step0 raw9624; decide +kernel
      have hl : raw9624step0Labels = raw9624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9624 raw9624Labels permutation346 hz
    mixedMoment B raw9624step0 raw9624step0Labels = mixedMoment B raw9624step1 raw9624step1Labels := by
      have ha : raw9624step1 = (fun i j => raw9624step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9624step1 raw9624step0; decide +kernel
      have hl : raw9624step1Labels = raw9624step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9624step0 raw9624step0Labels permutation149 permutation3
    mixedMoment B raw9624step1 raw9624step1Labels = mixedMoment B raw9624step2 raw9624step2Labels := by
      have ha : raw9624step2 = -raw9624step1 := by apply Matrix.ext; change ∀ i j, raw9624step2 i j = -(raw9624step1 i j); unfold raw9624step2 raw9624step1; decide +kernel
      have hl : raw9624step2Labels = raw9624step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw9625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw9625step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw9625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9625step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9625step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9625 raw9625Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw9625 raw9625Labels = mixedMoment B raw9625step0 raw9625step0Labels := by
      have hz : ∀ j, raw9625 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9625step0 = (fun i j => raw9625 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9625step0 raw9625; decide +kernel
      have hl : raw9625step0Labels = raw9625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9625 raw9625Labels permutation434 hz
    mixedMoment B raw9625step0 raw9625step0Labels = mixedMoment B raw9625step1 raw9625step1Labels := by
      have hz : ∀ j, raw9625step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9625step1 = (fun i j => raw9625step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9625step1 raw9625step0; decide +kernel
      have hl : raw9625step1Labels = raw9625step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9625step0 raw9625step0Labels permutation80 hz
    mixedMoment B raw9625step1 raw9625step1Labels = mixedMoment B raw9625step2 raw9625step2Labels := by
      have ha : raw9625step2 = (fun i j => raw9625step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9625step2 raw9625step1; decide +kernel
      have hl : raw9625step2Labels = raw9625step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9625step1 raw9625step1Labels permutation29 permutation3
    mixedMoment B raw9625step2 raw9625step2Labels = mixedMoment B raw9625step3 raw9625step3Labels := by
      have ha : raw9625step3 = -raw9625step2 := by apply Matrix.ext; change ∀ i j, raw9625step3 i j = -(raw9625step2 i j); unfold raw9625step3 raw9625step2; decide +kernel
      have hl : raw9625step3Labels = raw9625step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw9626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw9626step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw9626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9626 raw9626Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw9626 raw9626Labels = mixedMoment B raw9626step0 raw9626step0Labels := by
      have hz : ∀ j, raw9626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9626step0 = (fun i j => raw9626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9626step0 raw9626; decide +kernel
      have hl : raw9626step0Labels = raw9626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9626 raw9626Labels permutation434 hz
    mixedMoment B raw9626step0 raw9626step0Labels = mixedMoment B raw9626step1 raw9626step1Labels := by
      have hz : ∀ j, raw9626step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9626step1 = (fun i j => raw9626step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9626step1 raw9626step0; decide +kernel
      have hl : raw9626step1Labels = raw9626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9626step0 raw9626step0Labels permutation80 hz
    mixedMoment B raw9626step1 raw9626step1Labels = mixedMoment B raw9626step2 raw9626step2Labels := by
      have ha : raw9626step2 = (fun i j => raw9626step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9626step2 raw9626step1; decide +kernel
      have hl : raw9626step2Labels = raw9626step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9626step1 raw9626step1Labels permutation8 permutation3
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw9627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9627step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9627 raw9627Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw9627 raw9627Labels = mixedMoment B raw9627step0 raw9627step0Labels := by
      have hz : ∀ j, raw9627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9627step0 = (fun i j => raw9627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9627step0 raw9627; decide +kernel
      have hl : raw9627step0Labels = raw9627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9627 raw9627Labels permutation434 hz
    mixedMoment B raw9627step0 raw9627step0Labels = mixedMoment B raw9627step1 raw9627step1Labels := by
      have hz : ∀ j, raw9627step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9627step1 = (fun i j => raw9627step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9627step1 raw9627step0; decide +kernel
      have hl : raw9627step1Labels = raw9627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9627step0 raw9627step0Labels permutation80 hz
    mixedMoment B raw9627step1 raw9627step1Labels = mixedMoment B raw9627step2 raw9627step2Labels := by
      have ha : raw9627step2 = (fun i j => raw9627step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9627step2 raw9627step1; decide +kernel
      have hl : raw9627step2Labels = raw9627step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9627step1 raw9627step1Labels permutation10 permutation3
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw9628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9628step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9628 raw9628Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw9628 raw9628Labels = mixedMoment B raw9628step0 raw9628step0Labels := by
      have hz : ∀ j, raw9628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9628step0 = (fun i j => raw9628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9628step0 raw9628; decide +kernel
      have hl : raw9628step0Labels = raw9628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9628 raw9628Labels permutation434 hz
    mixedMoment B raw9628step0 raw9628step0Labels = mixedMoment B raw9628step1 raw9628step1Labels := by
      have ha : raw9628step1 = (fun i j => raw9628step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9628step1 raw9628step0; decide +kernel
      have hl : raw9628step1Labels = raw9628step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9628step0 raw9628step0Labels permutation40 permutation3
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw9629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9629 raw9629Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw9629 raw9629Labels = mixedMoment B raw9629step0 raw9629step0Labels := by
      have hz : ∀ j, raw9629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9629step0 = (fun i j => raw9629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9629step0 raw9629; decide +kernel
      have hl : raw9629step0Labels = raw9629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9629 raw9629Labels permutation346 hz
    mixedMoment B raw9629step0 raw9629step0Labels = mixedMoment B raw9629step1 raw9629step1Labels := by
      have ha : raw9629step1 = (fun i j => raw9629step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9629step1 raw9629step0; decide +kernel
      have hl : raw9629step1Labels = raw9629step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9629step0 raw9629step0Labels permutation40 permutation3
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw9630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![2, -2, 0]]
def raw9630step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw9630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9630 raw9630Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw9630 raw9630Labels = mixedMoment B raw9630step0 raw9630step0Labels := by
      have hz : ∀ j, raw9630 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9630step0 = (fun i j => raw9630 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9630step0 raw9630; decide +kernel
      have hl : raw9630step0Labels = raw9630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9630 raw9630Labels permutation434 hz
    mixedMoment B raw9630step0 raw9630step0Labels = mixedMoment B raw9630step1 raw9630step1Labels := by
      have hz : ∀ j, raw9630step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9630step1 = (fun i j => raw9630step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9630step1 raw9630step0; decide +kernel
      have hl : raw9630step1Labels = raw9630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9630step0 raw9630step0Labels permutation80 hz
    mixedMoment B raw9630step1 raw9630step1Labels = mixedMoment B raw9630step2 raw9630step2Labels := by
      have ha : raw9630step2 = (fun i j => raw9630step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9630step2 raw9630step1; decide +kernel
      have hl : raw9630step2Labels = raw9630step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9630step1 raw9630step1Labels permutation10 permutation3
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw9631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]
def raw9631step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9631 raw9631Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw9631 raw9631Labels = mixedMoment B raw9631step0 raw9631step0Labels := by
      have hz : ∀ j, raw9631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9631step0 = (fun i j => raw9631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9631step0 raw9631; decide +kernel
      have hl : raw9631step0Labels = raw9631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9631 raw9631Labels permutation434 hz
    mixedMoment B raw9631step0 raw9631step0Labels = mixedMoment B raw9631step1 raw9631step1Labels := by
      have hz : ∀ j, raw9631step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9631step1 = (fun i j => raw9631step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9631step1 raw9631step0; decide +kernel
      have hl : raw9631step1Labels = raw9631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9631step0 raw9631step0Labels permutation80 hz
    mixedMoment B raw9631step1 raw9631step1Labels = mixedMoment B raw9631step2 raw9631step2Labels := by
      have ha : raw9631step2 = (fun i j => raw9631step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9631step2 raw9631step1; decide +kernel
      have hl : raw9631step2Labels = raw9631step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9631step1 raw9631step1Labels permutation11 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw9632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9632 raw9632Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw9632 raw9632Labels = mixedMoment B raw9632step0 raw9632step0Labels := by
      have hz : ∀ j, raw9632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9632step0 = (fun i j => raw9632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9632step0 raw9632; decide +kernel
      have hl : raw9632step0Labels = raw9632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9632 raw9632Labels permutation434 hz
    mixedMoment B raw9632step0 raw9632step0Labels = mixedMoment B raw9632step1 raw9632step1Labels := by
      have ha : raw9632step1 = (fun i j => raw9632step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9632step1 raw9632step0; decide +kernel
      have hl : raw9632step1Labels = raw9632step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9632step0 raw9632step0Labels permutation34 permutation3
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw9633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9633 raw9633Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw9633 raw9633Labels = mixedMoment B raw9633step0 raw9633step0Labels := by
      have hz : ∀ j, raw9633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9633step0 = (fun i j => raw9633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9633step0 raw9633; decide +kernel
      have hl : raw9633step0Labels = raw9633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9633 raw9633Labels permutation434 hz
    mixedMoment B raw9633step0 raw9633step0Labels = mixedMoment B raw9633step1 raw9633step1Labels := by
      have ha : raw9633step1 = (fun i j => raw9633step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9633step1 raw9633step0; decide +kernel
      have hl : raw9633step1Labels = raw9633step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9633step0 raw9633step0Labels permutation34 permutation3
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw9634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9634 raw9634Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw9634 raw9634Labels = mixedMoment B raw9634step0 raw9634step0Labels := by
      have ha : raw9634step0 = (fun i j => raw9634 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9634step0 raw9634; decide +kernel
      have hl : raw9634step0Labels = raw9634Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9634 raw9634Labels permutation202 permutation3
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw9635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9635 raw9635Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw9635 raw9635Labels = mixedMoment B raw9635step0 raw9635step0Labels := by
      have hz : ∀ j, raw9635 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9635step0 = (fun i j => raw9635 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9635step0 raw9635; decide +kernel
      have hl : raw9635step0Labels = raw9635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9635 raw9635Labels permutation434 hz
    mixedMoment B raw9635step0 raw9635step0Labels = mixedMoment B raw9635step1 raw9635step1Labels := by
      have ha : raw9635step1 = (fun i j => raw9635step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9635step1 raw9635step0; decide +kernel
      have hl : raw9635step1Labels = raw9635step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9635step0 raw9635step0Labels permutation44 permutation3
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw9636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9636 raw9636Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw9636 raw9636Labels = mixedMoment B raw9636step0 raw9636step0Labels := by
      have hz : ∀ j, raw9636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9636step0 = (fun i j => raw9636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9636step0 raw9636; decide +kernel
      have hl : raw9636step0Labels = raw9636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9636 raw9636Labels permutation434 hz
    mixedMoment B raw9636step0 raw9636step0Labels = mixedMoment B raw9636step1 raw9636step1Labels := by
      have ha : raw9636step1 = (fun i j => raw9636step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9636step1 raw9636step0; decide +kernel
      have hl : raw9636step1Labels = raw9636step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9636step0 raw9636step0Labels permutation34 permutation3
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw9637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9637 raw9637Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw9637 raw9637Labels = mixedMoment B raw9637step0 raw9637step0Labels := by
      have hz : ∀ j, raw9637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9637step0 = (fun i j => raw9637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9637step0 raw9637; decide +kernel
      have hl : raw9637step0Labels = raw9637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9637 raw9637Labels permutation346 hz
    mixedMoment B raw9637step0 raw9637step0Labels = mixedMoment B raw9637step1 raw9637step1Labels := by
      have ha : raw9637step1 = (fun i j => raw9637step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9637step1 raw9637step0; decide +kernel
      have hl : raw9637step1Labels = raw9637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9637step0 raw9637step0Labels permutation34 permutation3
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw9638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9638 raw9638Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw9638 raw9638Labels = mixedMoment B raw9638step0 raw9638step0Labels := by
      have hz : ∀ j, raw9638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9638step0 = (fun i j => raw9638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9638step0 raw9638; decide +kernel
      have hl : raw9638step0Labels = raw9638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9638 raw9638Labels permutation346 hz
    mixedMoment B raw9638step0 raw9638step0Labels = mixedMoment B raw9638step1 raw9638step1Labels := by
      have ha : raw9638step1 = (fun i j => raw9638step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9638step1 raw9638step0; decide +kernel
      have hl : raw9638step1Labels = raw9638step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9638step0 raw9638step0Labels permutation34 permutation3
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw9639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9639 raw9639Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw9639 raw9639Labels = mixedMoment B raw9639step0 raw9639step0Labels := by
      have ha : raw9639step0 = (fun i j => raw9639 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9639step0 raw9639; decide +kernel
      have hl : raw9639step0Labels = raw9639Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9639 raw9639Labels permutation178 permutation3
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw9640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9640 raw9640Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw9640 raw9640Labels = mixedMoment B raw9640step0 raw9640step0Labels := by
      have hz : ∀ j, raw9640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9640step0 = (fun i j => raw9640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9640step0 raw9640; decide +kernel
      have hl : raw9640step0Labels = raw9640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9640 raw9640Labels permutation346 hz
    mixedMoment B raw9640step0 raw9640step0Labels = mixedMoment B raw9640step1 raw9640step1Labels := by
      have ha : raw9640step1 = (fun i j => raw9640step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9640step1 raw9640step0; decide +kernel
      have hl : raw9640step1Labels = raw9640step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9640step0 raw9640step0Labels permutation44 permutation3
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw9641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9641 raw9641Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw9641 raw9641Labels = mixedMoment B raw9641step0 raw9641step0Labels := by
      have hz : ∀ j, raw9641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9641step0 = (fun i j => raw9641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9641step0 raw9641; decide +kernel
      have hl : raw9641step0Labels = raw9641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9641 raw9641Labels permutation346 hz
    mixedMoment B raw9641step0 raw9641step0Labels = mixedMoment B raw9641step1 raw9641step1Labels := by
      have ha : raw9641step1 = (fun i j => raw9641step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9641step1 raw9641step0; decide +kernel
      have hl : raw9641step1Labels = raw9641step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9641step0 raw9641step0Labels permutation34 permutation3
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw9642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw9642step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9642 raw9642Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw9642 raw9642Labels = mixedMoment B raw9642step0 raw9642step0Labels := by
      have hz : ∀ j, raw9642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9642step0 = (fun i j => raw9642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9642step0 raw9642; decide +kernel
      have hl : raw9642step0Labels = raw9642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9642 raw9642Labels permutation434 hz
    mixedMoment B raw9642step0 raw9642step0Labels = mixedMoment B raw9642step1 raw9642step1Labels := by
      have hz : ∀ j, raw9642step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9642step1 = (fun i j => raw9642step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9642step1 raw9642step0; decide +kernel
      have hl : raw9642step1Labels = raw9642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9642step0 raw9642step0Labels permutation80 hz
    mixedMoment B raw9642step1 raw9642step1Labels = mixedMoment B raw9642step2 raw9642step2Labels := by
      have ha : raw9642step2 = (fun i j => raw9642step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9642step2 raw9642step1; decide +kernel
      have hl : raw9642step2Labels = raw9642step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9642step1 raw9642step1Labels permutation8 permutation3
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw9643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw9643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw9643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9643 raw9643Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw9643 raw9643Labels = mixedMoment B raw9643step0 raw9643step0Labels := by
      have hz : ∀ j, raw9643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9643step0 = (fun i j => raw9643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9643step0 raw9643; decide +kernel
      have hl : raw9643step0Labels = raw9643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9643 raw9643Labels permutation434 hz
    mixedMoment B raw9643step0 raw9643step0Labels = mixedMoment B raw9643step1 raw9643step1Labels := by
      have hz : ∀ j, raw9643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9643step1 = (fun i j => raw9643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9643step1 raw9643step0; decide +kernel
      have hl : raw9643step1Labels = raw9643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9643step0 raw9643step0Labels permutation80 hz
    mixedMoment B raw9643step1 raw9643step1Labels = mixedMoment B raw9643step2 raw9643step2Labels := by
      have ha : raw9643step2 = (fun i j => raw9643step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9643step2 raw9643step1; decide +kernel
      have hl : raw9643step2Labels = raw9643step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9643step1 raw9643step1Labels permutation8 permutation3
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw9644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9644 raw9644Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw9644 raw9644Labels = mixedMoment B raw9644step0 raw9644step0Labels := by
      have hz : ∀ j, raw9644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9644step0 = (fun i j => raw9644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9644step0 raw9644; decide +kernel
      have hl : raw9644step0Labels = raw9644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9644 raw9644Labels permutation434 hz
    mixedMoment B raw9644step0 raw9644step0Labels = mixedMoment B raw9644step1 raw9644step1Labels := by
      have ha : raw9644step1 = (fun i j => raw9644step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9644step1 raw9644step0; decide +kernel
      have hl : raw9644step1Labels = raw9644step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9644step0 raw9644step0Labels permutation38 permutation3
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw9645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9645 raw9645Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw9645 raw9645Labels = mixedMoment B raw9645step0 raw9645step0Labels := by
      have hz : ∀ j, raw9645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9645step0 = (fun i j => raw9645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9645step0 raw9645; decide +kernel
      have hl : raw9645step0Labels = raw9645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9645 raw9645Labels permutation346 hz
    mixedMoment B raw9645step0 raw9645step0Labels = mixedMoment B raw9645step1 raw9645step1Labels := by
      have ha : raw9645step1 = (fun i j => raw9645step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9645step1 raw9645step0; decide +kernel
      have hl : raw9645step1Labels = raw9645step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9645step0 raw9645step0Labels permutation38 permutation3
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw9646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw9646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw9646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw9646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9646 raw9646Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw9646 raw9646Labels = mixedMoment B raw9646step0 raw9646step0Labels := by
      have hz : ∀ j, raw9646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9646step0 = (fun i j => raw9646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9646step0 raw9646; decide +kernel
      have hl : raw9646step0Labels = raw9646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9646 raw9646Labels permutation434 hz
    mixedMoment B raw9646step0 raw9646step0Labels = mixedMoment B raw9646step1 raw9646step1Labels := by
      have hz : ∀ j, raw9646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9646step1 = (fun i j => raw9646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9646step1 raw9646step0; decide +kernel
      have hl : raw9646step1Labels = raw9646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9646step0 raw9646step0Labels permutation80 hz
    mixedMoment B raw9646step1 raw9646step1Labels = mixedMoment B raw9646step2 raw9646step2Labels := by
      have ha : raw9646step2 = (fun i j => raw9646step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9646step2 raw9646step1; decide +kernel
      have hl : raw9646step2Labels = raw9646step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9646step1 raw9646step1Labels permutation9 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw9647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9647step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw9647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9647 raw9647Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw9647 raw9647Labels = mixedMoment B raw9647step0 raw9647step0Labels := by
      have hz : ∀ j, raw9647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9647step0 = (fun i j => raw9647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9647step0 raw9647; decide +kernel
      have hl : raw9647step0Labels = raw9647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9647 raw9647Labels permutation434 hz
    mixedMoment B raw9647step0 raw9647step0Labels = mixedMoment B raw9647step1 raw9647step1Labels := by
      have hz : ∀ j, raw9647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9647step1 = (fun i j => raw9647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9647step1 raw9647step0; decide +kernel
      have hl : raw9647step1Labels = raw9647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9647step0 raw9647step0Labels permutation80 hz
    mixedMoment B raw9647step1 raw9647step1Labels = mixedMoment B raw9647step2 raw9647step2Labels := by
      have ha : raw9647step2 = (fun i j => raw9647step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9647step2 raw9647step1; decide +kernel
      have hl : raw9647step2Labels = raw9647step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9647step1 raw9647step1Labels permutation8 permutation3
    _ = mixedMoment B node1037 node1037Labels := by rfl

def raw9648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9648step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9648step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9648 raw9648Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw9648 raw9648Labels = mixedMoment B raw9648step0 raw9648step0Labels := by
      have hz : ∀ j, raw9648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9648step0 = (fun i j => raw9648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9648step0 raw9648; decide +kernel
      have hl : raw9648step0Labels = raw9648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9648 raw9648Labels permutation434 hz
    mixedMoment B raw9648step0 raw9648step0Labels = mixedMoment B raw9648step1 raw9648step1Labels := by
      have hz : ∀ j, raw9648step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9648step1 = (fun i j => raw9648step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9648step1 raw9648step0; decide +kernel
      have hl : raw9648step1Labels = raw9648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9648step0 raw9648step0Labels permutation80 hz
    mixedMoment B raw9648step1 raw9648step1Labels = mixedMoment B raw9648step2 raw9648step2Labels := by
      have ha : raw9648step2 = (fun i j => raw9648step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9648step2 raw9648step1; decide +kernel
      have hl : raw9648step2Labels = raw9648step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9648step1 raw9648step1Labels permutation31 permutation3
    mixedMoment B raw9648step2 raw9648step2Labels = mixedMoment B raw9648step3 raw9648step3Labels := by
      have ha : raw9648step3 = -raw9648step2 := by apply Matrix.ext; change ∀ i j, raw9648step3 i j = -(raw9648step2 i j); unfold raw9648step3 raw9648step2; decide +kernel
      have hl : raw9648step3Labels = raw9648step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw9649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw9649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9649 raw9649Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw9649 raw9649Labels = mixedMoment B raw9649step0 raw9649step0Labels := by
      have hz : ∀ j, raw9649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9649step0 = (fun i j => raw9649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9649step0 raw9649; decide +kernel
      have hl : raw9649step0Labels = raw9649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9649 raw9649Labels permutation434 hz
    mixedMoment B raw9649step0 raw9649step0Labels = mixedMoment B raw9649step1 raw9649step1Labels := by
      have ha : raw9649step1 = (fun i j => raw9649step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9649step1 raw9649step0; decide +kernel
      have hl : raw9649step1Labels = raw9649step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9649step0 raw9649step0Labels permutation149 permutation3
    mixedMoment B raw9649step1 raw9649step1Labels = mixedMoment B raw9649step2 raw9649step2Labels := by
      have ha : raw9649step2 = -raw9649step1 := by apply Matrix.ext; change ∀ i j, raw9649step2 i j = -(raw9649step1 i j); unfold raw9649step2 raw9649step1; decide +kernel
      have hl : raw9649step2Labels = raw9649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw9650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw9650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9650 raw9650Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw9650 raw9650Labels = mixedMoment B raw9650step0 raw9650step0Labels := by
      have hz : ∀ j, raw9650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9650step0 = (fun i j => raw9650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9650step0 raw9650; decide +kernel
      have hl : raw9650step0Labels = raw9650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9650 raw9650Labels permutation346 hz
    mixedMoment B raw9650step0 raw9650step0Labels = mixedMoment B raw9650step1 raw9650step1Labels := by
      have ha : raw9650step1 = (fun i j => raw9650step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9650step1 raw9650step0; decide +kernel
      have hl : raw9650step1Labels = raw9650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9650step0 raw9650step0Labels permutation149 permutation3
    mixedMoment B raw9650step1 raw9650step1Labels = mixedMoment B raw9650step2 raw9650step2Labels := by
      have ha : raw9650step2 = -raw9650step1 := by apply Matrix.ext; change ∀ i j, raw9650step2 i j = -(raw9650step1 i j); unfold raw9650step2 raw9650step1; decide +kernel
      have hl : raw9650step2Labels = raw9650step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw9651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw9651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw9651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw9651step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw9651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw9651step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9651 raw9651Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw9651 raw9651Labels = mixedMoment B raw9651step0 raw9651step0Labels := by
      have hz : ∀ j, raw9651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9651step0 = (fun i j => raw9651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9651step0 raw9651; decide +kernel
      have hl : raw9651step0Labels = raw9651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9651 raw9651Labels permutation434 hz
    mixedMoment B raw9651step0 raw9651step0Labels = mixedMoment B raw9651step1 raw9651step1Labels := by
      have hz : ∀ j, raw9651step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9651step1 = (fun i j => raw9651step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9651step1 raw9651step0; decide +kernel
      have hl : raw9651step1Labels = raw9651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9651step0 raw9651step0Labels permutation80 hz
    mixedMoment B raw9651step1 raw9651step1Labels = mixedMoment B raw9651step2 raw9651step2Labels := by
      have ha : raw9651step2 = (fun i j => raw9651step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9651step2 raw9651step1; decide +kernel
      have hl : raw9651step2Labels = raw9651step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9651step1 raw9651step1Labels permutation29 permutation3
    mixedMoment B raw9651step2 raw9651step2Labels = mixedMoment B raw9651step3 raw9651step3Labels := by
      have ha : raw9651step3 = -raw9651step2 := by apply Matrix.ext; change ∀ i j, raw9651step3 i j = -(raw9651step2 i j); unfold raw9651step3 raw9651step2; decide +kernel
      have hl : raw9651step3Labels = raw9651step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw9652 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9652step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![0, -2, 2]]
def raw9652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9652step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw9652step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9652step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw9652step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9652 raw9652Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw9652 raw9652Labels = mixedMoment B raw9652step0 raw9652step0Labels := by
      have hz : ∀ j, raw9652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9652step0 = (fun i j => raw9652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9652step0 raw9652; decide +kernel
      have hl : raw9652step0Labels = raw9652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9652 raw9652Labels permutation434 hz
    mixedMoment B raw9652step0 raw9652step0Labels = mixedMoment B raw9652step1 raw9652step1Labels := by
      have hz : ∀ j, raw9652step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9652step1 = (fun i j => raw9652step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9652step1 raw9652step0; decide +kernel
      have hl : raw9652step1Labels = raw9652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9652step0 raw9652step0Labels permutation80 hz
    mixedMoment B raw9652step1 raw9652step1Labels = mixedMoment B raw9652step2 raw9652step2Labels := by
      have hz : ∀ j, raw9652step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw9652step2 = (fun i j => raw9652step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw9652step2 raw9652step1; decide +kernel
      have hl : raw9652step2Labels = raw9652step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9652step1 raw9652step1Labels permutation14 hz
    mixedMoment B raw9652step2 raw9652step2Labels = mixedMoment B raw9652step3 raw9652step3Labels := by
      have ha : raw9652step3 = (fun i j => raw9652step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9652step3 raw9652step2; decide +kernel
      have hl : raw9652step3Labels = raw9652step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9652step2 raw9652step2Labels permutation2 permutation7
    mixedMoment B raw9652step3 raw9652step3Labels = mixedMoment B raw9652step4 raw9652step4Labels := by
      have ha : raw9652step4 = raw9652step3 := by apply Matrix.ext; unfold raw9652step4 raw9652step3; decide +kernel
      have hl : raw9652step3Labels = labelEmbedding10 ∘ raw9652step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9652step3 raw9652step3Labels raw9652step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw9653 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9653step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9653 raw9653Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw9653 raw9653Labels = mixedMoment B raw9653step0 raw9653step0Labels := by
      have hz : ∀ j, raw9653 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9653step0 = (fun i j => raw9653 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9653step0 raw9653; decide +kernel
      have hl : raw9653step0Labels = raw9653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9653 raw9653Labels permutation434 hz
    mixedMoment B raw9653step0 raw9653step0Labels = mixedMoment B raw9653step1 raw9653step1Labels := by
      have ha : raw9653step1 = (fun i j => raw9653step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9653step1 raw9653step0; decide +kernel
      have hl : raw9653step1Labels = raw9653step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9653step0 raw9653step0Labels permutation32 permutation7
    mixedMoment B raw9653step1 raw9653step1Labels = mixedMoment B raw9653step2 raw9653step2Labels := by
      have ha : raw9653step2 = raw9653step1 := by apply Matrix.ext; unfold raw9653step2 raw9653step1; decide +kernel
      have hl : raw9653step1Labels = labelEmbedding10 ∘ raw9653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9653step1 raw9653step1Labels raw9653step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw9654 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9654step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9654step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9654 raw9654Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw9654 raw9654Labels = mixedMoment B raw9654step0 raw9654step0Labels := by
      have hz : ∀ j, raw9654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9654step0 = (fun i j => raw9654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9654step0 raw9654; decide +kernel
      have hl : raw9654step0Labels = raw9654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9654 raw9654Labels permutation346 hz
    mixedMoment B raw9654step0 raw9654step0Labels = mixedMoment B raw9654step1 raw9654step1Labels := by
      have ha : raw9654step1 = (fun i j => raw9654step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9654step1 raw9654step0; decide +kernel
      have hl : raw9654step1Labels = raw9654step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9654step0 raw9654step0Labels permutation32 permutation7
    mixedMoment B raw9654step1 raw9654step1Labels = mixedMoment B raw9654step2 raw9654step2Labels := by
      have ha : raw9654step2 = raw9654step1 := by apply Matrix.ext; unfold raw9654step2 raw9654step1; decide +kernel
      have hl : raw9654step1Labels = labelEmbedding10 ∘ raw9654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9654step1 raw9654step1Labels raw9654step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw9655 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9655step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9655step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9655step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9655 raw9655Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw9655 raw9655Labels = mixedMoment B raw9655step0 raw9655step0Labels := by
      have hz : ∀ j, raw9655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9655step0 = (fun i j => raw9655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9655step0 raw9655; decide +kernel
      have hl : raw9655step0Labels = raw9655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9655 raw9655Labels permutation434 hz
    mixedMoment B raw9655step0 raw9655step0Labels = mixedMoment B raw9655step1 raw9655step1Labels := by
      have hz : ∀ j, raw9655step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9655step1 = (fun i j => raw9655step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9655step1 raw9655step0; decide +kernel
      have hl : raw9655step1Labels = raw9655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9655step0 raw9655step0Labels permutation80 hz
    mixedMoment B raw9655step1 raw9655step1Labels = mixedMoment B raw9655step2 raw9655step2Labels := by
      have ha : raw9655step2 = (fun i j => raw9655step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9655step2 raw9655step1; decide +kernel
      have hl : raw9655step2Labels = raw9655step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9655step1 raw9655step1Labels permutation8 permutation7
    mixedMoment B raw9655step2 raw9655step2Labels = mixedMoment B raw9655step3 raw9655step3Labels := by
      have ha : raw9655step3 = raw9655step2 := by apply Matrix.ext; unfold raw9655step3 raw9655step2; decide +kernel
      have hl : raw9655step2Labels = labelEmbedding10 ∘ raw9655step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9655step2 raw9655step2Labels raw9655step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw9656 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9656step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9656 raw9656Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw9656 raw9656Labels = mixedMoment B raw9656step0 raw9656step0Labels := by
      have hz : ∀ j, raw9656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9656step0 = (fun i j => raw9656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9656step0 raw9656; decide +kernel
      have hl : raw9656step0Labels = raw9656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9656 raw9656Labels permutation434 hz
    mixedMoment B raw9656step0 raw9656step0Labels = mixedMoment B raw9656step1 raw9656step1Labels := by
      have hz : ∀ j, raw9656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9656step1 = (fun i j => raw9656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9656step1 raw9656step0; decide +kernel
      have hl : raw9656step1Labels = raw9656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9656step0 raw9656step0Labels permutation80 hz
    mixedMoment B raw9656step1 raw9656step1Labels = mixedMoment B raw9656step2 raw9656step2Labels := by
      have ha : raw9656step2 = (fun i j => raw9656step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9656step2 raw9656step1; decide +kernel
      have hl : raw9656step2Labels = raw9656step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9656step1 raw9656step1Labels permutation8 permutation7
    mixedMoment B raw9656step2 raw9656step2Labels = mixedMoment B raw9656step3 raw9656step3Labels := by
      have ha : raw9656step3 = raw9656step2 := by apply Matrix.ext; unfold raw9656step3 raw9656step2; decide +kernel
      have hl : raw9656step2Labels = labelEmbedding10 ∘ raw9656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9656step2 raw9656step2Labels raw9656step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw9657 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw9657step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9657step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9657step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9657step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9657 raw9657Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw9657 raw9657Labels = mixedMoment B raw9657step0 raw9657step0Labels := by
      have hz : ∀ j, raw9657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9657step0 = (fun i j => raw9657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9657step0 raw9657; decide +kernel
      have hl : raw9657step0Labels = raw9657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9657 raw9657Labels permutation434 hz
    mixedMoment B raw9657step0 raw9657step0Labels = mixedMoment B raw9657step1 raw9657step1Labels := by
      have hz : ∀ j, raw9657step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9657step1 = (fun i j => raw9657step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9657step1 raw9657step0; decide +kernel
      have hl : raw9657step1Labels = raw9657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9657step0 raw9657step0Labels permutation80 hz
    mixedMoment B raw9657step1 raw9657step1Labels = mixedMoment B raw9657step2 raw9657step2Labels := by
      have ha : raw9657step2 = (fun i j => raw9657step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9657step2 raw9657step1; decide +kernel
      have hl : raw9657step2Labels = raw9657step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9657step1 raw9657step1Labels permutation10 permutation4
    mixedMoment B raw9657step2 raw9657step2Labels = mixedMoment B raw9657step3 raw9657step3Labels := by
      have ha : raw9657step3 = -raw9657step2 := by apply Matrix.ext; change ∀ i j, raw9657step3 i j = -(raw9657step2 i j); unfold raw9657step3 raw9657step2; decide +kernel
      have hl : raw9657step3Labels = raw9657step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9657step3 raw9657step3Labels = mixedMoment B raw9657step4 raw9657step4Labels := by
      have ha : raw9657step4 = raw9657step3 := by apply Matrix.ext; unfold raw9657step4 raw9657step3; decide +kernel
      have hl : raw9657step3Labels = labelEmbedding7 ∘ raw9657step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9657step3 raw9657step3Labels raw9657step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw9658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9658step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9658 raw9658Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw9658 raw9658Labels = mixedMoment B raw9658step0 raw9658step0Labels := by
      have hz : ∀ j, raw9658 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9658step0 = (fun i j => raw9658 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9658step0 raw9658; decide +kernel
      have hl : raw9658step0Labels = raw9658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9658 raw9658Labels permutation434 hz
    mixedMoment B raw9658step0 raw9658step0Labels = mixedMoment B raw9658step1 raw9658step1Labels := by
      have ha : raw9658step1 = (fun i j => raw9658step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9658step1 raw9658step0; decide +kernel
      have hl : raw9658step1Labels = raw9658step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9658step0 raw9658step0Labels permutation38 permutation6
    mixedMoment B raw9658step1 raw9658step1Labels = mixedMoment B raw9658step2 raw9658step2Labels := by
      have ha : raw9658step2 = raw9658step1 := by apply Matrix.ext; unfold raw9658step2 raw9658step1; decide +kernel
      have hl : raw9658step1Labels = labelEmbedding9 ∘ raw9658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9658step1 raw9658step1Labels raw9658step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw9659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9659step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9659step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9659 raw9659Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw9659 raw9659Labels = mixedMoment B raw9659step0 raw9659step0Labels := by
      have hz : ∀ j, raw9659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9659step0 = (fun i j => raw9659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9659step0 raw9659; decide +kernel
      have hl : raw9659step0Labels = raw9659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9659 raw9659Labels permutation346 hz
    mixedMoment B raw9659step0 raw9659step0Labels = mixedMoment B raw9659step1 raw9659step1Labels := by
      have ha : raw9659step1 = (fun i j => raw9659step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9659step1 raw9659step0; decide +kernel
      have hl : raw9659step1Labels = raw9659step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9659step0 raw9659step0Labels permutation38 permutation6
    mixedMoment B raw9659step1 raw9659step1Labels = mixedMoment B raw9659step2 raw9659step2Labels := by
      have ha : raw9659step2 = raw9659step1 := by apply Matrix.ext; unfold raw9659step2 raw9659step1; decide +kernel
      have hl : raw9659step1Labels = labelEmbedding9 ∘ raw9659step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9659step1 raw9659step1Labels raw9659step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw9660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9660step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw9660step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9660step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw9660step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9660 raw9660Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw9660 raw9660Labels = mixedMoment B raw9660step0 raw9660step0Labels := by
      have hz : ∀ j, raw9660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9660step0 = (fun i j => raw9660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9660step0 raw9660; decide +kernel
      have hl : raw9660step0Labels = raw9660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9660 raw9660Labels permutation434 hz
    mixedMoment B raw9660step0 raw9660step0Labels = mixedMoment B raw9660step1 raw9660step1Labels := by
      have hz : ∀ j, raw9660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9660step1 = (fun i j => raw9660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9660step1 raw9660step0; decide +kernel
      have hl : raw9660step1Labels = raw9660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9660step0 raw9660step0Labels permutation80 hz
    mixedMoment B raw9660step1 raw9660step1Labels = mixedMoment B raw9660step2 raw9660step2Labels := by
      have ha : raw9660step2 = (fun i j => raw9660step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9660step2 raw9660step1; decide +kernel
      have hl : raw9660step2Labels = raw9660step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9660step1 raw9660step1Labels permutation24 permutation3
    mixedMoment B raw9660step2 raw9660step2Labels = mixedMoment B raw9660step3 raw9660step3Labels := by
      have ha : raw9660step3 = raw9660step2 := by apply Matrix.ext; unfold raw9660step3 raw9660step2; decide +kernel
      have hl : raw9660step2Labels = labelEmbedding6 ∘ raw9660step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9660step2 raw9660step2Labels raw9660step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5297 node5297Labels := by rfl

def raw9661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9661step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9661step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9661 raw9661Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw9661 raw9661Labels = mixedMoment B raw9661step0 raw9661step0Labels := by
      have hz : ∀ j, raw9661 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9661step0 = (fun i j => raw9661 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9661step0 raw9661; decide +kernel
      have hl : raw9661step0Labels = raw9661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9661 raw9661Labels permutation434 hz
    mixedMoment B raw9661step0 raw9661step0Labels = mixedMoment B raw9661step1 raw9661step1Labels := by
      have hz : ∀ j, raw9661step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9661step1 = (fun i j => raw9661step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9661step1 raw9661step0; decide +kernel
      have hl : raw9661step1Labels = raw9661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9661step0 raw9661step0Labels permutation80 hz
    mixedMoment B raw9661step1 raw9661step1Labels = mixedMoment B raw9661step2 raw9661step2Labels := by
      have ha : raw9661step2 = (fun i j => raw9661step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9661step2 raw9661step1; decide +kernel
      have hl : raw9661step2Labels = raw9661step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9661step1 raw9661step1Labels permutation8 permutation6
    mixedMoment B raw9661step2 raw9661step2Labels = mixedMoment B raw9661step3 raw9661step3Labels := by
      have ha : raw9661step3 = raw9661step2 := by apply Matrix.ext; unfold raw9661step3 raw9661step2; decide +kernel
      have hl : raw9661step2Labels = labelEmbedding9 ∘ raw9661step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9661step2 raw9661step2Labels raw9661step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw9662 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9662step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9662step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9662step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9662step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9662 raw9662Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw9662 raw9662Labels = mixedMoment B raw9662step0 raw9662step0Labels := by
      have hz : ∀ j, raw9662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9662step0 = (fun i j => raw9662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9662step0 raw9662; decide +kernel
      have hl : raw9662step0Labels = raw9662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9662 raw9662Labels permutation434 hz
    mixedMoment B raw9662step0 raw9662step0Labels = mixedMoment B raw9662step1 raw9662step1Labels := by
      have ha : raw9662step1 = (fun i j => raw9662step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9662step1 raw9662step0; decide +kernel
      have hl : raw9662step1Labels = raw9662step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9662step0 raw9662step0Labels permutation44 permutation4
    mixedMoment B raw9662step1 raw9662step1Labels = mixedMoment B raw9662step2 raw9662step2Labels := by
      have ha : raw9662step2 = -raw9662step1 := by apply Matrix.ext; change ∀ i j, raw9662step2 i j = -(raw9662step1 i j); unfold raw9662step2 raw9662step1; decide +kernel
      have hl : raw9662step2Labels = raw9662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9662step2 raw9662step2Labels = mixedMoment B raw9662step3 raw9662step3Labels := by
      have ha : raw9662step3 = raw9662step2 := by apply Matrix.ext; unfold raw9662step3 raw9662step2; decide +kernel
      have hl : raw9662step2Labels = labelEmbedding7 ∘ raw9662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9662step2 raw9662step2Labels raw9662step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw9663 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9663step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9663 raw9663Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw9663 raw9663Labels = mixedMoment B raw9663step0 raw9663step0Labels := by
      have ha : raw9663step0 = (fun i j => raw9663 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9663step0 raw9663; decide +kernel
      have hl : raw9663step0Labels = raw9663Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9663 raw9663Labels permutation200 permutation6
    mixedMoment B raw9663step0 raw9663step0Labels = mixedMoment B raw9663step1 raw9663step1Labels := by
      have ha : raw9663step1 = raw9663step0 := by apply Matrix.ext; unfold raw9663step1 raw9663step0; decide +kernel
      have hl : raw9663step0Labels = labelEmbedding9 ∘ raw9663step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9663step0 raw9663step0Labels raw9663step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw9664 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9664step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9664 raw9664Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw9664 raw9664Labels = mixedMoment B raw9664step0 raw9664step0Labels := by
      have hz : ∀ j, raw9664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9664step0 = (fun i j => raw9664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9664step0 raw9664; decide +kernel
      have hl : raw9664step0Labels = raw9664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9664 raw9664Labels permutation434 hz
    mixedMoment B raw9664step0 raw9664step0Labels = mixedMoment B raw9664step1 raw9664step1Labels := by
      have ha : raw9664step1 = (fun i j => raw9664step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9664step1 raw9664step0; decide +kernel
      have hl : raw9664step1Labels = raw9664step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9664step0 raw9664step0Labels permutation32 permutation6
    mixedMoment B raw9664step1 raw9664step1Labels = mixedMoment B raw9664step2 raw9664step2Labels := by
      have ha : raw9664step2 = raw9664step1 := by apply Matrix.ext; unfold raw9664step2 raw9664step1; decide +kernel
      have hl : raw9664step1Labels = labelEmbedding9 ∘ raw9664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9664step1 raw9664step1Labels raw9664step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw9665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9665step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9665step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9665 raw9665Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw9665 raw9665Labels = mixedMoment B raw9665step0 raw9665step0Labels := by
      have hz : ∀ j, raw9665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9665step0 = (fun i j => raw9665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9665step0 raw9665; decide +kernel
      have hl : raw9665step0Labels = raw9665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9665 raw9665Labels permutation346 hz
    mixedMoment B raw9665step0 raw9665step0Labels = mixedMoment B raw9665step1 raw9665step1Labels := by
      have ha : raw9665step1 = (fun i j => raw9665step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9665step1 raw9665step0; decide +kernel
      have hl : raw9665step1Labels = raw9665step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9665step0 raw9665step0Labels permutation44 permutation4
    mixedMoment B raw9665step1 raw9665step1Labels = mixedMoment B raw9665step2 raw9665step2Labels := by
      have ha : raw9665step2 = -raw9665step1 := by apply Matrix.ext; change ∀ i j, raw9665step2 i j = -(raw9665step1 i j); unfold raw9665step2 raw9665step1; decide +kernel
      have hl : raw9665step2Labels = raw9665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9665step2 raw9665step2Labels = mixedMoment B raw9665step3 raw9665step3Labels := by
      have ha : raw9665step3 = raw9665step2 := by apply Matrix.ext; unfold raw9665step3 raw9665step2; decide +kernel
      have hl : raw9665step2Labels = labelEmbedding7 ∘ raw9665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9665step2 raw9665step2Labels raw9665step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw9666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9666step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9666 raw9666Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw9666 raw9666Labels = mixedMoment B raw9666step0 raw9666step0Labels := by
      have ha : raw9666step0 = (fun i j => raw9666 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9666step0 raw9666; decide +kernel
      have hl : raw9666step0Labels = raw9666Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9666 raw9666Labels permutation176 permutation6
    mixedMoment B raw9666step0 raw9666step0Labels = mixedMoment B raw9666step1 raw9666step1Labels := by
      have ha : raw9666step1 = raw9666step0 := by apply Matrix.ext; unfold raw9666step1 raw9666step0; decide +kernel
      have hl : raw9666step0Labels = labelEmbedding9 ∘ raw9666step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9666step0 raw9666step0Labels raw9666step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw9667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9667step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9667 raw9667Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw9667 raw9667Labels = mixedMoment B raw9667step0 raw9667step0Labels := by
      have hz : ∀ j, raw9667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9667step0 = (fun i j => raw9667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9667step0 raw9667; decide +kernel
      have hl : raw9667step0Labels = raw9667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9667 raw9667Labels permutation346 hz
    mixedMoment B raw9667step0 raw9667step0Labels = mixedMoment B raw9667step1 raw9667step1Labels := by
      have ha : raw9667step1 = (fun i j => raw9667step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9667step1 raw9667step0; decide +kernel
      have hl : raw9667step1Labels = raw9667step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9667step0 raw9667step0Labels permutation32 permutation6
    mixedMoment B raw9667step1 raw9667step1Labels = mixedMoment B raw9667step2 raw9667step2Labels := by
      have ha : raw9667step2 = raw9667step1 := by apply Matrix.ext; unfold raw9667step2 raw9667step1; decide +kernel
      have hl : raw9667step1Labels = labelEmbedding9 ∘ raw9667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9667step1 raw9667step1Labels raw9667step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw9668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9668step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9668step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9668step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9668step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9668 raw9668Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw9668 raw9668Labels = mixedMoment B raw9668step0 raw9668step0Labels := by
      have hz : ∀ j, raw9668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9668step0 = (fun i j => raw9668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9668step0 raw9668; decide +kernel
      have hl : raw9668step0Labels = raw9668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9668 raw9668Labels permutation434 hz
    mixedMoment B raw9668step0 raw9668step0Labels = mixedMoment B raw9668step1 raw9668step1Labels := by
      have hz : ∀ j, raw9668step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9668step1 = (fun i j => raw9668step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9668step1 raw9668step0; decide +kernel
      have hl : raw9668step1Labels = raw9668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9668step0 raw9668step0Labels permutation80 hz
    mixedMoment B raw9668step1 raw9668step1Labels = mixedMoment B raw9668step2 raw9668step2Labels := by
      have ha : raw9668step2 = (fun i j => raw9668step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9668step2 raw9668step1; decide +kernel
      have hl : raw9668step2Labels = raw9668step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9668step1 raw9668step1Labels permutation10 permutation4
    mixedMoment B raw9668step2 raw9668step2Labels = mixedMoment B raw9668step3 raw9668step3Labels := by
      have ha : raw9668step3 = -raw9668step2 := by apply Matrix.ext; change ∀ i j, raw9668step3 i j = -(raw9668step2 i j); unfold raw9668step3 raw9668step2; decide +kernel
      have hl : raw9668step3Labels = raw9668step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9668step3 raw9668step3Labels = mixedMoment B raw9668step4 raw9668step4Labels := by
      have ha : raw9668step4 = raw9668step3 := by apply Matrix.ext; unfold raw9668step4 raw9668step3; decide +kernel
      have hl : raw9668step3Labels = labelEmbedding7 ∘ raw9668step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9668step3 raw9668step3Labels raw9668step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw9669 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9669step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9669 raw9669Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw9669 raw9669Labels = mixedMoment B raw9669step0 raw9669step0Labels := by
      have hz : ∀ j, raw9669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9669step0 = (fun i j => raw9669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9669step0 raw9669; decide +kernel
      have hl : raw9669step0Labels = raw9669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9669 raw9669Labels permutation434 hz
    mixedMoment B raw9669step0 raw9669step0Labels = mixedMoment B raw9669step1 raw9669step1Labels := by
      have ha : raw9669step1 = (fun i j => raw9669step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9669step1 raw9669step0; decide +kernel
      have hl : raw9669step1Labels = raw9669step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9669step0 raw9669step0Labels permutation38 permutation6
    mixedMoment B raw9669step1 raw9669step1Labels = mixedMoment B raw9669step2 raw9669step2Labels := by
      have ha : raw9669step2 = raw9669step1 := by apply Matrix.ext; unfold raw9669step2 raw9669step1; decide +kernel
      have hl : raw9669step1Labels = labelEmbedding9 ∘ raw9669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9669step1 raw9669step1Labels raw9669step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw9670 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9670step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9670 raw9670Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw9670 raw9670Labels = mixedMoment B raw9670step0 raw9670step0Labels := by
      have hz : ∀ j, raw9670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9670step0 = (fun i j => raw9670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9670step0 raw9670; decide +kernel
      have hl : raw9670step0Labels = raw9670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9670 raw9670Labels permutation346 hz
    mixedMoment B raw9670step0 raw9670step0Labels = mixedMoment B raw9670step1 raw9670step1Labels := by
      have ha : raw9670step1 = (fun i j => raw9670step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9670step1 raw9670step0; decide +kernel
      have hl : raw9670step1Labels = raw9670step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9670step0 raw9670step0Labels permutation38 permutation6
    mixedMoment B raw9670step1 raw9670step1Labels = mixedMoment B raw9670step2 raw9670step2Labels := by
      have ha : raw9670step2 = raw9670step1 := by apply Matrix.ext; unfold raw9670step2 raw9670step1; decide +kernel
      have hl : raw9670step1Labels = labelEmbedding9 ∘ raw9670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9670step1 raw9670step1Labels raw9670step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw9671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9671step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9671step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9671step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9671step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9671 raw9671Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw9671 raw9671Labels = mixedMoment B raw9671step0 raw9671step0Labels := by
      have hz : ∀ j, raw9671 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9671step0 = (fun i j => raw9671 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9671step0 raw9671; decide +kernel
      have hl : raw9671step0Labels = raw9671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9671 raw9671Labels permutation434 hz
    mixedMoment B raw9671step0 raw9671step0Labels = mixedMoment B raw9671step1 raw9671step1Labels := by
      have hz : ∀ j, raw9671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9671step1 = (fun i j => raw9671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9671step1 raw9671step0; decide +kernel
      have hl : raw9671step1Labels = raw9671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9671step0 raw9671step0Labels permutation80 hz
    mixedMoment B raw9671step1 raw9671step1Labels = mixedMoment B raw9671step2 raw9671step2Labels := by
      have ha : raw9671step2 = (fun i j => raw9671step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9671step2 raw9671step1; decide +kernel
      have hl : raw9671step2Labels = raw9671step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9671step1 raw9671step1Labels permutation10 permutation4
    mixedMoment B raw9671step2 raw9671step2Labels = mixedMoment B raw9671step3 raw9671step3Labels := by
      have ha : raw9671step3 = -raw9671step2 := by apply Matrix.ext; change ∀ i j, raw9671step3 i j = -(raw9671step2 i j); unfold raw9671step3 raw9671step2; decide +kernel
      have hl : raw9671step3Labels = raw9671step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9671step3 raw9671step3Labels = mixedMoment B raw9671step4 raw9671step4Labels := by
      have ha : raw9671step4 = raw9671step3 := by apply Matrix.ext; unfold raw9671step4 raw9671step3; decide +kernel
      have hl : raw9671step3Labels = labelEmbedding7 ∘ raw9671step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9671step3 raw9671step3Labels raw9671step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw9672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9672step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![1, -3, 2]]
def raw9672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9672step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw9672step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9672step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw9672step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9672 raw9672Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw9672 raw9672Labels = mixedMoment B raw9672step0 raw9672step0Labels := by
      have hz : ∀ j, raw9672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9672step0 = (fun i j => raw9672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9672step0 raw9672; decide +kernel
      have hl : raw9672step0Labels = raw9672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9672 raw9672Labels permutation434 hz
    mixedMoment B raw9672step0 raw9672step0Labels = mixedMoment B raw9672step1 raw9672step1Labels := by
      have hz : ∀ j, raw9672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9672step1 = (fun i j => raw9672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9672step1 raw9672step0; decide +kernel
      have hl : raw9672step1Labels = raw9672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9672step0 raw9672step0Labels permutation80 hz
    mixedMoment B raw9672step1 raw9672step1Labels = mixedMoment B raw9672step2 raw9672step2Labels := by
      have hz : ∀ j, raw9672step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw9672step2 = (fun i j => raw9672step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw9672step2 raw9672step1; decide +kernel
      have hl : raw9672step2Labels = raw9672step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9672step1 raw9672step1Labels permutation14 hz
    mixedMoment B raw9672step2 raw9672step2Labels = mixedMoment B raw9672step3 raw9672step3Labels := by
      have ha : raw9672step3 = (fun i j => raw9672step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9672step3 raw9672step2; decide +kernel
      have hl : raw9672step3Labels = raw9672step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9672step2 raw9672step2Labels permutation7 permutation4
    mixedMoment B raw9672step3 raw9672step3Labels = mixedMoment B raw9672step4 raw9672step4Labels := by
      have ha : raw9672step4 = raw9672step3 := by apply Matrix.ext; unfold raw9672step4 raw9672step3; decide +kernel
      have hl : raw9672step3Labels = labelEmbedding7 ∘ raw9672step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9672step3 raw9672step3Labels raw9672step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

def raw9673 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9673step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9673 raw9673Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw9673 raw9673Labels = mixedMoment B raw9673step0 raw9673step0Labels := by
      have hz : ∀ j, raw9673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9673step0 = (fun i j => raw9673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9673step0 raw9673; decide +kernel
      have hl : raw9673step0Labels = raw9673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9673 raw9673Labels permutation434 hz
    mixedMoment B raw9673step0 raw9673step0Labels = mixedMoment B raw9673step1 raw9673step1Labels := by
      have ha : raw9673step1 = (fun i j => raw9673step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9673step1 raw9673step0; decide +kernel
      have hl : raw9673step1Labels = raw9673step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9673step0 raw9673step0Labels permutation139 permutation4
    mixedMoment B raw9673step1 raw9673step1Labels = mixedMoment B raw9673step2 raw9673step2Labels := by
      have ha : raw9673step2 = raw9673step1 := by apply Matrix.ext; unfold raw9673step2 raw9673step1; decide +kernel
      have hl : raw9673step1Labels = labelEmbedding7 ∘ raw9673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9673step1 raw9673step1Labels raw9673step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw9674 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9674step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9674 raw9674Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw9674 raw9674Labels = mixedMoment B raw9674step0 raw9674step0Labels := by
      have hz : ∀ j, raw9674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9674step0 = (fun i j => raw9674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9674step0 raw9674; decide +kernel
      have hl : raw9674step0Labels = raw9674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9674 raw9674Labels permutation346 hz
    mixedMoment B raw9674step0 raw9674step0Labels = mixedMoment B raw9674step1 raw9674step1Labels := by
      have ha : raw9674step1 = (fun i j => raw9674step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9674step1 raw9674step0; decide +kernel
      have hl : raw9674step1Labels = raw9674step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9674step0 raw9674step0Labels permutation139 permutation4
    mixedMoment B raw9674step1 raw9674step1Labels = mixedMoment B raw9674step2 raw9674step2Labels := by
      have ha : raw9674step2 = raw9674step1 := by apply Matrix.ext; unfold raw9674step2 raw9674step1; decide +kernel
      have hl : raw9674step1Labels = labelEmbedding7 ∘ raw9674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9674step1 raw9674step1Labels raw9674step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw9675 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw9675step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw9675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9675 raw9675Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw9675 raw9675Labels = mixedMoment B raw9675step0 raw9675step0Labels := by
      have hz : ∀ j, raw9675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9675step0 = (fun i j => raw9675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9675step0 raw9675; decide +kernel
      have hl : raw9675step0Labels = raw9675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9675 raw9675Labels permutation434 hz
    mixedMoment B raw9675step0 raw9675step0Labels = mixedMoment B raw9675step1 raw9675step1Labels := by
      have hz : ∀ j, raw9675step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9675step1 = (fun i j => raw9675step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9675step1 raw9675step0; decide +kernel
      have hl : raw9675step1Labels = raw9675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9675step0 raw9675step0Labels permutation80 hz
    mixedMoment B raw9675step1 raw9675step1Labels = mixedMoment B raw9675step2 raw9675step2Labels := by
      have ha : raw9675step2 = (fun i j => raw9675step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9675step2 raw9675step1; decide +kernel
      have hl : raw9675step2Labels = raw9675step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9675step1 raw9675step1Labels permutation29 permutation4
    mixedMoment B raw9675step2 raw9675step2Labels = mixedMoment B raw9675step3 raw9675step3Labels := by
      have ha : raw9675step3 = raw9675step2 := by apply Matrix.ext; unfold raw9675step3 raw9675step2; decide +kernel
      have hl : raw9675step2Labels = labelEmbedding7 ∘ raw9675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9675step2 raw9675step2Labels raw9675step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw9676 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9676step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9676step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9676step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![0, -2, 2]]
def raw9676step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9676step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw9676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9676 raw9676Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw9676 raw9676Labels = mixedMoment B raw9676step0 raw9676step0Labels := by
      have hz : ∀ j, raw9676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9676step0 = (fun i j => raw9676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9676step0 raw9676; decide +kernel
      have hl : raw9676step0Labels = raw9676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9676 raw9676Labels permutation434 hz
    mixedMoment B raw9676step0 raw9676step0Labels = mixedMoment B raw9676step1 raw9676step1Labels := by
      have hz : ∀ j, raw9676step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9676step1 = (fun i j => raw9676step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9676step1 raw9676step0; decide +kernel
      have hl : raw9676step1Labels = raw9676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9676step0 raw9676step0Labels permutation80 hz
    mixedMoment B raw9676step1 raw9676step1Labels = mixedMoment B raw9676step2 raw9676step2Labels := by
      have hz : ∀ j, raw9676step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw9676step2 = (fun i j => raw9676step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw9676step2 raw9676step1; decide +kernel
      have hl : raw9676step2Labels = raw9676step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9676step1 raw9676step1Labels permutation14 hz
    mixedMoment B raw9676step2 raw9676step2Labels = mixedMoment B raw9676step3 raw9676step3Labels := by
      have ha : raw9676step3 = (fun i j => raw9676step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9676step3 raw9676step2; decide +kernel
      have hl : raw9676step3Labels = raw9676step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9676step2 raw9676step2Labels permutation2 permutation6
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw9677 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9677 raw9677Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw9677 raw9677Labels = mixedMoment B raw9677step0 raw9677step0Labels := by
      have hz : ∀ j, raw9677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9677step0 = (fun i j => raw9677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9677step0 raw9677; decide +kernel
      have hl : raw9677step0Labels = raw9677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9677 raw9677Labels permutation434 hz
    mixedMoment B raw9677step0 raw9677step0Labels = mixedMoment B raw9677step1 raw9677step1Labels := by
      have ha : raw9677step1 = (fun i j => raw9677step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9677step1 raw9677step0; decide +kernel
      have hl : raw9677step1Labels = raw9677step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9677step0 raw9677step0Labels permutation38 permutation6
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw9678 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9678 raw9678Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw9678 raw9678Labels = mixedMoment B raw9678step0 raw9678step0Labels := by
      have hz : ∀ j, raw9678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9678step0 = (fun i j => raw9678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9678step0 raw9678; decide +kernel
      have hl : raw9678step0Labels = raw9678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9678 raw9678Labels permutation346 hz
    mixedMoment B raw9678step0 raw9678step0Labels = mixedMoment B raw9678step1 raw9678step1Labels := by
      have ha : raw9678step1 = (fun i j => raw9678step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9678step1 raw9678step0; decide +kernel
      have hl : raw9678step1Labels = raw9678step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9678step0 raw9678step0Labels permutation38 permutation6
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw9679 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9679step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw9679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9679 raw9679Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw9679 raw9679Labels = mixedMoment B raw9679step0 raw9679step0Labels := by
      have hz : ∀ j, raw9679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9679step0 = (fun i j => raw9679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9679step0 raw9679; decide +kernel
      have hl : raw9679step0Labels = raw9679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9679 raw9679Labels permutation434 hz
    mixedMoment B raw9679step0 raw9679step0Labels = mixedMoment B raw9679step1 raw9679step1Labels := by
      have hz : ∀ j, raw9679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9679step1 = (fun i j => raw9679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9679step1 raw9679step0; decide +kernel
      have hl : raw9679step1Labels = raw9679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9679step0 raw9679step0Labels permutation80 hz
    mixedMoment B raw9679step1 raw9679step1Labels = mixedMoment B raw9679step2 raw9679step2Labels := by
      have ha : raw9679step2 = (fun i j => raw9679step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9679step2 raw9679step1; decide +kernel
      have hl : raw9679step2Labels = raw9679step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9679step1 raw9679step1Labels permutation25 permutation3
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw9680 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9680step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9680 raw9680Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw9680 raw9680Labels = mixedMoment B raw9680step0 raw9680step0Labels := by
      have hz : ∀ j, raw9680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9680step0 = (fun i j => raw9680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9680step0 raw9680; decide +kernel
      have hl : raw9680step0Labels = raw9680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9680 raw9680Labels permutation434 hz
    mixedMoment B raw9680step0 raw9680step0Labels = mixedMoment B raw9680step1 raw9680step1Labels := by
      have hz : ∀ j, raw9680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9680step1 = (fun i j => raw9680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9680step1 raw9680step0; decide +kernel
      have hl : raw9680step1Labels = raw9680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9680step0 raw9680step0Labels permutation80 hz
    mixedMoment B raw9680step1 raw9680step1Labels = mixedMoment B raw9680step2 raw9680step2Labels := by
      have ha : raw9680step2 = (fun i j => raw9680step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9680step2 raw9680step1; decide +kernel
      have hl : raw9680step2Labels = raw9680step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9680step1 raw9680step1Labels permutation8 permutation6
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw9681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9681step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9681step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9681 raw9681Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw9681 raw9681Labels = mixedMoment B raw9681step0 raw9681step0Labels := by
      have hz : ∀ j, raw9681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9681step0 = (fun i j => raw9681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9681step0 raw9681; decide +kernel
      have hl : raw9681step0Labels = raw9681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9681 raw9681Labels permutation434 hz
    mixedMoment B raw9681step0 raw9681step0Labels = mixedMoment B raw9681step1 raw9681step1Labels := by
      have hz : ∀ j, raw9681step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9681step1 = (fun i j => raw9681step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9681step1 raw9681step0; decide +kernel
      have hl : raw9681step1Labels = raw9681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9681step0 raw9681step0Labels permutation80 hz
    mixedMoment B raw9681step1 raw9681step1Labels = mixedMoment B raw9681step2 raw9681step2Labels := by
      have ha : raw9681step2 = (fun i j => raw9681step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9681step2 raw9681step1; decide +kernel
      have hl : raw9681step2Labels = raw9681step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9681step1 raw9681step1Labels permutation8 permutation6
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw9682 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9682 raw9682Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw9682 raw9682Labels = mixedMoment B raw9682step0 raw9682step0Labels := by
      have hz : ∀ j, raw9682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9682step0 = (fun i j => raw9682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9682step0 raw9682; decide +kernel
      have hl : raw9682step0Labels = raw9682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9682 raw9682Labels permutation434 hz
    mixedMoment B raw9682step0 raw9682step0Labels = mixedMoment B raw9682step1 raw9682step1Labels := by
      have ha : raw9682step1 = (fun i j => raw9682step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9682step1 raw9682step0; decide +kernel
      have hl : raw9682step1Labels = raw9682step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9682step0 raw9682step0Labels permutation38 permutation6
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw9683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9683 raw9683Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw9683 raw9683Labels = mixedMoment B raw9683step0 raw9683step0Labels := by
      have hz : ∀ j, raw9683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9683step0 = (fun i j => raw9683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9683step0 raw9683; decide +kernel
      have hl : raw9683step0Labels = raw9683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9683 raw9683Labels permutation346 hz
    mixedMoment B raw9683step0 raw9683step0Labels = mixedMoment B raw9683step1 raw9683step1Labels := by
      have ha : raw9683step1 = (fun i j => raw9683step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9683step1 raw9683step0; decide +kernel
      have hl : raw9683step1Labels = raw9683step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9683step0 raw9683step0Labels permutation38 permutation6
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw9684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9684step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw9684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9684 raw9684Labels = mixedMoment B node2771 node2771Labels := by
  calc
    mixedMoment B raw9684 raw9684Labels = mixedMoment B raw9684step0 raw9684step0Labels := by
      have hz : ∀ j, raw9684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9684step0 = (fun i j => raw9684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9684step0 raw9684; decide +kernel
      have hl : raw9684step0Labels = raw9684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9684 raw9684Labels permutation434 hz
    mixedMoment B raw9684step0 raw9684step0Labels = mixedMoment B raw9684step1 raw9684step1Labels := by
      have hz : ∀ j, raw9684step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9684step1 = (fun i j => raw9684step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9684step1 raw9684step0; decide +kernel
      have hl : raw9684step1Labels = raw9684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9684step0 raw9684step0Labels permutation80 hz
    mixedMoment B raw9684step1 raw9684step1Labels = mixedMoment B raw9684step2 raw9684step2Labels := by
      have ha : raw9684step2 = (fun i j => raw9684step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9684step2 raw9684step1; decide +kernel
      have hl : raw9684step2Labels = raw9684step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9684step1 raw9684step1Labels permutation24 permutation3
    _ = mixedMoment B node2771 node2771Labels := by rfl

def raw9685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9685step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9685 raw9685Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw9685 raw9685Labels = mixedMoment B raw9685step0 raw9685step0Labels := by
      have hz : ∀ j, raw9685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9685step0 = (fun i j => raw9685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9685step0 raw9685; decide +kernel
      have hl : raw9685step0Labels = raw9685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9685 raw9685Labels permutation434 hz
    mixedMoment B raw9685step0 raw9685step0Labels = mixedMoment B raw9685step1 raw9685step1Labels := by
      have hz : ∀ j, raw9685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9685step1 = (fun i j => raw9685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9685step1 raw9685step0; decide +kernel
      have hl : raw9685step1Labels = raw9685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9685step0 raw9685step0Labels permutation80 hz
    mixedMoment B raw9685step1 raw9685step1Labels = mixedMoment B raw9685step2 raw9685step2Labels := by
      have ha : raw9685step2 = (fun i j => raw9685step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9685step2 raw9685step1; decide +kernel
      have hl : raw9685step2Labels = raw9685step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9685step1 raw9685step1Labels permutation8 permutation6
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw9686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9686 raw9686Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw9686 raw9686Labels = mixedMoment B raw9686step0 raw9686step0Labels := by
      have hz : ∀ j, raw9686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9686step0 = (fun i j => raw9686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9686step0 raw9686; decide +kernel
      have hl : raw9686step0Labels = raw9686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9686 raw9686Labels permutation434 hz
    mixedMoment B raw9686step0 raw9686step0Labels = mixedMoment B raw9686step1 raw9686step1Labels := by
      have ha : raw9686step1 = (fun i j => raw9686step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9686step1 raw9686step0; decide +kernel
      have hl : raw9686step1Labels = raw9686step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9686step0 raw9686step0Labels permutation32 permutation6
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw9687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9687 raw9687Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw9687 raw9687Labels = mixedMoment B raw9687step0 raw9687step0Labels := by
      have ha : raw9687step0 = (fun i j => raw9687 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9687step0 raw9687; decide +kernel
      have hl : raw9687step0Labels = raw9687Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9687 raw9687Labels permutation200 permutation6
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw9688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9688 raw9688Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw9688 raw9688Labels = mixedMoment B raw9688step0 raw9688step0Labels := by
      have hz : ∀ j, raw9688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9688step0 = (fun i j => raw9688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9688step0 raw9688; decide +kernel
      have hl : raw9688step0Labels = raw9688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9688 raw9688Labels permutation434 hz
    mixedMoment B raw9688step0 raw9688step0Labels = mixedMoment B raw9688step1 raw9688step1Labels := by
      have ha : raw9688step1 = (fun i j => raw9688step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9688step1 raw9688step0; decide +kernel
      have hl : raw9688step1Labels = raw9688step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9688step0 raw9688step0Labels permutation32 permutation6
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw9689 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9689 raw9689Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw9689 raw9689Labels = mixedMoment B raw9689step0 raw9689step0Labels := by
      have hz : ∀ j, raw9689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9689step0 = (fun i j => raw9689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9689step0 raw9689; decide +kernel
      have hl : raw9689step0Labels = raw9689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9689 raw9689Labels permutation346 hz
    mixedMoment B raw9689step0 raw9689step0Labels = mixedMoment B raw9689step1 raw9689step1Labels := by
      have ha : raw9689step1 = (fun i j => raw9689step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9689step1 raw9689step0; decide +kernel
      have hl : raw9689step1Labels = raw9689step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9689step0 raw9689step0Labels permutation32 permutation6
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw9690 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9690 raw9690Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw9690 raw9690Labels = mixedMoment B raw9690step0 raw9690step0Labels := by
      have ha : raw9690step0 = (fun i j => raw9690 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9690step0 raw9690; decide +kernel
      have hl : raw9690step0Labels = raw9690Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9690 raw9690Labels permutation176 permutation6
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw9691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9691 raw9691Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw9691 raw9691Labels = mixedMoment B raw9691step0 raw9691step0Labels := by
      have hz : ∀ j, raw9691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9691step0 = (fun i j => raw9691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9691step0 raw9691; decide +kernel
      have hl : raw9691step0Labels = raw9691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9691 raw9691Labels permutation346 hz
    mixedMoment B raw9691step0 raw9691step0Labels = mixedMoment B raw9691step1 raw9691step1Labels := by
      have ha : raw9691step1 = (fun i j => raw9691step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9691step1 raw9691step0; decide +kernel
      have hl : raw9691step1Labels = raw9691step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9691step0 raw9691step0Labels permutation32 permutation6
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw9692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9692step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9692 raw9692Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw9692 raw9692Labels = mixedMoment B raw9692step0 raw9692step0Labels := by
      have hz : ∀ j, raw9692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9692step0 = (fun i j => raw9692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9692step0 raw9692; decide +kernel
      have hl : raw9692step0Labels = raw9692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9692 raw9692Labels permutation434 hz
    mixedMoment B raw9692step0 raw9692step0Labels = mixedMoment B raw9692step1 raw9692step1Labels := by
      have hz : ∀ j, raw9692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9692step1 = (fun i j => raw9692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9692step1 raw9692step0; decide +kernel
      have hl : raw9692step1Labels = raw9692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9692step0 raw9692step0Labels permutation80 hz
    mixedMoment B raw9692step1 raw9692step1Labels = mixedMoment B raw9692step2 raw9692step2Labels := by
      have ha : raw9692step2 = (fun i j => raw9692step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9692step2 raw9692step1; decide +kernel
      have hl : raw9692step2Labels = raw9692step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9692step1 raw9692step1Labels permutation8 permutation6
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw9693 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9693 raw9693Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw9693 raw9693Labels = mixedMoment B raw9693step0 raw9693step0Labels := by
      have hz : ∀ j, raw9693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9693step0 = (fun i j => raw9693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9693step0 raw9693; decide +kernel
      have hl : raw9693step0Labels = raw9693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9693 raw9693Labels permutation434 hz
    mixedMoment B raw9693step0 raw9693step0Labels = mixedMoment B raw9693step1 raw9693step1Labels := by
      have ha : raw9693step1 = (fun i j => raw9693step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9693step1 raw9693step0; decide +kernel
      have hl : raw9693step1Labels = raw9693step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9693step0 raw9693step0Labels permutation38 permutation6
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw9694 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9694 raw9694Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw9694 raw9694Labels = mixedMoment B raw9694step0 raw9694step0Labels := by
      have hz : ∀ j, raw9694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9694step0 = (fun i j => raw9694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9694step0 raw9694; decide +kernel
      have hl : raw9694step0Labels = raw9694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9694 raw9694Labels permutation346 hz
    mixedMoment B raw9694step0 raw9694step0Labels = mixedMoment B raw9694step1 raw9694step1Labels := by
      have ha : raw9694step1 = (fun i j => raw9694step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9694step1 raw9694step0; decide +kernel
      have hl : raw9694step1Labels = raw9694step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9694step0 raw9694step0Labels permutation38 permutation6
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw9695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9695step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9695 raw9695Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw9695 raw9695Labels = mixedMoment B raw9695step0 raw9695step0Labels := by
      have hz : ∀ j, raw9695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9695step0 = (fun i j => raw9695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9695step0 raw9695; decide +kernel
      have hl : raw9695step0Labels = raw9695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9695 raw9695Labels permutation434 hz
    mixedMoment B raw9695step0 raw9695step0Labels = mixedMoment B raw9695step1 raw9695step1Labels := by
      have hz : ∀ j, raw9695step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9695step1 = (fun i j => raw9695step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9695step1 raw9695step0; decide +kernel
      have hl : raw9695step1Labels = raw9695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9695step0 raw9695step0Labels permutation80 hz
    mixedMoment B raw9695step1 raw9695step1Labels = mixedMoment B raw9695step2 raw9695step2Labels := by
      have ha : raw9695step2 = (fun i j => raw9695step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9695step2 raw9695step1; decide +kernel
      have hl : raw9695step2Labels = raw9695step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9695step1 raw9695step1Labels permutation8 permutation6
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw9696 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9696step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9696step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![1, -3, 2]]
def raw9696step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9696step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw9696step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9696 raw9696Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw9696 raw9696Labels = mixedMoment B raw9696step0 raw9696step0Labels := by
      have hz : ∀ j, raw9696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9696step0 = (fun i j => raw9696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9696step0 raw9696; decide +kernel
      have hl : raw9696step0Labels = raw9696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9696 raw9696Labels permutation434 hz
    mixedMoment B raw9696step0 raw9696step0Labels = mixedMoment B raw9696step1 raw9696step1Labels := by
      have hz : ∀ j, raw9696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9696step1 = (fun i j => raw9696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9696step1 raw9696step0; decide +kernel
      have hl : raw9696step1Labels = raw9696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9696step0 raw9696step0Labels permutation80 hz
    mixedMoment B raw9696step1 raw9696step1Labels = mixedMoment B raw9696step2 raw9696step2Labels := by
      have hz : ∀ j, raw9696step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw9696step2 = (fun i j => raw9696step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw9696step2 raw9696step1; decide +kernel
      have hl : raw9696step2Labels = raw9696step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9696step1 raw9696step1Labels permutation14 hz
    mixedMoment B raw9696step2 raw9696step2Labels = mixedMoment B raw9696step3 raw9696step3Labels := by
      have ha : raw9696step3 = (fun i j => raw9696step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9696step3 raw9696step2; decide +kernel
      have hl : raw9696step3Labels = raw9696step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9696step2 raw9696step2Labels permutation2 permutation6
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw9697 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9697 raw9697Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw9697 raw9697Labels = mixedMoment B raw9697step0 raw9697step0Labels := by
      have hz : ∀ j, raw9697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9697step0 = (fun i j => raw9697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9697step0 raw9697; decide +kernel
      have hl : raw9697step0Labels = raw9697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9697 raw9697Labels permutation434 hz
    mixedMoment B raw9697step0 raw9697step0Labels = mixedMoment B raw9697step1 raw9697step1Labels := by
      have ha : raw9697step1 = (fun i j => raw9697step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9697step1 raw9697step0; decide +kernel
      have hl : raw9697step1Labels = raw9697step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9697step0 raw9697step0Labels permutation38 permutation6
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw9698 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9698 raw9698Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw9698 raw9698Labels = mixedMoment B raw9698step0 raw9698step0Labels := by
      have hz : ∀ j, raw9698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9698step0 = (fun i j => raw9698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9698step0 raw9698; decide +kernel
      have hl : raw9698step0Labels = raw9698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9698 raw9698Labels permutation346 hz
    mixedMoment B raw9698step0 raw9698step0Labels = mixedMoment B raw9698step1 raw9698step1Labels := by
      have ha : raw9698step1 = (fun i j => raw9698step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9698step1 raw9698step0; decide +kernel
      have hl : raw9698step1Labels = raw9698step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9698step0 raw9698step0Labels permutation38 permutation6
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw9699 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9699step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw9699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9699 raw9699Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw9699 raw9699Labels = mixedMoment B raw9699step0 raw9699step0Labels := by
      have hz : ∀ j, raw9699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9699step0 = (fun i j => raw9699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9699step0 raw9699; decide +kernel
      have hl : raw9699step0Labels = raw9699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9699 raw9699Labels permutation434 hz
    mixedMoment B raw9699step0 raw9699step0Labels = mixedMoment B raw9699step1 raw9699step1Labels := by
      have hz : ∀ j, raw9699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9699step1 = (fun i j => raw9699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9699step1 raw9699step0; decide +kernel
      have hl : raw9699step1Labels = raw9699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9699step0 raw9699step0Labels permutation80 hz
    mixedMoment B raw9699step1 raw9699step1Labels = mixedMoment B raw9699step2 raw9699step2Labels := by
      have ha : raw9699step2 = (fun i j => raw9699step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9699step2 raw9699step1; decide +kernel
      have hl : raw9699step2Labels = raw9699step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9699step1 raw9699step1Labels permutation8 permutation6
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw9700 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9700step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9700step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![0, -2, 2]]
def raw9700step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9700step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw9700step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9700step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw9700step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9700 raw9700Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw9700 raw9700Labels = mixedMoment B raw9700step0 raw9700step0Labels := by
      have hz : ∀ j, raw9700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9700step0 = (fun i j => raw9700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9700step0 raw9700; decide +kernel
      have hl : raw9700step0Labels = raw9700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9700 raw9700Labels permutation434 hz
    mixedMoment B raw9700step0 raw9700step0Labels = mixedMoment B raw9700step1 raw9700step1Labels := by
      have hz : ∀ j, raw9700step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9700step1 = (fun i j => raw9700step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9700step1 raw9700step0; decide +kernel
      have hl : raw9700step1Labels = raw9700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9700step0 raw9700step0Labels permutation80 hz
    mixedMoment B raw9700step1 raw9700step1Labels = mixedMoment B raw9700step2 raw9700step2Labels := by
      have hz : ∀ j, raw9700step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw9700step2 = (fun i j => raw9700step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw9700step2 raw9700step1; decide +kernel
      have hl : raw9700step2Labels = raw9700step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9700step1 raw9700step1Labels permutation14 hz
    mixedMoment B raw9700step2 raw9700step2Labels = mixedMoment B raw9700step3 raw9700step3Labels := by
      have ha : raw9700step3 = (fun i j => raw9700step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9700step3 raw9700step2; decide +kernel
      have hl : raw9700step3Labels = raw9700step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9700step2 raw9700step2Labels permutation2 permutation7
    mixedMoment B raw9700step3 raw9700step3Labels = mixedMoment B raw9700step4 raw9700step4Labels := by
      have ha : raw9700step4 = raw9700step3 := by apply Matrix.ext; unfold raw9700step4 raw9700step3; decide +kernel
      have hl : raw9700step3Labels = labelEmbedding1 ∘ raw9700step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9700step3 raw9700step3Labels raw9700step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw9701 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9701 raw9701Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw9701 raw9701Labels = mixedMoment B raw9701step0 raw9701step0Labels := by
      have hz : ∀ j, raw9701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9701step0 = (fun i j => raw9701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9701step0 raw9701; decide +kernel
      have hl : raw9701step0Labels = raw9701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9701 raw9701Labels permutation434 hz
    mixedMoment B raw9701step0 raw9701step0Labels = mixedMoment B raw9701step1 raw9701step1Labels := by
      have ha : raw9701step1 = (fun i j => raw9701step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9701step1 raw9701step0; decide +kernel
      have hl : raw9701step1Labels = raw9701step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9701step0 raw9701step0Labels permutation32 permutation7
    mixedMoment B raw9701step1 raw9701step1Labels = mixedMoment B raw9701step2 raw9701step2Labels := by
      have ha : raw9701step2 = raw9701step1 := by apply Matrix.ext; unfold raw9701step2 raw9701step1; decide +kernel
      have hl : raw9701step1Labels = labelEmbedding1 ∘ raw9701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9701step1 raw9701step1Labels raw9701step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw9702 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9702 raw9702Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw9702 raw9702Labels = mixedMoment B raw9702step0 raw9702step0Labels := by
      have hz : ∀ j, raw9702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9702step0 = (fun i j => raw9702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9702step0 raw9702; decide +kernel
      have hl : raw9702step0Labels = raw9702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9702 raw9702Labels permutation346 hz
    mixedMoment B raw9702step0 raw9702step0Labels = mixedMoment B raw9702step1 raw9702step1Labels := by
      have ha : raw9702step1 = (fun i j => raw9702step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9702step1 raw9702step0; decide +kernel
      have hl : raw9702step1Labels = raw9702step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9702step0 raw9702step0Labels permutation32 permutation7
    mixedMoment B raw9702step1 raw9702step1Labels = mixedMoment B raw9702step2 raw9702step2Labels := by
      have ha : raw9702step2 = raw9702step1 := by apply Matrix.ext; unfold raw9702step2 raw9702step1; decide +kernel
      have hl : raw9702step1Labels = labelEmbedding1 ∘ raw9702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9702step1 raw9702step1Labels raw9702step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw9703 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9703step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9703step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9703 raw9703Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw9703 raw9703Labels = mixedMoment B raw9703step0 raw9703step0Labels := by
      have hz : ∀ j, raw9703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9703step0 = (fun i j => raw9703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9703step0 raw9703; decide +kernel
      have hl : raw9703step0Labels = raw9703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9703 raw9703Labels permutation434 hz
    mixedMoment B raw9703step0 raw9703step0Labels = mixedMoment B raw9703step1 raw9703step1Labels := by
      have hz : ∀ j, raw9703step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9703step1 = (fun i j => raw9703step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9703step1 raw9703step0; decide +kernel
      have hl : raw9703step1Labels = raw9703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9703step0 raw9703step0Labels permutation80 hz
    mixedMoment B raw9703step1 raw9703step1Labels = mixedMoment B raw9703step2 raw9703step2Labels := by
      have ha : raw9703step2 = (fun i j => raw9703step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9703step2 raw9703step1; decide +kernel
      have hl : raw9703step2Labels = raw9703step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9703step1 raw9703step1Labels permutation8 permutation7
    mixedMoment B raw9703step2 raw9703step2Labels = mixedMoment B raw9703step3 raw9703step3Labels := by
      have ha : raw9703step3 = raw9703step2 := by apply Matrix.ext; unfold raw9703step3 raw9703step2; decide +kernel
      have hl : raw9703step2Labels = labelEmbedding1 ∘ raw9703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9703step2 raw9703step2Labels raw9703step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw9704 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9704step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9704 raw9704Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw9704 raw9704Labels = mixedMoment B raw9704step0 raw9704step0Labels := by
      have hz : ∀ j, raw9704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9704step0 = (fun i j => raw9704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9704step0 raw9704; decide +kernel
      have hl : raw9704step0Labels = raw9704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9704 raw9704Labels permutation434 hz
    mixedMoment B raw9704step0 raw9704step0Labels = mixedMoment B raw9704step1 raw9704step1Labels := by
      have hz : ∀ j, raw9704step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9704step1 = (fun i j => raw9704step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9704step1 raw9704step0; decide +kernel
      have hl : raw9704step1Labels = raw9704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9704step0 raw9704step0Labels permutation80 hz
    mixedMoment B raw9704step1 raw9704step1Labels = mixedMoment B raw9704step2 raw9704step2Labels := by
      have ha : raw9704step2 = (fun i j => raw9704step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9704step2 raw9704step1; decide +kernel
      have hl : raw9704step2Labels = raw9704step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9704step1 raw9704step1Labels permutation8 permutation7
    mixedMoment B raw9704step2 raw9704step2Labels = mixedMoment B raw9704step3 raw9704step3Labels := by
      have ha : raw9704step3 = raw9704step2 := by apply Matrix.ext; unfold raw9704step3 raw9704step2; decide +kernel
      have hl : raw9704step2Labels = labelEmbedding1 ∘ raw9704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9704step2 raw9704step2Labels raw9704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw9705 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9705step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw9705step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw9705step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9705step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw9705step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9705 raw9705Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw9705 raw9705Labels = mixedMoment B raw9705step0 raw9705step0Labels := by
      have hz : ∀ j, raw9705 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9705step0 = (fun i j => raw9705 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9705step0 raw9705; decide +kernel
      have hl : raw9705step0Labels = raw9705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9705 raw9705Labels permutation434 hz
    mixedMoment B raw9705step0 raw9705step0Labels = mixedMoment B raw9705step1 raw9705step1Labels := by
      have hz : ∀ j, raw9705step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9705step1 = (fun i j => raw9705step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9705step1 raw9705step0; decide +kernel
      have hl : raw9705step1Labels = raw9705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9705step0 raw9705step0Labels permutation80 hz
    mixedMoment B raw9705step1 raw9705step1Labels = mixedMoment B raw9705step2 raw9705step2Labels := by
      have ha : raw9705step2 = (fun i j => raw9705step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9705step2 raw9705step1; decide +kernel
      have hl : raw9705step2Labels = raw9705step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9705step1 raw9705step1Labels permutation11 permutation5
    mixedMoment B raw9705step2 raw9705step2Labels = mixedMoment B raw9705step3 raw9705step3Labels := by
      have ha : raw9705step3 = -raw9705step2 := by apply Matrix.ext; change ∀ i j, raw9705step3 i j = -(raw9705step2 i j); unfold raw9705step3 raw9705step2; decide +kernel
      have hl : raw9705step3Labels = raw9705step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9705step3 raw9705step3Labels = mixedMoment B raw9705step4 raw9705step4Labels := by
      have ha : raw9705step4 = raw9705step3 := by apply Matrix.ext; unfold raw9705step4 raw9705step3; decide +kernel
      have hl : raw9705step3Labels = labelEmbedding1 ∘ raw9705step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9705step3 raw9705step3Labels raw9705step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3187 node3187Labels := by rfl

def raw9706 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9706 raw9706Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw9706 raw9706Labels = mixedMoment B raw9706step0 raw9706step0Labels := by
      have hz : ∀ j, raw9706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9706step0 = (fun i j => raw9706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9706step0 raw9706; decide +kernel
      have hl : raw9706step0Labels = raw9706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9706 raw9706Labels permutation434 hz
    mixedMoment B raw9706step0 raw9706step0Labels = mixedMoment B raw9706step1 raw9706step1Labels := by
      have ha : raw9706step1 = (fun i j => raw9706step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9706step1 raw9706step0; decide +kernel
      have hl : raw9706step1Labels = raw9706step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9706step0 raw9706step0Labels permutation32 permutation7
    mixedMoment B raw9706step1 raw9706step1Labels = mixedMoment B raw9706step2 raw9706step2Labels := by
      have ha : raw9706step2 = raw9706step1 := by apply Matrix.ext; unfold raw9706step2 raw9706step1; decide +kernel
      have hl : raw9706step1Labels = labelEmbedding1 ∘ raw9706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9706step1 raw9706step1Labels raw9706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw9707 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9707 raw9707Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw9707 raw9707Labels = mixedMoment B raw9707step0 raw9707step0Labels := by
      have hz : ∀ j, raw9707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9707step0 = (fun i j => raw9707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9707step0 raw9707; decide +kernel
      have hl : raw9707step0Labels = raw9707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9707 raw9707Labels permutation346 hz
    mixedMoment B raw9707step0 raw9707step0Labels = mixedMoment B raw9707step1 raw9707step1Labels := by
      have ha : raw9707step1 = (fun i j => raw9707step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9707step1 raw9707step0; decide +kernel
      have hl : raw9707step1Labels = raw9707step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9707step0 raw9707step0Labels permutation32 permutation7
    mixedMoment B raw9707step1 raw9707step1Labels = mixedMoment B raw9707step2 raw9707step2Labels := by
      have ha : raw9707step2 = raw9707step1 := by apply Matrix.ext; unfold raw9707step2 raw9707step1; decide +kernel
      have hl : raw9707step1Labels = labelEmbedding1 ∘ raw9707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9707step1 raw9707step1Labels raw9707step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw9708 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9708step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw9708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw9708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9708 raw9708Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw9708 raw9708Labels = mixedMoment B raw9708step0 raw9708step0Labels := by
      have hz : ∀ j, raw9708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9708step0 = (fun i j => raw9708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9708step0 raw9708; decide +kernel
      have hl : raw9708step0Labels = raw9708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9708 raw9708Labels permutation434 hz
    mixedMoment B raw9708step0 raw9708step0Labels = mixedMoment B raw9708step1 raw9708step1Labels := by
      have hz : ∀ j, raw9708step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9708step1 = (fun i j => raw9708step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9708step1 raw9708step0; decide +kernel
      have hl : raw9708step1Labels = raw9708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9708step0 raw9708step0Labels permutation80 hz
    mixedMoment B raw9708step1 raw9708step1Labels = mixedMoment B raw9708step2 raw9708step2Labels := by
      have ha : raw9708step2 = (fun i j => raw9708step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9708step2 raw9708step1; decide +kernel
      have hl : raw9708step2Labels = raw9708step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9708step1 raw9708step1Labels permutation8 permutation7
    mixedMoment B raw9708step2 raw9708step2Labels = mixedMoment B raw9708step3 raw9708step3Labels := by
      have ha : raw9708step3 = raw9708step2 := by apply Matrix.ext; unfold raw9708step3 raw9708step2; decide +kernel
      have hl : raw9708step2Labels = labelEmbedding1 ∘ raw9708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9708step2 raw9708step2Labels raw9708step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3056 node3056Labels := by rfl

def raw9709 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9709step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw9709step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw9709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9709 raw9709Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw9709 raw9709Labels = mixedMoment B raw9709step0 raw9709step0Labels := by
      have hz : ∀ j, raw9709 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9709step0 = (fun i j => raw9709 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9709step0 raw9709; decide +kernel
      have hl : raw9709step0Labels = raw9709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9709 raw9709Labels permutation434 hz
    mixedMoment B raw9709step0 raw9709step0Labels = mixedMoment B raw9709step1 raw9709step1Labels := by
      have hz : ∀ j, raw9709step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9709step1 = (fun i j => raw9709step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9709step1 raw9709step0; decide +kernel
      have hl : raw9709step1Labels = raw9709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9709step0 raw9709step0Labels permutation80 hz
    mixedMoment B raw9709step1 raw9709step1Labels = mixedMoment B raw9709step2 raw9709step2Labels := by
      have ha : raw9709step2 = (fun i j => raw9709step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9709step2 raw9709step1; decide +kernel
      have hl : raw9709step2Labels = raw9709step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9709step1 raw9709step1Labels permutation8 permutation7
    mixedMoment B raw9709step2 raw9709step2Labels = mixedMoment B raw9709step3 raw9709step3Labels := by
      have ha : raw9709step3 = raw9709step2 := by apply Matrix.ext; unfold raw9709step3 raw9709step2; decide +kernel
      have hl : raw9709step2Labels = labelEmbedding1 ∘ raw9709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9709step2 raw9709step2Labels raw9709step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw9710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9710 raw9710Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw9710 raw9710Labels = mixedMoment B raw9710step0 raw9710step0Labels := by
      have hz : ∀ j, raw9710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9710step0 = (fun i j => raw9710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9710step0 raw9710; decide +kernel
      have hl : raw9710step0Labels = raw9710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9710 raw9710Labels permutation434 hz
    mixedMoment B raw9710step0 raw9710step0Labels = mixedMoment B raw9710step1 raw9710step1Labels := by
      have ha : raw9710step1 = (fun i j => raw9710step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9710step1 raw9710step0; decide +kernel
      have hl : raw9710step1Labels = raw9710step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9710step0 raw9710step0Labels permutation44 permutation5
    mixedMoment B raw9710step1 raw9710step1Labels = mixedMoment B raw9710step2 raw9710step2Labels := by
      have ha : raw9710step2 = -raw9710step1 := by apply Matrix.ext; change ∀ i j, raw9710step2 i j = -(raw9710step1 i j); unfold raw9710step2 raw9710step1; decide +kernel
      have hl : raw9710step2Labels = raw9710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9710step2 raw9710step2Labels = mixedMoment B raw9710step3 raw9710step3Labels := by
      have ha : raw9710step3 = raw9710step2 := by apply Matrix.ext; unfold raw9710step3 raw9710step2; decide +kernel
      have hl : raw9710step2Labels = labelEmbedding1 ∘ raw9710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9710step2 raw9710step2Labels raw9710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw9711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9711step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9711 raw9711Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw9711 raw9711Labels = mixedMoment B raw9711step0 raw9711step0Labels := by
      have ha : raw9711step0 = (fun i j => raw9711 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9711step0 raw9711; decide +kernel
      have hl : raw9711step0Labels = raw9711Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9711 raw9711Labels permutation152 permutation7
    mixedMoment B raw9711step0 raw9711step0Labels = mixedMoment B raw9711step1 raw9711step1Labels := by
      have ha : raw9711step1 = raw9711step0 := by apply Matrix.ext; unfold raw9711step1 raw9711step0; decide +kernel
      have hl : raw9711step0Labels = labelEmbedding1 ∘ raw9711step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9711step0 raw9711step0Labels raw9711step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3066 node3066Labels := by rfl

def raw9712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9712 raw9712Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw9712 raw9712Labels = mixedMoment B raw9712step0 raw9712step0Labels := by
      have hz : ∀ j, raw9712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9712step0 = (fun i j => raw9712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9712step0 raw9712; decide +kernel
      have hl : raw9712step0Labels = raw9712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9712 raw9712Labels permutation434 hz
    mixedMoment B raw9712step0 raw9712step0Labels = mixedMoment B raw9712step1 raw9712step1Labels := by
      have ha : raw9712step1 = (fun i j => raw9712step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9712step1 raw9712step0; decide +kernel
      have hl : raw9712step1Labels = raw9712step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9712step0 raw9712step0Labels permutation32 permutation7
    mixedMoment B raw9712step1 raw9712step1Labels = mixedMoment B raw9712step2 raw9712step2Labels := by
      have ha : raw9712step2 = raw9712step1 := by apply Matrix.ext; unfold raw9712step2 raw9712step1; decide +kernel
      have hl : raw9712step1Labels = labelEmbedding1 ∘ raw9712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9712step1 raw9712step1Labels raw9712step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw9713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9713 raw9713Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw9713 raw9713Labels = mixedMoment B raw9713step0 raw9713step0Labels := by
      have hz : ∀ j, raw9713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9713step0 = (fun i j => raw9713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9713step0 raw9713; decide +kernel
      have hl : raw9713step0Labels = raw9713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9713 raw9713Labels permutation346 hz
    mixedMoment B raw9713step0 raw9713step0Labels = mixedMoment B raw9713step1 raw9713step1Labels := by
      have ha : raw9713step1 = (fun i j => raw9713step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9713step1 raw9713step0; decide +kernel
      have hl : raw9713step1Labels = raw9713step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9713step0 raw9713step0Labels permutation44 permutation5
    mixedMoment B raw9713step1 raw9713step1Labels = mixedMoment B raw9713step2 raw9713step2Labels := by
      have ha : raw9713step2 = -raw9713step1 := by apply Matrix.ext; change ∀ i j, raw9713step2 i j = -(raw9713step1 i j); unfold raw9713step2 raw9713step1; decide +kernel
      have hl : raw9713step2Labels = raw9713step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9713step2 raw9713step2Labels = mixedMoment B raw9713step3 raw9713step3Labels := by
      have ha : raw9713step3 = raw9713step2 := by apply Matrix.ext; unfold raw9713step3 raw9713step2; decide +kernel
      have hl : raw9713step2Labels = labelEmbedding1 ∘ raw9713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9713step2 raw9713step2Labels raw9713step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw9714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9714 raw9714Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw9714 raw9714Labels = mixedMoment B raw9714step0 raw9714step0Labels := by
      have ha : raw9714step0 = (fun i j => raw9714 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9714step0 raw9714; decide +kernel
      have hl : raw9714step0Labels = raw9714Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9714 raw9714Labels permutation158 permutation7
    mixedMoment B raw9714step0 raw9714step0Labels = mixedMoment B raw9714step1 raw9714step1Labels := by
      have ha : raw9714step1 = raw9714step0 := by apply Matrix.ext; unfold raw9714step1 raw9714step0; decide +kernel
      have hl : raw9714step0Labels = labelEmbedding1 ∘ raw9714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9714step0 raw9714step0Labels raw9714step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3066 node3066Labels := by rfl

def raw9715 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9715 raw9715Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw9715 raw9715Labels = mixedMoment B raw9715step0 raw9715step0Labels := by
      have hz : ∀ j, raw9715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9715step0 = (fun i j => raw9715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9715step0 raw9715; decide +kernel
      have hl : raw9715step0Labels = raw9715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9715 raw9715Labels permutation346 hz
    mixedMoment B raw9715step0 raw9715step0Labels = mixedMoment B raw9715step1 raw9715step1Labels := by
      have ha : raw9715step1 = (fun i j => raw9715step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9715step1 raw9715step0; decide +kernel
      have hl : raw9715step1Labels = raw9715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9715step0 raw9715step0Labels permutation32 permutation7
    mixedMoment B raw9715step1 raw9715step1Labels = mixedMoment B raw9715step2 raw9715step2Labels := by
      have ha : raw9715step2 = raw9715step1 := by apply Matrix.ext; unfold raw9715step2 raw9715step1; decide +kernel
      have hl : raw9715step1Labels = labelEmbedding1 ∘ raw9715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9715step1 raw9715step1Labels raw9715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw9716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9716step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9716step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw9716step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9716step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw9716step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9716 raw9716Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw9716 raw9716Labels = mixedMoment B raw9716step0 raw9716step0Labels := by
      have hz : ∀ j, raw9716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9716step0 = (fun i j => raw9716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9716step0 raw9716; decide +kernel
      have hl : raw9716step0Labels = raw9716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9716 raw9716Labels permutation434 hz
    mixedMoment B raw9716step0 raw9716step0Labels = mixedMoment B raw9716step1 raw9716step1Labels := by
      have hz : ∀ j, raw9716step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9716step1 = (fun i j => raw9716step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9716step1 raw9716step0; decide +kernel
      have hl : raw9716step1Labels = raw9716step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9716step0 raw9716step0Labels permutation80 hz
    mixedMoment B raw9716step1 raw9716step1Labels = mixedMoment B raw9716step2 raw9716step2Labels := by
      have ha : raw9716step2 = (fun i j => raw9716step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9716step2 raw9716step1; decide +kernel
      have hl : raw9716step2Labels = raw9716step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9716step1 raw9716step1Labels permutation10 permutation5
    mixedMoment B raw9716step2 raw9716step2Labels = mixedMoment B raw9716step3 raw9716step3Labels := by
      have ha : raw9716step3 = -raw9716step2 := by apply Matrix.ext; change ∀ i j, raw9716step3 i j = -(raw9716step2 i j); unfold raw9716step3 raw9716step2; decide +kernel
      have hl : raw9716step3Labels = raw9716step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9716step3 raw9716step3Labels = mixedMoment B raw9716step4 raw9716step4Labels := by
      have ha : raw9716step4 = raw9716step3 := by apply Matrix.ext; unfold raw9716step4 raw9716step3; decide +kernel
      have hl : raw9716step3Labels = labelEmbedding1 ∘ raw9716step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9716step3 raw9716step3Labels raw9716step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw9717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9717 raw9717Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw9717 raw9717Labels = mixedMoment B raw9717step0 raw9717step0Labels := by
      have hz : ∀ j, raw9717 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9717step0 = (fun i j => raw9717 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9717step0 raw9717; decide +kernel
      have hl : raw9717step0Labels = raw9717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9717 raw9717Labels permutation434 hz
    mixedMoment B raw9717step0 raw9717step0Labels = mixedMoment B raw9717step1 raw9717step1Labels := by
      have ha : raw9717step1 = (fun i j => raw9717step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9717step1 raw9717step0; decide +kernel
      have hl : raw9717step1Labels = raw9717step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9717step0 raw9717step0Labels permutation32 permutation7
    mixedMoment B raw9717step1 raw9717step1Labels = mixedMoment B raw9717step2 raw9717step2Labels := by
      have ha : raw9717step2 = raw9717step1 := by apply Matrix.ext; unfold raw9717step2 raw9717step1; decide +kernel
      have hl : raw9717step1Labels = labelEmbedding1 ∘ raw9717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9717step1 raw9717step1Labels raw9717step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw9718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9718 raw9718Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw9718 raw9718Labels = mixedMoment B raw9718step0 raw9718step0Labels := by
      have hz : ∀ j, raw9718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9718step0 = (fun i j => raw9718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9718step0 raw9718; decide +kernel
      have hl : raw9718step0Labels = raw9718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9718 raw9718Labels permutation346 hz
    mixedMoment B raw9718step0 raw9718step0Labels = mixedMoment B raw9718step1 raw9718step1Labels := by
      have ha : raw9718step1 = (fun i j => raw9718step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9718step1 raw9718step0; decide +kernel
      have hl : raw9718step1Labels = raw9718step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9718step0 raw9718step0Labels permutation32 permutation7
    mixedMoment B raw9718step1 raw9718step1Labels = mixedMoment B raw9718step2 raw9718step2Labels := by
      have ha : raw9718step2 = raw9718step1 := by apply Matrix.ext; unfold raw9718step2 raw9718step1; decide +kernel
      have hl : raw9718step1Labels = labelEmbedding1 ∘ raw9718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9718step1 raw9718step1Labels raw9718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw9719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9719step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9719step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9719step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9719 raw9719Labels = mixedMoment B node2966 node2966Labels := by
  calc
    mixedMoment B raw9719 raw9719Labels = mixedMoment B raw9719step0 raw9719step0Labels := by
      have hz : ∀ j, raw9719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9719step0 = (fun i j => raw9719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9719step0 raw9719; decide +kernel
      have hl : raw9719step0Labels = raw9719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9719 raw9719Labels permutation434 hz
    mixedMoment B raw9719step0 raw9719step0Labels = mixedMoment B raw9719step1 raw9719step1Labels := by
      have hz : ∀ j, raw9719step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9719step1 = (fun i j => raw9719step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9719step1 raw9719step0; decide +kernel
      have hl : raw9719step1Labels = raw9719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9719step0 raw9719step0Labels permutation80 hz
    mixedMoment B raw9719step1 raw9719step1Labels = mixedMoment B raw9719step2 raw9719step2Labels := by
      have ha : raw9719step2 = (fun i j => raw9719step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9719step2 raw9719step1; decide +kernel
      have hl : raw9719step2Labels = raw9719step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9719step1 raw9719step1Labels permutation29 permutation5
    mixedMoment B raw9719step2 raw9719step2Labels = mixedMoment B raw9719step3 raw9719step3Labels := by
      have ha : raw9719step3 = raw9719step2 := by apply Matrix.ext; unfold raw9719step3 raw9719step2; decide +kernel
      have hl : raw9719step2Labels = labelEmbedding1 ∘ raw9719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9719step2 raw9719step2Labels raw9719step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2966 node2966Labels := by rfl

def raw9720 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9720step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9720step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![1, -3, 2]]
def raw9720step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9720step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw9720step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9720step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw9720step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9720 raw9720Labels = mixedMoment B node3125 node3125Labels := by
  calc
    mixedMoment B raw9720 raw9720Labels = mixedMoment B raw9720step0 raw9720step0Labels := by
      have hz : ∀ j, raw9720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9720step0 = (fun i j => raw9720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9720step0 raw9720; decide +kernel
      have hl : raw9720step0Labels = raw9720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9720 raw9720Labels permutation434 hz
    mixedMoment B raw9720step0 raw9720step0Labels = mixedMoment B raw9720step1 raw9720step1Labels := by
      have hz : ∀ j, raw9720step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9720step1 = (fun i j => raw9720step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9720step1 raw9720step0; decide +kernel
      have hl : raw9720step1Labels = raw9720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9720step0 raw9720step0Labels permutation80 hz
    mixedMoment B raw9720step1 raw9720step1Labels = mixedMoment B raw9720step2 raw9720step2Labels := by
      have hz : ∀ j, raw9720step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw9720step2 = (fun i j => raw9720step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw9720step2 raw9720step1; decide +kernel
      have hl : raw9720step2Labels = raw9720step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9720step1 raw9720step1Labels permutation14 hz
    mixedMoment B raw9720step2 raw9720step2Labels = mixedMoment B raw9720step3 raw9720step3Labels := by
      have ha : raw9720step3 = (fun i j => raw9720step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9720step3 raw9720step2; decide +kernel
      have hl : raw9720step3Labels = raw9720step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9720step2 raw9720step2Labels permutation7 permutation5
    mixedMoment B raw9720step3 raw9720step3Labels = mixedMoment B raw9720step4 raw9720step4Labels := by
      have ha : raw9720step4 = raw9720step3 := by apply Matrix.ext; unfold raw9720step4 raw9720step3; decide +kernel
      have hl : raw9720step3Labels = labelEmbedding1 ∘ raw9720step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9720step3 raw9720step3Labels raw9720step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3125 node3125Labels := by rfl

def raw9721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9721 raw9721Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw9721 raw9721Labels = mixedMoment B raw9721step0 raw9721step0Labels := by
      have hz : ∀ j, raw9721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9721step0 = (fun i j => raw9721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9721step0 raw9721; decide +kernel
      have hl : raw9721step0Labels = raw9721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9721 raw9721Labels permutation434 hz
    mixedMoment B raw9721step0 raw9721step0Labels = mixedMoment B raw9721step1 raw9721step1Labels := by
      have ha : raw9721step1 = (fun i j => raw9721step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9721step1 raw9721step0; decide +kernel
      have hl : raw9721step1Labels = raw9721step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9721step0 raw9721step0Labels permutation137 permutation5
    mixedMoment B raw9721step1 raw9721step1Labels = mixedMoment B raw9721step2 raw9721step2Labels := by
      have ha : raw9721step2 = raw9721step1 := by apply Matrix.ext; unfold raw9721step2 raw9721step1; decide +kernel
      have hl : raw9721step1Labels = labelEmbedding1 ∘ raw9721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9721step1 raw9721step1Labels raw9721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw9722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9722 raw9722Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw9722 raw9722Labels = mixedMoment B raw9722step0 raw9722step0Labels := by
      have hz : ∀ j, raw9722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9722step0 = (fun i j => raw9722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9722step0 raw9722; decide +kernel
      have hl : raw9722step0Labels = raw9722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9722 raw9722Labels permutation346 hz
    mixedMoment B raw9722step0 raw9722step0Labels = mixedMoment B raw9722step1 raw9722step1Labels := by
      have ha : raw9722step1 = (fun i j => raw9722step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9722step1 raw9722step0; decide +kernel
      have hl : raw9722step1Labels = raw9722step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9722step0 raw9722step0Labels permutation137 permutation5
    mixedMoment B raw9722step1 raw9722step1Labels = mixedMoment B raw9722step2 raw9722step2Labels := by
      have ha : raw9722step2 = raw9722step1 := by apply Matrix.ext; unfold raw9722step2 raw9722step1; decide +kernel
      have hl : raw9722step1Labels = labelEmbedding1 ∘ raw9722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9722step1 raw9722step1Labels raw9722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw9723 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw9723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw9723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9723 raw9723Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw9723 raw9723Labels = mixedMoment B raw9723step0 raw9723step0Labels := by
      have hz : ∀ j, raw9723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9723step0 = (fun i j => raw9723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9723step0 raw9723; decide +kernel
      have hl : raw9723step0Labels = raw9723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9723 raw9723Labels permutation434 hz
    mixedMoment B raw9723step0 raw9723step0Labels = mixedMoment B raw9723step1 raw9723step1Labels := by
      have hz : ∀ j, raw9723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9723step1 = (fun i j => raw9723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9723step1 raw9723step0; decide +kernel
      have hl : raw9723step1Labels = raw9723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9723step0 raw9723step0Labels permutation80 hz
    mixedMoment B raw9723step1 raw9723step1Labels = mixedMoment B raw9723step2 raw9723step2Labels := by
      have ha : raw9723step2 = (fun i j => raw9723step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9723step2 raw9723step1; decide +kernel
      have hl : raw9723step2Labels = raw9723step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9723step1 raw9723step1Labels permutation28 permutation5
    mixedMoment B raw9723step2 raw9723step2Labels = mixedMoment B raw9723step3 raw9723step3Labels := by
      have ha : raw9723step3 = raw9723step2 := by apply Matrix.ext; unfold raw9723step3 raw9723step2; decide +kernel
      have hl : raw9723step2Labels = labelEmbedding1 ∘ raw9723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9723step2 raw9723step2Labels raw9723step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw9724 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9724step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9724 raw9724Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw9724 raw9724Labels = mixedMoment B raw9724step0 raw9724step0Labels := by
      have hz : ∀ j, raw9724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9724step0 = (fun i j => raw9724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9724step0 raw9724; decide +kernel
      have hl : raw9724step0Labels = raw9724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9724 raw9724Labels permutation434 hz
    mixedMoment B raw9724step0 raw9724step0Labels = mixedMoment B raw9724step1 raw9724step1Labels := by
      have hz : ∀ j, raw9724step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9724step1 = (fun i j => raw9724step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9724step1 raw9724step0; decide +kernel
      have hl : raw9724step1Labels = raw9724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9724step0 raw9724step0Labels permutation80 hz
    mixedMoment B raw9724step1 raw9724step1Labels = mixedMoment B raw9724step2 raw9724step2Labels := by
      have ha : raw9724step2 = (fun i j => raw9724step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9724step2 raw9724step1; decide +kernel
      have hl : raw9724step2Labels = raw9724step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9724step1 raw9724step1Labels permutation10 permutation4
    mixedMoment B raw9724step2 raw9724step2Labels = mixedMoment B raw9724step3 raw9724step3Labels := by
      have ha : raw9724step3 = -raw9724step2 := by apply Matrix.ext; change ∀ i j, raw9724step3 i j = -(raw9724step2 i j); unfold raw9724step3 raw9724step2; decide +kernel
      have hl : raw9724step3Labels = raw9724step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw9725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw9725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9725 raw9725Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw9725 raw9725Labels = mixedMoment B raw9725step0 raw9725step0Labels := by
      have hz : ∀ j, raw9725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9725step0 = (fun i j => raw9725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9725step0 raw9725; decide +kernel
      have hl : raw9725step0Labels = raw9725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9725 raw9725Labels permutation434 hz
    mixedMoment B raw9725step0 raw9725step0Labels = mixedMoment B raw9725step1 raw9725step1Labels := by
      have hz : ∀ j, raw9725step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9725step1 = (fun i j => raw9725step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9725step1 raw9725step0; decide +kernel
      have hl : raw9725step1Labels = raw9725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9725step0 raw9725step0Labels permutation80 hz
    mixedMoment B raw9725step1 raw9725step1Labels = mixedMoment B raw9725step2 raw9725step2Labels := by
      have ha : raw9725step2 = (fun i j => raw9725step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9725step2 raw9725step1; decide +kernel
      have hl : raw9725step2Labels = raw9725step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9725step1 raw9725step1Labels permutation10 permutation4
    mixedMoment B raw9725step2 raw9725step2Labels = mixedMoment B raw9725step3 raw9725step3Labels := by
      have ha : raw9725step3 = -raw9725step2 := by apply Matrix.ext; change ∀ i j, raw9725step3 i j = -(raw9725step2 i j); unfold raw9725step3 raw9725step2; decide +kernel
      have hl : raw9725step3Labels = raw9725step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw9726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9726 raw9726Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw9726 raw9726Labels = mixedMoment B raw9726step0 raw9726step0Labels := by
      have hz : ∀ j, raw9726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9726step0 = (fun i j => raw9726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9726step0 raw9726; decide +kernel
      have hl : raw9726step0Labels = raw9726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9726 raw9726Labels permutation434 hz
    mixedMoment B raw9726step0 raw9726step0Labels = mixedMoment B raw9726step1 raw9726step1Labels := by
      have ha : raw9726step1 = (fun i j => raw9726step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9726step1 raw9726step0; decide +kernel
      have hl : raw9726step1Labels = raw9726step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9726step0 raw9726step0Labels permutation44 permutation4
    mixedMoment B raw9726step1 raw9726step1Labels = mixedMoment B raw9726step2 raw9726step2Labels := by
      have ha : raw9726step2 = -raw9726step1 := by apply Matrix.ext; change ∀ i j, raw9726step2 i j = -(raw9726step1 i j); unfold raw9726step2 raw9726step1; decide +kernel
      have hl : raw9726step2Labels = raw9726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw9727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9727 raw9727Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw9727 raw9727Labels = mixedMoment B raw9727step0 raw9727step0Labels := by
      have hz : ∀ j, raw9727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9727step0 = (fun i j => raw9727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9727step0 raw9727; decide +kernel
      have hl : raw9727step0Labels = raw9727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9727 raw9727Labels permutation346 hz
    mixedMoment B raw9727step0 raw9727step0Labels = mixedMoment B raw9727step1 raw9727step1Labels := by
      have ha : raw9727step1 = (fun i j => raw9727step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9727step1 raw9727step0; decide +kernel
      have hl : raw9727step1Labels = raw9727step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9727step0 raw9727step0Labels permutation44 permutation4
    mixedMoment B raw9727step1 raw9727step1Labels = mixedMoment B raw9727step2 raw9727step2Labels := by
      have ha : raw9727step2 = -raw9727step1 := by apply Matrix.ext; change ∀ i j, raw9727step2 i j = -(raw9727step1 i j); unfold raw9727step2 raw9727step1; decide +kernel
      have hl : raw9727step2Labels = raw9727step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2106 node2106Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
