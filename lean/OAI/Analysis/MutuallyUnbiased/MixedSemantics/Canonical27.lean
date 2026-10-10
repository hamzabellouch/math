import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3456step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3456 raw3456Labels = mixedMoment B node4484 node4484Labels := by
  calc
    mixedMoment B raw3456 raw3456Labels = mixedMoment B raw3456step0 raw3456step0Labels := by
      have hz : ∀ j, raw3456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3456step0 = (fun i j => raw3456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3456step0 raw3456; decide +kernel
      have hl : raw3456step0Labels = raw3456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3456 raw3456Labels permutation434 hz
    mixedMoment B raw3456step0 raw3456step0Labels = mixedMoment B raw3456step1 raw3456step1Labels := by
      have hz : ∀ j, raw3456step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3456step1 = (fun i j => raw3456step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3456step1 raw3456step0; decide +kernel
      have hl : raw3456step1Labels = raw3456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3456step0 raw3456step0Labels permutation80 hz
    mixedMoment B raw3456step1 raw3456step1Labels = mixedMoment B raw3456step2 raw3456step2Labels := by
      have ha : raw3456step2 = (fun i j => raw3456step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3456step2 raw3456step1; decide +kernel
      have hl : raw3456step2Labels = raw3456step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3456step1 raw3456step1Labels permutation10 permutation2
    _ = mixedMoment B node4484 node4484Labels := by rfl

def raw3457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3457step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3457step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3457step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3457step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3457 raw3457Labels = mixedMoment B node4751 node4751Labels := by
  calc
    mixedMoment B raw3457 raw3457Labels = mixedMoment B raw3457step0 raw3457step0Labels := by
      have hz : ∀ j, raw3457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3457step0 = (fun i j => raw3457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3457step0 raw3457; decide +kernel
      have hl : raw3457step0Labels = raw3457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3457 raw3457Labels permutation434 hz
    mixedMoment B raw3457step0 raw3457step0Labels = mixedMoment B raw3457step1 raw3457step1Labels := by
      have ha : raw3457step1 = (fun i j => raw3457step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3457step1 raw3457step0; decide +kernel
      have hl : raw3457step1Labels = raw3457step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3457step0 raw3457step0Labels permutation139 permutation3
    mixedMoment B raw3457step1 raw3457step1Labels = mixedMoment B raw3457step2 raw3457step2Labels := by
      have ha : raw3457step2 = -raw3457step1 := by apply Matrix.ext; change ∀ i j, raw3457step2 i j = -(raw3457step1 i j); unfold raw3457step2 raw3457step1; decide +kernel
      have hl : raw3457step2Labels = raw3457step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3457step2 raw3457step2Labels = mixedMoment B raw3457step3 raw3457step3Labels := by
      have ha : raw3457step3 = raw3457step2 := by apply Matrix.ext; unfold raw3457step3 raw3457step2; decide +kernel
      have hl : raw3457step2Labels = labelEmbedding6 ∘ raw3457step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3457step2 raw3457step2Labels raw3457step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4751 node4751Labels := by rfl

def raw3458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3458step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3458step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3458step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3458step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3458 raw3458Labels = mixedMoment B node4751 node4751Labels := by
  calc
    mixedMoment B raw3458 raw3458Labels = mixedMoment B raw3458step0 raw3458step0Labels := by
      have hz : ∀ j, raw3458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3458step0 = (fun i j => raw3458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3458step0 raw3458; decide +kernel
      have hl : raw3458step0Labels = raw3458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3458 raw3458Labels permutation346 hz
    mixedMoment B raw3458step0 raw3458step0Labels = mixedMoment B raw3458step1 raw3458step1Labels := by
      have ha : raw3458step1 = (fun i j => raw3458step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3458step1 raw3458step0; decide +kernel
      have hl : raw3458step1Labels = raw3458step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3458step0 raw3458step0Labels permutation139 permutation3
    mixedMoment B raw3458step1 raw3458step1Labels = mixedMoment B raw3458step2 raw3458step2Labels := by
      have ha : raw3458step2 = -raw3458step1 := by apply Matrix.ext; change ∀ i j, raw3458step2 i j = -(raw3458step1 i j); unfold raw3458step2 raw3458step1; decide +kernel
      have hl : raw3458step2Labels = raw3458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3458step2 raw3458step2Labels = mixedMoment B raw3458step3 raw3458step3Labels := by
      have ha : raw3458step3 = raw3458step2 := by apply Matrix.ext; unfold raw3458step3 raw3458step2; decide +kernel
      have hl : raw3458step2Labels = labelEmbedding6 ∘ raw3458step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3458step2 raw3458step2Labels raw3458step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4751 node4751Labels := by rfl

def raw3459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3459step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3459step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-3, 3, 0]]
def raw3459step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3459step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3459step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3459step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3459step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3459 raw3459Labels = mixedMoment B node4484 node4484Labels := by
  calc
    mixedMoment B raw3459 raw3459Labels = mixedMoment B raw3459step0 raw3459step0Labels := by
      have hz : ∀ j, raw3459 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3459step0 = (fun i j => raw3459 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3459step0 raw3459; decide +kernel
      have hl : raw3459step0Labels = raw3459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3459 raw3459Labels permutation434 hz
    mixedMoment B raw3459step0 raw3459step0Labels = mixedMoment B raw3459step1 raw3459step1Labels := by
      have hz : ∀ j, raw3459step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3459step1 = (fun i j => raw3459step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3459step1 raw3459step0; decide +kernel
      have hl : raw3459step1Labels = raw3459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3459step0 raw3459step0Labels permutation80 hz
    mixedMoment B raw3459step1 raw3459step1Labels = mixedMoment B raw3459step2 raw3459step2Labels := by
      have ha : raw3459step2 = (fun i j => raw3459step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3459step2 raw3459step1; decide +kernel
      have hl : raw3459step2Labels = raw3459step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3459step1 raw3459step1Labels permutation20 permutation4
    mixedMoment B raw3459step2 raw3459step2Labels = mixedMoment B raw3459step3 raw3459step3Labels := by
      have ha : raw3459step3 = -raw3459step2 := by apply Matrix.ext; change ∀ i j, raw3459step3 i j = -(raw3459step2 i j); unfold raw3459step3 raw3459step2; decide +kernel
      have hl : raw3459step3Labels = raw3459step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3459step3 raw3459step3Labels = mixedMoment B raw3459step4 raw3459step4Labels := by
      have ha : raw3459step4 = raw3459step3 := by apply Matrix.ext; unfold raw3459step4 raw3459step3; decide +kernel
      have hl : raw3459step3Labels = labelEmbedding7 ∘ raw3459step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3459step3 raw3459step3Labels raw3459step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4484 node4484Labels := by rfl

def raw3460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3460step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3460step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3460step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3460 raw3460Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw3460 raw3460Labels = mixedMoment B raw3460step0 raw3460step0Labels := by
      have hz : ∀ j, raw3460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3460step0 = (fun i j => raw3460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3460step0 raw3460; decide +kernel
      have hl : raw3460step0Labels = raw3460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3460 raw3460Labels permutation434 hz
    mixedMoment B raw3460step0 raw3460step0Labels = mixedMoment B raw3460step1 raw3460step1Labels := by
      have hz : ∀ j, raw3460step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3460step1 = (fun i j => raw3460step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3460step1 raw3460step0; decide +kernel
      have hl : raw3460step1Labels = raw3460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3460step0 raw3460step0Labels permutation80 hz
    mixedMoment B raw3460step1 raw3460step1Labels = mixedMoment B raw3460step2 raw3460step2Labels := by
      have ha : raw3460step2 = (fun i j => raw3460step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3460step2 raw3460step1; decide +kernel
      have hl : raw3460step2Labels = raw3460step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3460step1 raw3460step1Labels permutation23 permutation6
    mixedMoment B raw3460step2 raw3460step2Labels = mixedMoment B raw3460step3 raw3460step3Labels := by
      have ha : raw3460step3 = raw3460step2 := by apply Matrix.ext; unfold raw3460step3 raw3460step2; decide +kernel
      have hl : raw3460step2Labels = labelEmbedding9 ∘ raw3460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3460step2 raw3460step2Labels raw3460step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw3461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3461step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3461 raw3461Labels = mixedMoment B node4484 node4484Labels := by
  calc
    mixedMoment B raw3461 raw3461Labels = mixedMoment B raw3461step0 raw3461step0Labels := by
      have hz : ∀ j, raw3461 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3461step0 = (fun i j => raw3461 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3461step0 raw3461; decide +kernel
      have hl : raw3461step0Labels = raw3461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3461 raw3461Labels permutation434 hz
    mixedMoment B raw3461step0 raw3461step0Labels = mixedMoment B raw3461step1 raw3461step1Labels := by
      have hz : ∀ j, raw3461step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3461step1 = (fun i j => raw3461step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3461step1 raw3461step0; decide +kernel
      have hl : raw3461step1Labels = raw3461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3461step0 raw3461step0Labels permutation56 hz
    mixedMoment B raw3461step1 raw3461step1Labels = mixedMoment B raw3461step2 raw3461step2Labels := by
      have ha : raw3461step2 = (fun i j => raw3461step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3461step2 raw3461step1; decide +kernel
      have hl : raw3461step2Labels = raw3461step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3461step1 raw3461step1Labels permutation10 permutation2
    _ = mixedMoment B node4484 node4484Labels := by rfl

def raw3462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3462step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3462step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3462step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3462 raw3462Labels = mixedMoment B node4751 node4751Labels := by
  calc
    mixedMoment B raw3462 raw3462Labels = mixedMoment B raw3462step0 raw3462step0Labels := by
      have hz : ∀ j, raw3462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3462step0 = (fun i j => raw3462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3462step0 raw3462; decide +kernel
      have hl : raw3462step0Labels = raw3462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3462 raw3462Labels permutation434 hz
    mixedMoment B raw3462step0 raw3462step0Labels = mixedMoment B raw3462step1 raw3462step1Labels := by
      have ha : raw3462step1 = (fun i j => raw3462step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3462step1 raw3462step0; decide +kernel
      have hl : raw3462step1Labels = raw3462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3462step0 raw3462step0Labels permutation145 permutation3
    mixedMoment B raw3462step1 raw3462step1Labels = mixedMoment B raw3462step2 raw3462step2Labels := by
      have ha : raw3462step2 = -raw3462step1 := by apply Matrix.ext; change ∀ i j, raw3462step2 i j = -(raw3462step1 i j); unfold raw3462step2 raw3462step1; decide +kernel
      have hl : raw3462step2Labels = raw3462step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3462step2 raw3462step2Labels = mixedMoment B raw3462step3 raw3462step3Labels := by
      have ha : raw3462step3 = raw3462step2 := by apply Matrix.ext; unfold raw3462step3 raw3462step2; decide +kernel
      have hl : raw3462step2Labels = labelEmbedding6 ∘ raw3462step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3462step2 raw3462step2Labels raw3462step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4751 node4751Labels := by rfl

def raw3463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3463step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3463step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3463step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3463step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3463 raw3463Labels = mixedMoment B node4751 node4751Labels := by
  calc
    mixedMoment B raw3463 raw3463Labels = mixedMoment B raw3463step0 raw3463step0Labels := by
      have hz : ∀ j, raw3463 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3463step0 = (fun i j => raw3463 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3463step0 raw3463; decide +kernel
      have hl : raw3463step0Labels = raw3463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3463 raw3463Labels permutation265 hz
    mixedMoment B raw3463step0 raw3463step0Labels = mixedMoment B raw3463step1 raw3463step1Labels := by
      have ha : raw3463step1 = (fun i j => raw3463step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3463step1 raw3463step0; decide +kernel
      have hl : raw3463step1Labels = raw3463step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3463step0 raw3463step0Labels permutation139 permutation3
    mixedMoment B raw3463step1 raw3463step1Labels = mixedMoment B raw3463step2 raw3463step2Labels := by
      have ha : raw3463step2 = -raw3463step1 := by apply Matrix.ext; change ∀ i j, raw3463step2 i j = -(raw3463step1 i j); unfold raw3463step2 raw3463step1; decide +kernel
      have hl : raw3463step2Labels = raw3463step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3463step2 raw3463step2Labels = mixedMoment B raw3463step3 raw3463step3Labels := by
      have ha : raw3463step3 = raw3463step2 := by apply Matrix.ext; unfold raw3463step3 raw3463step2; decide +kernel
      have hl : raw3463step2Labels = labelEmbedding6 ∘ raw3463step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3463step2 raw3463step2Labels raw3463step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4751 node4751Labels := by rfl

def raw3464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3464step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-3, 3, 0]]
def raw3464step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3464step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3464step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3464step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3464step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3464 raw3464Labels = mixedMoment B node4484 node4484Labels := by
  calc
    mixedMoment B raw3464 raw3464Labels = mixedMoment B raw3464step0 raw3464step0Labels := by
      have hz : ∀ j, raw3464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3464step0 = (fun i j => raw3464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3464step0 raw3464; decide +kernel
      have hl : raw3464step0Labels = raw3464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3464 raw3464Labels permutation434 hz
    mixedMoment B raw3464step0 raw3464step0Labels = mixedMoment B raw3464step1 raw3464step1Labels := by
      have hz : ∀ j, raw3464step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3464step1 = (fun i j => raw3464step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3464step1 raw3464step0; decide +kernel
      have hl : raw3464step1Labels = raw3464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3464step0 raw3464step0Labels permutation56 hz
    mixedMoment B raw3464step1 raw3464step1Labels = mixedMoment B raw3464step2 raw3464step2Labels := by
      have ha : raw3464step2 = (fun i j => raw3464step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3464step2 raw3464step1; decide +kernel
      have hl : raw3464step2Labels = raw3464step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3464step1 raw3464step1Labels permutation20 permutation4
    mixedMoment B raw3464step2 raw3464step2Labels = mixedMoment B raw3464step3 raw3464step3Labels := by
      have ha : raw3464step3 = -raw3464step2 := by apply Matrix.ext; change ∀ i j, raw3464step3 i j = -(raw3464step2 i j); unfold raw3464step3 raw3464step2; decide +kernel
      have hl : raw3464step3Labels = raw3464step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3464step3 raw3464step3Labels = mixedMoment B raw3464step4 raw3464step4Labels := by
      have ha : raw3464step4 = raw3464step3 := by apply Matrix.ext; unfold raw3464step4 raw3464step3; decide +kernel
      have hl : raw3464step3Labels = labelEmbedding7 ∘ raw3464step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3464step3 raw3464step3Labels raw3464step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4484 node4484Labels := by rfl

def raw3465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3465step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3465step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3465step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3465step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3465 raw3465Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw3465 raw3465Labels = mixedMoment B raw3465step0 raw3465step0Labels := by
      have hz : ∀ j, raw3465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3465step0 = (fun i j => raw3465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3465step0 raw3465; decide +kernel
      have hl : raw3465step0Labels = raw3465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3465 raw3465Labels permutation434 hz
    mixedMoment B raw3465step0 raw3465step0Labels = mixedMoment B raw3465step1 raw3465step1Labels := by
      have hz : ∀ j, raw3465step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3465step1 = (fun i j => raw3465step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3465step1 raw3465step0; decide +kernel
      have hl : raw3465step1Labels = raw3465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3465step0 raw3465step0Labels permutation56 hz
    mixedMoment B raw3465step1 raw3465step1Labels = mixedMoment B raw3465step2 raw3465step2Labels := by
      have ha : raw3465step2 = (fun i j => raw3465step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3465step2 raw3465step1; decide +kernel
      have hl : raw3465step2Labels = raw3465step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3465step1 raw3465step1Labels permutation23 permutation6
    mixedMoment B raw3465step2 raw3465step2Labels = mixedMoment B raw3465step3 raw3465step3Labels := by
      have ha : raw3465step3 = raw3465step2 := by apply Matrix.ext; unfold raw3465step3 raw3465step2; decide +kernel
      have hl : raw3465step2Labels = labelEmbedding9 ∘ raw3465step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3465step2 raw3465step2Labels raw3465step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw3466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3466 raw3466Labels = mixedMoment B node4484 node4484Labels := by
  calc
    mixedMoment B raw3466 raw3466Labels = mixedMoment B raw3466step0 raw3466step0Labels := by
      have hz : ∀ j, raw3466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3466step0 = (fun i j => raw3466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3466step0 raw3466; decide +kernel
      have hl : raw3466step0Labels = raw3466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3466 raw3466Labels permutation346 hz
    mixedMoment B raw3466step0 raw3466step0Labels = mixedMoment B raw3466step1 raw3466step1Labels := by
      have hz : ∀ j, raw3466step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3466step1 = (fun i j => raw3466step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3466step1 raw3466step0; decide +kernel
      have hl : raw3466step1Labels = raw3466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3466step0 raw3466step0Labels permutation56 hz
    mixedMoment B raw3466step1 raw3466step1Labels = mixedMoment B raw3466step2 raw3466step2Labels := by
      have ha : raw3466step2 = (fun i j => raw3466step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3466step2 raw3466step1; decide +kernel
      have hl : raw3466step2Labels = raw3466step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3466step1 raw3466step1Labels permutation10 permutation2
    _ = mixedMoment B node4484 node4484Labels := by rfl

def raw3467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3467step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3467step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3467step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3467step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3467 raw3467Labels = mixedMoment B node4751 node4751Labels := by
  calc
    mixedMoment B raw3467 raw3467Labels = mixedMoment B raw3467step0 raw3467step0Labels := by
      have hz : ∀ j, raw3467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3467step0 = (fun i j => raw3467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3467step0 raw3467; decide +kernel
      have hl : raw3467step0Labels = raw3467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3467 raw3467Labels permutation346 hz
    mixedMoment B raw3467step0 raw3467step0Labels = mixedMoment B raw3467step1 raw3467step1Labels := by
      have ha : raw3467step1 = (fun i j => raw3467step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3467step1 raw3467step0; decide +kernel
      have hl : raw3467step1Labels = raw3467step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3467step0 raw3467step0Labels permutation145 permutation3
    mixedMoment B raw3467step1 raw3467step1Labels = mixedMoment B raw3467step2 raw3467step2Labels := by
      have ha : raw3467step2 = -raw3467step1 := by apply Matrix.ext; change ∀ i j, raw3467step2 i j = -(raw3467step1 i j); unfold raw3467step2 raw3467step1; decide +kernel
      have hl : raw3467step2Labels = raw3467step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3467step2 raw3467step2Labels = mixedMoment B raw3467step3 raw3467step3Labels := by
      have ha : raw3467step3 = raw3467step2 := by apply Matrix.ext; unfold raw3467step3 raw3467step2; decide +kernel
      have hl : raw3467step2Labels = labelEmbedding6 ∘ raw3467step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3467step2 raw3467step2Labels raw3467step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4751 node4751Labels := by rfl

def raw3468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3468step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3468step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3468step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3468 raw3468Labels = mixedMoment B node4751 node4751Labels := by
  calc
    mixedMoment B raw3468 raw3468Labels = mixedMoment B raw3468step0 raw3468step0Labels := by
      have hz : ∀ j, raw3468 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3468step0 = (fun i j => raw3468 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3468step0 raw3468; decide +kernel
      have hl : raw3468step0Labels = raw3468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3468 raw3468Labels permutation265 hz
    mixedMoment B raw3468step0 raw3468step0Labels = mixedMoment B raw3468step1 raw3468step1Labels := by
      have ha : raw3468step1 = (fun i j => raw3468step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3468step1 raw3468step0; decide +kernel
      have hl : raw3468step1Labels = raw3468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3468step0 raw3468step0Labels permutation145 permutation3
    mixedMoment B raw3468step1 raw3468step1Labels = mixedMoment B raw3468step2 raw3468step2Labels := by
      have ha : raw3468step2 = -raw3468step1 := by apply Matrix.ext; change ∀ i j, raw3468step2 i j = -(raw3468step1 i j); unfold raw3468step2 raw3468step1; decide +kernel
      have hl : raw3468step2Labels = raw3468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3468step2 raw3468step2Labels = mixedMoment B raw3468step3 raw3468step3Labels := by
      have ha : raw3468step3 = raw3468step2 := by apply Matrix.ext; unfold raw3468step3 raw3468step2; decide +kernel
      have hl : raw3468step2Labels = labelEmbedding6 ∘ raw3468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3468step2 raw3468step2Labels raw3468step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4751 node4751Labels := by rfl

def raw3469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-3, 3, 0]]
def raw3469step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3469step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3469step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3469step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3469step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3469 raw3469Labels = mixedMoment B node4484 node4484Labels := by
  calc
    mixedMoment B raw3469 raw3469Labels = mixedMoment B raw3469step0 raw3469step0Labels := by
      have hz : ∀ j, raw3469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3469step0 = (fun i j => raw3469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3469step0 raw3469; decide +kernel
      have hl : raw3469step0Labels = raw3469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3469 raw3469Labels permutation346 hz
    mixedMoment B raw3469step0 raw3469step0Labels = mixedMoment B raw3469step1 raw3469step1Labels := by
      have hz : ∀ j, raw3469step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3469step1 = (fun i j => raw3469step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3469step1 raw3469step0; decide +kernel
      have hl : raw3469step1Labels = raw3469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3469step0 raw3469step0Labels permutation56 hz
    mixedMoment B raw3469step1 raw3469step1Labels = mixedMoment B raw3469step2 raw3469step2Labels := by
      have ha : raw3469step2 = (fun i j => raw3469step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3469step2 raw3469step1; decide +kernel
      have hl : raw3469step2Labels = raw3469step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3469step1 raw3469step1Labels permutation20 permutation4
    mixedMoment B raw3469step2 raw3469step2Labels = mixedMoment B raw3469step3 raw3469step3Labels := by
      have ha : raw3469step3 = -raw3469step2 := by apply Matrix.ext; change ∀ i j, raw3469step3 i j = -(raw3469step2 i j); unfold raw3469step3 raw3469step2; decide +kernel
      have hl : raw3469step3Labels = raw3469step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3469step3 raw3469step3Labels = mixedMoment B raw3469step4 raw3469step4Labels := by
      have ha : raw3469step4 = raw3469step3 := by apply Matrix.ext; unfold raw3469step4 raw3469step3; decide +kernel
      have hl : raw3469step3Labels = labelEmbedding7 ∘ raw3469step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3469step3 raw3469step3Labels raw3469step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4484 node4484Labels := by rfl

def raw3470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3470step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3470step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3470step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3470step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3470 raw3470Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw3470 raw3470Labels = mixedMoment B raw3470step0 raw3470step0Labels := by
      have hz : ∀ j, raw3470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3470step0 = (fun i j => raw3470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3470step0 raw3470; decide +kernel
      have hl : raw3470step0Labels = raw3470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3470 raw3470Labels permutation346 hz
    mixedMoment B raw3470step0 raw3470step0Labels = mixedMoment B raw3470step1 raw3470step1Labels := by
      have hz : ∀ j, raw3470step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3470step1 = (fun i j => raw3470step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3470step1 raw3470step0; decide +kernel
      have hl : raw3470step1Labels = raw3470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3470step0 raw3470step0Labels permutation56 hz
    mixedMoment B raw3470step1 raw3470step1Labels = mixedMoment B raw3470step2 raw3470step2Labels := by
      have ha : raw3470step2 = (fun i j => raw3470step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3470step2 raw3470step1; decide +kernel
      have hl : raw3470step2Labels = raw3470step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3470step1 raw3470step1Labels permutation23 permutation6
    mixedMoment B raw3470step2 raw3470step2Labels = mixedMoment B raw3470step3 raw3470step3Labels := by
      have ha : raw3470step3 = raw3470step2 := by apply Matrix.ext; unfold raw3470step3 raw3470step2; decide +kernel
      have hl : raw3470step2Labels = labelEmbedding9 ∘ raw3470step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3470step2 raw3470step2Labels raw3470step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw3471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3471step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3471step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3471 raw3471Labels = mixedMoment B node4508 node4508Labels := by
  calc
    mixedMoment B raw3471 raw3471Labels = mixedMoment B raw3471step0 raw3471step0Labels := by
      have hz : ∀ j, raw3471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3471step0 = (fun i j => raw3471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3471step0 raw3471; decide +kernel
      have hl : raw3471step0Labels = raw3471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3471 raw3471Labels permutation434 hz
    mixedMoment B raw3471step0 raw3471step0Labels = mixedMoment B raw3471step1 raw3471step1Labels := by
      have hz : ∀ j, raw3471step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3471step1 = (fun i j => raw3471step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3471step1 raw3471step0; decide +kernel
      have hl : raw3471step1Labels = raw3471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3471step0 raw3471step0Labels permutation80 hz
    mixedMoment B raw3471step1 raw3471step1Labels = mixedMoment B raw3471step2 raw3471step2Labels := by
      have hz : ∀ j, raw3471step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3471step2 = (fun i j => raw3471step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3471step2 raw3471step1; decide +kernel
      have hl : raw3471step2Labels = raw3471step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3471step1 raw3471step1Labels permutation14 hz
    _ = mixedMoment B node4508 node4508Labels := by rfl

def raw3472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3472 raw3472Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw3472 raw3472Labels = mixedMoment B raw3472step0 raw3472step0Labels := by
      have hz : ∀ j, raw3472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3472step0 = (fun i j => raw3472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3472step0 raw3472; decide +kernel
      have hl : raw3472step0Labels = raw3472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3472 raw3472Labels permutation434 hz
    mixedMoment B raw3472step0 raw3472step0Labels = mixedMoment B raw3472step1 raw3472step1Labels := by
      have hz : ∀ j, raw3472step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3472step1 = (fun i j => raw3472step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3472step1 raw3472step0; decide +kernel
      have hl : raw3472step1Labels = raw3472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3472step0 raw3472step0Labels permutation80 hz
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw3473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3473 raw3473Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw3473 raw3473Labels = mixedMoment B raw3473step0 raw3473step0Labels := by
      have hz : ∀ j, raw3473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3473step0 = (fun i j => raw3473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3473step0 raw3473; decide +kernel
      have hl : raw3473step0Labels = raw3473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3473 raw3473Labels permutation434 hz
    mixedMoment B raw3473step0 raw3473step0Labels = mixedMoment B raw3473step1 raw3473step1Labels := by
      have hz : ∀ j, raw3473step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3473step1 = (fun i j => raw3473step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3473step1 raw3473step0; decide +kernel
      have hl : raw3473step1Labels = raw3473step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3473step0 raw3473step0Labels permutation56 hz
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw3474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3474 raw3474Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw3474 raw3474Labels = mixedMoment B raw3474step0 raw3474step0Labels := by
      have hz : ∀ j, raw3474 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3474step0 = (fun i j => raw3474 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3474step0 raw3474; decide +kernel
      have hl : raw3474step0Labels = raw3474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3474 raw3474Labels permutation346 hz
    mixedMoment B raw3474step0 raw3474step0Labels = mixedMoment B raw3474step1 raw3474step1Labels := by
      have hz : ∀ j, raw3474step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3474step1 = (fun i j => raw3474step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3474step1 raw3474step0; decide +kernel
      have hl : raw3474step1Labels = raw3474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3474step0 raw3474step0Labels permutation56 hz
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw3475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw3475step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3475step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw3475step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3475step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3475step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3475step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3475step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3475 raw3475Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw3475 raw3475Labels = mixedMoment B raw3475step0 raw3475step0Labels := by
      have hz : ∀ j, raw3475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3475step0 = (fun i j => raw3475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3475step0 raw3475; decide +kernel
      have hl : raw3475step0Labels = raw3475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3475 raw3475Labels permutation434 hz
    mixedMoment B raw3475step0 raw3475step0Labels = mixedMoment B raw3475step1 raw3475step1Labels := by
      have hz : ∀ j, raw3475step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3475step1 = (fun i j => raw3475step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3475step1 raw3475step0; decide +kernel
      have hl : raw3475step1Labels = raw3475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3475step0 raw3475step0Labels permutation80 hz
    mixedMoment B raw3475step1 raw3475step1Labels = mixedMoment B raw3475step2 raw3475step2Labels := by
      have hz : ∀ j, raw3475step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3475step2 = (fun i j => raw3475step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3475step2 raw3475step1; decide +kernel
      have hl : raw3475step2Labels = raw3475step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3475step1 raw3475step1Labels permutation14 hz
    mixedMoment B raw3475step2 raw3475step2Labels = mixedMoment B raw3475step3 raw3475step3Labels := by
      have ha : raw3475step3 = (fun i j => raw3475step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3475step3 raw3475step2; decide +kernel
      have hl : raw3475step3Labels = raw3475step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3475step2 raw3475step2Labels permutation3 permutation7
    mixedMoment B raw3475step3 raw3475step3Labels = mixedMoment B raw3475step4 raw3475step4Labels := by
      have ha : raw3475step4 = -raw3475step3 := by apply Matrix.ext; change ∀ i j, raw3475step4 i j = -(raw3475step3 i j); unfold raw3475step4 raw3475step3; decide +kernel
      have hl : raw3475step4Labels = raw3475step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3475step4 raw3475step4Labels = mixedMoment B raw3475step5 raw3475step5Labels := by
      have ha : raw3475step5 = raw3475step4 := by apply Matrix.ext; unfold raw3475step5 raw3475step4; decide +kernel
      have hl : raw3475step4Labels = labelEmbedding10 ∘ raw3475step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3475step4 raw3475step4Labels raw3475step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw3476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3476step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![4, -4, 0]]
def raw3476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3476step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-4, 3, 1]]
def raw3476step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3476step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![4, -3, -1]]
def raw3476step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3476step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![4, -3, -1]]
def raw3476step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3476 raw3476Labels = mixedMoment B node4282 node4282Labels := by
  calc
    mixedMoment B raw3476 raw3476Labels = mixedMoment B raw3476step0 raw3476step0Labels := by
      have hz : ∀ j, raw3476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3476step0 = (fun i j => raw3476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3476step0 raw3476; decide +kernel
      have hl : raw3476step0Labels = raw3476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3476 raw3476Labels permutation434 hz
    mixedMoment B raw3476step0 raw3476step0Labels = mixedMoment B raw3476step1 raw3476step1Labels := by
      have hz : ∀ j, raw3476step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3476step1 = (fun i j => raw3476step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3476step1 raw3476step0; decide +kernel
      have hl : raw3476step1Labels = raw3476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3476step0 raw3476step0Labels permutation80 hz
    mixedMoment B raw3476step1 raw3476step1Labels = mixedMoment B raw3476step2 raw3476step2Labels := by
      have hz : ∀ j, raw3476step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3476step2 = (fun i j => raw3476step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3476step2 raw3476step1; decide +kernel
      have hl : raw3476step2Labels = raw3476step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3476step1 raw3476step1Labels permutation14 hz
    mixedMoment B raw3476step2 raw3476step2Labels = mixedMoment B raw3476step3 raw3476step3Labels := by
      have ha : raw3476step3 = (fun i j => raw3476step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3476step3 raw3476step2; decide +kernel
      have hl : raw3476step3Labels = raw3476step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3476step2 raw3476step2Labels permutation7 permutation3
    mixedMoment B raw3476step3 raw3476step3Labels = mixedMoment B raw3476step4 raw3476step4Labels := by
      have ha : raw3476step4 = -raw3476step3 := by apply Matrix.ext; change ∀ i j, raw3476step4 i j = -(raw3476step3 i j); unfold raw3476step4 raw3476step3; decide +kernel
      have hl : raw3476step4Labels = raw3476step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3476step4 raw3476step4Labels = mixedMoment B raw3476step5 raw3476step5Labels := by
      have ha : raw3476step5 = raw3476step4 := by apply Matrix.ext; unfold raw3476step5 raw3476step4; decide +kernel
      have hl : raw3476step4Labels = labelEmbedding6 ∘ raw3476step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3476step4 raw3476step4Labels raw3476step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4282 node4282Labels := by rfl

def raw3477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3477step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3477step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3477step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3477step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3477step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3477 raw3477Labels = mixedMoment B node4281 node4281Labels := by
  calc
    mixedMoment B raw3477 raw3477Labels = mixedMoment B raw3477step0 raw3477step0Labels := by
      have hz : ∀ j, raw3477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3477step0 = (fun i j => raw3477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3477step0 raw3477; decide +kernel
      have hl : raw3477step0Labels = raw3477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3477 raw3477Labels permutation434 hz
    mixedMoment B raw3477step0 raw3477step0Labels = mixedMoment B raw3477step1 raw3477step1Labels := by
      have hz : ∀ j, raw3477step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3477step1 = (fun i j => raw3477step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3477step1 raw3477step0; decide +kernel
      have hl : raw3477step1Labels = raw3477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3477step0 raw3477step0Labels permutation80 hz
    mixedMoment B raw3477step1 raw3477step1Labels = mixedMoment B raw3477step2 raw3477step2Labels := by
      have ha : raw3477step2 = (fun i j => raw3477step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3477step2 raw3477step1; decide +kernel
      have hl : raw3477step2Labels = raw3477step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3477step1 raw3477step1Labels permutation31 permutation3
    mixedMoment B raw3477step2 raw3477step2Labels = mixedMoment B raw3477step3 raw3477step3Labels := by
      have ha : raw3477step3 = -raw3477step2 := by apply Matrix.ext; change ∀ i j, raw3477step3 i j = -(raw3477step2 i j); unfold raw3477step3 raw3477step2; decide +kernel
      have hl : raw3477step3Labels = raw3477step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3477step3 raw3477step3Labels = mixedMoment B raw3477step4 raw3477step4Labels := by
      have ha : raw3477step4 = raw3477step3 := by apply Matrix.ext; unfold raw3477step4 raw3477step3; decide +kernel
      have hl : raw3477step3Labels = labelEmbedding6 ∘ raw3477step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3477step3 raw3477step3Labels raw3477step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4281 node4281Labels := by rfl

def raw3478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3478step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3478step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3478step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3478step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3478 raw3478Labels = mixedMoment B node4281 node4281Labels := by
  calc
    mixedMoment B raw3478 raw3478Labels = mixedMoment B raw3478step0 raw3478step0Labels := by
      have hz : ∀ j, raw3478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3478step0 = (fun i j => raw3478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3478step0 raw3478; decide +kernel
      have hl : raw3478step0Labels = raw3478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3478 raw3478Labels permutation434 hz
    mixedMoment B raw3478step0 raw3478step0Labels = mixedMoment B raw3478step1 raw3478step1Labels := by
      have hz : ∀ j, raw3478step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3478step1 = (fun i j => raw3478step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3478step1 raw3478step0; decide +kernel
      have hl : raw3478step1Labels = raw3478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3478step0 raw3478step0Labels permutation56 hz
    mixedMoment B raw3478step1 raw3478step1Labels = mixedMoment B raw3478step2 raw3478step2Labels := by
      have ha : raw3478step2 = (fun i j => raw3478step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3478step2 raw3478step1; decide +kernel
      have hl : raw3478step2Labels = raw3478step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3478step1 raw3478step1Labels permutation31 permutation3
    mixedMoment B raw3478step2 raw3478step2Labels = mixedMoment B raw3478step3 raw3478step3Labels := by
      have ha : raw3478step3 = -raw3478step2 := by apply Matrix.ext; change ∀ i j, raw3478step3 i j = -(raw3478step2 i j); unfold raw3478step3 raw3478step2; decide +kernel
      have hl : raw3478step3Labels = raw3478step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3478step3 raw3478step3Labels = mixedMoment B raw3478step4 raw3478step4Labels := by
      have ha : raw3478step4 = raw3478step3 := by apply Matrix.ext; unfold raw3478step4 raw3478step3; decide +kernel
      have hl : raw3478step3Labels = labelEmbedding6 ∘ raw3478step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3478step3 raw3478step3Labels raw3478step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4281 node4281Labels := by rfl

def raw3479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3479step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3479step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3479step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3479step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3479step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3479 raw3479Labels = mixedMoment B node4281 node4281Labels := by
  calc
    mixedMoment B raw3479 raw3479Labels = mixedMoment B raw3479step0 raw3479step0Labels := by
      have hz : ∀ j, raw3479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3479step0 = (fun i j => raw3479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3479step0 raw3479; decide +kernel
      have hl : raw3479step0Labels = raw3479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3479 raw3479Labels permutation346 hz
    mixedMoment B raw3479step0 raw3479step0Labels = mixedMoment B raw3479step1 raw3479step1Labels := by
      have hz : ∀ j, raw3479step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3479step1 = (fun i j => raw3479step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3479step1 raw3479step0; decide +kernel
      have hl : raw3479step1Labels = raw3479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3479step0 raw3479step0Labels permutation56 hz
    mixedMoment B raw3479step1 raw3479step1Labels = mixedMoment B raw3479step2 raw3479step2Labels := by
      have ha : raw3479step2 = (fun i j => raw3479step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3479step2 raw3479step1; decide +kernel
      have hl : raw3479step2Labels = raw3479step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3479step1 raw3479step1Labels permutation31 permutation3
    mixedMoment B raw3479step2 raw3479step2Labels = mixedMoment B raw3479step3 raw3479step3Labels := by
      have ha : raw3479step3 = -raw3479step2 := by apply Matrix.ext; change ∀ i j, raw3479step3 i j = -(raw3479step2 i j); unfold raw3479step3 raw3479step2; decide +kernel
      have hl : raw3479step3Labels = raw3479step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3479step3 raw3479step3Labels = mixedMoment B raw3479step4 raw3479step4Labels := by
      have ha : raw3479step4 = raw3479step3 := by apply Matrix.ext; unfold raw3479step4 raw3479step3; decide +kernel
      have hl : raw3479step3Labels = labelEmbedding6 ∘ raw3479step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3479step3 raw3479step3Labels raw3479step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4281 node4281Labels := by rfl

def raw3480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3480step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 4, -3], ![4, -4, 0]]
def raw3480step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3480step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![4, -3, -1]]
def raw3480step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3480step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![4, -3, -1]]
def raw3480step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3480 raw3480Labels = mixedMoment B node4282 node4282Labels := by
  calc
    mixedMoment B raw3480 raw3480Labels = mixedMoment B raw3480step0 raw3480step0Labels := by
      have hz : ∀ j, raw3480 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3480step0 = (fun i j => raw3480 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3480step0 raw3480; decide +kernel
      have hl : raw3480step0Labels = raw3480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3480 raw3480Labels permutation434 hz
    mixedMoment B raw3480step0 raw3480step0Labels = mixedMoment B raw3480step1 raw3480step1Labels := by
      have hz : ∀ j, raw3480step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3480step1 = (fun i j => raw3480step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3480step1 raw3480step0; decide +kernel
      have hl : raw3480step1Labels = raw3480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3480step0 raw3480step0Labels permutation80 hz
    mixedMoment B raw3480step1 raw3480step1Labels = mixedMoment B raw3480step2 raw3480step2Labels := by
      have hz : ∀ j, raw3480step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3480step2 = (fun i j => raw3480step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3480step2 raw3480step1; decide +kernel
      have hl : raw3480step2Labels = raw3480step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3480step1 raw3480step1Labels permutation14 hz
    mixedMoment B raw3480step2 raw3480step2Labels = mixedMoment B raw3480step3 raw3480step3Labels := by
      have ha : raw3480step3 = (fun i j => raw3480step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3480step3 raw3480step2; decide +kernel
      have hl : raw3480step3Labels = raw3480step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3480step2 raw3480step2Labels permutation6 permutation5
    mixedMoment B raw3480step3 raw3480step3Labels = mixedMoment B raw3480step4 raw3480step4Labels := by
      have ha : raw3480step4 = raw3480step3 := by apply Matrix.ext; unfold raw3480step4 raw3480step3; decide +kernel
      have hl : raw3480step3Labels = labelEmbedding8 ∘ raw3480step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3480step3 raw3480step3Labels raw3480step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4282 node4282Labels := by rfl

def raw3481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3481step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw3481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3481 raw3481Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw3481 raw3481Labels = mixedMoment B raw3481step0 raw3481step0Labels := by
      have hz : ∀ j, raw3481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3481step0 = (fun i j => raw3481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3481step0 raw3481; decide +kernel
      have hl : raw3481step0Labels = raw3481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3481 raw3481Labels permutation434 hz
    mixedMoment B raw3481step0 raw3481step0Labels = mixedMoment B raw3481step1 raw3481step1Labels := by
      have hz : ∀ j, raw3481step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3481step1 = (fun i j => raw3481step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3481step1 raw3481step0; decide +kernel
      have hl : raw3481step1Labels = raw3481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3481step0 raw3481step0Labels permutation80 hz
    mixedMoment B raw3481step1 raw3481step1Labels = mixedMoment B raw3481step2 raw3481step2Labels := by
      have ha : raw3481step2 = (fun i j => raw3481step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3481step2 raw3481step1; decide +kernel
      have hl : raw3481step2Labels = raw3481step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3481step1 raw3481step1Labels permutation23 permutation6
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw3482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3482step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw3482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3482 raw3482Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw3482 raw3482Labels = mixedMoment B raw3482step0 raw3482step0Labels := by
      have hz : ∀ j, raw3482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3482step0 = (fun i j => raw3482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3482step0 raw3482; decide +kernel
      have hl : raw3482step0Labels = raw3482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3482 raw3482Labels permutation434 hz
    mixedMoment B raw3482step0 raw3482step0Labels = mixedMoment B raw3482step1 raw3482step1Labels := by
      have hz : ∀ j, raw3482step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3482step1 = (fun i j => raw3482step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3482step1 raw3482step0; decide +kernel
      have hl : raw3482step1Labels = raw3482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3482step0 raw3482step0Labels permutation56 hz
    mixedMoment B raw3482step1 raw3482step1Labels = mixedMoment B raw3482step2 raw3482step2Labels := by
      have ha : raw3482step2 = (fun i j => raw3482step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3482step2 raw3482step1; decide +kernel
      have hl : raw3482step2Labels = raw3482step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3482step1 raw3482step1Labels permutation23 permutation6
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw3483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw3483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3483 raw3483Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw3483 raw3483Labels = mixedMoment B raw3483step0 raw3483step0Labels := by
      have hz : ∀ j, raw3483 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3483step0 = (fun i j => raw3483 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3483step0 raw3483; decide +kernel
      have hl : raw3483step0Labels = raw3483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3483 raw3483Labels permutation346 hz
    mixedMoment B raw3483step0 raw3483step0Labels = mixedMoment B raw3483step1 raw3483step1Labels := by
      have hz : ∀ j, raw3483step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3483step1 = (fun i j => raw3483step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3483step1 raw3483step0; decide +kernel
      have hl : raw3483step1Labels = raw3483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3483step0 raw3483step0Labels permutation56 hz
    mixedMoment B raw3483step1 raw3483step1Labels = mixedMoment B raw3483step2 raw3483step2Labels := by
      have ha : raw3483step2 = (fun i j => raw3483step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3483step2 raw3483step1; decide +kernel
      have hl : raw3483step2Labels = raw3483step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3483step1 raw3483step1Labels permutation23 permutation6
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw3484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3484step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![3, -3, 0]]
def raw3484step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3484step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw3484step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3484 raw3484Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw3484 raw3484Labels = mixedMoment B raw3484step0 raw3484step0Labels := by
      have hz : ∀ j, raw3484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3484step0 = (fun i j => raw3484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3484step0 raw3484; decide +kernel
      have hl : raw3484step0Labels = raw3484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3484 raw3484Labels permutation434 hz
    mixedMoment B raw3484step0 raw3484step0Labels = mixedMoment B raw3484step1 raw3484step1Labels := by
      have hz : ∀ j, raw3484step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3484step1 = (fun i j => raw3484step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3484step1 raw3484step0; decide +kernel
      have hl : raw3484step1Labels = raw3484step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3484step0 raw3484step0Labels permutation80 hz
    mixedMoment B raw3484step1 raw3484step1Labels = mixedMoment B raw3484step2 raw3484step2Labels := by
      have hz : ∀ j, raw3484step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3484step2 = (fun i j => raw3484step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3484step2 raw3484step1; decide +kernel
      have hl : raw3484step2Labels = raw3484step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3484step1 raw3484step1Labels permutation14 hz
    mixedMoment B raw3484step2 raw3484step2Labels = mixedMoment B raw3484step3 raw3484step3Labels := by
      have ha : raw3484step3 = (fun i j => raw3484step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3484step3 raw3484step2; decide +kernel
      have hl : raw3484step3Labels = raw3484step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3484step2 raw3484step2Labels permutation5 permutation6
    _ = mixedMoment B node1747 node1747Labels := by rfl

def raw3485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3485step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3485step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]
def raw3485step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3485step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3485step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3485 raw3485Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw3485 raw3485Labels = mixedMoment B raw3485step0 raw3485step0Labels := by
      have hz : ∀ j, raw3485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3485step0 = (fun i j => raw3485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3485step0 raw3485; decide +kernel
      have hl : raw3485step0Labels = raw3485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3485 raw3485Labels permutation434 hz
    mixedMoment B raw3485step0 raw3485step0Labels = mixedMoment B raw3485step1 raw3485step1Labels := by
      have hz : ∀ j, raw3485step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3485step1 = (fun i j => raw3485step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3485step1 raw3485step0; decide +kernel
      have hl : raw3485step1Labels = raw3485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3485step0 raw3485step0Labels permutation80 hz
    mixedMoment B raw3485step1 raw3485step1Labels = mixedMoment B raw3485step2 raw3485step2Labels := by
      have hz : ∀ j, raw3485step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3485step2 = (fun i j => raw3485step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3485step2 raw3485step1; decide +kernel
      have hl : raw3485step2Labels = raw3485step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3485step1 raw3485step1Labels permutation14 hz
    mixedMoment B raw3485step2 raw3485step2Labels = mixedMoment B raw3485step3 raw3485step3Labels := by
      have ha : raw3485step3 = (fun i j => raw3485step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3485step3 raw3485step2; decide +kernel
      have hl : raw3485step3Labels = raw3485step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3485step2 raw3485step2Labels permutation5 permutation6
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw3486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3486step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw3486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3486 raw3486Labels = mixedMoment B node1352 node1352Labels := by
  calc
    mixedMoment B raw3486 raw3486Labels = mixedMoment B raw3486step0 raw3486step0Labels := by
      have hz : ∀ j, raw3486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3486step0 = (fun i j => raw3486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3486step0 raw3486; decide +kernel
      have hl : raw3486step0Labels = raw3486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3486 raw3486Labels permutation434 hz
    mixedMoment B raw3486step0 raw3486step0Labels = mixedMoment B raw3486step1 raw3486step1Labels := by
      have hz : ∀ j, raw3486step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3486step1 = (fun i j => raw3486step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3486step1 raw3486step0; decide +kernel
      have hl : raw3486step1Labels = raw3486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3486step0 raw3486step0Labels permutation80 hz
    mixedMoment B raw3486step1 raw3486step1Labels = mixedMoment B raw3486step2 raw3486step2Labels := by
      have ha : raw3486step2 = (fun i j => raw3486step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3486step2 raw3486step1; decide +kernel
      have hl : raw3486step2Labels = raw3486step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3486step1 raw3486step1Labels permutation10 permutation3
    _ = mixedMoment B node1352 node1352Labels := by rfl

def raw3487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3487 raw3487Labels = mixedMoment B node1933 node1933Labels := by
  calc
    mixedMoment B raw3487 raw3487Labels = mixedMoment B raw3487step0 raw3487step0Labels := by
      have hz : ∀ j, raw3487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3487step0 = (fun i j => raw3487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3487step0 raw3487; decide +kernel
      have hl : raw3487step0Labels = raw3487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3487 raw3487Labels permutation434 hz
    mixedMoment B raw3487step0 raw3487step0Labels = mixedMoment B raw3487step1 raw3487step1Labels := by
      have ha : raw3487step1 = (fun i j => raw3487step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3487step1 raw3487step0; decide +kernel
      have hl : raw3487step1Labels = raw3487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3487step0 raw3487step0Labels permutation139 permutation3
    mixedMoment B raw3487step1 raw3487step1Labels = mixedMoment B raw3487step2 raw3487step2Labels := by
      have ha : raw3487step2 = -raw3487step1 := by apply Matrix.ext; change ∀ i j, raw3487step2 i j = -(raw3487step1 i j); unfold raw3487step2 raw3487step1; decide +kernel
      have hl : raw3487step2Labels = raw3487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1933 node1933Labels := by rfl

def raw3488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3488 raw3488Labels = mixedMoment B node1933 node1933Labels := by
  calc
    mixedMoment B raw3488 raw3488Labels = mixedMoment B raw3488step0 raw3488step0Labels := by
      have hz : ∀ j, raw3488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3488step0 = (fun i j => raw3488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3488step0 raw3488; decide +kernel
      have hl : raw3488step0Labels = raw3488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3488 raw3488Labels permutation346 hz
    mixedMoment B raw3488step0 raw3488step0Labels = mixedMoment B raw3488step1 raw3488step1Labels := by
      have ha : raw3488step1 = (fun i j => raw3488step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3488step1 raw3488step0; decide +kernel
      have hl : raw3488step1Labels = raw3488step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3488step0 raw3488step0Labels permutation139 permutation3
    mixedMoment B raw3488step1 raw3488step1Labels = mixedMoment B raw3488step2 raw3488step2Labels := by
      have ha : raw3488step2 = -raw3488step1 := by apply Matrix.ext; change ∀ i j, raw3488step2 i j = -(raw3488step1 i j); unfold raw3488step2 raw3488step1; decide +kernel
      have hl : raw3488step2Labels = raw3488step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1933 node1933Labels := by rfl

def raw3489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3489step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![3, -3, 0]]
def raw3489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3489 raw3489Labels = mixedMoment B node1719 node1719Labels := by
  calc
    mixedMoment B raw3489 raw3489Labels = mixedMoment B raw3489step0 raw3489step0Labels := by
      have hz : ∀ j, raw3489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3489step0 = (fun i j => raw3489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3489step0 raw3489; decide +kernel
      have hl : raw3489step0Labels = raw3489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3489 raw3489Labels permutation434 hz
    mixedMoment B raw3489step0 raw3489step0Labels = mixedMoment B raw3489step1 raw3489step1Labels := by
      have hz : ∀ j, raw3489step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3489step1 = (fun i j => raw3489step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3489step1 raw3489step0; decide +kernel
      have hl : raw3489step1Labels = raw3489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3489step0 raw3489step0Labels permutation80 hz
    mixedMoment B raw3489step1 raw3489step1Labels = mixedMoment B raw3489step2 raw3489step2Labels := by
      have ha : raw3489step2 = (fun i j => raw3489step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3489step2 raw3489step1; decide +kernel
      have hl : raw3489step2Labels = raw3489step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3489step1 raw3489step1Labels permutation23 permutation6
    _ = mixedMoment B node1719 node1719Labels := by rfl

def raw3490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3490 raw3490Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3490 raw3490Labels = mixedMoment B raw3490step0 raw3490step0Labels := by
      have hz : ∀ j, raw3490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3490step0 = (fun i j => raw3490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3490step0 raw3490; decide +kernel
      have hl : raw3490step0Labels = raw3490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3490 raw3490Labels permutation434 hz
    mixedMoment B raw3490step0 raw3490step0Labels = mixedMoment B raw3490step1 raw3490step1Labels := by
      have hz : ∀ j, raw3490step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3490step1 = (fun i j => raw3490step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3490step1 raw3490step0; decide +kernel
      have hl : raw3490step1Labels = raw3490step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3490step0 raw3490step0Labels permutation80 hz
    mixedMoment B raw3490step1 raw3490step1Labels = mixedMoment B raw3490step2 raw3490step2Labels := by
      have ha : raw3490step2 = (fun i j => raw3490step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3490step2 raw3490step1; decide +kernel
      have hl : raw3490step2Labels = raw3490step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3490step1 raw3490step1Labels permutation23 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3491step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3491step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3491step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw3491step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3491 raw3491Labels = mixedMoment B node1352 node1352Labels := by
  calc
    mixedMoment B raw3491 raw3491Labels = mixedMoment B raw3491step0 raw3491step0Labels := by
      have hz : ∀ j, raw3491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3491step0 = (fun i j => raw3491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3491step0 raw3491; decide +kernel
      have hl : raw3491step0Labels = raw3491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3491 raw3491Labels permutation434 hz
    mixedMoment B raw3491step0 raw3491step0Labels = mixedMoment B raw3491step1 raw3491step1Labels := by
      have hz : ∀ j, raw3491step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3491step1 = (fun i j => raw3491step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3491step1 raw3491step0; decide +kernel
      have hl : raw3491step1Labels = raw3491step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3491step0 raw3491step0Labels permutation56 hz
    mixedMoment B raw3491step1 raw3491step1Labels = mixedMoment B raw3491step2 raw3491step2Labels := by
      have ha : raw3491step2 = (fun i j => raw3491step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3491step2 raw3491step1; decide +kernel
      have hl : raw3491step2Labels = raw3491step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3491step1 raw3491step1Labels permutation10 permutation3
    _ = mixedMoment B node1352 node1352Labels := by rfl

def raw3492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3492 raw3492Labels = mixedMoment B node1933 node1933Labels := by
  calc
    mixedMoment B raw3492 raw3492Labels = mixedMoment B raw3492step0 raw3492step0Labels := by
      have hz : ∀ j, raw3492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3492step0 = (fun i j => raw3492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3492step0 raw3492; decide +kernel
      have hl : raw3492step0Labels = raw3492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3492 raw3492Labels permutation434 hz
    mixedMoment B raw3492step0 raw3492step0Labels = mixedMoment B raw3492step1 raw3492step1Labels := by
      have ha : raw3492step1 = (fun i j => raw3492step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3492step1 raw3492step0; decide +kernel
      have hl : raw3492step1Labels = raw3492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3492step0 raw3492step0Labels permutation145 permutation3
    mixedMoment B raw3492step1 raw3492step1Labels = mixedMoment B raw3492step2 raw3492step2Labels := by
      have ha : raw3492step2 = -raw3492step1 := by apply Matrix.ext; change ∀ i j, raw3492step2 i j = -(raw3492step1 i j); unfold raw3492step2 raw3492step1; decide +kernel
      have hl : raw3492step2Labels = raw3492step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1933 node1933Labels := by rfl

def raw3493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3493 raw3493Labels = mixedMoment B node1933 node1933Labels := by
  calc
    mixedMoment B raw3493 raw3493Labels = mixedMoment B raw3493step0 raw3493step0Labels := by
      have hz : ∀ j, raw3493 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3493step0 = (fun i j => raw3493 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3493step0 raw3493; decide +kernel
      have hl : raw3493step0Labels = raw3493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3493 raw3493Labels permutation265 hz
    mixedMoment B raw3493step0 raw3493step0Labels = mixedMoment B raw3493step1 raw3493step1Labels := by
      have ha : raw3493step1 = (fun i j => raw3493step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3493step1 raw3493step0; decide +kernel
      have hl : raw3493step1Labels = raw3493step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3493step0 raw3493step0Labels permutation139 permutation3
    mixedMoment B raw3493step1 raw3493step1Labels = mixedMoment B raw3493step2 raw3493step2Labels := by
      have ha : raw3493step2 = -raw3493step1 := by apply Matrix.ext; change ∀ i j, raw3493step2 i j = -(raw3493step1 i j); unfold raw3493step2 raw3493step1; decide +kernel
      have hl : raw3493step2Labels = raw3493step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1933 node1933Labels := by rfl

def raw3494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3494step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![3, -3, 0]]
def raw3494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3494 raw3494Labels = mixedMoment B node1719 node1719Labels := by
  calc
    mixedMoment B raw3494 raw3494Labels = mixedMoment B raw3494step0 raw3494step0Labels := by
      have hz : ∀ j, raw3494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3494step0 = (fun i j => raw3494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3494step0 raw3494; decide +kernel
      have hl : raw3494step0Labels = raw3494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3494 raw3494Labels permutation434 hz
    mixedMoment B raw3494step0 raw3494step0Labels = mixedMoment B raw3494step1 raw3494step1Labels := by
      have hz : ∀ j, raw3494step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3494step1 = (fun i j => raw3494step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3494step1 raw3494step0; decide +kernel
      have hl : raw3494step1Labels = raw3494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3494step0 raw3494step0Labels permutation56 hz
    mixedMoment B raw3494step1 raw3494step1Labels = mixedMoment B raw3494step2 raw3494step2Labels := by
      have ha : raw3494step2 = (fun i j => raw3494step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3494step2 raw3494step1; decide +kernel
      have hl : raw3494step2Labels = raw3494step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3494step1 raw3494step1Labels permutation23 permutation6
    _ = mixedMoment B node1719 node1719Labels := by rfl

def raw3495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3495step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3495 raw3495Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3495 raw3495Labels = mixedMoment B raw3495step0 raw3495step0Labels := by
      have hz : ∀ j, raw3495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3495step0 = (fun i j => raw3495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3495step0 raw3495; decide +kernel
      have hl : raw3495step0Labels = raw3495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3495 raw3495Labels permutation434 hz
    mixedMoment B raw3495step0 raw3495step0Labels = mixedMoment B raw3495step1 raw3495step1Labels := by
      have hz : ∀ j, raw3495step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3495step1 = (fun i j => raw3495step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3495step1 raw3495step0; decide +kernel
      have hl : raw3495step1Labels = raw3495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3495step0 raw3495step0Labels permutation56 hz
    mixedMoment B raw3495step1 raw3495step1Labels = mixedMoment B raw3495step2 raw3495step2Labels := by
      have ha : raw3495step2 = (fun i j => raw3495step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3495step2 raw3495step1; decide +kernel
      have hl : raw3495step2Labels = raw3495step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3495step1 raw3495step1Labels permutation23 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3496step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3496step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw3496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3496 raw3496Labels = mixedMoment B node1352 node1352Labels := by
  calc
    mixedMoment B raw3496 raw3496Labels = mixedMoment B raw3496step0 raw3496step0Labels := by
      have hz : ∀ j, raw3496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3496step0 = (fun i j => raw3496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3496step0 raw3496; decide +kernel
      have hl : raw3496step0Labels = raw3496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3496 raw3496Labels permutation346 hz
    mixedMoment B raw3496step0 raw3496step0Labels = mixedMoment B raw3496step1 raw3496step1Labels := by
      have hz : ∀ j, raw3496step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3496step1 = (fun i j => raw3496step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3496step1 raw3496step0; decide +kernel
      have hl : raw3496step1Labels = raw3496step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3496step0 raw3496step0Labels permutation56 hz
    mixedMoment B raw3496step1 raw3496step1Labels = mixedMoment B raw3496step2 raw3496step2Labels := by
      have ha : raw3496step2 = (fun i j => raw3496step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3496step2 raw3496step1; decide +kernel
      have hl : raw3496step2Labels = raw3496step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3496step1 raw3496step1Labels permutation10 permutation3
    _ = mixedMoment B node1352 node1352Labels := by rfl

def raw3497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3497 raw3497Labels = mixedMoment B node1933 node1933Labels := by
  calc
    mixedMoment B raw3497 raw3497Labels = mixedMoment B raw3497step0 raw3497step0Labels := by
      have hz : ∀ j, raw3497 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3497step0 = (fun i j => raw3497 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3497step0 raw3497; decide +kernel
      have hl : raw3497step0Labels = raw3497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3497 raw3497Labels permutation346 hz
    mixedMoment B raw3497step0 raw3497step0Labels = mixedMoment B raw3497step1 raw3497step1Labels := by
      have ha : raw3497step1 = (fun i j => raw3497step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3497step1 raw3497step0; decide +kernel
      have hl : raw3497step1Labels = raw3497step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3497step0 raw3497step0Labels permutation145 permutation3
    mixedMoment B raw3497step1 raw3497step1Labels = mixedMoment B raw3497step2 raw3497step2Labels := by
      have ha : raw3497step2 = -raw3497step1 := by apply Matrix.ext; change ∀ i j, raw3497step2 i j = -(raw3497step1 i j); unfold raw3497step2 raw3497step1; decide +kernel
      have hl : raw3497step2Labels = raw3497step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1933 node1933Labels := by rfl

def raw3498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3498 raw3498Labels = mixedMoment B node1933 node1933Labels := by
  calc
    mixedMoment B raw3498 raw3498Labels = mixedMoment B raw3498step0 raw3498step0Labels := by
      have hz : ∀ j, raw3498 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3498step0 = (fun i j => raw3498 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3498step0 raw3498; decide +kernel
      have hl : raw3498step0Labels = raw3498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3498 raw3498Labels permutation265 hz
    mixedMoment B raw3498step0 raw3498step0Labels = mixedMoment B raw3498step1 raw3498step1Labels := by
      have ha : raw3498step1 = (fun i j => raw3498step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3498step1 raw3498step0; decide +kernel
      have hl : raw3498step1Labels = raw3498step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3498step0 raw3498step0Labels permutation145 permutation3
    mixedMoment B raw3498step1 raw3498step1Labels = mixedMoment B raw3498step2 raw3498step2Labels := by
      have ha : raw3498step2 = -raw3498step1 := by apply Matrix.ext; change ∀ i j, raw3498step2 i j = -(raw3498step1 i j); unfold raw3498step2 raw3498step1; decide +kernel
      have hl : raw3498step2Labels = raw3498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1933 node1933Labels := by rfl

def raw3499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3499step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![3, -3, 0]]
def raw3499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3499 raw3499Labels = mixedMoment B node1719 node1719Labels := by
  calc
    mixedMoment B raw3499 raw3499Labels = mixedMoment B raw3499step0 raw3499step0Labels := by
      have hz : ∀ j, raw3499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3499step0 = (fun i j => raw3499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3499step0 raw3499; decide +kernel
      have hl : raw3499step0Labels = raw3499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3499 raw3499Labels permutation346 hz
    mixedMoment B raw3499step0 raw3499step0Labels = mixedMoment B raw3499step1 raw3499step1Labels := by
      have hz : ∀ j, raw3499step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3499step1 = (fun i j => raw3499step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3499step1 raw3499step0; decide +kernel
      have hl : raw3499step1Labels = raw3499step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3499step0 raw3499step0Labels permutation56 hz
    mixedMoment B raw3499step1 raw3499step1Labels = mixedMoment B raw3499step2 raw3499step2Labels := by
      have ha : raw3499step2 = (fun i j => raw3499step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3499step2 raw3499step1; decide +kernel
      have hl : raw3499step2Labels = raw3499step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3499step1 raw3499step1Labels permutation23 permutation6
    _ = mixedMoment B node1719 node1719Labels := by rfl

def raw3500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3500step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3500 raw3500Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3500 raw3500Labels = mixedMoment B raw3500step0 raw3500step0Labels := by
      have hz : ∀ j, raw3500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3500step0 = (fun i j => raw3500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3500step0 raw3500; decide +kernel
      have hl : raw3500step0Labels = raw3500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3500 raw3500Labels permutation346 hz
    mixedMoment B raw3500step0 raw3500step0Labels = mixedMoment B raw3500step1 raw3500step1Labels := by
      have hz : ∀ j, raw3500step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3500step1 = (fun i j => raw3500step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3500step1 raw3500step0; decide +kernel
      have hl : raw3500step1Labels = raw3500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3500step0 raw3500step0Labels permutation56 hz
    mixedMoment B raw3500step1 raw3500step1Labels = mixedMoment B raw3500step2 raw3500step2Labels := by
      have ha : raw3500step2 = (fun i j => raw3500step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3500step2 raw3500step1; decide +kernel
      have hl : raw3500step2Labels = raw3500step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3500step1 raw3500step1Labels permutation23 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3501step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3501step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3501step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3501step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw3501step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3501 raw3501Labels = mixedMoment B node1438 node1438Labels := by
  calc
    mixedMoment B raw3501 raw3501Labels = mixedMoment B raw3501step0 raw3501step0Labels := by
      have hz : ∀ j, raw3501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3501step0 = (fun i j => raw3501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3501step0 raw3501; decide +kernel
      have hl : raw3501step0Labels = raw3501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3501 raw3501Labels permutation434 hz
    mixedMoment B raw3501step0 raw3501step0Labels = mixedMoment B raw3501step1 raw3501step1Labels := by
      have hz : ∀ j, raw3501step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3501step1 = (fun i j => raw3501step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3501step1 raw3501step0; decide +kernel
      have hl : raw3501step1Labels = raw3501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3501step0 raw3501step0Labels permutation80 hz
    mixedMoment B raw3501step1 raw3501step1Labels = mixedMoment B raw3501step2 raw3501step2Labels := by
      have hz : ∀ j, raw3501step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3501step2 = (fun i j => raw3501step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3501step2 raw3501step1; decide +kernel
      have hl : raw3501step2Labels = raw3501step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3501step1 raw3501step1Labels permutation14 hz
    mixedMoment B raw3501step2 raw3501step2Labels = mixedMoment B raw3501step3 raw3501step3Labels := by
      have ha : raw3501step3 = (fun i j => raw3501step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3501step3 raw3501step2; decide +kernel
      have hl : raw3501step3Labels = raw3501step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3501step2 raw3501step2Labels permutation2 permutation3
    _ = mixedMoment B node1438 node1438Labels := by rfl

def raw3502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3502step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3502step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3502step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3502 raw3502Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw3502 raw3502Labels = mixedMoment B raw3502step0 raw3502step0Labels := by
      have hz : ∀ j, raw3502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3502step0 = (fun i j => raw3502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3502step0 raw3502; decide +kernel
      have hl : raw3502step0Labels = raw3502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3502 raw3502Labels permutation434 hz
    mixedMoment B raw3502step0 raw3502step0Labels = mixedMoment B raw3502step1 raw3502step1Labels := by
      have hz : ∀ j, raw3502step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3502step1 = (fun i j => raw3502step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3502step1 raw3502step0; decide +kernel
      have hl : raw3502step1Labels = raw3502step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3502step0 raw3502step0Labels permutation80 hz
    mixedMoment B raw3502step1 raw3502step1Labels = mixedMoment B raw3502step2 raw3502step2Labels := by
      have ha : raw3502step2 = (fun i j => raw3502step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3502step2 raw3502step1; decide +kernel
      have hl : raw3502step2Labels = raw3502step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3502step1 raw3502step1Labels permutation31 permutation3
    mixedMoment B raw3502step2 raw3502step2Labels = mixedMoment B raw3502step3 raw3502step3Labels := by
      have ha : raw3502step3 = -raw3502step2 := by apply Matrix.ext; change ∀ i j, raw3502step3 i j = -(raw3502step2 i j); unfold raw3502step3 raw3502step2; decide +kernel
      have hl : raw3502step3Labels = raw3502step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2136 node2136Labels := by rfl

def raw3503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3503step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3503step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3503step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3503 raw3503Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw3503 raw3503Labels = mixedMoment B raw3503step0 raw3503step0Labels := by
      have hz : ∀ j, raw3503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3503step0 = (fun i j => raw3503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3503step0 raw3503; decide +kernel
      have hl : raw3503step0Labels = raw3503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3503 raw3503Labels permutation434 hz
    mixedMoment B raw3503step0 raw3503step0Labels = mixedMoment B raw3503step1 raw3503step1Labels := by
      have hz : ∀ j, raw3503step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3503step1 = (fun i j => raw3503step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3503step1 raw3503step0; decide +kernel
      have hl : raw3503step1Labels = raw3503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3503step0 raw3503step0Labels permutation56 hz
    mixedMoment B raw3503step1 raw3503step1Labels = mixedMoment B raw3503step2 raw3503step2Labels := by
      have ha : raw3503step2 = (fun i j => raw3503step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3503step2 raw3503step1; decide +kernel
      have hl : raw3503step2Labels = raw3503step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3503step1 raw3503step1Labels permutation31 permutation3
    mixedMoment B raw3503step2 raw3503step2Labels = mixedMoment B raw3503step3 raw3503step3Labels := by
      have ha : raw3503step3 = -raw3503step2 := by apply Matrix.ext; change ∀ i j, raw3503step3 i j = -(raw3503step2 i j); unfold raw3503step3 raw3503step2; decide +kernel
      have hl : raw3503step3Labels = raw3503step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2136 node2136Labels := by rfl

def raw3504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3504step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3504step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3504step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3504step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3504 raw3504Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw3504 raw3504Labels = mixedMoment B raw3504step0 raw3504step0Labels := by
      have hz : ∀ j, raw3504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3504step0 = (fun i j => raw3504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3504step0 raw3504; decide +kernel
      have hl : raw3504step0Labels = raw3504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3504 raw3504Labels permutation346 hz
    mixedMoment B raw3504step0 raw3504step0Labels = mixedMoment B raw3504step1 raw3504step1Labels := by
      have hz : ∀ j, raw3504step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3504step1 = (fun i j => raw3504step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3504step1 raw3504step0; decide +kernel
      have hl : raw3504step1Labels = raw3504step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3504step0 raw3504step0Labels permutation56 hz
    mixedMoment B raw3504step1 raw3504step1Labels = mixedMoment B raw3504step2 raw3504step2Labels := by
      have ha : raw3504step2 = (fun i j => raw3504step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3504step2 raw3504step1; decide +kernel
      have hl : raw3504step2Labels = raw3504step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3504step1 raw3504step1Labels permutation31 permutation3
    mixedMoment B raw3504step2 raw3504step2Labels = mixedMoment B raw3504step3 raw3504step3Labels := by
      have ha : raw3504step3 = -raw3504step2 := by apply Matrix.ext; change ∀ i j, raw3504step3 i j = -(raw3504step2 i j); unfold raw3504step3 raw3504step2; decide +kernel
      have hl : raw3504step3Labels = raw3504step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2136 node2136Labels := by rfl

def raw3505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3505step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3505step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw3505step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3505step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw3505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3505 raw3505Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw3505 raw3505Labels = mixedMoment B raw3505step0 raw3505step0Labels := by
      have hz : ∀ j, raw3505 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3505step0 = (fun i j => raw3505 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3505step0 raw3505; decide +kernel
      have hl : raw3505step0Labels = raw3505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3505 raw3505Labels permutation434 hz
    mixedMoment B raw3505step0 raw3505step0Labels = mixedMoment B raw3505step1 raw3505step1Labels := by
      have hz : ∀ j, raw3505step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3505step1 = (fun i j => raw3505step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3505step1 raw3505step0; decide +kernel
      have hl : raw3505step1Labels = raw3505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3505step0 raw3505step0Labels permutation80 hz
    mixedMoment B raw3505step1 raw3505step1Labels = mixedMoment B raw3505step2 raw3505step2Labels := by
      have hz : ∀ j, raw3505step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3505step2 = (fun i j => raw3505step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3505step2 raw3505step1; decide +kernel
      have hl : raw3505step2Labels = raw3505step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3505step1 raw3505step1Labels permutation14 hz
    mixedMoment B raw3505step2 raw3505step2Labels = mixedMoment B raw3505step3 raw3505step3Labels := by
      have ha : raw3505step3 = (fun i j => raw3505step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3505step3 raw3505step2; decide +kernel
      have hl : raw3505step3Labels = raw3505step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3505step2 raw3505step2Labels permutation5 permutation6
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw3506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3506step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3506step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![4, -4, 0]]
def raw3506step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3506step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-4, 3, 1]]
def raw3506step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3506step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![4, -3, -1]]
def raw3506step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3506 raw3506Labels = mixedMoment B node839 node839Labels := by
  calc
    mixedMoment B raw3506 raw3506Labels = mixedMoment B raw3506step0 raw3506step0Labels := by
      have hz : ∀ j, raw3506 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3506step0 = (fun i j => raw3506 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3506step0 raw3506; decide +kernel
      have hl : raw3506step0Labels = raw3506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3506 raw3506Labels permutation434 hz
    mixedMoment B raw3506step0 raw3506step0Labels = mixedMoment B raw3506step1 raw3506step1Labels := by
      have hz : ∀ j, raw3506step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3506step1 = (fun i j => raw3506step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3506step1 raw3506step0; decide +kernel
      have hl : raw3506step1Labels = raw3506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3506step0 raw3506step0Labels permutation80 hz
    mixedMoment B raw3506step1 raw3506step1Labels = mixedMoment B raw3506step2 raw3506step2Labels := by
      have hz : ∀ j, raw3506step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3506step2 = (fun i j => raw3506step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3506step2 raw3506step1; decide +kernel
      have hl : raw3506step2Labels = raw3506step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3506step1 raw3506step1Labels permutation14 hz
    mixedMoment B raw3506step2 raw3506step2Labels = mixedMoment B raw3506step3 raw3506step3Labels := by
      have ha : raw3506step3 = (fun i j => raw3506step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3506step3 raw3506step2; decide +kernel
      have hl : raw3506step3Labels = raw3506step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3506step2 raw3506step2Labels permutation7 permutation3
    mixedMoment B raw3506step3 raw3506step3Labels = mixedMoment B raw3506step4 raw3506step4Labels := by
      have ha : raw3506step4 = -raw3506step3 := by apply Matrix.ext; change ∀ i j, raw3506step4 i j = -(raw3506step3 i j); unfold raw3506step4 raw3506step3; decide +kernel
      have hl : raw3506step4Labels = raw3506step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node839 node839Labels := by rfl

def raw3507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3507step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3507step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3507step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3507 raw3507Labels = mixedMoment B node837 node837Labels := by
  calc
    mixedMoment B raw3507 raw3507Labels = mixedMoment B raw3507step0 raw3507step0Labels := by
      have hz : ∀ j, raw3507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3507step0 = (fun i j => raw3507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3507step0 raw3507; decide +kernel
      have hl : raw3507step0Labels = raw3507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3507 raw3507Labels permutation434 hz
    mixedMoment B raw3507step0 raw3507step0Labels = mixedMoment B raw3507step1 raw3507step1Labels := by
      have hz : ∀ j, raw3507step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3507step1 = (fun i j => raw3507step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3507step1 raw3507step0; decide +kernel
      have hl : raw3507step1Labels = raw3507step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3507step0 raw3507step0Labels permutation80 hz
    mixedMoment B raw3507step1 raw3507step1Labels = mixedMoment B raw3507step2 raw3507step2Labels := by
      have ha : raw3507step2 = (fun i j => raw3507step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3507step2 raw3507step1; decide +kernel
      have hl : raw3507step2Labels = raw3507step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3507step1 raw3507step1Labels permutation31 permutation3
    mixedMoment B raw3507step2 raw3507step2Labels = mixedMoment B raw3507step3 raw3507step3Labels := by
      have ha : raw3507step3 = -raw3507step2 := by apply Matrix.ext; change ∀ i j, raw3507step3 i j = -(raw3507step2 i j); unfold raw3507step3 raw3507step2; decide +kernel
      have hl : raw3507step3Labels = raw3507step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node837 node837Labels := by rfl

def raw3508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3508step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3508step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3508step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3508 raw3508Labels = mixedMoment B node837 node837Labels := by
  calc
    mixedMoment B raw3508 raw3508Labels = mixedMoment B raw3508step0 raw3508step0Labels := by
      have hz : ∀ j, raw3508 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3508step0 = (fun i j => raw3508 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3508step0 raw3508; decide +kernel
      have hl : raw3508step0Labels = raw3508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3508 raw3508Labels permutation434 hz
    mixedMoment B raw3508step0 raw3508step0Labels = mixedMoment B raw3508step1 raw3508step1Labels := by
      have hz : ∀ j, raw3508step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3508step1 = (fun i j => raw3508step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3508step1 raw3508step0; decide +kernel
      have hl : raw3508step1Labels = raw3508step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3508step0 raw3508step0Labels permutation56 hz
    mixedMoment B raw3508step1 raw3508step1Labels = mixedMoment B raw3508step2 raw3508step2Labels := by
      have ha : raw3508step2 = (fun i j => raw3508step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3508step2 raw3508step1; decide +kernel
      have hl : raw3508step2Labels = raw3508step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3508step1 raw3508step1Labels permutation31 permutation3
    mixedMoment B raw3508step2 raw3508step2Labels = mixedMoment B raw3508step3 raw3508step3Labels := by
      have ha : raw3508step3 = -raw3508step2 := by apply Matrix.ext; change ∀ i j, raw3508step3 i j = -(raw3508step2 i j); unfold raw3508step3 raw3508step2; decide +kernel
      have hl : raw3508step3Labels = raw3508step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node837 node837Labels := by rfl

def raw3509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3509step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3509step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3509step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3509 raw3509Labels = mixedMoment B node837 node837Labels := by
  calc
    mixedMoment B raw3509 raw3509Labels = mixedMoment B raw3509step0 raw3509step0Labels := by
      have hz : ∀ j, raw3509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3509step0 = (fun i j => raw3509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3509step0 raw3509; decide +kernel
      have hl : raw3509step0Labels = raw3509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3509 raw3509Labels permutation346 hz
    mixedMoment B raw3509step0 raw3509step0Labels = mixedMoment B raw3509step1 raw3509step1Labels := by
      have hz : ∀ j, raw3509step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3509step1 = (fun i j => raw3509step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3509step1 raw3509step0; decide +kernel
      have hl : raw3509step1Labels = raw3509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3509step0 raw3509step0Labels permutation56 hz
    mixedMoment B raw3509step1 raw3509step1Labels = mixedMoment B raw3509step2 raw3509step2Labels := by
      have ha : raw3509step2 = (fun i j => raw3509step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3509step2 raw3509step1; decide +kernel
      have hl : raw3509step2Labels = raw3509step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3509step1 raw3509step1Labels permutation31 permutation3
    mixedMoment B raw3509step2 raw3509step2Labels = mixedMoment B raw3509step3 raw3509step3Labels := by
      have ha : raw3509step3 = -raw3509step2 := by apply Matrix.ext; change ∀ i j, raw3509step3 i j = -(raw3509step2 i j); unfold raw3509step3 raw3509step2; decide +kernel
      have hl : raw3509step3Labels = raw3509step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node837 node837Labels := by rfl

def raw3510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3510step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3510step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 4, -3], ![4, -4, 0]]
def raw3510step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3510step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -3, 4], ![-3, 3, 0]]
def raw3510step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3510step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 3, -4], ![3, -3, 0]]
def raw3510step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3510 raw3510Labels = mixedMoment B node861 node861Labels := by
  calc
    mixedMoment B raw3510 raw3510Labels = mixedMoment B raw3510step0 raw3510step0Labels := by
      have hz : ∀ j, raw3510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3510step0 = (fun i j => raw3510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3510step0 raw3510; decide +kernel
      have hl : raw3510step0Labels = raw3510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3510 raw3510Labels permutation434 hz
    mixedMoment B raw3510step0 raw3510step0Labels = mixedMoment B raw3510step1 raw3510step1Labels := by
      have hz : ∀ j, raw3510step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3510step1 = (fun i j => raw3510step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3510step1 raw3510step0; decide +kernel
      have hl : raw3510step1Labels = raw3510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3510step0 raw3510step0Labels permutation80 hz
    mixedMoment B raw3510step1 raw3510step1Labels = mixedMoment B raw3510step2 raw3510step2Labels := by
      have hz : ∀ j, raw3510step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3510step2 = (fun i j => raw3510step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3510step2 raw3510step1; decide +kernel
      have hl : raw3510step2Labels = raw3510step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3510step1 raw3510step1Labels permutation14 hz
    mixedMoment B raw3510step2 raw3510step2Labels = mixedMoment B raw3510step3 raw3510step3Labels := by
      have ha : raw3510step3 = (fun i j => raw3510step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3510step3 raw3510step2; decide +kernel
      have hl : raw3510step3Labels = raw3510step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3510step2 raw3510step2Labels permutation7 permutation3
    mixedMoment B raw3510step3 raw3510step3Labels = mixedMoment B raw3510step4 raw3510step4Labels := by
      have ha : raw3510step4 = -raw3510step3 := by apply Matrix.ext; change ∀ i j, raw3510step4 i j = -(raw3510step3 i j); unfold raw3510step4 raw3510step3; decide +kernel
      have hl : raw3510step4Labels = raw3510step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node861 node861Labels := by rfl

def raw3511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3511step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw3511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3511 raw3511Labels = mixedMoment B node2285 node2285Labels := by
  calc
    mixedMoment B raw3511 raw3511Labels = mixedMoment B raw3511step0 raw3511step0Labels := by
      have hz : ∀ j, raw3511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3511step0 = (fun i j => raw3511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3511step0 raw3511; decide +kernel
      have hl : raw3511step0Labels = raw3511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3511 raw3511Labels permutation434 hz
    mixedMoment B raw3511step0 raw3511step0Labels = mixedMoment B raw3511step1 raw3511step1Labels := by
      have hz : ∀ j, raw3511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3511step1 = (fun i j => raw3511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3511step1 raw3511step0; decide +kernel
      have hl : raw3511step1Labels = raw3511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3511step0 raw3511step0Labels permutation80 hz
    mixedMoment B raw3511step1 raw3511step1Labels = mixedMoment B raw3511step2 raw3511step2Labels := by
      have hz : ∀ j, raw3511step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3511step2 = (fun i j => raw3511step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3511step2 raw3511step1; decide +kernel
      have hl : raw3511step2Labels = raw3511step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3511step1 raw3511step1Labels permutation14 hz
    _ = mixedMoment B node2285 node2285Labels := by rfl

def raw3512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3512step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3512step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3512 raw3512Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3512 raw3512Labels = mixedMoment B raw3512step0 raw3512step0Labels := by
      have hz : ∀ j, raw3512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3512step0 = (fun i j => raw3512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3512step0 raw3512; decide +kernel
      have hl : raw3512step0Labels = raw3512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3512 raw3512Labels permutation434 hz
    mixedMoment B raw3512step0 raw3512step0Labels = mixedMoment B raw3512step1 raw3512step1Labels := by
      have hz : ∀ j, raw3512step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3512step1 = (fun i j => raw3512step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3512step1 raw3512step0; decide +kernel
      have hl : raw3512step1Labels = raw3512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3512step0 raw3512step0Labels permutation80 hz
    mixedMoment B raw3512step1 raw3512step1Labels = mixedMoment B raw3512step2 raw3512step2Labels := by
      have ha : raw3512step2 = (fun i j => raw3512step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3512step2 raw3512step1; decide +kernel
      have hl : raw3512step2Labels = raw3512step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3512step1 raw3512step1Labels permutation22 permutation4
    mixedMoment B raw3512step2 raw3512step2Labels = mixedMoment B raw3512step3 raw3512step3Labels := by
      have ha : raw3512step3 = -raw3512step2 := by apply Matrix.ext; change ∀ i j, raw3512step3 i j = -(raw3512step2 i j); unfold raw3512step3 raw3512step2; decide +kernel
      have hl : raw3512step3Labels = raw3512step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

def raw3513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3513step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3513 raw3513Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3513 raw3513Labels = mixedMoment B raw3513step0 raw3513step0Labels := by
      have hz : ∀ j, raw3513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3513step0 = (fun i j => raw3513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3513step0 raw3513; decide +kernel
      have hl : raw3513step0Labels = raw3513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3513 raw3513Labels permutation434 hz
    mixedMoment B raw3513step0 raw3513step0Labels = mixedMoment B raw3513step1 raw3513step1Labels := by
      have hz : ∀ j, raw3513step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3513step1 = (fun i j => raw3513step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3513step1 raw3513step0; decide +kernel
      have hl : raw3513step1Labels = raw3513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3513step0 raw3513step0Labels permutation56 hz
    mixedMoment B raw3513step1 raw3513step1Labels = mixedMoment B raw3513step2 raw3513step2Labels := by
      have ha : raw3513step2 = (fun i j => raw3513step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3513step2 raw3513step1; decide +kernel
      have hl : raw3513step2Labels = raw3513step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3513step1 raw3513step1Labels permutation22 permutation4
    mixedMoment B raw3513step2 raw3513step2Labels = mixedMoment B raw3513step3 raw3513step3Labels := by
      have ha : raw3513step3 = -raw3513step2 := by apply Matrix.ext; change ∀ i j, raw3513step3 i j = -(raw3513step2 i j); unfold raw3513step3 raw3513step2; decide +kernel
      have hl : raw3513step3Labels = raw3513step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

def raw3514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3514step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3514 raw3514Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3514 raw3514Labels = mixedMoment B raw3514step0 raw3514step0Labels := by
      have hz : ∀ j, raw3514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3514step0 = (fun i j => raw3514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3514step0 raw3514; decide +kernel
      have hl : raw3514step0Labels = raw3514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3514 raw3514Labels permutation346 hz
    mixedMoment B raw3514step0 raw3514step0Labels = mixedMoment B raw3514step1 raw3514step1Labels := by
      have hz : ∀ j, raw3514step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3514step1 = (fun i j => raw3514step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3514step1 raw3514step0; decide +kernel
      have hl : raw3514step1Labels = raw3514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3514step0 raw3514step0Labels permutation56 hz
    mixedMoment B raw3514step1 raw3514step1Labels = mixedMoment B raw3514step2 raw3514step2Labels := by
      have ha : raw3514step2 = (fun i j => raw3514step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3514step2 raw3514step1; decide +kernel
      have hl : raw3514step2Labels = raw3514step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3514step1 raw3514step1Labels permutation22 permutation4
    mixedMoment B raw3514step2 raw3514step2Labels = mixedMoment B raw3514step3 raw3514step3Labels := by
      have ha : raw3514step3 = -raw3514step2 := by apply Matrix.ext; change ∀ i j, raw3514step3 i j = -(raw3514step2 i j); unfold raw3514step3 raw3514step2; decide +kernel
      have hl : raw3514step3Labels = raw3514step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

def raw3515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![3, -3, 0]]
def raw3515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -2, 3], ![-3, 3, 0]]
def raw3515step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3515step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3515step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3515 raw3515Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw3515 raw3515Labels = mixedMoment B raw3515step0 raw3515step0Labels := by
      have hz : ∀ j, raw3515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3515step0 = (fun i j => raw3515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3515step0 raw3515; decide +kernel
      have hl : raw3515step0Labels = raw3515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3515 raw3515Labels permutation434 hz
    mixedMoment B raw3515step0 raw3515step0Labels = mixedMoment B raw3515step1 raw3515step1Labels := by
      have hz : ∀ j, raw3515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3515step1 = (fun i j => raw3515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3515step1 raw3515step0; decide +kernel
      have hl : raw3515step1Labels = raw3515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3515step0 raw3515step0Labels permutation80 hz
    mixedMoment B raw3515step1 raw3515step1Labels = mixedMoment B raw3515step2 raw3515step2Labels := by
      have hz : ∀ j, raw3515step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3515step2 = (fun i j => raw3515step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3515step2 raw3515step1; decide +kernel
      have hl : raw3515step2Labels = raw3515step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3515step1 raw3515step1Labels permutation14 hz
    mixedMoment B raw3515step2 raw3515step2Labels = mixedMoment B raw3515step3 raw3515step3Labels := by
      have ha : raw3515step3 = (fun i j => raw3515step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3515step3 raw3515step2; decide +kernel
      have hl : raw3515step3Labels = raw3515step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3515step2 raw3515step2Labels permutation4 permutation4
    mixedMoment B raw3515step3 raw3515step3Labels = mixedMoment B raw3515step4 raw3515step4Labels := by
      have ha : raw3515step4 = -raw3515step3 := by apply Matrix.ext; change ∀ i j, raw3515step4 i j = -(raw3515step3 i j); unfold raw3515step4 raw3515step3; decide +kernel
      have hl : raw3515step4Labels = raw3515step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1092 node1092Labels := by rfl

def raw3516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]
def raw3516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw3516step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3516step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw3516step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3516 raw3516Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw3516 raw3516Labels = mixedMoment B raw3516step0 raw3516step0Labels := by
      have hz : ∀ j, raw3516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3516step0 = (fun i j => raw3516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3516step0 raw3516; decide +kernel
      have hl : raw3516step0Labels = raw3516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3516 raw3516Labels permutation434 hz
    mixedMoment B raw3516step0 raw3516step0Labels = mixedMoment B raw3516step1 raw3516step1Labels := by
      have hz : ∀ j, raw3516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3516step1 = (fun i j => raw3516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3516step1 raw3516step0; decide +kernel
      have hl : raw3516step1Labels = raw3516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3516step0 raw3516step0Labels permutation80 hz
    mixedMoment B raw3516step1 raw3516step1Labels = mixedMoment B raw3516step2 raw3516step2Labels := by
      have hz : ∀ j, raw3516step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3516step2 = (fun i j => raw3516step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3516step2 raw3516step1; decide +kernel
      have hl : raw3516step2Labels = raw3516step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3516step1 raw3516step1Labels permutation14 hz
    mixedMoment B raw3516step2 raw3516step2Labels = mixedMoment B raw3516step3 raw3516step3Labels := by
      have ha : raw3516step3 = (fun i j => raw3516step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3516step3 raw3516step2; decide +kernel
      have hl : raw3516step3Labels = raw3516step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3516step2 raw3516step2Labels permutation4 permutation4
    mixedMoment B raw3516step3 raw3516step3Labels = mixedMoment B raw3516step4 raw3516step4Labels := by
      have ha : raw3516step4 = -raw3516step3 := by apply Matrix.ext; change ∀ i j, raw3516step4 i j = -(raw3516step3 i j); unfold raw3516step4 raw3516step3; decide +kernel
      have hl : raw3516step4Labels = raw3516step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw3517 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![3, -3], ![0, 0]]
def raw3517Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3517step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw3517step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3517step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]
def raw3517step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3517step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]
def raw3517step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3517step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw3517step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3517 raw3517Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3517 raw3517Labels = mixedMoment B raw3517step0 raw3517step0Labels := by
      have hz : ∀ j, raw3517 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3517step0 = (fun i j => raw3517 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3517step0 raw3517; decide +kernel
      have hl : raw3517step0Labels = raw3517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517 raw3517Labels permutation590 hz
    mixedMoment B raw3517step0 raw3517step0Labels = mixedMoment B raw3517step1 raw3517step1Labels := by
      have hz : ∀ j, raw3517step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3517step1 = (fun i j => raw3517step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3517step1 raw3517step0; decide +kernel
      have hl : raw3517step1Labels = raw3517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step0 raw3517step0Labels permutation104 hz
    mixedMoment B raw3517step1 raw3517step1Labels = mixedMoment B raw3517step2 raw3517step2Labels := by
      have hz : ∀ j, raw3517step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3517step2 = (fun i j => raw3517step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3517step2 raw3517step1; decide +kernel
      have hl : raw3517step2Labels = raw3517step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step1 raw3517step1Labels permutation20 hz
    mixedMoment B raw3517step2 raw3517step2Labels = mixedMoment B raw3517step3 raw3517step3Labels := by
      have hz : ∀ j, raw3517step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3517step3 = (fun i j => raw3517step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3517step3 raw3517step2; decide +kernel
      have hl : raw3517step3Labels = raw3517step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step2 raw3517step2Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

def raw3518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3518 raw3518Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3518 raw3518Labels = mixedMoment B raw3518step0 raw3518step0Labels := by
      have hz : ∀ j, raw3518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3518step0 = (fun i j => raw3518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3518step0 raw3518; decide +kernel
      have hl : raw3518step0Labels = raw3518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3518 raw3518Labels permutation434 hz
    mixedMoment B raw3518step0 raw3518step0Labels = mixedMoment B raw3518step1 raw3518step1Labels := by
      have hz : ∀ j, raw3518step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3518step1 = (fun i j => raw3518step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3518step1 raw3518step0; decide +kernel
      have hl : raw3518step1Labels = raw3518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3518step0 raw3518step0Labels permutation80 hz
    mixedMoment B raw3518step1 raw3518step1Labels = mixedMoment B raw3518step2 raw3518step2Labels := by
      have ha : raw3518step2 = (fun i j => raw3518step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3518step2 raw3518step1; decide +kernel
      have hl : raw3518step2Labels = raw3518step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3518step1 raw3518step1Labels permutation10 permutation2
    _ = mixedMoment B node1067 node1067Labels := by rfl

def raw3519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3519 raw3519Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3519 raw3519Labels = mixedMoment B raw3519step0 raw3519step0Labels := by
      have hz : ∀ j, raw3519 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3519step0 = (fun i j => raw3519 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3519step0 raw3519; decide +kernel
      have hl : raw3519step0Labels = raw3519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3519 raw3519Labels permutation434 hz
    mixedMoment B raw3519step0 raw3519step0Labels = mixedMoment B raw3519step1 raw3519step1Labels := by
      have hz : ∀ j, raw3519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3519step1 = (fun i j => raw3519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3519step1 raw3519step0; decide +kernel
      have hl : raw3519step1Labels = raw3519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3519step0 raw3519step0Labels permutation56 hz
    mixedMoment B raw3519step1 raw3519step1Labels = mixedMoment B raw3519step2 raw3519step2Labels := by
      have ha : raw3519step2 = (fun i j => raw3519step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3519step2 raw3519step1; decide +kernel
      have hl : raw3519step2Labels = raw3519step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3519step1 raw3519step1Labels permutation10 permutation2
    _ = mixedMoment B node1067 node1067Labels := by rfl

def raw3520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3520step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3520 raw3520Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3520 raw3520Labels = mixedMoment B raw3520step0 raw3520step0Labels := by
      have hz : ∀ j, raw3520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3520step0 = (fun i j => raw3520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3520step0 raw3520; decide +kernel
      have hl : raw3520step0Labels = raw3520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3520 raw3520Labels permutation346 hz
    mixedMoment B raw3520step0 raw3520step0Labels = mixedMoment B raw3520step1 raw3520step1Labels := by
      have hz : ∀ j, raw3520step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3520step1 = (fun i j => raw3520step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3520step1 raw3520step0; decide +kernel
      have hl : raw3520step1Labels = raw3520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3520step0 raw3520step0Labels permutation56 hz
    mixedMoment B raw3520step1 raw3520step1Labels = mixedMoment B raw3520step2 raw3520step2Labels := by
      have ha : raw3520step2 = (fun i j => raw3520step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3520step2 raw3520step1; decide +kernel
      have hl : raw3520step2Labels = raw3520step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3520step1 raw3520step1Labels permutation10 permutation2
    _ = mixedMoment B node1067 node1067Labels := by rfl

def raw3521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3521 raw3521Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw3521 raw3521Labels = mixedMoment B raw3521step0 raw3521step0Labels := by
      have hz : ∀ j, raw3521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3521step0 = (fun i j => raw3521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3521step0 raw3521; decide +kernel
      have hl : raw3521step0Labels = raw3521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3521 raw3521Labels permutation434 hz
    mixedMoment B raw3521step0 raw3521step0Labels = mixedMoment B raw3521step1 raw3521step1Labels := by
      have hz : ∀ j, raw3521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3521step1 = (fun i j => raw3521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3521step1 raw3521step0; decide +kernel
      have hl : raw3521step1Labels = raw3521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3521step0 raw3521step0Labels permutation80 hz
    mixedMoment B raw3521step1 raw3521step1Labels = mixedMoment B raw3521step2 raw3521step2Labels := by
      have hz : ∀ j, raw3521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3521step2 = (fun i j => raw3521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3521step2 raw3521step1; decide +kernel
      have hl : raw3521step2Labels = raw3521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3521step1 raw3521step1Labels permutation14 hz
    _ = mixedMoment B node1092 node1092Labels := by rfl

def raw3522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3522step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![4, -4, 0]]
def raw3522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3522 raw3522Labels = mixedMoment B node1069 node1069Labels := by
  calc
    mixedMoment B raw3522 raw3522Labels = mixedMoment B raw3522step0 raw3522step0Labels := by
      have hz : ∀ j, raw3522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3522step0 = (fun i j => raw3522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3522step0 raw3522; decide +kernel
      have hl : raw3522step0Labels = raw3522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3522 raw3522Labels permutation434 hz
    mixedMoment B raw3522step0 raw3522step0Labels = mixedMoment B raw3522step1 raw3522step1Labels := by
      have hz : ∀ j, raw3522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3522step1 = (fun i j => raw3522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3522step1 raw3522step0; decide +kernel
      have hl : raw3522step1Labels = raw3522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3522step0 raw3522step0Labels permutation80 hz
    mixedMoment B raw3522step1 raw3522step1Labels = mixedMoment B raw3522step2 raw3522step2Labels := by
      have hz : ∀ j, raw3522step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3522step2 = (fun i j => raw3522step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3522step2 raw3522step1; decide +kernel
      have hl : raw3522step2Labels = raw3522step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3522step1 raw3522step1Labels permutation14 hz
    _ = mixedMoment B node1069 node1069Labels := by rfl

def raw3523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3523 raw3523Labels = mixedMoment B node2041 node2041Labels := by
  calc
    mixedMoment B raw3523 raw3523Labels = mixedMoment B raw3523step0 raw3523step0Labels := by
      have hz : ∀ j, raw3523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3523step0 = (fun i j => raw3523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3523step0 raw3523; decide +kernel
      have hl : raw3523step0Labels = raw3523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3523 raw3523Labels permutation434 hz
    mixedMoment B raw3523step0 raw3523step0Labels = mixedMoment B raw3523step1 raw3523step1Labels := by
      have ha : raw3523step1 = (fun i j => raw3523step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3523step1 raw3523step0; decide +kernel
      have hl : raw3523step1Labels = raw3523step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3523step0 raw3523step0Labels permutation40 permutation2
    _ = mixedMoment B node2041 node2041Labels := by rfl

def raw3524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3524 raw3524Labels = mixedMoment B node2041 node2041Labels := by
  calc
    mixedMoment B raw3524 raw3524Labels = mixedMoment B raw3524step0 raw3524step0Labels := by
      have hz : ∀ j, raw3524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3524step0 = (fun i j => raw3524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3524step0 raw3524; decide +kernel
      have hl : raw3524step0Labels = raw3524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3524 raw3524Labels permutation346 hz
    mixedMoment B raw3524step0 raw3524step0Labels = mixedMoment B raw3524step1 raw3524step1Labels := by
      have ha : raw3524step1 = (fun i j => raw3524step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3524step1 raw3524step0; decide +kernel
      have hl : raw3524step1Labels = raw3524step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3524step0 raw3524step0Labels permutation40 permutation2
    _ = mixedMoment B node2041 node2041Labels := by rfl

def raw3525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-3, 3, 0]]
def raw3525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3525step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3525 raw3525Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3525 raw3525Labels = mixedMoment B raw3525step0 raw3525step0Labels := by
      have hz : ∀ j, raw3525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3525step0 = (fun i j => raw3525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3525step0 raw3525; decide +kernel
      have hl : raw3525step0Labels = raw3525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3525 raw3525Labels permutation434 hz
    mixedMoment B raw3525step0 raw3525step0Labels = mixedMoment B raw3525step1 raw3525step1Labels := by
      have hz : ∀ j, raw3525step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3525step1 = (fun i j => raw3525step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3525step1 raw3525step0; decide +kernel
      have hl : raw3525step1Labels = raw3525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3525step0 raw3525step0Labels permutation80 hz
    mixedMoment B raw3525step1 raw3525step1Labels = mixedMoment B raw3525step2 raw3525step2Labels := by
      have ha : raw3525step2 = (fun i j => raw3525step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3525step2 raw3525step1; decide +kernel
      have hl : raw3525step2Labels = raw3525step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3525step1 raw3525step1Labels permutation20 permutation4
    mixedMoment B raw3525step2 raw3525step2Labels = mixedMoment B raw3525step3 raw3525step3Labels := by
      have ha : raw3525step3 = -raw3525step2 := by apply Matrix.ext; change ∀ i j, raw3525step3 i j = -(raw3525step2 i j); unfold raw3525step3 raw3525step2; decide +kernel
      have hl : raw3525step3Labels = raw3525step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1067 node1067Labels := by rfl

def raw3526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3526 raw3526Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw3526 raw3526Labels = mixedMoment B raw3526step0 raw3526step0Labels := by
      have hz : ∀ j, raw3526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3526step0 = (fun i j => raw3526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3526step0 raw3526; decide +kernel
      have hl : raw3526step0Labels = raw3526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3526 raw3526Labels permutation434 hz
    mixedMoment B raw3526step0 raw3526step0Labels = mixedMoment B raw3526step1 raw3526step1Labels := by
      have hz : ∀ j, raw3526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3526step1 = (fun i j => raw3526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3526step1 raw3526step0; decide +kernel
      have hl : raw3526step1Labels = raw3526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3526step0 raw3526step0Labels permutation80 hz
    mixedMoment B raw3526step1 raw3526step1Labels = mixedMoment B raw3526step2 raw3526step2Labels := by
      have ha : raw3526step2 = (fun i j => raw3526step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3526step2 raw3526step1; decide +kernel
      have hl : raw3526step2Labels = raw3526step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3526step1 raw3526step1Labels permutation10 permutation2
    _ = mixedMoment B node2284 node2284Labels := by rfl

def raw3527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3527 raw3527Labels = mixedMoment B node2041 node2041Labels := by
  calc
    mixedMoment B raw3527 raw3527Labels = mixedMoment B raw3527step0 raw3527step0Labels := by
      have hz : ∀ j, raw3527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3527step0 = (fun i j => raw3527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3527step0 raw3527; decide +kernel
      have hl : raw3527step0Labels = raw3527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3527 raw3527Labels permutation434 hz
    mixedMoment B raw3527step0 raw3527step0Labels = mixedMoment B raw3527step1 raw3527step1Labels := by
      have ha : raw3527step1 = (fun i j => raw3527step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3527step1 raw3527step0; decide +kernel
      have hl : raw3527step1Labels = raw3527step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3527step0 raw3527step0Labels permutation34 permutation2
    _ = mixedMoment B node2041 node2041Labels := by rfl

def raw3528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3528 raw3528Labels = mixedMoment B node2041 node2041Labels := by
  calc
    mixedMoment B raw3528 raw3528Labels = mixedMoment B raw3528step0 raw3528step0Labels := by
      have hz : ∀ j, raw3528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3528step0 = (fun i j => raw3528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3528step0 raw3528; decide +kernel
      have hl : raw3528step0Labels = raw3528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3528 raw3528Labels permutation346 hz
    mixedMoment B raw3528step0 raw3528step0Labels = mixedMoment B raw3528step1 raw3528step1Labels := by
      have ha : raw3528step1 = (fun i j => raw3528step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3528step1 raw3528step0; decide +kernel
      have hl : raw3528step1Labels = raw3528step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3528step0 raw3528step0Labels permutation34 permutation2
    _ = mixedMoment B node2041 node2041Labels := by rfl

def raw3529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3529 raw3529Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3529 raw3529Labels = mixedMoment B raw3529step0 raw3529step0Labels := by
      have hz : ∀ j, raw3529 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3529step0 = (fun i j => raw3529 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3529step0 raw3529; decide +kernel
      have hl : raw3529step0Labels = raw3529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3529 raw3529Labels permutation434 hz
    mixedMoment B raw3529step0 raw3529step0Labels = mixedMoment B raw3529step1 raw3529step1Labels := by
      have hz : ∀ j, raw3529step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3529step1 = (fun i j => raw3529step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3529step1 raw3529step0; decide +kernel
      have hl : raw3529step1Labels = raw3529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3529step0 raw3529step0Labels permutation80 hz
    _ = mixedMoment B node2063 node2063Labels := by rfl

def raw3530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 3, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw3530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3530step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![3, 0, -3]]
def raw3530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3530 raw3530Labels = mixedMoment B node1459 node1459Labels := by
  calc
    mixedMoment B raw3530 raw3530Labels = mixedMoment B raw3530step0 raw3530step0Labels := by
      have hz : ∀ j, raw3530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3530step0 = (fun i j => raw3530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3530step0 raw3530; decide +kernel
      have hl : raw3530step0Labels = raw3530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3530 raw3530Labels permutation434 hz
    mixedMoment B raw3530step0 raw3530step0Labels = mixedMoment B raw3530step1 raw3530step1Labels := by
      have hz : ∀ j, raw3530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3530step1 = (fun i j => raw3530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3530step1 raw3530step0; decide +kernel
      have hl : raw3530step1Labels = raw3530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3530step0 raw3530step0Labels permutation80 hz
    mixedMoment B raw3530step1 raw3530step1Labels = mixedMoment B raw3530step2 raw3530step2Labels := by
      have ha : raw3530step2 = (fun i j => raw3530step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3530step2 raw3530step1; decide +kernel
      have hl : raw3530step2Labels = raw3530step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3530step1 raw3530step1Labels permutation31 permutation2
    mixedMoment B raw3530step2 raw3530step2Labels = mixedMoment B raw3530step3 raw3530step3Labels := by
      have ha : raw3530step3 = -raw3530step2 := by apply Matrix.ext; change ∀ i j, raw3530step3 i j = -(raw3530step2 i j); unfold raw3530step3 raw3530step2; decide +kernel
      have hl : raw3530step3Labels = raw3530step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1459 node1459Labels := by rfl

def raw3531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 3, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw3531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3531step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![3, 0, -3]]
def raw3531step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3531 raw3531Labels = mixedMoment B node1459 node1459Labels := by
  calc
    mixedMoment B raw3531 raw3531Labels = mixedMoment B raw3531step0 raw3531step0Labels := by
      have hz : ∀ j, raw3531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3531step0 = (fun i j => raw3531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3531step0 raw3531; decide +kernel
      have hl : raw3531step0Labels = raw3531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3531 raw3531Labels permutation434 hz
    mixedMoment B raw3531step0 raw3531step0Labels = mixedMoment B raw3531step1 raw3531step1Labels := by
      have hz : ∀ j, raw3531step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3531step1 = (fun i j => raw3531step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3531step1 raw3531step0; decide +kernel
      have hl : raw3531step1Labels = raw3531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3531step0 raw3531step0Labels permutation56 hz
    mixedMoment B raw3531step1 raw3531step1Labels = mixedMoment B raw3531step2 raw3531step2Labels := by
      have ha : raw3531step2 = (fun i j => raw3531step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3531step2 raw3531step1; decide +kernel
      have hl : raw3531step2Labels = raw3531step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3531step1 raw3531step1Labels permutation31 permutation2
    mixedMoment B raw3531step2 raw3531step2Labels = mixedMoment B raw3531step3 raw3531step3Labels := by
      have ha : raw3531step3 = -raw3531step2 := by apply Matrix.ext; change ∀ i j, raw3531step3 i j = -(raw3531step2 i j); unfold raw3531step3 raw3531step2; decide +kernel
      have hl : raw3531step3Labels = raw3531step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1459 node1459Labels := by rfl

def raw3532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![4, -4, 0]]
def raw3532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 3, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw3532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3532step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![3, 0, -3]]
def raw3532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3532 raw3532Labels = mixedMoment B node1459 node1459Labels := by
  calc
    mixedMoment B raw3532 raw3532Labels = mixedMoment B raw3532step0 raw3532step0Labels := by
      have hz : ∀ j, raw3532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3532step0 = (fun i j => raw3532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3532step0 raw3532; decide +kernel
      have hl : raw3532step0Labels = raw3532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3532 raw3532Labels permutation346 hz
    mixedMoment B raw3532step0 raw3532step0Labels = mixedMoment B raw3532step1 raw3532step1Labels := by
      have hz : ∀ j, raw3532step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3532step1 = (fun i j => raw3532step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3532step1 raw3532step0; decide +kernel
      have hl : raw3532step1Labels = raw3532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3532step0 raw3532step0Labels permutation56 hz
    mixedMoment B raw3532step1 raw3532step1Labels = mixedMoment B raw3532step2 raw3532step2Labels := by
      have ha : raw3532step2 = (fun i j => raw3532step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3532step2 raw3532step1; decide +kernel
      have hl : raw3532step2Labels = raw3532step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3532step1 raw3532step1Labels permutation31 permutation2
    mixedMoment B raw3532step2 raw3532step2Labels = mixedMoment B raw3532step3 raw3532step3Labels := by
      have ha : raw3532step3 = -raw3532step2 := by apply Matrix.ext; change ∀ i j, raw3532step3 i j = -(raw3532step2 i j); unfold raw3532step3 raw3532step2; decide +kernel
      have hl : raw3532step3Labels = raw3532step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1459 node1459Labels := by rfl

def raw3533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 4, -3], ![4, -4, 0]]
def raw3533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 4, -3], ![4, -4, 0]]
def raw3533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-4, 4, 0]]
def raw3533step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3533step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![4, -4, 0]]
def raw3533step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3533 raw3533Labels = mixedMoment B node1069 node1069Labels := by
  calc
    mixedMoment B raw3533 raw3533Labels = mixedMoment B raw3533step0 raw3533step0Labels := by
      have hz : ∀ j, raw3533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3533step0 = (fun i j => raw3533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3533step0 raw3533; decide +kernel
      have hl : raw3533step0Labels = raw3533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3533 raw3533Labels permutation434 hz
    mixedMoment B raw3533step0 raw3533step0Labels = mixedMoment B raw3533step1 raw3533step1Labels := by
      have hz : ∀ j, raw3533step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3533step1 = (fun i j => raw3533step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3533step1 raw3533step0; decide +kernel
      have hl : raw3533step1Labels = raw3533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3533step0 raw3533step0Labels permutation80 hz
    mixedMoment B raw3533step1 raw3533step1Labels = mixedMoment B raw3533step2 raw3533step2Labels := by
      have hz : ∀ j, raw3533step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3533step2 = (fun i j => raw3533step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3533step2 raw3533step1; decide +kernel
      have hl : raw3533step2Labels = raw3533step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3533step1 raw3533step1Labels permutation14 hz
    mixedMoment B raw3533step2 raw3533step2Labels = mixedMoment B raw3533step3 raw3533step3Labels := by
      have ha : raw3533step3 = (fun i j => raw3533step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3533step3 raw3533step2; decide +kernel
      have hl : raw3533step3Labels = raw3533step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3533step2 raw3533step2Labels permutation4 permutation4
    mixedMoment B raw3533step3 raw3533step3Labels = mixedMoment B raw3533step4 raw3533step4Labels := by
      have ha : raw3533step4 = -raw3533step3 := by apply Matrix.ext; change ∀ i j, raw3533step4 i j = -(raw3533step3 i j); unfold raw3533step4 raw3533step3; decide +kernel
      have hl : raw3533step4Labels = raw3533step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1069 node1069Labels := by rfl

def raw3534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3534step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3534step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3534 raw3534Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw3534 raw3534Labels = mixedMoment B raw3534step0 raw3534step0Labels := by
      have hz : ∀ j, raw3534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3534step0 = (fun i j => raw3534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3534step0 raw3534; decide +kernel
      have hl : raw3534step0Labels = raw3534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3534 raw3534Labels permutation346 hz
    mixedMoment B raw3534step0 raw3534step0Labels = mixedMoment B raw3534step1 raw3534step1Labels := by
      have ha : raw3534step1 = (fun i j => raw3534step0 (permutation130 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3534step1 raw3534step0; decide +kernel
      have hl : raw3534step1Labels = raw3534step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3534step0 raw3534step0Labels permutation130 permutation5
    mixedMoment B raw3534step1 raw3534step1Labels = mixedMoment B raw3534step2 raw3534step2Labels := by
      have ha : raw3534step2 = raw3534step1 := by apply Matrix.ext; unfold raw3534step2 raw3534step1; decide +kernel
      have hl : raw3534step1Labels = labelEmbedding8 ∘ raw3534step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3534step1 raw3534step1Labels raw3534step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw3535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3535step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3535 raw3535Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw3535 raw3535Labels = mixedMoment B raw3535step0 raw3535step0Labels := by
      have hz : ∀ j, raw3535 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3535step0 = (fun i j => raw3535 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3535step0 raw3535; decide +kernel
      have hl : raw3535step0Labels = raw3535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3535 raw3535Labels permutation265 hz
    mixedMoment B raw3535step0 raw3535step0Labels = mixedMoment B raw3535step1 raw3535step1Labels := by
      have ha : raw3535step1 = (fun i j => raw3535step0 (permutation130 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3535step1 raw3535step0; decide +kernel
      have hl : raw3535step1Labels = raw3535step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3535step0 raw3535step0Labels permutation130 permutation5
    mixedMoment B raw3535step1 raw3535step1Labels = mixedMoment B raw3535step2 raw3535step2Labels := by
      have ha : raw3535step2 = raw3535step1 := by apply Matrix.ext; unfold raw3535step2 raw3535step1; decide +kernel
      have hl : raw3535step1Labels = labelEmbedding8 ∘ raw3535step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3535step1 raw3535step1Labels raw3535step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw3536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw3536step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3536step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw3536step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3536 raw3536Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw3536 raw3536Labels = mixedMoment B raw3536step0 raw3536step0Labels := by
      have hz : ∀ j, raw3536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3536step0 = (fun i j => raw3536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3536step0 raw3536; decide +kernel
      have hl : raw3536step0Labels = raw3536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3536 raw3536Labels permutation346 hz
    mixedMoment B raw3536step0 raw3536step0Labels = mixedMoment B raw3536step1 raw3536step1Labels := by
      have hz : ∀ j, raw3536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3536step1 = (fun i j => raw3536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3536step1 raw3536step0; decide +kernel
      have hl : raw3536step1Labels = raw3536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3536step0 raw3536step0Labels permutation56 hz
    mixedMoment B raw3536step1 raw3536step1Labels = mixedMoment B raw3536step2 raw3536step2Labels := by
      have ha : raw3536step2 = (fun i j => raw3536step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3536step2 raw3536step1; decide +kernel
      have hl : raw3536step2Labels = raw3536step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3536step1 raw3536step1Labels permutation27 permutation5
    mixedMoment B raw3536step2 raw3536step2Labels = mixedMoment B raw3536step3 raw3536step3Labels := by
      have ha : raw3536step3 = raw3536step2 := by apply Matrix.ext; unfold raw3536step3 raw3536step2; decide +kernel
      have hl : raw3536step2Labels = labelEmbedding8 ∘ raw3536step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3536step2 raw3536step2Labels raw3536step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4884 node4884Labels := by rfl

def raw3537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3537step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3537step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3537step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3537 raw3537Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw3537 raw3537Labels = mixedMoment B raw3537step0 raw3537step0Labels := by
      have hz : ∀ j, raw3537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3537step0 = (fun i j => raw3537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3537step0 raw3537; decide +kernel
      have hl : raw3537step0Labels = raw3537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3537 raw3537Labels permutation346 hz
    mixedMoment B raw3537step0 raw3537step0Labels = mixedMoment B raw3537step1 raw3537step1Labels := by
      have hz : ∀ j, raw3537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3537step1 = (fun i j => raw3537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3537step1 raw3537step0; decide +kernel
      have hl : raw3537step1Labels = raw3537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3537step0 raw3537step0Labels permutation56 hz
    mixedMoment B raw3537step1 raw3537step1Labels = mixedMoment B raw3537step2 raw3537step2Labels := by
      have ha : raw3537step2 = (fun i j => raw3537step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3537step2 raw3537step1; decide +kernel
      have hl : raw3537step2Labels = raw3537step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3537step1 raw3537step1Labels permutation26 permutation5
    mixedMoment B raw3537step2 raw3537step2Labels = mixedMoment B raw3537step3 raw3537step3Labels := by
      have ha : raw3537step3 = raw3537step2 := by apply Matrix.ext; unfold raw3537step3 raw3537step2; decide +kernel
      have hl : raw3537step2Labels = labelEmbedding8 ∘ raw3537step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3537step2 raw3537step2Labels raw3537step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw3538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw3538step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3538step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3538step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3538step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3538step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3538 raw3538Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw3538 raw3538Labels = mixedMoment B raw3538step0 raw3538step0Labels := by
      have hz : ∀ j, raw3538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3538step0 = (fun i j => raw3538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3538step0 raw3538; decide +kernel
      have hl : raw3538step0Labels = raw3538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3538 raw3538Labels permutation346 hz
    mixedMoment B raw3538step0 raw3538step0Labels = mixedMoment B raw3538step1 raw3538step1Labels := by
      have hz : ∀ j, raw3538step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3538step1 = (fun i j => raw3538step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3538step1 raw3538step0; decide +kernel
      have hl : raw3538step1Labels = raw3538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3538step0 raw3538step0Labels permutation56 hz
    mixedMoment B raw3538step1 raw3538step1Labels = mixedMoment B raw3538step2 raw3538step2Labels := by
      have ha : raw3538step2 = (fun i j => raw3538step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3538step2 raw3538step1; decide +kernel
      have hl : raw3538step2Labels = raw3538step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3538step1 raw3538step1Labels permutation12 permutation7
    mixedMoment B raw3538step2 raw3538step2Labels = mixedMoment B raw3538step3 raw3538step3Labels := by
      have ha : raw3538step3 = -raw3538step2 := by apply Matrix.ext; change ∀ i j, raw3538step3 i j = -(raw3538step2 i j); unfold raw3538step3 raw3538step2; decide +kernel
      have hl : raw3538step3Labels = raw3538step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3538step3 raw3538step3Labels = mixedMoment B raw3538step4 raw3538step4Labels := by
      have ha : raw3538step4 = raw3538step3 := by apply Matrix.ext; unfold raw3538step4 raw3538step3; decide +kernel
      have hl : raw3538step3Labels = labelEmbedding10 ∘ raw3538step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3538step3 raw3538step3Labels raw3538step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw3539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3539 raw3539Labels = mixedMoment B node4447 node4447Labels := by
  calc
    mixedMoment B raw3539 raw3539Labels = mixedMoment B raw3539step0 raw3539step0Labels := by
      have hz : ∀ j, raw3539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3539step0 = (fun i j => raw3539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3539step0 raw3539; decide +kernel
      have hl : raw3539step0Labels = raw3539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3539 raw3539Labels permutation346 hz
    mixedMoment B raw3539step0 raw3539step0Labels = mixedMoment B raw3539step1 raw3539step1Labels := by
      have ha : raw3539step1 = (fun i j => raw3539step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3539step1 raw3539step0; decide +kernel
      have hl : raw3539step1Labels = raw3539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3539step0 raw3539step0Labels permutation40 permutation2
    _ = mixedMoment B node4447 node4447Labels := by rfl

def raw3540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3540step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3540step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3540step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3540step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3540 raw3540Labels = mixedMoment B node4734 node4734Labels := by
  calc
    mixedMoment B raw3540 raw3540Labels = mixedMoment B raw3540step0 raw3540step0Labels := by
      have ha : raw3540step0 = (fun i j => raw3540 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3540step0 raw3540; decide +kernel
      have hl : raw3540step0Labels = raw3540Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3540 raw3540Labels permutation616 permutation3
    mixedMoment B raw3540step0 raw3540step0Labels = mixedMoment B raw3540step1 raw3540step1Labels := by
      have ha : raw3540step1 = -raw3540step0 := by apply Matrix.ext; change ∀ i j, raw3540step1 i j = -(raw3540step0 i j); unfold raw3540step1 raw3540step0; decide +kernel
      have hl : raw3540step1Labels = raw3540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3540step1 raw3540step1Labels = mixedMoment B raw3540step2 raw3540step2Labels := by
      have ha : raw3540step2 = raw3540step1 := by apply Matrix.ext; unfold raw3540step2 raw3540step1; decide +kernel
      have hl : raw3540step1Labels = labelEmbedding6 ∘ raw3540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3540step1 raw3540step1Labels raw3540step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4734 node4734Labels := by rfl

def raw3541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw3541step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3541step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3541step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3541 raw3541Labels = mixedMoment B node4748 node4748Labels := by
  calc
    mixedMoment B raw3541 raw3541Labels = mixedMoment B raw3541step0 raw3541step0Labels := by
      have hz : ∀ j, raw3541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3541step0 = (fun i j => raw3541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3541step0 raw3541; decide +kernel
      have hl : raw3541step0Labels = raw3541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3541 raw3541Labels permutation346 hz
    mixedMoment B raw3541step0 raw3541step0Labels = mixedMoment B raw3541step1 raw3541step1Labels := by
      have ha : raw3541step1 = (fun i j => raw3541step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3541step1 raw3541step0; decide +kernel
      have hl : raw3541step1Labels = raw3541step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3541step0 raw3541step0Labels permutation139 permutation3
    mixedMoment B raw3541step1 raw3541step1Labels = mixedMoment B raw3541step2 raw3541step2Labels := by
      have ha : raw3541step2 = -raw3541step1 := by apply Matrix.ext; change ∀ i j, raw3541step2 i j = -(raw3541step1 i j); unfold raw3541step2 raw3541step1; decide +kernel
      have hl : raw3541step2Labels = raw3541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3541step2 raw3541step2Labels = mixedMoment B raw3541step3 raw3541step3Labels := by
      have ha : raw3541step3 = raw3541step2 := by apply Matrix.ext; unfold raw3541step3 raw3541step2; decide +kernel
      have hl : raw3541step2Labels = labelEmbedding6 ∘ raw3541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3541step2 raw3541step2Labels raw3541step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4748 node4748Labels := by rfl

def raw3542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3542step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3542step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3542step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3542step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3542 raw3542Labels = mixedMoment B node4743 node4743Labels := by
  calc
    mixedMoment B raw3542 raw3542Labels = mixedMoment B raw3542step0 raw3542step0Labels := by
      have hz : ∀ j, raw3542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3542step0 = (fun i j => raw3542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3542step0 raw3542; decide +kernel
      have hl : raw3542step0Labels = raw3542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3542 raw3542Labels permutation346 hz
    mixedMoment B raw3542step0 raw3542step0Labels = mixedMoment B raw3542step1 raw3542step1Labels := by
      have ha : raw3542step1 = (fun i j => raw3542step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3542step1 raw3542step0; decide +kernel
      have hl : raw3542step1Labels = raw3542step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3542step0 raw3542step0Labels permutation137 permutation3
    mixedMoment B raw3542step1 raw3542step1Labels = mixedMoment B raw3542step2 raw3542step2Labels := by
      have ha : raw3542step2 = -raw3542step1 := by apply Matrix.ext; change ∀ i j, raw3542step2 i j = -(raw3542step1 i j); unfold raw3542step2 raw3542step1; decide +kernel
      have hl : raw3542step2Labels = raw3542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3542step2 raw3542step2Labels = mixedMoment B raw3542step3 raw3542step3Labels := by
      have ha : raw3542step3 = raw3542step2 := by apply Matrix.ext; unfold raw3542step3 raw3542step2; decide +kernel
      have hl : raw3542step2Labels = labelEmbedding6 ∘ raw3542step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3542step2 raw3542step2Labels raw3542step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4743 node4743Labels := by rfl

def raw3543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3543 raw3543Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw3543 raw3543Labels = mixedMoment B raw3543step0 raw3543step0Labels := by
      have hz : ∀ j, raw3543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3543step0 = (fun i j => raw3543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3543step0 raw3543; decide +kernel
      have hl : raw3543step0Labels = raw3543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3543 raw3543Labels permutation346 hz
    mixedMoment B raw3543step0 raw3543step0Labels = mixedMoment B raw3543step1 raw3543step1Labels := by
      have ha : raw3543step1 = (fun i j => raw3543step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3543step1 raw3543step0; decide +kernel
      have hl : raw3543step1Labels = raw3543step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3543step0 raw3543step0Labels permutation40 permutation2
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw3544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3544 raw3544Labels = mixedMoment B node4447 node4447Labels := by
  calc
    mixedMoment B raw3544 raw3544Labels = mixedMoment B raw3544step0 raw3544step0Labels := by
      have hz : ∀ j, raw3544 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3544step0 = (fun i j => raw3544 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3544step0 raw3544; decide +kernel
      have hl : raw3544step0Labels = raw3544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3544 raw3544Labels permutation265 hz
    mixedMoment B raw3544step0 raw3544step0Labels = mixedMoment B raw3544step1 raw3544step1Labels := by
      have ha : raw3544step1 = (fun i j => raw3544step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3544step1 raw3544step0; decide +kernel
      have hl : raw3544step1Labels = raw3544step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3544step0 raw3544step0Labels permutation40 permutation2
    _ = mixedMoment B node4447 node4447Labels := by rfl

def raw3545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3545step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3545step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3545step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3545step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3545 raw3545Labels = mixedMoment B node4734 node4734Labels := by
  calc
    mixedMoment B raw3545 raw3545Labels = mixedMoment B raw3545step0 raw3545step0Labels := by
      have ha : raw3545step0 = (fun i j => raw3545 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3545step0 raw3545; decide +kernel
      have hl : raw3545step0Labels = raw3545Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3545 raw3545Labels permutation640 permutation3
    mixedMoment B raw3545step0 raw3545step0Labels = mixedMoment B raw3545step1 raw3545step1Labels := by
      have ha : raw3545step1 = -raw3545step0 := by apply Matrix.ext; change ∀ i j, raw3545step1 i j = -(raw3545step0 i j); unfold raw3545step1 raw3545step0; decide +kernel
      have hl : raw3545step1Labels = raw3545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3545step1 raw3545step1Labels = mixedMoment B raw3545step2 raw3545step2Labels := by
      have ha : raw3545step2 = raw3545step1 := by apply Matrix.ext; unfold raw3545step2 raw3545step1; decide +kernel
      have hl : raw3545step1Labels = labelEmbedding6 ∘ raw3545step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3545step1 raw3545step1Labels raw3545step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4734 node4734Labels := by rfl

def raw3546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw3546step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3546step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3546step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3546 raw3546Labels = mixedMoment B node4748 node4748Labels := by
  calc
    mixedMoment B raw3546 raw3546Labels = mixedMoment B raw3546step0 raw3546step0Labels := by
      have hz : ∀ j, raw3546 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3546step0 = (fun i j => raw3546 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3546step0 raw3546; decide +kernel
      have hl : raw3546step0Labels = raw3546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3546 raw3546Labels permutation265 hz
    mixedMoment B raw3546step0 raw3546step0Labels = mixedMoment B raw3546step1 raw3546step1Labels := by
      have ha : raw3546step1 = (fun i j => raw3546step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3546step1 raw3546step0; decide +kernel
      have hl : raw3546step1Labels = raw3546step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3546step0 raw3546step0Labels permutation139 permutation3
    mixedMoment B raw3546step1 raw3546step1Labels = mixedMoment B raw3546step2 raw3546step2Labels := by
      have ha : raw3546step2 = -raw3546step1 := by apply Matrix.ext; change ∀ i j, raw3546step2 i j = -(raw3546step1 i j); unfold raw3546step2 raw3546step1; decide +kernel
      have hl : raw3546step2Labels = raw3546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3546step2 raw3546step2Labels = mixedMoment B raw3546step3 raw3546step3Labels := by
      have ha : raw3546step3 = raw3546step2 := by apply Matrix.ext; unfold raw3546step3 raw3546step2; decide +kernel
      have hl : raw3546step2Labels = labelEmbedding6 ∘ raw3546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3546step2 raw3546step2Labels raw3546step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4748 node4748Labels := by rfl

def raw3547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3547step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3547step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3547step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3547step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3547 raw3547Labels = mixedMoment B node4743 node4743Labels := by
  calc
    mixedMoment B raw3547 raw3547Labels = mixedMoment B raw3547step0 raw3547step0Labels := by
      have hz : ∀ j, raw3547 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3547step0 = (fun i j => raw3547 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3547step0 raw3547; decide +kernel
      have hl : raw3547step0Labels = raw3547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3547 raw3547Labels permutation265 hz
    mixedMoment B raw3547step0 raw3547step0Labels = mixedMoment B raw3547step1 raw3547step1Labels := by
      have ha : raw3547step1 = (fun i j => raw3547step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3547step1 raw3547step0; decide +kernel
      have hl : raw3547step1Labels = raw3547step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3547step0 raw3547step0Labels permutation137 permutation3
    mixedMoment B raw3547step1 raw3547step1Labels = mixedMoment B raw3547step2 raw3547step2Labels := by
      have ha : raw3547step2 = -raw3547step1 := by apply Matrix.ext; change ∀ i j, raw3547step2 i j = -(raw3547step1 i j); unfold raw3547step2 raw3547step1; decide +kernel
      have hl : raw3547step2Labels = raw3547step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3547step2 raw3547step2Labels = mixedMoment B raw3547step3 raw3547step3Labels := by
      have ha : raw3547step3 = raw3547step2 := by apply Matrix.ext; unfold raw3547step3 raw3547step2; decide +kernel
      have hl : raw3547step2Labels = labelEmbedding6 ∘ raw3547step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3547step2 raw3547step2Labels raw3547step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4743 node4743Labels := by rfl

def raw3548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3548 raw3548Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw3548 raw3548Labels = mixedMoment B raw3548step0 raw3548step0Labels := by
      have hz : ∀ j, raw3548 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3548step0 = (fun i j => raw3548 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3548step0 raw3548; decide +kernel
      have hl : raw3548step0Labels = raw3548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3548 raw3548Labels permutation265 hz
    mixedMoment B raw3548step0 raw3548step0Labels = mixedMoment B raw3548step1 raw3548step1Labels := by
      have ha : raw3548step1 = (fun i j => raw3548step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3548step1 raw3548step0; decide +kernel
      have hl : raw3548step1Labels = raw3548step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3548step0 raw3548step0Labels permutation40 permutation2
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw3549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3549step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3549 raw3549Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw3549 raw3549Labels = mixedMoment B raw3549step0 raw3549step0Labels := by
      have hz : ∀ j, raw3549 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3549step0 = (fun i j => raw3549 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3549step0 raw3549; decide +kernel
      have hl : raw3549step0Labels = raw3549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3549 raw3549Labels permutation346 hz
    mixedMoment B raw3549step0 raw3549step0Labels = mixedMoment B raw3549step1 raw3549step1Labels := by
      have hz : ∀ j, raw3549step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3549step1 = (fun i j => raw3549step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3549step1 raw3549step0; decide +kernel
      have hl : raw3549step1Labels = raw3549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3549step0 raw3549step0Labels permutation56 hz
    mixedMoment B raw3549step1 raw3549step1Labels = mixedMoment B raw3549step2 raw3549step2Labels := by
      have ha : raw3549step2 = (fun i j => raw3549step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3549step2 raw3549step1; decide +kernel
      have hl : raw3549step2Labels = raw3549step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3549step1 raw3549step1Labels permutation10 permutation2
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw3550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3550 raw3550Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw3550 raw3550Labels = mixedMoment B raw3550step0 raw3550step0Labels := by
      have hz : ∀ j, raw3550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3550step0 = (fun i j => raw3550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3550step0 raw3550; decide +kernel
      have hl : raw3550step0Labels = raw3550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3550 raw3550Labels permutation346 hz
    mixedMoment B raw3550step0 raw3550step0Labels = mixedMoment B raw3550step1 raw3550step1Labels := by
      have ha : raw3550step1 = (fun i j => raw3550step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3550step1 raw3550step0; decide +kernel
      have hl : raw3550step1Labels = raw3550step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3550step0 raw3550step0Labels permutation34 permutation2
    _ = mixedMoment B node4819 node4819Labels := by rfl

def raw3551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3551step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3551 raw3551Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw3551 raw3551Labels = mixedMoment B raw3551step0 raw3551step0Labels := by
      have hz : ∀ j, raw3551 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3551step0 = (fun i j => raw3551 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3551step0 raw3551; decide +kernel
      have hl : raw3551step0Labels = raw3551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3551 raw3551Labels permutation265 hz
    mixedMoment B raw3551step0 raw3551step0Labels = mixedMoment B raw3551step1 raw3551step1Labels := by
      have ha : raw3551step1 = (fun i j => raw3551step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3551step1 raw3551step0; decide +kernel
      have hl : raw3551step1Labels = raw3551step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3551step0 raw3551step0Labels permutation34 permutation2
    _ = mixedMoment B node4819 node4819Labels := by rfl

def raw3552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3552step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3552step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3552step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3552step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3552step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3552step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3552 raw3552Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw3552 raw3552Labels = mixedMoment B raw3552step0 raw3552step0Labels := by
      have hz : ∀ j, raw3552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3552step0 = (fun i j => raw3552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3552step0 raw3552; decide +kernel
      have hl : raw3552step0Labels = raw3552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3552 raw3552Labels permutation346 hz
    mixedMoment B raw3552step0 raw3552step0Labels = mixedMoment B raw3552step1 raw3552step1Labels := by
      have hz : ∀ j, raw3552step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3552step1 = (fun i j => raw3552step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3552step1 raw3552step0; decide +kernel
      have hl : raw3552step1Labels = raw3552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3552step0 raw3552step0Labels permutation56 hz
    mixedMoment B raw3552step1 raw3552step1Labels = mixedMoment B raw3552step2 raw3552step2Labels := by
      have ha : raw3552step2 = (fun i j => raw3552step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3552step2 raw3552step1; decide +kernel
      have hl : raw3552step2Labels = raw3552step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3552step1 raw3552step1Labels permutation29 permutation3
    mixedMoment B raw3552step2 raw3552step2Labels = mixedMoment B raw3552step3 raw3552step3Labels := by
      have ha : raw3552step3 = -raw3552step2 := by apply Matrix.ext; change ∀ i j, raw3552step3 i j = -(raw3552step2 i j); unfold raw3552step3 raw3552step2; decide +kernel
      have hl : raw3552step3Labels = raw3552step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3552step3 raw3552step3Labels = mixedMoment B raw3552step4 raw3552step4Labels := by
      have ha : raw3552step4 = raw3552step3 := by apply Matrix.ext; unfold raw3552step4 raw3552step3; decide +kernel
      have hl : raw3552step3Labels = labelEmbedding6 ∘ raw3552step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3552step3 raw3552step3Labels raw3552step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw3553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3553step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3553 raw3553Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw3553 raw3553Labels = mixedMoment B raw3553step0 raw3553step0Labels := by
      have hz : ∀ j, raw3553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3553step0 = (fun i j => raw3553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3553step0 raw3553; decide +kernel
      have hl : raw3553step0Labels = raw3553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3553 raw3553Labels permutation346 hz
    mixedMoment B raw3553step0 raw3553step0Labels = mixedMoment B raw3553step1 raw3553step1Labels := by
      have hz : ∀ j, raw3553step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3553step1 = (fun i j => raw3553step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3553step1 raw3553step0; decide +kernel
      have hl : raw3553step1Labels = raw3553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3553step0 raw3553step0Labels permutation56 hz
    mixedMoment B raw3553step1 raw3553step1Labels = mixedMoment B raw3553step2 raw3553step2Labels := by
      have ha : raw3553step2 = (fun i j => raw3553step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3553step2 raw3553step1; decide +kernel
      have hl : raw3553step2Labels = raw3553step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3553step1 raw3553step1Labels permutation10 permutation2
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw3554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3554 raw3554Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw3554 raw3554Labels = mixedMoment B raw3554step0 raw3554step0Labels := by
      have hz : ∀ j, raw3554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3554step0 = (fun i j => raw3554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3554step0 raw3554; decide +kernel
      have hl : raw3554step0Labels = raw3554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3554 raw3554Labels permutation346 hz
    mixedMoment B raw3554step0 raw3554step0Labels = mixedMoment B raw3554step1 raw3554step1Labels := by
      have hz : ∀ j, raw3554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3554step1 = (fun i j => raw3554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3554step1 raw3554step0; decide +kernel
      have hl : raw3554step1Labels = raw3554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3554step0 raw3554step0Labels permutation56 hz
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw3555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3555 raw3555Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw3555 raw3555Labels = mixedMoment B raw3555step0 raw3555step0Labels := by
      have hz : ∀ j, raw3555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3555step0 = (fun i j => raw3555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3555step0 raw3555; decide +kernel
      have hl : raw3555step0Labels = raw3555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3555 raw3555Labels permutation346 hz
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw3556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3556 raw3556Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw3556 raw3556Labels = mixedMoment B raw3556step0 raw3556step0Labels := by
      have hz : ∀ j, raw3556 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3556step0 = (fun i j => raw3556 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3556step0 raw3556; decide +kernel
      have hl : raw3556step0Labels = raw3556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3556 raw3556Labels permutation265 hz
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw3557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3557 raw3557Labels = mixedMoment B node4872 node4872Labels := by
  calc
    mixedMoment B raw3557 raw3557Labels = mixedMoment B raw3557step0 raw3557step0Labels := by
      have hz : ∀ j, raw3557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3557step0 = (fun i j => raw3557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3557step0 raw3557; decide +kernel
      have hl : raw3557step0Labels = raw3557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3557 raw3557Labels permutation346 hz
    mixedMoment B raw3557step0 raw3557step0Labels = mixedMoment B raw3557step1 raw3557step1Labels := by
      have hz : ∀ j, raw3557step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3557step1 = (fun i j => raw3557step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3557step1 raw3557step0; decide +kernel
      have hl : raw3557step1Labels = raw3557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3557step0 raw3557step0Labels permutation56 hz
    _ = mixedMoment B node4872 node4872Labels := by rfl

def raw3558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3558 raw3558Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw3558 raw3558Labels = mixedMoment B raw3558step0 raw3558step0Labels := by
      have hz : ∀ j, raw3558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3558step0 = (fun i j => raw3558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3558step0 raw3558; decide +kernel
      have hl : raw3558step0Labels = raw3558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3558 raw3558Labels permutation346 hz
    mixedMoment B raw3558step0 raw3558step0Labels = mixedMoment B raw3558step1 raw3558step1Labels := by
      have hz : ∀ j, raw3558step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3558step1 = (fun i j => raw3558step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3558step1 raw3558step0; decide +kernel
      have hl : raw3558step1Labels = raw3558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3558step0 raw3558step0Labels permutation56 hz
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw3559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-4, 3, 1]]
def raw3559step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3559step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![4, -3, -1]]
def raw3559step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3559step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![4, -3, -1]]
def raw3559step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3559 raw3559Labels = mixedMoment B node4262 node4262Labels := by
  calc
    mixedMoment B raw3559 raw3559Labels = mixedMoment B raw3559step0 raw3559step0Labels := by
      have hz : ∀ j, raw3559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3559step0 = (fun i j => raw3559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3559step0 raw3559; decide +kernel
      have hl : raw3559step0Labels = raw3559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3559 raw3559Labels permutation346 hz
    mixedMoment B raw3559step0 raw3559step0Labels = mixedMoment B raw3559step1 raw3559step1Labels := by
      have hz : ∀ j, raw3559step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3559step1 = (fun i j => raw3559step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3559step1 raw3559step0; decide +kernel
      have hl : raw3559step1Labels = raw3559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3559step0 raw3559step0Labels permutation56 hz
    mixedMoment B raw3559step1 raw3559step1Labels = mixedMoment B raw3559step2 raw3559step2Labels := by
      have ha : raw3559step2 = (fun i j => raw3559step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3559step2 raw3559step1; decide +kernel
      have hl : raw3559step2Labels = raw3559step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3559step1 raw3559step1Labels permutation29 permutation3
    mixedMoment B raw3559step2 raw3559step2Labels = mixedMoment B raw3559step3 raw3559step3Labels := by
      have ha : raw3559step3 = -raw3559step2 := by apply Matrix.ext; change ∀ i j, raw3559step3 i j = -(raw3559step2 i j); unfold raw3559step3 raw3559step2; decide +kernel
      have hl : raw3559step3Labels = raw3559step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3559step3 raw3559step3Labels = mixedMoment B raw3559step4 raw3559step4Labels := by
      have ha : raw3559step4 = raw3559step3 := by apply Matrix.ext; unfold raw3559step4 raw3559step3; decide +kernel
      have hl : raw3559step3Labels = labelEmbedding6 ∘ raw3559step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3559step3 raw3559step3Labels raw3559step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4262 node4262Labels := by rfl

def raw3560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3560step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3560step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3560step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3560step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3560 raw3560Labels = mixedMoment B node4260 node4260Labels := by
  calc
    mixedMoment B raw3560 raw3560Labels = mixedMoment B raw3560step0 raw3560step0Labels := by
      have hz : ∀ j, raw3560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3560step0 = (fun i j => raw3560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3560step0 raw3560; decide +kernel
      have hl : raw3560step0Labels = raw3560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3560 raw3560Labels permutation346 hz
    mixedMoment B raw3560step0 raw3560step0Labels = mixedMoment B raw3560step1 raw3560step1Labels := by
      have ha : raw3560step1 = (fun i j => raw3560step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3560step1 raw3560step0; decide +kernel
      have hl : raw3560step1Labels = raw3560step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3560step0 raw3560step0Labels permutation145 permutation3
    mixedMoment B raw3560step1 raw3560step1Labels = mixedMoment B raw3560step2 raw3560step2Labels := by
      have ha : raw3560step2 = -raw3560step1 := by apply Matrix.ext; change ∀ i j, raw3560step2 i j = -(raw3560step1 i j); unfold raw3560step2 raw3560step1; decide +kernel
      have hl : raw3560step2Labels = raw3560step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3560step2 raw3560step2Labels = mixedMoment B raw3560step3 raw3560step3Labels := by
      have ha : raw3560step3 = raw3560step2 := by apply Matrix.ext; unfold raw3560step3 raw3560step2; decide +kernel
      have hl : raw3560step2Labels = labelEmbedding6 ∘ raw3560step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3560step2 raw3560step2Labels raw3560step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4260 node4260Labels := by rfl

def raw3561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3561step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3561step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3561step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3561step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3561 raw3561Labels = mixedMoment B node4260 node4260Labels := by
  calc
    mixedMoment B raw3561 raw3561Labels = mixedMoment B raw3561step0 raw3561step0Labels := by
      have hz : ∀ j, raw3561 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3561step0 = (fun i j => raw3561 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3561step0 raw3561; decide +kernel
      have hl : raw3561step0Labels = raw3561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3561 raw3561Labels permutation265 hz
    mixedMoment B raw3561step0 raw3561step0Labels = mixedMoment B raw3561step1 raw3561step1Labels := by
      have ha : raw3561step1 = (fun i j => raw3561step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3561step1 raw3561step0; decide +kernel
      have hl : raw3561step1Labels = raw3561step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3561step0 raw3561step0Labels permutation145 permutation3
    mixedMoment B raw3561step1 raw3561step1Labels = mixedMoment B raw3561step2 raw3561step2Labels := by
      have ha : raw3561step2 = -raw3561step1 := by apply Matrix.ext; change ∀ i j, raw3561step2 i j = -(raw3561step1 i j); unfold raw3561step2 raw3561step1; decide +kernel
      have hl : raw3561step2Labels = raw3561step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3561step2 raw3561step2Labels = mixedMoment B raw3561step3 raw3561step3Labels := by
      have ha : raw3561step3 = raw3561step2 := by apply Matrix.ext; unfold raw3561step3 raw3561step2; decide +kernel
      have hl : raw3561step2Labels = labelEmbedding6 ∘ raw3561step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3561step2 raw3561step2Labels raw3561step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4260 node4260Labels := by rfl

def raw3562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw3562step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3562step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3562step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3562step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3562 raw3562Labels = mixedMoment B node4277 node4277Labels := by
  calc
    mixedMoment B raw3562 raw3562Labels = mixedMoment B raw3562step0 raw3562step0Labels := by
      have hz : ∀ j, raw3562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3562step0 = (fun i j => raw3562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3562step0 raw3562; decide +kernel
      have hl : raw3562step0Labels = raw3562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3562 raw3562Labels permutation346 hz
    mixedMoment B raw3562step0 raw3562step0Labels = mixedMoment B raw3562step1 raw3562step1Labels := by
      have hz : ∀ j, raw3562step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3562step1 = (fun i j => raw3562step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3562step1 raw3562step0; decide +kernel
      have hl : raw3562step1Labels = raw3562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3562step0 raw3562step0Labels permutation56 hz
    mixedMoment B raw3562step1 raw3562step1Labels = mixedMoment B raw3562step2 raw3562step2Labels := by
      have ha : raw3562step2 = (fun i j => raw3562step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3562step2 raw3562step1; decide +kernel
      have hl : raw3562step2Labels = raw3562step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3562step1 raw3562step1Labels permutation31 permutation3
    mixedMoment B raw3562step2 raw3562step2Labels = mixedMoment B raw3562step3 raw3562step3Labels := by
      have ha : raw3562step3 = -raw3562step2 := by apply Matrix.ext; change ∀ i j, raw3562step3 i j = -(raw3562step2 i j); unfold raw3562step3 raw3562step2; decide +kernel
      have hl : raw3562step3Labels = raw3562step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3562step3 raw3562step3Labels = mixedMoment B raw3562step4 raw3562step4Labels := by
      have ha : raw3562step4 = raw3562step3 := by apply Matrix.ext; unfold raw3562step4 raw3562step3; decide +kernel
      have hl : raw3562step3Labels = labelEmbedding6 ∘ raw3562step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3562step3 raw3562step3Labels raw3562step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4277 node4277Labels := by rfl

def raw3563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3563step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3563step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3563step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3563step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3563step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3563 raw3563Labels = mixedMoment B node4271 node4271Labels := by
  calc
    mixedMoment B raw3563 raw3563Labels = mixedMoment B raw3563step0 raw3563step0Labels := by
      have hz : ∀ j, raw3563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3563step0 = (fun i j => raw3563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3563step0 raw3563; decide +kernel
      have hl : raw3563step0Labels = raw3563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3563 raw3563Labels permutation346 hz
    mixedMoment B raw3563step0 raw3563step0Labels = mixedMoment B raw3563step1 raw3563step1Labels := by
      have hz : ∀ j, raw3563step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3563step1 = (fun i j => raw3563step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3563step1 raw3563step0; decide +kernel
      have hl : raw3563step1Labels = raw3563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3563step0 raw3563step0Labels permutation56 hz
    mixedMoment B raw3563step1 raw3563step1Labels = mixedMoment B raw3563step2 raw3563step2Labels := by
      have ha : raw3563step2 = (fun i j => raw3563step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3563step2 raw3563step1; decide +kernel
      have hl : raw3563step2Labels = raw3563step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3563step1 raw3563step1Labels permutation29 permutation3
    mixedMoment B raw3563step2 raw3563step2Labels = mixedMoment B raw3563step3 raw3563step3Labels := by
      have ha : raw3563step3 = -raw3563step2 := by apply Matrix.ext; change ∀ i j, raw3563step3 i j = -(raw3563step2 i j); unfold raw3563step3 raw3563step2; decide +kernel
      have hl : raw3563step3Labels = raw3563step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3563step3 raw3563step3Labels = mixedMoment B raw3563step4 raw3563step4Labels := by
      have ha : raw3563step4 = raw3563step3 := by apply Matrix.ext; unfold raw3563step4 raw3563step3; decide +kernel
      have hl : raw3563step3Labels = labelEmbedding6 ∘ raw3563step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3563step3 raw3563step3Labels raw3563step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4271 node4271Labels := by rfl

def raw3564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw3564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw3564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3564 raw3564Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw3564 raw3564Labels = mixedMoment B raw3564step0 raw3564step0Labels := by
      have hz : ∀ j, raw3564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3564step0 = (fun i j => raw3564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3564step0 raw3564; decide +kernel
      have hl : raw3564step0Labels = raw3564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3564 raw3564Labels permutation346 hz
    mixedMoment B raw3564step0 raw3564step0Labels = mixedMoment B raw3564step1 raw3564step1Labels := by
      have ha : raw3564step1 = (fun i j => raw3564step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3564step1 raw3564step0; decide +kernel
      have hl : raw3564step1Labels = raw3564step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3564step0 raw3564step0Labels permutation145 permutation3
    mixedMoment B raw3564step1 raw3564step1Labels = mixedMoment B raw3564step2 raw3564step2Labels := by
      have ha : raw3564step2 = -raw3564step1 := by apply Matrix.ext; change ∀ i j, raw3564step2 i j = -(raw3564step1 i j); unfold raw3564step2 raw3564step1; decide +kernel
      have hl : raw3564step2Labels = raw3564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw3565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw3565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw3565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3565 raw3565Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw3565 raw3565Labels = mixedMoment B raw3565step0 raw3565step0Labels := by
      have hz : ∀ j, raw3565 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3565step0 = (fun i j => raw3565 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3565step0 raw3565; decide +kernel
      have hl : raw3565step0Labels = raw3565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3565 raw3565Labels permutation265 hz
    mixedMoment B raw3565step0 raw3565step0Labels = mixedMoment B raw3565step1 raw3565step1Labels := by
      have ha : raw3565step1 = (fun i j => raw3565step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3565step1 raw3565step0; decide +kernel
      have hl : raw3565step1Labels = raw3565step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3565step0 raw3565step0Labels permutation145 permutation3
    mixedMoment B raw3565step1 raw3565step1Labels = mixedMoment B raw3565step2 raw3565step2Labels := by
      have ha : raw3565step2 = -raw3565step1 := by apply Matrix.ext; change ∀ i j, raw3565step2 i j = -(raw3565step1 i j); unfold raw3565step2 raw3565step1; decide +kernel
      have hl : raw3565step2Labels = raw3565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw3566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3566step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3566step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw3566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw3566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3566 raw3566Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw3566 raw3566Labels = mixedMoment B raw3566step0 raw3566step0Labels := by
      have hz : ∀ j, raw3566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3566step0 = (fun i j => raw3566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3566step0 raw3566; decide +kernel
      have hl : raw3566step0Labels = raw3566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3566 raw3566Labels permutation346 hz
    mixedMoment B raw3566step0 raw3566step0Labels = mixedMoment B raw3566step1 raw3566step1Labels := by
      have hz : ∀ j, raw3566step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3566step1 = (fun i j => raw3566step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3566step1 raw3566step0; decide +kernel
      have hl : raw3566step1Labels = raw3566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3566step0 raw3566step0Labels permutation56 hz
    mixedMoment B raw3566step1 raw3566step1Labels = mixedMoment B raw3566step2 raw3566step2Labels := by
      have ha : raw3566step2 = (fun i j => raw3566step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3566step2 raw3566step1; decide +kernel
      have hl : raw3566step2Labels = raw3566step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3566step1 raw3566step1Labels permutation31 permutation3
    mixedMoment B raw3566step2 raw3566step2Labels = mixedMoment B raw3566step3 raw3566step3Labels := by
      have ha : raw3566step3 = -raw3566step2 := by apply Matrix.ext; change ∀ i j, raw3566step3 i j = -(raw3566step2 i j); unfold raw3566step3 raw3566step2; decide +kernel
      have hl : raw3566step3Labels = raw3566step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw3567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3567step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -2, 3], ![-2, 3, -1]]
def raw3567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw3567step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3567 raw3567Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw3567 raw3567Labels = mixedMoment B raw3567step0 raw3567step0Labels := by
      have hz : ∀ j, raw3567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3567step0 = (fun i j => raw3567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3567step0 raw3567; decide +kernel
      have hl : raw3567step0Labels = raw3567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3567 raw3567Labels permutation346 hz
    mixedMoment B raw3567step0 raw3567step0Labels = mixedMoment B raw3567step1 raw3567step1Labels := by
      have hz : ∀ j, raw3567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3567step1 = (fun i j => raw3567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3567step1 raw3567step0; decide +kernel
      have hl : raw3567step1Labels = raw3567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3567step0 raw3567step0Labels permutation56 hz
    mixedMoment B raw3567step1 raw3567step1Labels = mixedMoment B raw3567step2 raw3567step2Labels := by
      have ha : raw3567step2 = (fun i j => raw3567step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3567step2 raw3567step1; decide +kernel
      have hl : raw3567step2Labels = raw3567step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3567step1 raw3567step1Labels permutation29 permutation3
    mixedMoment B raw3567step2 raw3567step2Labels = mixedMoment B raw3567step3 raw3567step3Labels := by
      have ha : raw3567step3 = -raw3567step2 := by apply Matrix.ext; change ∀ i j, raw3567step3 i j = -(raw3567step2 i j); unfold raw3567step3 raw3567step2; decide +kernel
      have hl : raw3567step3Labels = raw3567step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw3568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3568step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw3568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw3568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3568 raw3568Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw3568 raw3568Labels = mixedMoment B raw3568step0 raw3568step0Labels := by
      have hz : ∀ j, raw3568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3568step0 = (fun i j => raw3568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3568step0 raw3568; decide +kernel
      have hl : raw3568step0Labels = raw3568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3568 raw3568Labels permutation346 hz
    mixedMoment B raw3568step0 raw3568step0Labels = mixedMoment B raw3568step1 raw3568step1Labels := by
      have hz : ∀ j, raw3568step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3568step1 = (fun i j => raw3568step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3568step1 raw3568step0; decide +kernel
      have hl : raw3568step1Labels = raw3568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3568step0 raw3568step0Labels permutation56 hz
    mixedMoment B raw3568step1 raw3568step1Labels = mixedMoment B raw3568step2 raw3568step2Labels := by
      have ha : raw3568step2 = (fun i j => raw3568step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3568step2 raw3568step1; decide +kernel
      have hl : raw3568step2Labels = raw3568step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3568step1 raw3568step1Labels permutation12 permutation6
    mixedMoment B raw3568step2 raw3568step2Labels = mixedMoment B raw3568step3 raw3568step3Labels := by
      have ha : raw3568step3 = -raw3568step2 := by apply Matrix.ext; change ∀ i j, raw3568step3 i j = -(raw3568step2 i j); unfold raw3568step3 raw3568step2; decide +kernel
      have hl : raw3568step3Labels = raw3568step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw3569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw3569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3569 raw3569Labels = mixedMoment B node1355 node1355Labels := by
  calc
    mixedMoment B raw3569 raw3569Labels = mixedMoment B raw3569step0 raw3569step0Labels := by
      have hz : ∀ j, raw3569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3569step0 = (fun i j => raw3569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3569step0 raw3569; decide +kernel
      have hl : raw3569step0Labels = raw3569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3569 raw3569Labels permutation346 hz
    mixedMoment B raw3569step0 raw3569step0Labels = mixedMoment B raw3569step1 raw3569step1Labels := by
      have ha : raw3569step1 = (fun i j => raw3569step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3569step1 raw3569step0; decide +kernel
      have hl : raw3569step1Labels = raw3569step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3569step0 raw3569step0Labels permutation46 permutation3
    _ = mixedMoment B node1355 node1355Labels := by rfl

def raw3570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3570 raw3570Labels = mixedMoment B node1903 node1903Labels := by
  calc
    mixedMoment B raw3570 raw3570Labels = mixedMoment B raw3570step0 raw3570step0Labels := by
      have ha : raw3570step0 = (fun i j => raw3570 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3570step0 raw3570; decide +kernel
      have hl : raw3570step0Labels = raw3570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3570 raw3570Labels permutation616 permutation3
    mixedMoment B raw3570step0 raw3570step0Labels = mixedMoment B raw3570step1 raw3570step1Labels := by
      have ha : raw3570step1 = -raw3570step0 := by apply Matrix.ext; change ∀ i j, raw3570step1 i j = -(raw3570step0 i j); unfold raw3570step1 raw3570step0; decide +kernel
      have hl : raw3570step1Labels = raw3570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1903 node1903Labels := by rfl

def raw3571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw3571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3571 raw3571Labels = mixedMoment B node1927 node1927Labels := by
  calc
    mixedMoment B raw3571 raw3571Labels = mixedMoment B raw3571step0 raw3571step0Labels := by
      have hz : ∀ j, raw3571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3571step0 = (fun i j => raw3571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3571step0 raw3571; decide +kernel
      have hl : raw3571step0Labels = raw3571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3571 raw3571Labels permutation346 hz
    mixedMoment B raw3571step0 raw3571step0Labels = mixedMoment B raw3571step1 raw3571step1Labels := by
      have ha : raw3571step1 = (fun i j => raw3571step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3571step1 raw3571step0; decide +kernel
      have hl : raw3571step1Labels = raw3571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3571step0 raw3571step0Labels permutation139 permutation3
    mixedMoment B raw3571step1 raw3571step1Labels = mixedMoment B raw3571step2 raw3571step2Labels := by
      have ha : raw3571step2 = -raw3571step1 := by apply Matrix.ext; change ∀ i j, raw3571step2 i j = -(raw3571step1 i j); unfold raw3571step2 raw3571step1; decide +kernel
      have hl : raw3571step2Labels = raw3571step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1927 node1927Labels := by rfl

def raw3572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3572 raw3572Labels = mixedMoment B node1916 node1916Labels := by
  calc
    mixedMoment B raw3572 raw3572Labels = mixedMoment B raw3572step0 raw3572step0Labels := by
      have hz : ∀ j, raw3572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3572step0 = (fun i j => raw3572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3572step0 raw3572; decide +kernel
      have hl : raw3572step0Labels = raw3572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3572 raw3572Labels permutation346 hz
    mixedMoment B raw3572step0 raw3572step0Labels = mixedMoment B raw3572step1 raw3572step1Labels := by
      have ha : raw3572step1 = (fun i j => raw3572step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3572step1 raw3572step0; decide +kernel
      have hl : raw3572step1Labels = raw3572step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3572step0 raw3572step0Labels permutation137 permutation3
    mixedMoment B raw3572step1 raw3572step1Labels = mixedMoment B raw3572step2 raw3572step2Labels := by
      have ha : raw3572step2 = -raw3572step1 := by apply Matrix.ext; change ∀ i j, raw3572step2 i j = -(raw3572step1 i j); unfold raw3572step2 raw3572step1; decide +kernel
      have hl : raw3572step2Labels = raw3572step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1916 node1916Labels := by rfl

def raw3573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw3573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3573 raw3573Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw3573 raw3573Labels = mixedMoment B raw3573step0 raw3573step0Labels := by
      have hz : ∀ j, raw3573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3573step0 = (fun i j => raw3573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3573step0 raw3573; decide +kernel
      have hl : raw3573step0Labels = raw3573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3573 raw3573Labels permutation346 hz
    mixedMoment B raw3573step0 raw3573step0Labels = mixedMoment B raw3573step1 raw3573step1Labels := by
      have ha : raw3573step1 = (fun i j => raw3573step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3573step1 raw3573step0; decide +kernel
      have hl : raw3573step1Labels = raw3573step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3573step0 raw3573step0Labels permutation46 permutation3
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw3574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3574step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw3574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3574 raw3574Labels = mixedMoment B node1355 node1355Labels := by
  calc
    mixedMoment B raw3574 raw3574Labels = mixedMoment B raw3574step0 raw3574step0Labels := by
      have hz : ∀ j, raw3574 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3574step0 = (fun i j => raw3574 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3574step0 raw3574; decide +kernel
      have hl : raw3574step0Labels = raw3574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3574 raw3574Labels permutation265 hz
    mixedMoment B raw3574step0 raw3574step0Labels = mixedMoment B raw3574step1 raw3574step1Labels := by
      have ha : raw3574step1 = (fun i j => raw3574step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3574step1 raw3574step0; decide +kernel
      have hl : raw3574step1Labels = raw3574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3574step0 raw3574step0Labels permutation46 permutation3
    _ = mixedMoment B node1355 node1355Labels := by rfl

def raw3575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3575 raw3575Labels = mixedMoment B node1903 node1903Labels := by
  calc
    mixedMoment B raw3575 raw3575Labels = mixedMoment B raw3575step0 raw3575step0Labels := by
      have ha : raw3575step0 = (fun i j => raw3575 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3575step0 raw3575; decide +kernel
      have hl : raw3575step0Labels = raw3575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3575 raw3575Labels permutation640 permutation3
    mixedMoment B raw3575step0 raw3575step0Labels = mixedMoment B raw3575step1 raw3575step1Labels := by
      have ha : raw3575step1 = -raw3575step0 := by apply Matrix.ext; change ∀ i j, raw3575step1 i j = -(raw3575step0 i j); unfold raw3575step1 raw3575step0; decide +kernel
      have hl : raw3575step1Labels = raw3575step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1903 node1903Labels := by rfl

def raw3576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw3576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3576 raw3576Labels = mixedMoment B node1927 node1927Labels := by
  calc
    mixedMoment B raw3576 raw3576Labels = mixedMoment B raw3576step0 raw3576step0Labels := by
      have hz : ∀ j, raw3576 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3576step0 = (fun i j => raw3576 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3576step0 raw3576; decide +kernel
      have hl : raw3576step0Labels = raw3576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3576 raw3576Labels permutation265 hz
    mixedMoment B raw3576step0 raw3576step0Labels = mixedMoment B raw3576step1 raw3576step1Labels := by
      have ha : raw3576step1 = (fun i j => raw3576step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3576step1 raw3576step0; decide +kernel
      have hl : raw3576step1Labels = raw3576step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3576step0 raw3576step0Labels permutation139 permutation3
    mixedMoment B raw3576step1 raw3576step1Labels = mixedMoment B raw3576step2 raw3576step2Labels := by
      have ha : raw3576step2 = -raw3576step1 := by apply Matrix.ext; change ∀ i j, raw3576step2 i j = -(raw3576step1 i j); unfold raw3576step2 raw3576step1; decide +kernel
      have hl : raw3576step2Labels = raw3576step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1927 node1927Labels := by rfl

def raw3577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3577 raw3577Labels = mixedMoment B node1916 node1916Labels := by
  calc
    mixedMoment B raw3577 raw3577Labels = mixedMoment B raw3577step0 raw3577step0Labels := by
      have hz : ∀ j, raw3577 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3577step0 = (fun i j => raw3577 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3577step0 raw3577; decide +kernel
      have hl : raw3577step0Labels = raw3577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3577 raw3577Labels permutation265 hz
    mixedMoment B raw3577step0 raw3577step0Labels = mixedMoment B raw3577step1 raw3577step1Labels := by
      have ha : raw3577step1 = (fun i j => raw3577step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3577step1 raw3577step0; decide +kernel
      have hl : raw3577step1Labels = raw3577step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3577step0 raw3577step0Labels permutation137 permutation3
    mixedMoment B raw3577step1 raw3577step1Labels = mixedMoment B raw3577step2 raw3577step2Labels := by
      have ha : raw3577step2 = -raw3577step1 := by apply Matrix.ext; change ∀ i j, raw3577step2 i j = -(raw3577step1 i j); unfold raw3577step2 raw3577step1; decide +kernel
      have hl : raw3577step2Labels = raw3577step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1916 node1916Labels := by rfl

def raw3578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw3578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3578 raw3578Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw3578 raw3578Labels = mixedMoment B raw3578step0 raw3578step0Labels := by
      have hz : ∀ j, raw3578 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3578step0 = (fun i j => raw3578 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3578step0 raw3578; decide +kernel
      have hl : raw3578step0Labels = raw3578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3578 raw3578Labels permutation265 hz
    mixedMoment B raw3578step0 raw3578step0Labels = mixedMoment B raw3578step1 raw3578step1Labels := by
      have ha : raw3578step1 = (fun i j => raw3578step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3578step1 raw3578step0; decide +kernel
      have hl : raw3578step1Labels = raw3578step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3578step0 raw3578step0Labels permutation46 permutation3
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw3579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3579step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw3579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3579 raw3579Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw3579 raw3579Labels = mixedMoment B raw3579step0 raw3579step0Labels := by
      have hz : ∀ j, raw3579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3579step0 = (fun i j => raw3579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3579step0 raw3579; decide +kernel
      have hl : raw3579step0Labels = raw3579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3579 raw3579Labels permutation346 hz
    mixedMoment B raw3579step0 raw3579step0Labels = mixedMoment B raw3579step1 raw3579step1Labels := by
      have hz : ∀ j, raw3579step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3579step1 = (fun i j => raw3579step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3579step1 raw3579step0; decide +kernel
      have hl : raw3579step1Labels = raw3579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3579step0 raw3579step0Labels permutation56 hz
    mixedMoment B raw3579step1 raw3579step1Labels = mixedMoment B raw3579step2 raw3579step2Labels := by
      have ha : raw3579step2 = (fun i j => raw3579step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3579step2 raw3579step1; decide +kernel
      have hl : raw3579step2Labels = raw3579step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3579step1 raw3579step1Labels permutation10 permutation3
    _ = mixedMoment B node1369 node1369Labels := by rfl

def raw3580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3580 raw3580Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw3580 raw3580Labels = mixedMoment B raw3580step0 raw3580step0Labels := by
      have hz : ∀ j, raw3580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3580step0 = (fun i j => raw3580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3580step0 raw3580; decide +kernel
      have hl : raw3580step0Labels = raw3580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3580 raw3580Labels permutation346 hz
    mixedMoment B raw3580step0 raw3580step0Labels = mixedMoment B raw3580step1 raw3580step1Labels := by
      have ha : raw3580step1 = (fun i j => raw3580step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3580step1 raw3580step0; decide +kernel
      have hl : raw3580step1Labels = raw3580step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3580step0 raw3580step0Labels permutation145 permutation3
    mixedMoment B raw3580step1 raw3580step1Labels = mixedMoment B raw3580step2 raw3580step2Labels := by
      have ha : raw3580step2 = -raw3580step1 := by apply Matrix.ext; change ∀ i j, raw3580step2 i j = -(raw3580step1 i j); unfold raw3580step2 raw3580step1; decide +kernel
      have hl : raw3580step2Labels = raw3580step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2037 node2037Labels := by rfl

def raw3581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3581 raw3581Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw3581 raw3581Labels = mixedMoment B raw3581step0 raw3581step0Labels := by
      have hz : ∀ j, raw3581 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3581step0 = (fun i j => raw3581 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3581step0 raw3581; decide +kernel
      have hl : raw3581step0Labels = raw3581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3581 raw3581Labels permutation265 hz
    mixedMoment B raw3581step0 raw3581step0Labels = mixedMoment B raw3581step1 raw3581step1Labels := by
      have ha : raw3581step1 = (fun i j => raw3581step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3581step1 raw3581step0; decide +kernel
      have hl : raw3581step1Labels = raw3581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3581step0 raw3581step0Labels permutation145 permutation3
    mixedMoment B raw3581step1 raw3581step1Labels = mixedMoment B raw3581step2 raw3581step2Labels := by
      have ha : raw3581step2 = -raw3581step1 := by apply Matrix.ext; change ∀ i j, raw3581step2 i j = -(raw3581step1 i j); unfold raw3581step2 raw3581step1; decide +kernel
      have hl : raw3581step2Labels = raw3581step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2037 node2037Labels := by rfl

def raw3582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3582step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3582step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3582 raw3582Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw3582 raw3582Labels = mixedMoment B raw3582step0 raw3582step0Labels := by
      have hz : ∀ j, raw3582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3582step0 = (fun i j => raw3582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3582step0 raw3582; decide +kernel
      have hl : raw3582step0Labels = raw3582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3582 raw3582Labels permutation346 hz
    mixedMoment B raw3582step0 raw3582step0Labels = mixedMoment B raw3582step1 raw3582step1Labels := by
      have hz : ∀ j, raw3582step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3582step1 = (fun i j => raw3582step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3582step1 raw3582step0; decide +kernel
      have hl : raw3582step1Labels = raw3582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3582step0 raw3582step0Labels permutation56 hz
    mixedMoment B raw3582step1 raw3582step1Labels = mixedMoment B raw3582step2 raw3582step2Labels := by
      have ha : raw3582step2 = (fun i j => raw3582step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3582step2 raw3582step1; decide +kernel
      have hl : raw3582step2Labels = raw3582step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3582step1 raw3582step1Labels permutation29 permutation3
    mixedMoment B raw3582step2 raw3582step2Labels = mixedMoment B raw3582step3 raw3582step3Labels := by
      have ha : raw3582step3 = -raw3582step2 := by apply Matrix.ext; change ∀ i j, raw3582step3 i j = -(raw3582step2 i j); unfold raw3582step3 raw3582step2; decide +kernel
      have hl : raw3582step3Labels = raw3582step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

def raw3583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3583step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw3583step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3583 raw3583Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw3583 raw3583Labels = mixedMoment B raw3583step0 raw3583step0Labels := by
      have hz : ∀ j, raw3583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3583step0 = (fun i j => raw3583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3583step0 raw3583; decide +kernel
      have hl : raw3583step0Labels = raw3583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3583 raw3583Labels permutation346 hz
    mixedMoment B raw3583step0 raw3583step0Labels = mixedMoment B raw3583step1 raw3583step1Labels := by
      have hz : ∀ j, raw3583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3583step1 = (fun i j => raw3583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3583step1 raw3583step0; decide +kernel
      have hl : raw3583step1Labels = raw3583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3583step0 raw3583step0Labels permutation56 hz
    mixedMoment B raw3583step1 raw3583step1Labels = mixedMoment B raw3583step2 raw3583step2Labels := by
      have ha : raw3583step2 = (fun i j => raw3583step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3583step2 raw3583step1; decide +kernel
      have hl : raw3583step2Labels = raw3583step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3583step1 raw3583step1Labels permutation10 permutation3
    _ = mixedMoment B node3224 node3224Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
