import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35200step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-2, -1, 3]]
def raw35200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw35200step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw35200step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35200 raw35200Labels = mixedMoment B node2273 node2273Labels := by
  calc
    mixedMoment B raw35200 raw35200Labels = mixedMoment B raw35200step0 raw35200step0Labels := by
      have hz : ∀ j, raw35200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35200step0 = (fun i j => raw35200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35200step0 raw35200; decide +kernel
      have hl : raw35200step0Labels = raw35200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35200 raw35200Labels permutation434 hz
    mixedMoment B raw35200step0 raw35200step0Labels = mixedMoment B raw35200step1 raw35200step1Labels := by
      have hz : ∀ j, raw35200step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35200step1 = (fun i j => raw35200step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35200step1 raw35200step0; decide +kernel
      have hl : raw35200step1Labels = raw35200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35200step0 raw35200step0Labels permutation80 hz
    mixedMoment B raw35200step1 raw35200step1Labels = mixedMoment B raw35200step2 raw35200step2Labels := by
      have ha : raw35200step2 = (fun i j => raw35200step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35200step2 raw35200step1; decide +kernel
      have hl : raw35200step2Labels = raw35200step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35200step1 raw35200step1Labels permutation10 permutation5
    mixedMoment B raw35200step2 raw35200step2Labels = mixedMoment B raw35200step3 raw35200step3Labels := by
      have ha : raw35200step3 = -raw35200step2 := by apply Matrix.ext; change ∀ i j, raw35200step3 i j = -(raw35200step2 i j); unfold raw35200step3 raw35200step2; decide +kernel
      have hl : raw35200step3Labels = raw35200step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35200step3 raw35200step3Labels = mixedMoment B raw35200step4 raw35200step4Labels := by
      have ha : raw35200step4 = raw35200step3 := by apply Matrix.ext; unfold raw35200step4 raw35200step3; decide +kernel
      have hl : raw35200step3Labels = labelEmbedding1 ∘ raw35200step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35200step3 raw35200step3Labels raw35200step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2273 node2273Labels := by rfl

def raw35201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35201step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw35201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35201step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35201step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35201step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35201 raw35201Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw35201 raw35201Labels = mixedMoment B raw35201step0 raw35201step0Labels := by
      have hz : ∀ j, raw35201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35201step0 = (fun i j => raw35201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35201step0 raw35201; decide +kernel
      have hl : raw35201step0Labels = raw35201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35201 raw35201Labels permutation434 hz
    mixedMoment B raw35201step0 raw35201step0Labels = mixedMoment B raw35201step1 raw35201step1Labels := by
      have hz : ∀ j, raw35201step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35201step1 = (fun i j => raw35201step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35201step1 raw35201step0; decide +kernel
      have hl : raw35201step1Labels = raw35201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35201step0 raw35201step0Labels permutation80 hz
    mixedMoment B raw35201step1 raw35201step1Labels = mixedMoment B raw35201step2 raw35201step2Labels := by
      have ha : raw35201step2 = (fun i j => raw35201step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35201step2 raw35201step1; decide +kernel
      have hl : raw35201step2Labels = raw35201step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35201step1 raw35201step1Labels permutation15 permutation7
    mixedMoment B raw35201step2 raw35201step2Labels = mixedMoment B raw35201step3 raw35201step3Labels := by
      have ha : raw35201step3 = -raw35201step2 := by apply Matrix.ext; change ∀ i j, raw35201step3 i j = -(raw35201step2 i j); unfold raw35201step3 raw35201step2; decide +kernel
      have hl : raw35201step3Labels = raw35201step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35201step3 raw35201step3Labels = mixedMoment B raw35201step4 raw35201step4Labels := by
      have ha : raw35201step4 = raw35201step3 := by apply Matrix.ext; unfold raw35201step4 raw35201step3; decide +kernel
      have hl : raw35201step3Labels = labelEmbedding1 ∘ raw35201step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35201step3 raw35201step3Labels raw35201step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

def raw35202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw35202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35202 raw35202Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw35202 raw35202Labels = mixedMoment B raw35202step0 raw35202step0Labels := by
      have hz : ∀ j, raw35202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35202step0 = (fun i j => raw35202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35202step0 raw35202; decide +kernel
      have hl : raw35202step0Labels = raw35202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35202 raw35202Labels permutation434 hz
    mixedMoment B raw35202step0 raw35202step0Labels = mixedMoment B raw35202step1 raw35202step1Labels := by
      have ha : raw35202step1 = (fun i j => raw35202step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35202step1 raw35202step0; decide +kernel
      have hl : raw35202step1Labels = raw35202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35202step0 raw35202step0Labels permutation57 permutation7
    mixedMoment B raw35202step1 raw35202step1Labels = mixedMoment B raw35202step2 raw35202step2Labels := by
      have ha : raw35202step2 = -raw35202step1 := by apply Matrix.ext; change ∀ i j, raw35202step2 i j = -(raw35202step1 i j); unfold raw35202step2 raw35202step1; decide +kernel
      have hl : raw35202step2Labels = raw35202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35202step2 raw35202step2Labels = mixedMoment B raw35202step3 raw35202step3Labels := by
      have ha : raw35202step3 = raw35202step2 := by apply Matrix.ext; unfold raw35202step3 raw35202step2; decide +kernel
      have hl : raw35202step2Labels = labelEmbedding1 ∘ raw35202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35202step2 raw35202step2Labels raw35202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

def raw35203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw35203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35203step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35203 raw35203Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw35203 raw35203Labels = mixedMoment B raw35203step0 raw35203step0Labels := by
      have hz : ∀ j, raw35203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35203step0 = (fun i j => raw35203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35203step0 raw35203; decide +kernel
      have hl : raw35203step0Labels = raw35203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35203 raw35203Labels permutation346 hz
    mixedMoment B raw35203step0 raw35203step0Labels = mixedMoment B raw35203step1 raw35203step1Labels := by
      have ha : raw35203step1 = (fun i j => raw35203step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35203step1 raw35203step0; decide +kernel
      have hl : raw35203step1Labels = raw35203step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35203step0 raw35203step0Labels permutation57 permutation7
    mixedMoment B raw35203step1 raw35203step1Labels = mixedMoment B raw35203step2 raw35203step2Labels := by
      have ha : raw35203step2 = -raw35203step1 := by apply Matrix.ext; change ∀ i j, raw35203step2 i j = -(raw35203step1 i j); unfold raw35203step2 raw35203step1; decide +kernel
      have hl : raw35203step2Labels = raw35203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35203step2 raw35203step2Labels = mixedMoment B raw35203step3 raw35203step3Labels := by
      have ha : raw35203step3 = raw35203step2 := by apply Matrix.ext; unfold raw35203step3 raw35203step2; decide +kernel
      have hl : raw35203step2Labels = labelEmbedding1 ∘ raw35203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35203step2 raw35203step2Labels raw35203step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

def raw35204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw35204step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35204step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -2, 3], ![-2, 1, 1]]
def raw35204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35204step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw35204step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35204step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw35204step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35204 raw35204Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw35204 raw35204Labels = mixedMoment B raw35204step0 raw35204step0Labels := by
      have hz : ∀ j, raw35204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35204step0 = (fun i j => raw35204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35204step0 raw35204; decide +kernel
      have hl : raw35204step0Labels = raw35204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35204 raw35204Labels permutation434 hz
    mixedMoment B raw35204step0 raw35204step0Labels = mixedMoment B raw35204step1 raw35204step1Labels := by
      have hz : ∀ j, raw35204step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35204step1 = (fun i j => raw35204step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35204step1 raw35204step0; decide +kernel
      have hl : raw35204step1Labels = raw35204step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35204step0 raw35204step0Labels permutation80 hz
    mixedMoment B raw35204step1 raw35204step1Labels = mixedMoment B raw35204step2 raw35204step2Labels := by
      have ha : raw35204step2 = (fun i j => raw35204step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35204step2 raw35204step1; decide +kernel
      have hl : raw35204step2Labels = raw35204step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35204step1 raw35204step1Labels permutation15 permutation7
    mixedMoment B raw35204step2 raw35204step2Labels = mixedMoment B raw35204step3 raw35204step3Labels := by
      have ha : raw35204step3 = -raw35204step2 := by apply Matrix.ext; change ∀ i j, raw35204step3 i j = -(raw35204step2 i j); unfold raw35204step3 raw35204step2; decide +kernel
      have hl : raw35204step3Labels = raw35204step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35204step3 raw35204step3Labels = mixedMoment B raw35204step4 raw35204step4Labels := by
      have ha : raw35204step4 = raw35204step3 := by apply Matrix.ext; unfold raw35204step4 raw35204step3; decide +kernel
      have hl : raw35204step3Labels = labelEmbedding1 ∘ raw35204step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35204step3 raw35204step3Labels raw35204step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw35205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35205 raw35205Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw35205 raw35205Labels = mixedMoment B raw35205step0 raw35205step0Labels := by
      have hz : ∀ j, raw35205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35205step0 = (fun i j => raw35205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35205step0 raw35205; decide +kernel
      have hl : raw35205step0Labels = raw35205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35205 raw35205Labels permutation434 hz
    mixedMoment B raw35205step0 raw35205step0Labels = mixedMoment B raw35205step1 raw35205step1Labels := by
      have ha : raw35205step1 = (fun i j => raw35205step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35205step1 raw35205step0; decide +kernel
      have hl : raw35205step1Labels = raw35205step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35205step0 raw35205step0Labels permutation57 permutation2
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw35206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35206 raw35206Labels = mixedMoment B node3364 node3364Labels := by
  calc
    mixedMoment B raw35206 raw35206Labels = mixedMoment B raw35206step0 raw35206step0Labels := by
      have ha : raw35206step0 = (fun i j => raw35206 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35206step0 raw35206; decide +kernel
      have hl : raw35206step0Labels = raw35206Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35206 raw35206Labels permutation272 permutation2
    _ = mixedMoment B node3364 node3364Labels := by rfl

def raw35207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35207step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35207 raw35207Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw35207 raw35207Labels = mixedMoment B raw35207step0 raw35207step0Labels := by
      have hz : ∀ j, raw35207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35207step0 = (fun i j => raw35207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35207step0 raw35207; decide +kernel
      have hl : raw35207step0Labels = raw35207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35207 raw35207Labels permutation434 hz
    mixedMoment B raw35207step0 raw35207step0Labels = mixedMoment B raw35207step1 raw35207step1Labels := by
      have ha : raw35207step1 = (fun i j => raw35207step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35207step1 raw35207step0; decide +kernel
      have hl : raw35207step1Labels = raw35207step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35207step0 raw35207step0Labels permutation56 permutation2
    _ = mixedMoment B node3392 node3392Labels := by rfl

def raw35208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35208 raw35208Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw35208 raw35208Labels = mixedMoment B raw35208step0 raw35208step0Labels := by
      have hz : ∀ j, raw35208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35208step0 = (fun i j => raw35208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35208step0 raw35208; decide +kernel
      have hl : raw35208step0Labels = raw35208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35208 raw35208Labels permutation434 hz
    mixedMoment B raw35208step0 raw35208step0Labels = mixedMoment B raw35208step1 raw35208step1Labels := by
      have ha : raw35208step1 = (fun i j => raw35208step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35208step1 raw35208step0; decide +kernel
      have hl : raw35208step1Labels = raw35208step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35208step0 raw35208step0Labels permutation57 permutation2
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw35209 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35209step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35209 raw35209Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw35209 raw35209Labels = mixedMoment B raw35209step0 raw35209step0Labels := by
      have hz : ∀ j, raw35209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35209step0 = (fun i j => raw35209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35209step0 raw35209; decide +kernel
      have hl : raw35209step0Labels = raw35209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35209 raw35209Labels permutation434 hz
    mixedMoment B raw35209step0 raw35209step0Labels = mixedMoment B raw35209step1 raw35209step1Labels := by
      have ha : raw35209step1 = (fun i j => raw35209step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35209step1 raw35209step0; decide +kernel
      have hl : raw35209step1Labels = raw35209step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35209step0 raw35209step0Labels permutation57 permutation2
    mixedMoment B raw35209step1 raw35209step1Labels = mixedMoment B raw35209step2 raw35209step2Labels := by
      have ha : raw35209step2 = -raw35209step1 := by apply Matrix.ext; change ∀ i j, raw35209step2 i j = -(raw35209step1 i j); unfold raw35209step2 raw35209step1; decide +kernel
      have hl : raw35209step2Labels = raw35209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw35210 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35210 raw35210Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw35210 raw35210Labels = mixedMoment B raw35210step0 raw35210step0Labels := by
      have hz : ∀ j, raw35210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35210step0 = (fun i j => raw35210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35210step0 raw35210; decide +kernel
      have hl : raw35210step0Labels = raw35210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35210 raw35210Labels permutation346 hz
    mixedMoment B raw35210step0 raw35210step0Labels = mixedMoment B raw35210step1 raw35210step1Labels := by
      have ha : raw35210step1 = (fun i j => raw35210step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35210step1 raw35210step0; decide +kernel
      have hl : raw35210step1Labels = raw35210step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35210step0 raw35210step0Labels permutation57 permutation2
    mixedMoment B raw35210step1 raw35210step1Labels = mixedMoment B raw35210step2 raw35210step2Labels := by
      have ha : raw35210step2 = -raw35210step1 := by apply Matrix.ext; change ∀ i j, raw35210step2 i j = -(raw35210step1 i j); unfold raw35210step2 raw35210step1; decide +kernel
      have hl : raw35210step2Labels = raw35210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw35211 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![0, 0, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![-3, 1, 2], ![-1, -1, 2]]
def raw35211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw35211step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35211 raw35211Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw35211 raw35211Labels = mixedMoment B raw35211step0 raw35211step0Labels := by
      have hz : ∀ j, raw35211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35211step0 = (fun i j => raw35211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35211step0 raw35211; decide +kernel
      have hl : raw35211step0Labels = raw35211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35211 raw35211Labels permutation434 hz
    mixedMoment B raw35211step0 raw35211step0Labels = mixedMoment B raw35211step1 raw35211step1Labels := by
      have hz : ∀ j, raw35211step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35211step1 = (fun i j => raw35211step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35211step1 raw35211step0; decide +kernel
      have hl : raw35211step1Labels = raw35211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35211step0 raw35211step0Labels permutation80 hz
    mixedMoment B raw35211step1 raw35211step1Labels = mixedMoment B raw35211step2 raw35211step2Labels := by
      have ha : raw35211step2 = (fun i j => raw35211step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35211step2 raw35211step1; decide +kernel
      have hl : raw35211step2Labels = raw35211step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35211step1 raw35211step1Labels permutation24 permutation2
    _ = mixedMoment B node5021 node5021Labels := by rfl

def raw35212 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw35212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw35212step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35212step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35212step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35212 raw35212Labels = mixedMoment B node5024 node5024Labels := by
  calc
    mixedMoment B raw35212 raw35212Labels = mixedMoment B raw35212step0 raw35212step0Labels := by
      have hz : ∀ j, raw35212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35212step0 = (fun i j => raw35212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35212step0 raw35212; decide +kernel
      have hl : raw35212step0Labels = raw35212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35212 raw35212Labels permutation434 hz
    mixedMoment B raw35212step0 raw35212step0Labels = mixedMoment B raw35212step1 raw35212step1Labels := by
      have hz : ∀ j, raw35212step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35212step1 = (fun i j => raw35212step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35212step1 raw35212step0; decide +kernel
      have hl : raw35212step1Labels = raw35212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35212step0 raw35212step0Labels permutation80 hz
    mixedMoment B raw35212step1 raw35212step1Labels = mixedMoment B raw35212step2 raw35212step2Labels := by
      have ha : raw35212step2 = (fun i j => raw35212step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35212step2 raw35212step1; decide +kernel
      have hl : raw35212step2Labels = raw35212step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35212step1 raw35212step1Labels permutation14 permutation2
    mixedMoment B raw35212step2 raw35212step2Labels = mixedMoment B raw35212step3 raw35212step3Labels := by
      have ha : raw35212step3 = -raw35212step2 := by apply Matrix.ext; change ∀ i j, raw35212step3 i j = -(raw35212step2 i j); unfold raw35212step3 raw35212step2; decide +kernel
      have hl : raw35212step3Labels = raw35212step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5024 node5024Labels := by rfl

def raw35213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![4, -2, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![4, -2, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![4, -2, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw35213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 3, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw35213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw35213step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35213 raw35213Labels = mixedMoment B node4615 node4615Labels := by
  calc
    mixedMoment B raw35213 raw35213Labels = mixedMoment B raw35213step0 raw35213step0Labels := by
      have hz : ∀ j, raw35213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35213step0 = (fun i j => raw35213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35213step0 raw35213; decide +kernel
      have hl : raw35213step0Labels = raw35213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35213 raw35213Labels permutation434 hz
    mixedMoment B raw35213step0 raw35213step0Labels = mixedMoment B raw35213step1 raw35213step1Labels := by
      have hz : ∀ j, raw35213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35213step1 = (fun i j => raw35213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35213step1 raw35213step0; decide +kernel
      have hl : raw35213step1Labels = raw35213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35213step0 raw35213step0Labels permutation80 hz
    mixedMoment B raw35213step1 raw35213step1Labels = mixedMoment B raw35213step2 raw35213step2Labels := by
      have ha : raw35213step2 = (fun i j => raw35213step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35213step2 raw35213step1; decide +kernel
      have hl : raw35213step2Labels = raw35213step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35213step1 raw35213step1Labels permutation15 permutation2
    mixedMoment B raw35213step2 raw35213step2Labels = mixedMoment B raw35213step3 raw35213step3Labels := by
      have ha : raw35213step3 = -raw35213step2 := by apply Matrix.ext; change ∀ i j, raw35213step3 i j = -(raw35213step2 i j); unfold raw35213step3 raw35213step2; decide +kernel
      have hl : raw35213step3Labels = raw35213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4615 node4615Labels := by rfl

def raw35214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35214step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35214 raw35214Labels = mixedMoment B node4568 node4568Labels := by
  calc
    mixedMoment B raw35214 raw35214Labels = mixedMoment B raw35214step0 raw35214step0Labels := by
      have hz : ∀ j, raw35214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35214step0 = (fun i j => raw35214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35214step0 raw35214; decide +kernel
      have hl : raw35214step0Labels = raw35214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35214 raw35214Labels permutation434 hz
    mixedMoment B raw35214step0 raw35214step0Labels = mixedMoment B raw35214step1 raw35214step1Labels := by
      have ha : raw35214step1 = (fun i j => raw35214step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35214step1 raw35214step0; decide +kernel
      have hl : raw35214step1Labels = raw35214step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35214step0 raw35214step0Labels permutation57 permutation2
    mixedMoment B raw35214step1 raw35214step1Labels = mixedMoment B raw35214step2 raw35214step2Labels := by
      have ha : raw35214step2 = -raw35214step1 := by apply Matrix.ext; change ∀ i j, raw35214step2 i j = -(raw35214step1 i j); unfold raw35214step2 raw35214step1; decide +kernel
      have hl : raw35214step2Labels = raw35214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4568 node4568Labels := by rfl

def raw35215 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35215 raw35215Labels = mixedMoment B node4568 node4568Labels := by
  calc
    mixedMoment B raw35215 raw35215Labels = mixedMoment B raw35215step0 raw35215step0Labels := by
      have hz : ∀ j, raw35215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35215step0 = (fun i j => raw35215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35215step0 raw35215; decide +kernel
      have hl : raw35215step0Labels = raw35215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35215 raw35215Labels permutation346 hz
    mixedMoment B raw35215step0 raw35215step0Labels = mixedMoment B raw35215step1 raw35215step1Labels := by
      have ha : raw35215step1 = (fun i j => raw35215step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35215step1 raw35215step0; decide +kernel
      have hl : raw35215step1Labels = raw35215step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35215step0 raw35215step0Labels permutation57 permutation2
    mixedMoment B raw35215step1 raw35215step1Labels = mixedMoment B raw35215step2 raw35215step2Labels := by
      have ha : raw35215step2 = -raw35215step1 := by apply Matrix.ext; change ∀ i j, raw35215step2 i j = -(raw35215step1 i j); unfold raw35215step2 raw35215step1; decide +kernel
      have hl : raw35215step2Labels = raw35215step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4568 node4568Labels := by rfl

def raw35216 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![0, 0, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![-3, 1, 2], ![-1, -1, 2]]
def raw35216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, -1, 2], ![-3, 1, 2]]
def raw35216step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35216step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw35216step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35216 raw35216Labels = mixedMoment B node4573 node4573Labels := by
  calc
    mixedMoment B raw35216 raw35216Labels = mixedMoment B raw35216step0 raw35216step0Labels := by
      have hz : ∀ j, raw35216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35216step0 = (fun i j => raw35216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35216step0 raw35216; decide +kernel
      have hl : raw35216step0Labels = raw35216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35216 raw35216Labels permutation434 hz
    mixedMoment B raw35216step0 raw35216step0Labels = mixedMoment B raw35216step1 raw35216step1Labels := by
      have hz : ∀ j, raw35216step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35216step1 = (fun i j => raw35216step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35216step1 raw35216step0; decide +kernel
      have hl : raw35216step1Labels = raw35216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35216step0 raw35216step0Labels permutation80 hz
    mixedMoment B raw35216step1 raw35216step1Labels = mixedMoment B raw35216step2 raw35216step2Labels := by
      have ha : raw35216step2 = (fun i j => raw35216step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35216step2 raw35216step1; decide +kernel
      have hl : raw35216step2Labels = raw35216step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35216step1 raw35216step1Labels permutation15 permutation2
    mixedMoment B raw35216step2 raw35216step2Labels = mixedMoment B raw35216step3 raw35216step3Labels := by
      have ha : raw35216step3 = -raw35216step2 := by apply Matrix.ext; change ∀ i j, raw35216step3 i j = -(raw35216step2 i j); unfold raw35216step3 raw35216step2; decide +kernel
      have hl : raw35216step3Labels = raw35216step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4573 node4573Labels := by rfl

def raw35217 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw35217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35217step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw35217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35217step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35217step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35217 raw35217Labels = mixedMoment B node4575 node4575Labels := by
  calc
    mixedMoment B raw35217 raw35217Labels = mixedMoment B raw35217step0 raw35217step0Labels := by
      have hz : ∀ j, raw35217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35217step0 = (fun i j => raw35217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35217step0 raw35217; decide +kernel
      have hl : raw35217step0Labels = raw35217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35217 raw35217Labels permutation434 hz
    mixedMoment B raw35217step0 raw35217step0Labels = mixedMoment B raw35217step1 raw35217step1Labels := by
      have hz : ∀ j, raw35217step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35217step1 = (fun i j => raw35217step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35217step1 raw35217step0; decide +kernel
      have hl : raw35217step1Labels = raw35217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35217step0 raw35217step0Labels permutation80 hz
    mixedMoment B raw35217step1 raw35217step1Labels = mixedMoment B raw35217step2 raw35217step2Labels := by
      have ha : raw35217step2 = (fun i j => raw35217step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35217step2 raw35217step1; decide +kernel
      have hl : raw35217step2Labels = raw35217step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35217step1 raw35217step1Labels permutation14 permutation2
    mixedMoment B raw35217step2 raw35217step2Labels = mixedMoment B raw35217step3 raw35217step3Labels := by
      have ha : raw35217step3 = -raw35217step2 := by apply Matrix.ext; change ∀ i j, raw35217step3 i j = -(raw35217step2 i j); unfold raw35217step3 raw35217step2; decide +kernel
      have hl : raw35217step3Labels = raw35217step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4575 node4575Labels := by rfl

def raw35218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 3, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw35218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw35218step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35218 raw35218Labels = mixedMoment B node5158 node5158Labels := by
  calc
    mixedMoment B raw35218 raw35218Labels = mixedMoment B raw35218step0 raw35218step0Labels := by
      have hz : ∀ j, raw35218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35218step0 = (fun i j => raw35218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35218step0 raw35218; decide +kernel
      have hl : raw35218step0Labels = raw35218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35218 raw35218Labels permutation434 hz
    mixedMoment B raw35218step0 raw35218step0Labels = mixedMoment B raw35218step1 raw35218step1Labels := by
      have ha : raw35218step1 = (fun i j => raw35218step0 (permutation63 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35218step1 raw35218step0; decide +kernel
      have hl : raw35218step1Labels = raw35218step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35218step0 raw35218step0Labels permutation63 permutation2
    mixedMoment B raw35218step1 raw35218step1Labels = mixedMoment B raw35218step2 raw35218step2Labels := by
      have ha : raw35218step2 = -raw35218step1 := by apply Matrix.ext; change ∀ i j, raw35218step2 i j = -(raw35218step1 i j); unfold raw35218step2 raw35218step1; decide +kernel
      have hl : raw35218step2Labels = raw35218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5158 node5158Labels := by rfl

def raw35219 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35219 raw35219Labels = mixedMoment B node5122 node5122Labels := by
  calc
    mixedMoment B raw35219 raw35219Labels = mixedMoment B raw35219step0 raw35219step0Labels := by
      have ha : raw35219step0 = (fun i j => raw35219 (permutation290 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35219step0 raw35219; decide +kernel
      have hl : raw35219step0Labels = raw35219Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35219 raw35219Labels permutation290 permutation2
    mixedMoment B raw35219step0 raw35219step0Labels = mixedMoment B raw35219step1 raw35219step1Labels := by
      have ha : raw35219step1 = -raw35219step0 := by apply Matrix.ext; change ∀ i j, raw35219step1 i j = -(raw35219step0 i j); unfold raw35219step1 raw35219step0; decide +kernel
      have hl : raw35219step1Labels = raw35219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5122 node5122Labels := by rfl

def raw35220 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw35220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35220 raw35220Labels = mixedMoment B node5006 node5006Labels := by
  calc
    mixedMoment B raw35220 raw35220Labels = mixedMoment B raw35220step0 raw35220step0Labels := by
      have hz : ∀ j, raw35220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35220step0 = (fun i j => raw35220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35220step0 raw35220; decide +kernel
      have hl : raw35220step0Labels = raw35220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35220 raw35220Labels permutation434 hz
    mixedMoment B raw35220step0 raw35220step0Labels = mixedMoment B raw35220step1 raw35220step1Labels := by
      have ha : raw35220step1 = (fun i j => raw35220step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35220step1 raw35220step0; decide +kernel
      have hl : raw35220step1Labels = raw35220step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35220step0 raw35220step0Labels permutation123 permutation2
    _ = mixedMoment B node5006 node5006Labels := by rfl

def raw35221 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw35221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35221step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35221 raw35221Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw35221 raw35221Labels = mixedMoment B raw35221step0 raw35221step0Labels := by
      have hz : ∀ j, raw35221 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35221step0 = (fun i j => raw35221 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35221step0 raw35221; decide +kernel
      have hl : raw35221step0Labels = raw35221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35221 raw35221Labels permutation434 hz
    mixedMoment B raw35221step0 raw35221step0Labels = mixedMoment B raw35221step1 raw35221step1Labels := by
      have ha : raw35221step1 = (fun i j => raw35221step0 (permutation62 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35221step1 raw35221step0; decide +kernel
      have hl : raw35221step1Labels = raw35221step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35221step0 raw35221step0Labels permutation62 permutation2
    mixedMoment B raw35221step1 raw35221step1Labels = mixedMoment B raw35221step2 raw35221step2Labels := by
      have ha : raw35221step2 = -raw35221step1 := by apply Matrix.ext; change ∀ i j, raw35221step2 i j = -(raw35221step1 i j); unfold raw35221step2 raw35221step1; decide +kernel
      have hl : raw35221step2Labels = raw35221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw35222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw35222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35222step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35222step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35222step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35222 raw35222Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw35222 raw35222Labels = mixedMoment B raw35222step0 raw35222step0Labels := by
      have hz : ∀ j, raw35222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35222step0 = (fun i j => raw35222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35222step0 raw35222; decide +kernel
      have hl : raw35222step0Labels = raw35222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35222 raw35222Labels permutation434 hz
    mixedMoment B raw35222step0 raw35222step0Labels = mixedMoment B raw35222step1 raw35222step1Labels := by
      have hz : ∀ j, raw35222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35222step1 = (fun i j => raw35222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35222step1 raw35222step0; decide +kernel
      have hl : raw35222step1Labels = raw35222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35222step0 raw35222step0Labels permutation80 hz
    mixedMoment B raw35222step1 raw35222step1Labels = mixedMoment B raw35222step2 raw35222step2Labels := by
      have ha : raw35222step2 = (fun i j => raw35222step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35222step2 raw35222step1; decide +kernel
      have hl : raw35222step2Labels = raw35222step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35222step1 raw35222step1Labels permutation14 permutation3
    mixedMoment B raw35222step2 raw35222step2Labels = mixedMoment B raw35222step3 raw35222step3Labels := by
      have ha : raw35222step3 = raw35222step2 := by apply Matrix.ext; unfold raw35222step3 raw35222step2; decide +kernel
      have hl : raw35222step2Labels = labelEmbedding6 ∘ raw35222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35222step2 raw35222step2Labels raw35222step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw35223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35223 raw35223Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35223 raw35223Labels = mixedMoment B raw35223step0 raw35223step0Labels := by
      have hz : ∀ j, raw35223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35223step0 = (fun i j => raw35223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35223step0 raw35223; decide +kernel
      have hl : raw35223step0Labels = raw35223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35223 raw35223Labels permutation434 hz
    mixedMoment B raw35223step0 raw35223step0Labels = mixedMoment B raw35223step1 raw35223step1Labels := by
      have ha : raw35223step1 = (fun i j => raw35223step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35223step1 raw35223step0; decide +kernel
      have hl : raw35223step1Labels = raw35223step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35223step0 raw35223step0Labels permutation126 permutation2
    mixedMoment B raw35223step1 raw35223step1Labels = mixedMoment B raw35223step2 raw35223step2Labels := by
      have ha : raw35223step2 = -raw35223step1 := by apply Matrix.ext; change ∀ i j, raw35223step2 i j = -(raw35223step1 i j); unfold raw35223step2 raw35223step1; decide +kernel
      have hl : raw35223step2Labels = raw35223step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw35224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35224 raw35224Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35224 raw35224Labels = mixedMoment B raw35224step0 raw35224step0Labels := by
      have hz : ∀ j, raw35224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35224step0 = (fun i j => raw35224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35224step0 raw35224; decide +kernel
      have hl : raw35224step0Labels = raw35224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35224 raw35224Labels permutation346 hz
    mixedMoment B raw35224step0 raw35224step0Labels = mixedMoment B raw35224step1 raw35224step1Labels := by
      have ha : raw35224step1 = (fun i j => raw35224step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35224step1 raw35224step0; decide +kernel
      have hl : raw35224step1Labels = raw35224step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35224step0 raw35224step0Labels permutation126 permutation2
    mixedMoment B raw35224step1 raw35224step1Labels = mixedMoment B raw35224step2 raw35224step2Labels := by
      have ha : raw35224step2 = -raw35224step1 := by apply Matrix.ext; change ∀ i j, raw35224step2 i j = -(raw35224step1 i j); unfold raw35224step2 raw35224step1; decide +kernel
      have hl : raw35224step2Labels = raw35224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw35225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw35225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw35225step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35225 raw35225Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw35225 raw35225Labels = mixedMoment B raw35225step0 raw35225step0Labels := by
      have hz : ∀ j, raw35225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35225step0 = (fun i j => raw35225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35225step0 raw35225; decide +kernel
      have hl : raw35225step0Labels = raw35225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35225 raw35225Labels permutation434 hz
    mixedMoment B raw35225step0 raw35225step0Labels = mixedMoment B raw35225step1 raw35225step1Labels := by
      have hz : ∀ j, raw35225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35225step1 = (fun i j => raw35225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35225step1 raw35225step0; decide +kernel
      have hl : raw35225step1Labels = raw35225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35225step0 raw35225step0Labels permutation80 hz
    mixedMoment B raw35225step1 raw35225step1Labels = mixedMoment B raw35225step2 raw35225step2Labels := by
      have ha : raw35225step2 = (fun i j => raw35225step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35225step2 raw35225step1; decide +kernel
      have hl : raw35225step2Labels = raw35225step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35225step1 raw35225step1Labels permutation15 permutation2
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw35226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35226step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35226step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35226 raw35226Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35226 raw35226Labels = mixedMoment B raw35226step0 raw35226step0Labels := by
      have hz : ∀ j, raw35226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35226step0 = (fun i j => raw35226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35226step0 raw35226; decide +kernel
      have hl : raw35226step0Labels = raw35226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35226 raw35226Labels permutation434 hz
    mixedMoment B raw35226step0 raw35226step0Labels = mixedMoment B raw35226step1 raw35226step1Labels := by
      have ha : raw35226step1 = (fun i j => raw35226step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35226step1 raw35226step0; decide +kernel
      have hl : raw35226step1Labels = raw35226step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35226step0 raw35226step0Labels permutation56 permutation3
    mixedMoment B raw35226step1 raw35226step1Labels = mixedMoment B raw35226step2 raw35226step2Labels := by
      have ha : raw35226step2 = raw35226step1 := by apply Matrix.ext; unfold raw35226step2 raw35226step1; decide +kernel
      have hl : raw35226step1Labels = labelEmbedding6 ∘ raw35226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35226step1 raw35226step1Labels raw35226step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw35227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35227step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35227 raw35227Labels = mixedMoment B node5457 node5457Labels := by
  calc
    mixedMoment B raw35227 raw35227Labels = mixedMoment B raw35227step0 raw35227step0Labels := by
      have ha : raw35227step0 = (fun i j => raw35227 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35227step0 raw35227; decide +kernel
      have hl : raw35227step0Labels = raw35227Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35227 raw35227Labels permutation158 permutation3
    mixedMoment B raw35227step0 raw35227step0Labels = mixedMoment B raw35227step1 raw35227step1Labels := by
      have ha : raw35227step1 = raw35227step0 := by apply Matrix.ext; unfold raw35227step1 raw35227step0; decide +kernel
      have hl : raw35227step0Labels = labelEmbedding6 ∘ raw35227step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35227step0 raw35227step0Labels raw35227step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5457 node5457Labels := by rfl

def raw35228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35228 raw35228Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35228 raw35228Labels = mixedMoment B raw35228step0 raw35228step0Labels := by
      have hz : ∀ j, raw35228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35228step0 = (fun i j => raw35228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35228step0 raw35228; decide +kernel
      have hl : raw35228step0Labels = raw35228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35228 raw35228Labels permutation434 hz
    mixedMoment B raw35228step0 raw35228step0Labels = mixedMoment B raw35228step1 raw35228step1Labels := by
      have ha : raw35228step1 = (fun i j => raw35228step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35228step1 raw35228step0; decide +kernel
      have hl : raw35228step1Labels = raw35228step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35228step0 raw35228step0Labels permutation33 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw35229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35229step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35229 raw35229Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35229 raw35229Labels = mixedMoment B raw35229step0 raw35229step0Labels := by
      have hz : ∀ j, raw35229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35229step0 = (fun i j => raw35229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35229step0 raw35229; decide +kernel
      have hl : raw35229step0Labels = raw35229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35229 raw35229Labels permutation346 hz
    mixedMoment B raw35229step0 raw35229step0Labels = mixedMoment B raw35229step1 raw35229step1Labels := by
      have ha : raw35229step1 = (fun i j => raw35229step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35229step1 raw35229step0; decide +kernel
      have hl : raw35229step1Labels = raw35229step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35229step0 raw35229step0Labels permutation56 permutation3
    mixedMoment B raw35229step1 raw35229step1Labels = mixedMoment B raw35229step2 raw35229step2Labels := by
      have ha : raw35229step2 = raw35229step1 := by apply Matrix.ext; unfold raw35229step2 raw35229step1; decide +kernel
      have hl : raw35229step1Labels = labelEmbedding6 ∘ raw35229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35229step1 raw35229step1Labels raw35229step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw35230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35230step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35230 raw35230Labels = mixedMoment B node5457 node5457Labels := by
  calc
    mixedMoment B raw35230 raw35230Labels = mixedMoment B raw35230step0 raw35230step0Labels := by
      have ha : raw35230step0 = (fun i j => raw35230 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35230step0 raw35230; decide +kernel
      have hl : raw35230step0Labels = raw35230Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35230 raw35230Labels permutation152 permutation3
    mixedMoment B raw35230step0 raw35230step0Labels = mixedMoment B raw35230step1 raw35230step1Labels := by
      have ha : raw35230step1 = raw35230step0 := by apply Matrix.ext; unfold raw35230step1 raw35230step0; decide +kernel
      have hl : raw35230step0Labels = labelEmbedding6 ∘ raw35230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35230step0 raw35230step0Labels raw35230step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5457 node5457Labels := by rfl

def raw35231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35231 raw35231Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35231 raw35231Labels = mixedMoment B raw35231step0 raw35231step0Labels := by
      have hz : ∀ j, raw35231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35231step0 = (fun i j => raw35231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35231step0 raw35231; decide +kernel
      have hl : raw35231step0Labels = raw35231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35231 raw35231Labels permutation346 hz
    mixedMoment B raw35231step0 raw35231step0Labels = mixedMoment B raw35231step1 raw35231step1Labels := by
      have ha : raw35231step1 = (fun i j => raw35231step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35231step1 raw35231step0; decide +kernel
      have hl : raw35231step1Labels = raw35231step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35231step0 raw35231step0Labels permutation33 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw35232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![3, -2, -1], ![2, -1, -1]]
def raw35232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35232step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35232step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35232step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35232step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35232 raw35232Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw35232 raw35232Labels = mixedMoment B raw35232step0 raw35232step0Labels := by
      have hz : ∀ j, raw35232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35232step0 = (fun i j => raw35232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35232step0 raw35232; decide +kernel
      have hl : raw35232step0Labels = raw35232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35232 raw35232Labels permutation434 hz
    mixedMoment B raw35232step0 raw35232step0Labels = mixedMoment B raw35232step1 raw35232step1Labels := by
      have hz : ∀ j, raw35232step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35232step1 = (fun i j => raw35232step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35232step1 raw35232step0; decide +kernel
      have hl : raw35232step1Labels = raw35232step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35232step0 raw35232step0Labels permutation80 hz
    mixedMoment B raw35232step1 raw35232step1Labels = mixedMoment B raw35232step2 raw35232step2Labels := by
      have ha : raw35232step2 = (fun i j => raw35232step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35232step2 raw35232step1; decide +kernel
      have hl : raw35232step2Labels = raw35232step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35232step1 raw35232step1Labels permutation15 permutation3
    mixedMoment B raw35232step2 raw35232step2Labels = mixedMoment B raw35232step3 raw35232step3Labels := by
      have ha : raw35232step3 = raw35232step2 := by apply Matrix.ext; unfold raw35232step3 raw35232step2; decide +kernel
      have hl : raw35232step2Labels = labelEmbedding6 ∘ raw35232step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35232step2 raw35232step2Labels raw35232step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

def raw35233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35233step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35233step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35233step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35233step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35233 raw35233Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35233 raw35233Labels = mixedMoment B raw35233step0 raw35233step0Labels := by
      have hz : ∀ j, raw35233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35233step0 = (fun i j => raw35233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35233step0 raw35233; decide +kernel
      have hl : raw35233step0Labels = raw35233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35233 raw35233Labels permutation434 hz
    mixedMoment B raw35233step0 raw35233step0Labels = mixedMoment B raw35233step1 raw35233step1Labels := by
      have ha : raw35233step1 = (fun i j => raw35233step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35233step1 raw35233step0; decide +kernel
      have hl : raw35233step1Labels = raw35233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35233step0 raw35233step0Labels permutation126 permutation3
    mixedMoment B raw35233step1 raw35233step1Labels = mixedMoment B raw35233step2 raw35233step2Labels := by
      have ha : raw35233step2 = -raw35233step1 := by apply Matrix.ext; change ∀ i j, raw35233step2 i j = -(raw35233step1 i j); unfold raw35233step2 raw35233step1; decide +kernel
      have hl : raw35233step2Labels = raw35233step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35233step2 raw35233step2Labels = mixedMoment B raw35233step3 raw35233step3Labels := by
      have ha : raw35233step3 = raw35233step2 := by apply Matrix.ext; unfold raw35233step3 raw35233step2; decide +kernel
      have hl : raw35233step2Labels = labelEmbedding6 ∘ raw35233step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35233step2 raw35233step2Labels raw35233step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw35234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35234step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35234step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35234step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35234step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35234 raw35234Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35234 raw35234Labels = mixedMoment B raw35234step0 raw35234step0Labels := by
      have hz : ∀ j, raw35234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35234step0 = (fun i j => raw35234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35234step0 raw35234; decide +kernel
      have hl : raw35234step0Labels = raw35234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35234 raw35234Labels permutation346 hz
    mixedMoment B raw35234step0 raw35234step0Labels = mixedMoment B raw35234step1 raw35234step1Labels := by
      have ha : raw35234step1 = (fun i j => raw35234step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35234step1 raw35234step0; decide +kernel
      have hl : raw35234step1Labels = raw35234step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35234step0 raw35234step0Labels permutation126 permutation3
    mixedMoment B raw35234step1 raw35234step1Labels = mixedMoment B raw35234step2 raw35234step2Labels := by
      have ha : raw35234step2 = -raw35234step1 := by apply Matrix.ext; change ∀ i j, raw35234step2 i j = -(raw35234step1 i j); unfold raw35234step2 raw35234step1; decide +kernel
      have hl : raw35234step2Labels = raw35234step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35234step2 raw35234step2Labels = mixedMoment B raw35234step3 raw35234step3Labels := by
      have ha : raw35234step3 = raw35234step2 := by apply Matrix.ext; unfold raw35234step3 raw35234step2; decide +kernel
      have hl : raw35234step2Labels = labelEmbedding6 ∘ raw35234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35234step2 raw35234step2Labels raw35234step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw35235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw35235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw35235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw35235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35235step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35235step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35235step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35235step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35235 raw35235Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw35235 raw35235Labels = mixedMoment B raw35235step0 raw35235step0Labels := by
      have hz : ∀ j, raw35235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35235step0 = (fun i j => raw35235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35235step0 raw35235; decide +kernel
      have hl : raw35235step0Labels = raw35235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35235 raw35235Labels permutation434 hz
    mixedMoment B raw35235step0 raw35235step0Labels = mixedMoment B raw35235step1 raw35235step1Labels := by
      have hz : ∀ j, raw35235step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35235step1 = (fun i j => raw35235step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35235step1 raw35235step0; decide +kernel
      have hl : raw35235step1Labels = raw35235step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35235step0 raw35235step0Labels permutation80 hz
    mixedMoment B raw35235step1 raw35235step1Labels = mixedMoment B raw35235step2 raw35235step2Labels := by
      have ha : raw35235step2 = (fun i j => raw35235step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35235step2 raw35235step1; decide +kernel
      have hl : raw35235step2Labels = raw35235step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35235step1 raw35235step1Labels permutation24 permutation3
    mixedMoment B raw35235step2 raw35235step2Labels = mixedMoment B raw35235step3 raw35235step3Labels := by
      have ha : raw35235step3 = -raw35235step2 := by apply Matrix.ext; change ∀ i j, raw35235step3 i j = -(raw35235step2 i j); unfold raw35235step3 raw35235step2; decide +kernel
      have hl : raw35235step3Labels = raw35235step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35235step3 raw35235step3Labels = mixedMoment B raw35235step4 raw35235step4Labels := by
      have ha : raw35235step4 = raw35235step3 := by apply Matrix.ext; unfold raw35235step4 raw35235step3; decide +kernel
      have hl : raw35235step3Labels = labelEmbedding6 ∘ raw35235step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35235step3 raw35235step3Labels raw35235step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw35236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -1, -1], ![3, -2, -1]]
def raw35236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35236step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35236step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35236step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35236step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35236 raw35236Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw35236 raw35236Labels = mixedMoment B raw35236step0 raw35236step0Labels := by
      have hz : ∀ j, raw35236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35236step0 = (fun i j => raw35236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35236step0 raw35236; decide +kernel
      have hl : raw35236step0Labels = raw35236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35236 raw35236Labels permutation434 hz
    mixedMoment B raw35236step0 raw35236step0Labels = mixedMoment B raw35236step1 raw35236step1Labels := by
      have hz : ∀ j, raw35236step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35236step1 = (fun i j => raw35236step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35236step1 raw35236step0; decide +kernel
      have hl : raw35236step1Labels = raw35236step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35236step0 raw35236step0Labels permutation80 hz
    mixedMoment B raw35236step1 raw35236step1Labels = mixedMoment B raw35236step2 raw35236step2Labels := by
      have ha : raw35236step2 = (fun i j => raw35236step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35236step2 raw35236step1; decide +kernel
      have hl : raw35236step2Labels = raw35236step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35236step1 raw35236step1Labels permutation14 permutation3
    mixedMoment B raw35236step2 raw35236step2Labels = mixedMoment B raw35236step3 raw35236step3Labels := by
      have ha : raw35236step3 = raw35236step2 := by apply Matrix.ext; unfold raw35236step3 raw35236step2; decide +kernel
      have hl : raw35236step2Labels = labelEmbedding6 ∘ raw35236step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35236step2 raw35236step2Labels raw35236step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

def raw35237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35237step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35237step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35237step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35237step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35237 raw35237Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35237 raw35237Labels = mixedMoment B raw35237step0 raw35237step0Labels := by
      have hz : ∀ j, raw35237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35237step0 = (fun i j => raw35237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35237step0 raw35237; decide +kernel
      have hl : raw35237step0Labels = raw35237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35237 raw35237Labels permutation434 hz
    mixedMoment B raw35237step0 raw35237step0Labels = mixedMoment B raw35237step1 raw35237step1Labels := by
      have ha : raw35237step1 = (fun i j => raw35237step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35237step1 raw35237step0; decide +kernel
      have hl : raw35237step1Labels = raw35237step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35237step0 raw35237step0Labels permutation150 permutation3
    mixedMoment B raw35237step1 raw35237step1Labels = mixedMoment B raw35237step2 raw35237step2Labels := by
      have ha : raw35237step2 = -raw35237step1 := by apply Matrix.ext; change ∀ i j, raw35237step2 i j = -(raw35237step1 i j); unfold raw35237step2 raw35237step1; decide +kernel
      have hl : raw35237step2Labels = raw35237step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35237step2 raw35237step2Labels = mixedMoment B raw35237step3 raw35237step3Labels := by
      have ha : raw35237step3 = raw35237step2 := by apply Matrix.ext; unfold raw35237step3 raw35237step2; decide +kernel
      have hl : raw35237step2Labels = labelEmbedding6 ∘ raw35237step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35237step2 raw35237step2Labels raw35237step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw35238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35238step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35238step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35238step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35238step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35238 raw35238Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35238 raw35238Labels = mixedMoment B raw35238step0 raw35238step0Labels := by
      have hz : ∀ j, raw35238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35238step0 = (fun i j => raw35238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35238step0 raw35238; decide +kernel
      have hl : raw35238step0Labels = raw35238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35238 raw35238Labels permutation346 hz
    mixedMoment B raw35238step0 raw35238step0Labels = mixedMoment B raw35238step1 raw35238step1Labels := by
      have ha : raw35238step1 = (fun i j => raw35238step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35238step1 raw35238step0; decide +kernel
      have hl : raw35238step1Labels = raw35238step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35238step0 raw35238step0Labels permutation150 permutation3
    mixedMoment B raw35238step1 raw35238step1Labels = mixedMoment B raw35238step2 raw35238step2Labels := by
      have ha : raw35238step2 = -raw35238step1 := by apply Matrix.ext; change ∀ i j, raw35238step2 i j = -(raw35238step1 i j); unfold raw35238step2 raw35238step1; decide +kernel
      have hl : raw35238step2Labels = raw35238step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35238step2 raw35238step2Labels = mixedMoment B raw35238step3 raw35238step3Labels := by
      have ha : raw35238step3 = raw35238step2 := by apply Matrix.ext; unfold raw35238step3 raw35238step2; decide +kernel
      have hl : raw35238step2Labels = labelEmbedding6 ∘ raw35238step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35238step2 raw35238step2Labels raw35238step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw35239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw35239step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35239 raw35239Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw35239 raw35239Labels = mixedMoment B raw35239step0 raw35239step0Labels := by
      have hz : ∀ j, raw35239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35239step0 = (fun i j => raw35239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35239step0 raw35239; decide +kernel
      have hl : raw35239step0Labels = raw35239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35239 raw35239Labels permutation434 hz
    mixedMoment B raw35239step0 raw35239step0Labels = mixedMoment B raw35239step1 raw35239step1Labels := by
      have hz : ∀ j, raw35239step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35239step1 = (fun i j => raw35239step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35239step1 raw35239step0; decide +kernel
      have hl : raw35239step1Labels = raw35239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35239step0 raw35239step0Labels permutation80 hz
    mixedMoment B raw35239step1 raw35239step1Labels = mixedMoment B raw35239step2 raw35239step2Labels := by
      have ha : raw35239step2 = (fun i j => raw35239step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35239step2 raw35239step1; decide +kernel
      have hl : raw35239step2Labels = raw35239step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35239step1 raw35239step1Labels permutation14 permutation3
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw35240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35240step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35240 raw35240Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw35240 raw35240Labels = mixedMoment B raw35240step0 raw35240step0Labels := by
      have hz : ∀ j, raw35240 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35240step0 = (fun i j => raw35240 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35240step0 raw35240; decide +kernel
      have hl : raw35240step0Labels = raw35240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35240 raw35240Labels permutation434 hz
    mixedMoment B raw35240step0 raw35240step0Labels = mixedMoment B raw35240step1 raw35240step1Labels := by
      have ha : raw35240step1 = (fun i j => raw35240step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35240step1 raw35240step0; decide +kernel
      have hl : raw35240step1Labels = raw35240step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35240step0 raw35240step0Labels permutation123 permutation3
    mixedMoment B raw35240step1 raw35240step1Labels = mixedMoment B raw35240step2 raw35240step2Labels := by
      have ha : raw35240step2 = -raw35240step1 := by apply Matrix.ext; change ∀ i j, raw35240step2 i j = -(raw35240step1 i j); unfold raw35240step2 raw35240step1; decide +kernel
      have hl : raw35240step2Labels = raw35240step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw35241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35241 raw35241Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw35241 raw35241Labels = mixedMoment B raw35241step0 raw35241step0Labels := by
      have hz : ∀ j, raw35241 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35241step0 = (fun i j => raw35241 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35241step0 raw35241; decide +kernel
      have hl : raw35241step0Labels = raw35241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35241 raw35241Labels permutation346 hz
    mixedMoment B raw35241step0 raw35241step0Labels = mixedMoment B raw35241step1 raw35241step1Labels := by
      have ha : raw35241step1 = (fun i j => raw35241step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35241step1 raw35241step0; decide +kernel
      have hl : raw35241step1Labels = raw35241step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35241step0 raw35241step0Labels permutation123 permutation3
    mixedMoment B raw35241step1 raw35241step1Labels = mixedMoment B raw35241step2 raw35241step2Labels := by
      have ha : raw35241step2 = -raw35241step1 := by apply Matrix.ext; change ∀ i j, raw35241step2 i j = -(raw35241step1 i j); unfold raw35241step2 raw35241step1; decide +kernel
      have hl : raw35241step2Labels = raw35241step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw35242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw35242step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35242 raw35242Labels = mixedMoment B node4000 node4000Labels := by
  calc
    mixedMoment B raw35242 raw35242Labels = mixedMoment B raw35242step0 raw35242step0Labels := by
      have hz : ∀ j, raw35242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35242step0 = (fun i j => raw35242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35242step0 raw35242; decide +kernel
      have hl : raw35242step0Labels = raw35242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35242 raw35242Labels permutation434 hz
    mixedMoment B raw35242step0 raw35242step0Labels = mixedMoment B raw35242step1 raw35242step1Labels := by
      have hz : ∀ j, raw35242step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35242step1 = (fun i j => raw35242step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35242step1 raw35242step0; decide +kernel
      have hl : raw35242step1Labels = raw35242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35242step0 raw35242step0Labels permutation80 hz
    mixedMoment B raw35242step1 raw35242step1Labels = mixedMoment B raw35242step2 raw35242step2Labels := by
      have ha : raw35242step2 = (fun i j => raw35242step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35242step2 raw35242step1; decide +kernel
      have hl : raw35242step2Labels = raw35242step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35242step1 raw35242step1Labels permutation14 permutation3
    _ = mixedMoment B node4000 node4000Labels := by rfl

def raw35243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw35243step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35243step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35243 raw35243Labels = mixedMoment B node4000 node4000Labels := by
  calc
    mixedMoment B raw35243 raw35243Labels = mixedMoment B raw35243step0 raw35243step0Labels := by
      have hz : ∀ j, raw35243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35243step0 = (fun i j => raw35243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35243step0 raw35243; decide +kernel
      have hl : raw35243step0Labels = raw35243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35243 raw35243Labels permutation434 hz
    mixedMoment B raw35243step0 raw35243step0Labels = mixedMoment B raw35243step1 raw35243step1Labels := by
      have hz : ∀ j, raw35243step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35243step1 = (fun i j => raw35243step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35243step1 raw35243step0; decide +kernel
      have hl : raw35243step1Labels = raw35243step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35243step0 raw35243step0Labels permutation80 hz
    mixedMoment B raw35243step1 raw35243step1Labels = mixedMoment B raw35243step2 raw35243step2Labels := by
      have ha : raw35243step2 = (fun i j => raw35243step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35243step2 raw35243step1; decide +kernel
      have hl : raw35243step2Labels = raw35243step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35243step1 raw35243step1Labels permutation15 permutation3
    _ = mixedMoment B node4000 node4000Labels := by rfl

def raw35244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35244step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35244 raw35244Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw35244 raw35244Labels = mixedMoment B raw35244step0 raw35244step0Labels := by
      have hz : ∀ j, raw35244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35244step0 = (fun i j => raw35244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35244step0 raw35244; decide +kernel
      have hl : raw35244step0Labels = raw35244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35244 raw35244Labels permutation434 hz
    mixedMoment B raw35244step0 raw35244step0Labels = mixedMoment B raw35244step1 raw35244step1Labels := by
      have ha : raw35244step1 = (fun i j => raw35244step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35244step1 raw35244step0; decide +kernel
      have hl : raw35244step1Labels = raw35244step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35244step0 raw35244step0Labels permutation56 permutation3
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw35245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35245 raw35245Labels = mixedMoment B node3917 node3917Labels := by
  calc
    mixedMoment B raw35245 raw35245Labels = mixedMoment B raw35245step0 raw35245step0Labels := by
      have ha : raw35245step0 = (fun i j => raw35245 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35245step0 raw35245; decide +kernel
      have hl : raw35245step0Labels = raw35245Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35245 raw35245Labels permutation158 permutation3
    _ = mixedMoment B node3917 node3917Labels := by rfl

def raw35246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35246 raw35246Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw35246 raw35246Labels = mixedMoment B raw35246step0 raw35246step0Labels := by
      have hz : ∀ j, raw35246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35246step0 = (fun i j => raw35246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35246step0 raw35246; decide +kernel
      have hl : raw35246step0Labels = raw35246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35246 raw35246Labels permutation434 hz
    mixedMoment B raw35246step0 raw35246step0Labels = mixedMoment B raw35246step1 raw35246step1Labels := by
      have ha : raw35246step1 = (fun i j => raw35246step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35246step1 raw35246step0; decide +kernel
      have hl : raw35246step1Labels = raw35246step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35246step0 raw35246step0Labels permutation34 permutation3
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw35247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35247 raw35247Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw35247 raw35247Labels = mixedMoment B raw35247step0 raw35247step0Labels := by
      have hz : ∀ j, raw35247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35247step0 = (fun i j => raw35247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35247step0 raw35247; decide +kernel
      have hl : raw35247step0Labels = raw35247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35247 raw35247Labels permutation434 hz
    mixedMoment B raw35247step0 raw35247step0Labels = mixedMoment B raw35247step1 raw35247step1Labels := by
      have ha : raw35247step1 = (fun i j => raw35247step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35247step1 raw35247step0; decide +kernel
      have hl : raw35247step1Labels = raw35247step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35247step0 raw35247step0Labels permutation36 permutation3
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw35248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35248step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35248 raw35248Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw35248 raw35248Labels = mixedMoment B raw35248step0 raw35248step0Labels := by
      have hz : ∀ j, raw35248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35248step0 = (fun i j => raw35248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35248step0 raw35248; decide +kernel
      have hl : raw35248step0Labels = raw35248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35248 raw35248Labels permutation346 hz
    mixedMoment B raw35248step0 raw35248step0Labels = mixedMoment B raw35248step1 raw35248step1Labels := by
      have ha : raw35248step1 = (fun i j => raw35248step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35248step1 raw35248step0; decide +kernel
      have hl : raw35248step1Labels = raw35248step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35248step0 raw35248step0Labels permutation56 permutation3
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw35249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35249 raw35249Labels = mixedMoment B node3917 node3917Labels := by
  calc
    mixedMoment B raw35249 raw35249Labels = mixedMoment B raw35249step0 raw35249step0Labels := by
      have ha : raw35249step0 = (fun i j => raw35249 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35249step0 raw35249; decide +kernel
      have hl : raw35249step0Labels = raw35249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35249 raw35249Labels permutation152 permutation3
    _ = mixedMoment B node3917 node3917Labels := by rfl

def raw35250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35250 raw35250Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw35250 raw35250Labels = mixedMoment B raw35250step0 raw35250step0Labels := by
      have hz : ∀ j, raw35250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35250step0 = (fun i j => raw35250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35250step0 raw35250; decide +kernel
      have hl : raw35250step0Labels = raw35250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35250 raw35250Labels permutation346 hz
    mixedMoment B raw35250step0 raw35250step0Labels = mixedMoment B raw35250step1 raw35250step1Labels := by
      have ha : raw35250step1 = (fun i j => raw35250step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35250step1 raw35250step0; decide +kernel
      have hl : raw35250step1Labels = raw35250step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35250step0 raw35250step0Labels permutation34 permutation3
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw35251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw35251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35251 raw35251Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw35251 raw35251Labels = mixedMoment B raw35251step0 raw35251step0Labels := by
      have hz : ∀ j, raw35251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35251step0 = (fun i j => raw35251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35251step0 raw35251; decide +kernel
      have hl : raw35251step0Labels = raw35251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35251 raw35251Labels permutation346 hz
    mixedMoment B raw35251step0 raw35251step0Labels = mixedMoment B raw35251step1 raw35251step1Labels := by
      have ha : raw35251step1 = (fun i j => raw35251step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35251step1 raw35251step0; decide +kernel
      have hl : raw35251step1Labels = raw35251step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35251step0 raw35251step0Labels permutation36 permutation3
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw35252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![3, -2, -1], ![2, -1, -1]]
def raw35252step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35252step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35252 raw35252Labels = mixedMoment B node2344 node2344Labels := by
  calc
    mixedMoment B raw35252 raw35252Labels = mixedMoment B raw35252step0 raw35252step0Labels := by
      have hz : ∀ j, raw35252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35252step0 = (fun i j => raw35252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35252step0 raw35252; decide +kernel
      have hl : raw35252step0Labels = raw35252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35252 raw35252Labels permutation434 hz
    mixedMoment B raw35252step0 raw35252step0Labels = mixedMoment B raw35252step1 raw35252step1Labels := by
      have hz : ∀ j, raw35252step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35252step1 = (fun i j => raw35252step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35252step1 raw35252step0; decide +kernel
      have hl : raw35252step1Labels = raw35252step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35252step0 raw35252step0Labels permutation80 hz
    mixedMoment B raw35252step1 raw35252step1Labels = mixedMoment B raw35252step2 raw35252step2Labels := by
      have ha : raw35252step2 = (fun i j => raw35252step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35252step2 raw35252step1; decide +kernel
      have hl : raw35252step2Labels = raw35252step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35252step1 raw35252step1Labels permutation15 permutation3
    _ = mixedMoment B node2344 node2344Labels := by rfl

def raw35253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35253 raw35253Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw35253 raw35253Labels = mixedMoment B raw35253step0 raw35253step0Labels := by
      have hz : ∀ j, raw35253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35253step0 = (fun i j => raw35253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35253step0 raw35253; decide +kernel
      have hl : raw35253step0Labels = raw35253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35253 raw35253Labels permutation434 hz
    mixedMoment B raw35253step0 raw35253step0Labels = mixedMoment B raw35253step1 raw35253step1Labels := by
      have ha : raw35253step1 = (fun i j => raw35253step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35253step1 raw35253step0; decide +kernel
      have hl : raw35253step1Labels = raw35253step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35253step0 raw35253step0Labels permutation126 permutation3
    mixedMoment B raw35253step1 raw35253step1Labels = mixedMoment B raw35253step2 raw35253step2Labels := by
      have ha : raw35253step2 = -raw35253step1 := by apply Matrix.ext; change ∀ i j, raw35253step2 i j = -(raw35253step1 i j); unfold raw35253step2 raw35253step1; decide +kernel
      have hl : raw35253step2Labels = raw35253step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw35254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw35254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35254 raw35254Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw35254 raw35254Labels = mixedMoment B raw35254step0 raw35254step0Labels := by
      have hz : ∀ j, raw35254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35254step0 = (fun i j => raw35254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35254step0 raw35254; decide +kernel
      have hl : raw35254step0Labels = raw35254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35254 raw35254Labels permutation346 hz
    mixedMoment B raw35254step0 raw35254step0Labels = mixedMoment B raw35254step1 raw35254step1Labels := by
      have ha : raw35254step1 = (fun i j => raw35254step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35254step1 raw35254step0; decide +kernel
      have hl : raw35254step1Labels = raw35254step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35254step0 raw35254step0Labels permutation126 permutation3
    mixedMoment B raw35254step1 raw35254step1Labels = mixedMoment B raw35254step2 raw35254step2Labels := by
      have ha : raw35254step2 = -raw35254step1 := by apply Matrix.ext; change ∀ i j, raw35254step2 i j = -(raw35254step1 i j); unfold raw35254step2 raw35254step1; decide +kernel
      have hl : raw35254step2Labels = raw35254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw35255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw35255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw35255step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw35255step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35255step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35255step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35255 raw35255Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw35255 raw35255Labels = mixedMoment B raw35255step0 raw35255step0Labels := by
      have hz : ∀ j, raw35255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35255step0 = (fun i j => raw35255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35255step0 raw35255; decide +kernel
      have hl : raw35255step0Labels = raw35255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35255 raw35255Labels permutation434 hz
    mixedMoment B raw35255step0 raw35255step0Labels = mixedMoment B raw35255step1 raw35255step1Labels := by
      have hz : ∀ j, raw35255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35255step1 = (fun i j => raw35255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35255step1 raw35255step0; decide +kernel
      have hl : raw35255step1Labels = raw35255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35255step0 raw35255step0Labels permutation80 hz
    mixedMoment B raw35255step1 raw35255step1Labels = mixedMoment B raw35255step2 raw35255step2Labels := by
      have ha : raw35255step2 = (fun i j => raw35255step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35255step2 raw35255step1; decide +kernel
      have hl : raw35255step2Labels = raw35255step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35255step1 raw35255step1Labels permutation24 permutation3
    mixedMoment B raw35255step2 raw35255step2Labels = mixedMoment B raw35255step3 raw35255step3Labels := by
      have ha : raw35255step3 = -raw35255step2 := by apply Matrix.ext; change ∀ i j, raw35255step3 i j = -(raw35255step2 i j); unfold raw35255step3 raw35255step2; decide +kernel
      have hl : raw35255step3Labels = raw35255step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw35256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -1, -1], ![3, -2, -1]]
def raw35256step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35256 raw35256Labels = mixedMoment B node2344 node2344Labels := by
  calc
    mixedMoment B raw35256 raw35256Labels = mixedMoment B raw35256step0 raw35256step0Labels := by
      have hz : ∀ j, raw35256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35256step0 = (fun i j => raw35256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35256step0 raw35256; decide +kernel
      have hl : raw35256step0Labels = raw35256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35256 raw35256Labels permutation434 hz
    mixedMoment B raw35256step0 raw35256step0Labels = mixedMoment B raw35256step1 raw35256step1Labels := by
      have hz : ∀ j, raw35256step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35256step1 = (fun i j => raw35256step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35256step1 raw35256step0; decide +kernel
      have hl : raw35256step1Labels = raw35256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35256step0 raw35256step0Labels permutation80 hz
    mixedMoment B raw35256step1 raw35256step1Labels = mixedMoment B raw35256step2 raw35256step2Labels := by
      have ha : raw35256step2 = (fun i j => raw35256step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35256step2 raw35256step1; decide +kernel
      have hl : raw35256step2Labels = raw35256step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35256step1 raw35256step1Labels permutation14 permutation3
    _ = mixedMoment B node2344 node2344Labels := by rfl

def raw35257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35257step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35257 raw35257Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw35257 raw35257Labels = mixedMoment B raw35257step0 raw35257step0Labels := by
      have hz : ∀ j, raw35257 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35257step0 = (fun i j => raw35257 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35257step0 raw35257; decide +kernel
      have hl : raw35257step0Labels = raw35257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35257 raw35257Labels permutation434 hz
    mixedMoment B raw35257step0 raw35257step0Labels = mixedMoment B raw35257step1 raw35257step1Labels := by
      have ha : raw35257step1 = (fun i j => raw35257step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35257step1 raw35257step0; decide +kernel
      have hl : raw35257step1Labels = raw35257step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35257step0 raw35257step0Labels permutation150 permutation3
    mixedMoment B raw35257step1 raw35257step1Labels = mixedMoment B raw35257step2 raw35257step2Labels := by
      have ha : raw35257step2 = -raw35257step1 := by apply Matrix.ext; change ∀ i j, raw35257step2 i j = -(raw35257step1 i j); unfold raw35257step2 raw35257step1; decide +kernel
      have hl : raw35257step2Labels = raw35257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw35258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw35258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35258 raw35258Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw35258 raw35258Labels = mixedMoment B raw35258step0 raw35258step0Labels := by
      have hz : ∀ j, raw35258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35258step0 = (fun i j => raw35258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35258step0 raw35258; decide +kernel
      have hl : raw35258step0Labels = raw35258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35258 raw35258Labels permutation346 hz
    mixedMoment B raw35258step0 raw35258step0Labels = mixedMoment B raw35258step1 raw35258step1Labels := by
      have ha : raw35258step1 = (fun i j => raw35258step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35258step1 raw35258step0; decide +kernel
      have hl : raw35258step1Labels = raw35258step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35258step0 raw35258step0Labels permutation150 permutation3
    mixedMoment B raw35258step1 raw35258step1Labels = mixedMoment B raw35258step2 raw35258step2Labels := by
      have ha : raw35258step2 = -raw35258step1 := by apply Matrix.ext; change ∀ i j, raw35258step2 i j = -(raw35258step1 i j); unfold raw35258step2 raw35258step1; decide +kernel
      have hl : raw35258step2Labels = raw35258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw35259 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw35259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35259step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35259step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35259 raw35259Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw35259 raw35259Labels = mixedMoment B raw35259step0 raw35259step0Labels := by
      have hz : ∀ j, raw35259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35259step0 = (fun i j => raw35259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35259step0 raw35259; decide +kernel
      have hl : raw35259step0Labels = raw35259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35259 raw35259Labels permutation434 hz
    mixedMoment B raw35259step0 raw35259step0Labels = mixedMoment B raw35259step1 raw35259step1Labels := by
      have hz : ∀ j, raw35259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35259step1 = (fun i j => raw35259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35259step1 raw35259step0; decide +kernel
      have hl : raw35259step1Labels = raw35259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35259step0 raw35259step0Labels permutation80 hz
    mixedMoment B raw35259step1 raw35259step1Labels = mixedMoment B raw35259step2 raw35259step2Labels := by
      have ha : raw35259step2 = (fun i j => raw35259step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35259step2 raw35259step1; decide +kernel
      have hl : raw35259step2Labels = raw35259step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35259step1 raw35259step1Labels permutation14 permutation6
    mixedMoment B raw35259step2 raw35259step2Labels = mixedMoment B raw35259step3 raw35259step3Labels := by
      have ha : raw35259step3 = raw35259step2 := by apply Matrix.ext; unfold raw35259step3 raw35259step2; decide +kernel
      have hl : raw35259step2Labels = labelEmbedding9 ∘ raw35259step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35259step2 raw35259step2Labels raw35259step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5390 node5390Labels := by rfl

def raw35260 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35260step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35260 raw35260Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35260 raw35260Labels = mixedMoment B raw35260step0 raw35260step0Labels := by
      have hz : ∀ j, raw35260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35260step0 = (fun i j => raw35260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35260step0 raw35260; decide +kernel
      have hl : raw35260step0Labels = raw35260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35260 raw35260Labels permutation434 hz
    mixedMoment B raw35260step0 raw35260step0Labels = mixedMoment B raw35260step1 raw35260step1Labels := by
      have ha : raw35260step1 = (fun i j => raw35260step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35260step1 raw35260step0; decide +kernel
      have hl : raw35260step1Labels = raw35260step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35260step0 raw35260step0Labels permutation32 permutation7
    mixedMoment B raw35260step1 raw35260step1Labels = mixedMoment B raw35260step2 raw35260step2Labels := by
      have ha : raw35260step2 = raw35260step1 := by apply Matrix.ext; unfold raw35260step2 raw35260step1; decide +kernel
      have hl : raw35260step1Labels = labelEmbedding10 ∘ raw35260step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35260step1 raw35260step1Labels raw35260step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35261 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35261step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35261 raw35261Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35261 raw35261Labels = mixedMoment B raw35261step0 raw35261step0Labels := by
      have hz : ∀ j, raw35261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35261step0 = (fun i j => raw35261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35261step0 raw35261; decide +kernel
      have hl : raw35261step0Labels = raw35261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35261 raw35261Labels permutation346 hz
    mixedMoment B raw35261step0 raw35261step0Labels = mixedMoment B raw35261step1 raw35261step1Labels := by
      have ha : raw35261step1 = (fun i j => raw35261step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35261step1 raw35261step0; decide +kernel
      have hl : raw35261step1Labels = raw35261step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35261step0 raw35261step0Labels permutation32 permutation7
    mixedMoment B raw35261step1 raw35261step1Labels = mixedMoment B raw35261step2 raw35261step2Labels := by
      have ha : raw35261step2 = raw35261step1 := by apply Matrix.ext; unfold raw35261step2 raw35261step1; decide +kernel
      have hl : raw35261step1Labels = labelEmbedding10 ∘ raw35261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35261step1 raw35261step1Labels raw35261step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35262 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw35262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35262step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35262step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35262step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35262step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35262 raw35262Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw35262 raw35262Labels = mixedMoment B raw35262step0 raw35262step0Labels := by
      have hz : ∀ j, raw35262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35262step0 = (fun i j => raw35262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35262step0 raw35262; decide +kernel
      have hl : raw35262step0Labels = raw35262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35262 raw35262Labels permutation434 hz
    mixedMoment B raw35262step0 raw35262step0Labels = mixedMoment B raw35262step1 raw35262step1Labels := by
      have hz : ∀ j, raw35262step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35262step1 = (fun i j => raw35262step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35262step1 raw35262step0; decide +kernel
      have hl : raw35262step1Labels = raw35262step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35262step0 raw35262step0Labels permutation80 hz
    mixedMoment B raw35262step1 raw35262step1Labels = mixedMoment B raw35262step2 raw35262step2Labels := by
      have ha : raw35262step2 = (fun i j => raw35262step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35262step2 raw35262step1; decide +kernel
      have hl : raw35262step2Labels = raw35262step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35262step1 raw35262step1Labels permutation9 permutation7
    mixedMoment B raw35262step2 raw35262step2Labels = mixedMoment B raw35262step3 raw35262step3Labels := by
      have ha : raw35262step3 = raw35262step2 := by apply Matrix.ext; unfold raw35262step3 raw35262step2; decide +kernel
      have hl : raw35262step2Labels = labelEmbedding10 ∘ raw35262step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35262step2 raw35262step2Labels raw35262step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw35263 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw35263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35263step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35263 raw35263Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw35263 raw35263Labels = mixedMoment B raw35263step0 raw35263step0Labels := by
      have hz : ∀ j, raw35263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35263step0 = (fun i j => raw35263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35263step0 raw35263; decide +kernel
      have hl : raw35263step0Labels = raw35263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35263 raw35263Labels permutation434 hz
    mixedMoment B raw35263step0 raw35263step0Labels = mixedMoment B raw35263step1 raw35263step1Labels := by
      have hz : ∀ j, raw35263step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35263step1 = (fun i j => raw35263step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35263step1 raw35263step0; decide +kernel
      have hl : raw35263step1Labels = raw35263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35263step0 raw35263step0Labels permutation80 hz
    mixedMoment B raw35263step1 raw35263step1Labels = mixedMoment B raw35263step2 raw35263step2Labels := by
      have ha : raw35263step2 = (fun i j => raw35263step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35263step2 raw35263step1; decide +kernel
      have hl : raw35263step2Labels = raw35263step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35263step1 raw35263step1Labels permutation8 permutation7
    mixedMoment B raw35263step2 raw35263step2Labels = mixedMoment B raw35263step3 raw35263step3Labels := by
      have ha : raw35263step3 = raw35263step2 := by apply Matrix.ext; unfold raw35263step3 raw35263step2; decide +kernel
      have hl : raw35263step2Labels = labelEmbedding10 ∘ raw35263step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35263step2 raw35263step2Labels raw35263step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw35264 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35264step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35264 raw35264Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35264 raw35264Labels = mixedMoment B raw35264step0 raw35264step0Labels := by
      have hz : ∀ j, raw35264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35264step0 = (fun i j => raw35264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35264step0 raw35264; decide +kernel
      have hl : raw35264step0Labels = raw35264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35264 raw35264Labels permutation434 hz
    mixedMoment B raw35264step0 raw35264step0Labels = mixedMoment B raw35264step1 raw35264step1Labels := by
      have ha : raw35264step1 = (fun i j => raw35264step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35264step1 raw35264step0; decide +kernel
      have hl : raw35264step1Labels = raw35264step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35264step0 raw35264step0Labels permutation56 permutation6
    mixedMoment B raw35264step1 raw35264step1Labels = mixedMoment B raw35264step2 raw35264step2Labels := by
      have ha : raw35264step2 = raw35264step1 := by apply Matrix.ext; unfold raw35264step2 raw35264step1; decide +kernel
      have hl : raw35264step1Labels = labelEmbedding9 ∘ raw35264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35264step1 raw35264step1Labels raw35264step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35265 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35265step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35265 raw35265Labels = mixedMoment B node5458 node5458Labels := by
  calc
    mixedMoment B raw35265 raw35265Labels = mixedMoment B raw35265step0 raw35265step0Labels := by
      have ha : raw35265step0 = (fun i j => raw35265 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35265step0 raw35265; decide +kernel
      have hl : raw35265step0Labels = raw35265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35265 raw35265Labels permutation158 permutation6
    mixedMoment B raw35265step0 raw35265step0Labels = mixedMoment B raw35265step1 raw35265step1Labels := by
      have ha : raw35265step1 = raw35265step0 := by apply Matrix.ext; unfold raw35265step1 raw35265step0; decide +kernel
      have hl : raw35265step0Labels = labelEmbedding9 ∘ raw35265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35265step0 raw35265step0Labels raw35265step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5458 node5458Labels := by rfl

def raw35266 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35266step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35266step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35266step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35266 raw35266Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35266 raw35266Labels = mixedMoment B raw35266step0 raw35266step0Labels := by
      have hz : ∀ j, raw35266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35266step0 = (fun i j => raw35266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35266step0 raw35266; decide +kernel
      have hl : raw35266step0Labels = raw35266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35266 raw35266Labels permutation434 hz
    mixedMoment B raw35266step0 raw35266step0Labels = mixedMoment B raw35266step1 raw35266step1Labels := by
      have ha : raw35266step1 = (fun i j => raw35266step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35266step1 raw35266step0; decide +kernel
      have hl : raw35266step1Labels = raw35266step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35266step0 raw35266step0Labels permutation126 permutation7
    mixedMoment B raw35266step1 raw35266step1Labels = mixedMoment B raw35266step2 raw35266step2Labels := by
      have ha : raw35266step2 = -raw35266step1 := by apply Matrix.ext; change ∀ i j, raw35266step2 i j = -(raw35266step1 i j); unfold raw35266step2 raw35266step1; decide +kernel
      have hl : raw35266step2Labels = raw35266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35266step2 raw35266step2Labels = mixedMoment B raw35266step3 raw35266step3Labels := by
      have ha : raw35266step3 = raw35266step2 := by apply Matrix.ext; unfold raw35266step3 raw35266step2; decide +kernel
      have hl : raw35266step2Labels = labelEmbedding10 ∘ raw35266step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35266step2 raw35266step2Labels raw35266step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35267 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35267step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35267step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35267step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35267 raw35267Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35267 raw35267Labels = mixedMoment B raw35267step0 raw35267step0Labels := by
      have hz : ∀ j, raw35267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35267step0 = (fun i j => raw35267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35267step0 raw35267; decide +kernel
      have hl : raw35267step0Labels = raw35267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35267 raw35267Labels permutation434 hz
    mixedMoment B raw35267step0 raw35267step0Labels = mixedMoment B raw35267step1 raw35267step1Labels := by
      have ha : raw35267step1 = (fun i j => raw35267step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35267step1 raw35267step0; decide +kernel
      have hl : raw35267step1Labels = raw35267step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35267step0 raw35267step0Labels permutation150 permutation7
    mixedMoment B raw35267step1 raw35267step1Labels = mixedMoment B raw35267step2 raw35267step2Labels := by
      have ha : raw35267step2 = -raw35267step1 := by apply Matrix.ext; change ∀ i j, raw35267step2 i j = -(raw35267step1 i j); unfold raw35267step2 raw35267step1; decide +kernel
      have hl : raw35267step2Labels = raw35267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35267step2 raw35267step2Labels = mixedMoment B raw35267step3 raw35267step3Labels := by
      have ha : raw35267step3 = raw35267step2 := by apply Matrix.ext; unfold raw35267step3 raw35267step2; decide +kernel
      have hl : raw35267step2Labels = labelEmbedding10 ∘ raw35267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35267step2 raw35267step2Labels raw35267step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35268 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35268step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35268step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35268 raw35268Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35268 raw35268Labels = mixedMoment B raw35268step0 raw35268step0Labels := by
      have hz : ∀ j, raw35268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35268step0 = (fun i j => raw35268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35268step0 raw35268; decide +kernel
      have hl : raw35268step0Labels = raw35268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35268 raw35268Labels permutation346 hz
    mixedMoment B raw35268step0 raw35268step0Labels = mixedMoment B raw35268step1 raw35268step1Labels := by
      have ha : raw35268step1 = (fun i j => raw35268step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35268step1 raw35268step0; decide +kernel
      have hl : raw35268step1Labels = raw35268step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35268step0 raw35268step0Labels permutation56 permutation6
    mixedMoment B raw35268step1 raw35268step1Labels = mixedMoment B raw35268step2 raw35268step2Labels := by
      have ha : raw35268step2 = raw35268step1 := by apply Matrix.ext; unfold raw35268step2 raw35268step1; decide +kernel
      have hl : raw35268step1Labels = labelEmbedding9 ∘ raw35268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35268step1 raw35268step1Labels raw35268step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35269step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35269step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35269 raw35269Labels = mixedMoment B node5458 node5458Labels := by
  calc
    mixedMoment B raw35269 raw35269Labels = mixedMoment B raw35269step0 raw35269step0Labels := by
      have ha : raw35269step0 = (fun i j => raw35269 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35269step0 raw35269; decide +kernel
      have hl : raw35269step0Labels = raw35269Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35269 raw35269Labels permutation152 permutation6
    mixedMoment B raw35269step0 raw35269step0Labels = mixedMoment B raw35269step1 raw35269step1Labels := by
      have ha : raw35269step1 = raw35269step0 := by apply Matrix.ext; unfold raw35269step1 raw35269step0; decide +kernel
      have hl : raw35269step0Labels = labelEmbedding9 ∘ raw35269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35269step0 raw35269step0Labels raw35269step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5458 node5458Labels := by rfl

def raw35270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35270step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35270step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35270step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35270step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35270 raw35270Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35270 raw35270Labels = mixedMoment B raw35270step0 raw35270step0Labels := by
      have hz : ∀ j, raw35270 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35270step0 = (fun i j => raw35270 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35270step0 raw35270; decide +kernel
      have hl : raw35270step0Labels = raw35270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35270 raw35270Labels permutation346 hz
    mixedMoment B raw35270step0 raw35270step0Labels = mixedMoment B raw35270step1 raw35270step1Labels := by
      have ha : raw35270step1 = (fun i j => raw35270step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35270step1 raw35270step0; decide +kernel
      have hl : raw35270step1Labels = raw35270step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35270step0 raw35270step0Labels permutation150 permutation7
    mixedMoment B raw35270step1 raw35270step1Labels = mixedMoment B raw35270step2 raw35270step2Labels := by
      have ha : raw35270step2 = -raw35270step1 := by apply Matrix.ext; change ∀ i j, raw35270step2 i j = -(raw35270step1 i j); unfold raw35270step2 raw35270step1; decide +kernel
      have hl : raw35270step2Labels = raw35270step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35270step2 raw35270step2Labels = mixedMoment B raw35270step3 raw35270step3Labels := by
      have ha : raw35270step3 = raw35270step2 := by apply Matrix.ext; unfold raw35270step3 raw35270step2; decide +kernel
      have hl : raw35270step2Labels = labelEmbedding10 ∘ raw35270step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35270step2 raw35270step2Labels raw35270step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35271 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2]]
def raw35271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35271step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35271step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35271step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35271 raw35271Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw35271 raw35271Labels = mixedMoment B raw35271step0 raw35271step0Labels := by
      have hz : ∀ j, raw35271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35271step0 = (fun i j => raw35271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35271step0 raw35271; decide +kernel
      have hl : raw35271step0Labels = raw35271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35271 raw35271Labels permutation434 hz
    mixedMoment B raw35271step0 raw35271step0Labels = mixedMoment B raw35271step1 raw35271step1Labels := by
      have hz : ∀ j, raw35271step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35271step1 = (fun i j => raw35271step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35271step1 raw35271step0; decide +kernel
      have hl : raw35271step1Labels = raw35271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35271step0 raw35271step0Labels permutation80 hz
    mixedMoment B raw35271step1 raw35271step1Labels = mixedMoment B raw35271step2 raw35271step2Labels := by
      have ha : raw35271step2 = (fun i j => raw35271step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35271step2 raw35271step1; decide +kernel
      have hl : raw35271step2Labels = raw35271step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35271step1 raw35271step1Labels permutation15 permutation6
    mixedMoment B raw35271step2 raw35271step2Labels = mixedMoment B raw35271step3 raw35271step3Labels := by
      have ha : raw35271step3 = raw35271step2 := by apply Matrix.ext; unfold raw35271step3 raw35271step2; decide +kernel
      have hl : raw35271step2Labels = labelEmbedding9 ∘ raw35271step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35271step2 raw35271step2Labels raw35271step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw35272 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35272step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35272step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35272step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35272 raw35272Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35272 raw35272Labels = mixedMoment B raw35272step0 raw35272step0Labels := by
      have hz : ∀ j, raw35272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35272step0 = (fun i j => raw35272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35272step0 raw35272; decide +kernel
      have hl : raw35272step0Labels = raw35272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35272 raw35272Labels permutation434 hz
    mixedMoment B raw35272step0 raw35272step0Labels = mixedMoment B raw35272step1 raw35272step1Labels := by
      have ha : raw35272step1 = (fun i j => raw35272step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35272step1 raw35272step0; decide +kernel
      have hl : raw35272step1Labels = raw35272step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35272step0 raw35272step0Labels permutation126 permutation6
    mixedMoment B raw35272step1 raw35272step1Labels = mixedMoment B raw35272step2 raw35272step2Labels := by
      have ha : raw35272step2 = -raw35272step1 := by apply Matrix.ext; change ∀ i j, raw35272step2 i j = -(raw35272step1 i j); unfold raw35272step2 raw35272step1; decide +kernel
      have hl : raw35272step2Labels = raw35272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35272step2 raw35272step2Labels = mixedMoment B raw35272step3 raw35272step3Labels := by
      have ha : raw35272step3 = raw35272step2 := by apply Matrix.ext; unfold raw35272step3 raw35272step2; decide +kernel
      have hl : raw35272step2Labels = labelEmbedding9 ∘ raw35272step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35272step2 raw35272step2Labels raw35272step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35273 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35273step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35273step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35273step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35273 raw35273Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35273 raw35273Labels = mixedMoment B raw35273step0 raw35273step0Labels := by
      have hz : ∀ j, raw35273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35273step0 = (fun i j => raw35273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35273step0 raw35273; decide +kernel
      have hl : raw35273step0Labels = raw35273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35273 raw35273Labels permutation346 hz
    mixedMoment B raw35273step0 raw35273step0Labels = mixedMoment B raw35273step1 raw35273step1Labels := by
      have ha : raw35273step1 = (fun i j => raw35273step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35273step1 raw35273step0; decide +kernel
      have hl : raw35273step1Labels = raw35273step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35273step0 raw35273step0Labels permutation126 permutation6
    mixedMoment B raw35273step1 raw35273step1Labels = mixedMoment B raw35273step2 raw35273step2Labels := by
      have ha : raw35273step2 = -raw35273step1 := by apply Matrix.ext; change ∀ i j, raw35273step2 i j = -(raw35273step1 i j); unfold raw35273step2 raw35273step1; decide +kernel
      have hl : raw35273step2Labels = raw35273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35273step2 raw35273step2Labels = mixedMoment B raw35273step3 raw35273step3Labels := by
      have ha : raw35273step3 = raw35273step2 := by apply Matrix.ext; unfold raw35273step3 raw35273step2; decide +kernel
      have hl : raw35273step2Labels = labelEmbedding9 ∘ raw35273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35273step2 raw35273step2Labels raw35273step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35274 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw35274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw35274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -2, 2], ![-2, 0, 2]]
def raw35274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35274step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35274step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35274step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35274step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35274step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35274 raw35274Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw35274 raw35274Labels = mixedMoment B raw35274step0 raw35274step0Labels := by
      have hz : ∀ j, raw35274 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35274step0 = (fun i j => raw35274 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35274step0 raw35274; decide +kernel
      have hl : raw35274step0Labels = raw35274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35274 raw35274Labels permutation434 hz
    mixedMoment B raw35274step0 raw35274step0Labels = mixedMoment B raw35274step1 raw35274step1Labels := by
      have hz : ∀ j, raw35274step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35274step1 = (fun i j => raw35274step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35274step1 raw35274step0; decide +kernel
      have hl : raw35274step1Labels = raw35274step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35274step0 raw35274step0Labels permutation80 hz
    mixedMoment B raw35274step1 raw35274step1Labels = mixedMoment B raw35274step2 raw35274step2Labels := by
      have ha : raw35274step2 = (fun i j => raw35274step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35274step2 raw35274step1; decide +kernel
      have hl : raw35274step2Labels = raw35274step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35274step1 raw35274step1Labels permutation24 permutation6
    mixedMoment B raw35274step2 raw35274step2Labels = mixedMoment B raw35274step3 raw35274step3Labels := by
      have ha : raw35274step3 = -raw35274step2 := by apply Matrix.ext; change ∀ i j, raw35274step3 i j = -(raw35274step2 i j); unfold raw35274step3 raw35274step2; decide +kernel
      have hl : raw35274step3Labels = raw35274step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35274step3 raw35274step3Labels = mixedMoment B raw35274step4 raw35274step4Labels := by
      have ha : raw35274step4 = raw35274step3 := by apply Matrix.ext; unfold raw35274step4 raw35274step3; decide +kernel
      have hl : raw35274step3Labels = labelEmbedding9 ∘ raw35274step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35274step3 raw35274step3Labels raw35274step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5390 node5390Labels := by rfl

def raw35275 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, -1, 2], ![0, -2, 2]]
def raw35275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35275step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35275step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35275step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35275 raw35275Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw35275 raw35275Labels = mixedMoment B raw35275step0 raw35275step0Labels := by
      have hz : ∀ j, raw35275 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35275step0 = (fun i j => raw35275 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35275step0 raw35275; decide +kernel
      have hl : raw35275step0Labels = raw35275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35275 raw35275Labels permutation434 hz
    mixedMoment B raw35275step0 raw35275step0Labels = mixedMoment B raw35275step1 raw35275step1Labels := by
      have hz : ∀ j, raw35275step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35275step1 = (fun i j => raw35275step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35275step1 raw35275step0; decide +kernel
      have hl : raw35275step1Labels = raw35275step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35275step0 raw35275step0Labels permutation80 hz
    mixedMoment B raw35275step1 raw35275step1Labels = mixedMoment B raw35275step2 raw35275step2Labels := by
      have ha : raw35275step2 = (fun i j => raw35275step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35275step2 raw35275step1; decide +kernel
      have hl : raw35275step2Labels = raw35275step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35275step1 raw35275step1Labels permutation14 permutation6
    mixedMoment B raw35275step2 raw35275step2Labels = mixedMoment B raw35275step3 raw35275step3Labels := by
      have ha : raw35275step3 = raw35275step2 := by apply Matrix.ext; unfold raw35275step3 raw35275step2; decide +kernel
      have hl : raw35275step2Labels = labelEmbedding9 ∘ raw35275step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35275step2 raw35275step2Labels raw35275step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw35276 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35276step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35276step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35276step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35276step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35276 raw35276Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35276 raw35276Labels = mixedMoment B raw35276step0 raw35276step0Labels := by
      have hz : ∀ j, raw35276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35276step0 = (fun i j => raw35276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35276step0 raw35276; decide +kernel
      have hl : raw35276step0Labels = raw35276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35276 raw35276Labels permutation434 hz
    mixedMoment B raw35276step0 raw35276step0Labels = mixedMoment B raw35276step1 raw35276step1Labels := by
      have ha : raw35276step1 = (fun i j => raw35276step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35276step1 raw35276step0; decide +kernel
      have hl : raw35276step1Labels = raw35276step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35276step0 raw35276step0Labels permutation150 permutation6
    mixedMoment B raw35276step1 raw35276step1Labels = mixedMoment B raw35276step2 raw35276step2Labels := by
      have ha : raw35276step2 = -raw35276step1 := by apply Matrix.ext; change ∀ i j, raw35276step2 i j = -(raw35276step1 i j); unfold raw35276step2 raw35276step1; decide +kernel
      have hl : raw35276step2Labels = raw35276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35276step2 raw35276step2Labels = mixedMoment B raw35276step3 raw35276step3Labels := by
      have ha : raw35276step3 = raw35276step2 := by apply Matrix.ext; unfold raw35276step3 raw35276step2; decide +kernel
      have hl : raw35276step2Labels = labelEmbedding9 ∘ raw35276step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35276step2 raw35276step2Labels raw35276step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35277 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35277step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35277step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35277step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35277step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35277 raw35277Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35277 raw35277Labels = mixedMoment B raw35277step0 raw35277step0Labels := by
      have hz : ∀ j, raw35277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35277step0 = (fun i j => raw35277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35277step0 raw35277; decide +kernel
      have hl : raw35277step0Labels = raw35277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35277 raw35277Labels permutation346 hz
    mixedMoment B raw35277step0 raw35277step0Labels = mixedMoment B raw35277step1 raw35277step1Labels := by
      have ha : raw35277step1 = (fun i j => raw35277step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35277step1 raw35277step0; decide +kernel
      have hl : raw35277step1Labels = raw35277step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35277step0 raw35277step0Labels permutation150 permutation6
    mixedMoment B raw35277step1 raw35277step1Labels = mixedMoment B raw35277step2 raw35277step2Labels := by
      have ha : raw35277step2 = -raw35277step1 := by apply Matrix.ext; change ∀ i j, raw35277step2 i j = -(raw35277step1 i j); unfold raw35277step2 raw35277step1; decide +kernel
      have hl : raw35277step2Labels = raw35277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35277step2 raw35277step2Labels = mixedMoment B raw35277step3 raw35277step3Labels := by
      have ha : raw35277step3 = raw35277step2 := by apply Matrix.ext; unfold raw35277step3 raw35277step2; decide +kernel
      have hl : raw35277step2Labels = labelEmbedding9 ∘ raw35277step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35277step2 raw35277step2Labels raw35277step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35278step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35278 raw35278Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw35278 raw35278Labels = mixedMoment B raw35278step0 raw35278step0Labels := by
      have hz : ∀ j, raw35278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35278step0 = (fun i j => raw35278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35278step0 raw35278; decide +kernel
      have hl : raw35278step0Labels = raw35278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35278 raw35278Labels permutation346 hz
    mixedMoment B raw35278step0 raw35278step0Labels = mixedMoment B raw35278step1 raw35278step1Labels := by
      have ha : raw35278step1 = (fun i j => raw35278step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35278step1 raw35278step0; decide +kernel
      have hl : raw35278step1Labels = raw35278step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35278step0 raw35278step0Labels permutation56 permutation3
    mixedMoment B raw35278step1 raw35278step1Labels = mixedMoment B raw35278step2 raw35278step2Labels := by
      have ha : raw35278step2 = raw35278step1 := by apply Matrix.ext; unfold raw35278step2 raw35278step1; decide +kernel
      have hl : raw35278step1Labels = labelEmbedding6 ∘ raw35278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35278step1 raw35278step1Labels raw35278step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw35279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35279 raw35279Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw35279 raw35279Labels = mixedMoment B raw35279step0 raw35279step0Labels := by
      have ha : raw35279step0 = (fun i j => raw35279 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35279step0 raw35279; decide +kernel
      have hl : raw35279step0Labels = raw35279Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35279 raw35279Labels permutation588 permutation2
    mixedMoment B raw35279step0 raw35279step0Labels = mixedMoment B raw35279step1 raw35279step1Labels := by
      have ha : raw35279step1 = -raw35279step0 := by apply Matrix.ext; change ∀ i j, raw35279step1 i j = -(raw35279step0 i j); unfold raw35279step1 raw35279step0; decide +kernel
      have hl : raw35279step1Labels = raw35279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw35280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35280 raw35280Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw35280 raw35280Labels = mixedMoment B raw35280step0 raw35280step0Labels := by
      have hz : ∀ j, raw35280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35280step0 = (fun i j => raw35280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35280step0 raw35280; decide +kernel
      have hl : raw35280step0Labels = raw35280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35280 raw35280Labels permutation346 hz
    mixedMoment B raw35280step0 raw35280step0Labels = mixedMoment B raw35280step1 raw35280step1Labels := by
      have ha : raw35280step1 = (fun i j => raw35280step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35280step1 raw35280step0; decide +kernel
      have hl : raw35280step1Labels = raw35280step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35280step0 raw35280step0Labels permutation123 permutation2
    mixedMoment B raw35280step1 raw35280step1Labels = mixedMoment B raw35280step2 raw35280step2Labels := by
      have ha : raw35280step2 = -raw35280step1 := by apply Matrix.ext; change ∀ i j, raw35280step2 i j = -(raw35280step1 i j); unfold raw35280step2 raw35280step1; decide +kernel
      have hl : raw35280step2Labels = raw35280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw35281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35281 raw35281Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw35281 raw35281Labels = mixedMoment B raw35281step0 raw35281step0Labels := by
      have hz : ∀ j, raw35281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35281step0 = (fun i j => raw35281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35281step0 raw35281; decide +kernel
      have hl : raw35281step0Labels = raw35281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35281 raw35281Labels permutation346 hz
    mixedMoment B raw35281step0 raw35281step0Labels = mixedMoment B raw35281step1 raw35281step1Labels := by
      have ha : raw35281step1 = (fun i j => raw35281step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35281step1 raw35281step0; decide +kernel
      have hl : raw35281step1Labels = raw35281step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35281step0 raw35281step0Labels permutation126 permutation2
    mixedMoment B raw35281step1 raw35281step1Labels = mixedMoment B raw35281step2 raw35281step2Labels := by
      have ha : raw35281step2 = -raw35281step1 := by apply Matrix.ext; change ∀ i j, raw35281step2 i j = -(raw35281step1 i j); unfold raw35281step2 raw35281step1; decide +kernel
      have hl : raw35281step2Labels = raw35281step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw35282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35282step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35282 raw35282Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw35282 raw35282Labels = mixedMoment B raw35282step0 raw35282step0Labels := by
      have ha : raw35282step0 = (fun i j => raw35282 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35282step0 raw35282; decide +kernel
      have hl : raw35282step0Labels = raw35282Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35282 raw35282Labels permutation271 permutation3
    mixedMoment B raw35282step0 raw35282step0Labels = mixedMoment B raw35282step1 raw35282step1Labels := by
      have ha : raw35282step1 = raw35282step0 := by apply Matrix.ext; unfold raw35282step1 raw35282step0; decide +kernel
      have hl : raw35282step0Labels = labelEmbedding6 ∘ raw35282step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35282step0 raw35282step0Labels raw35282step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4933 node4933Labels := by rfl

def raw35283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35283 raw35283Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw35283 raw35283Labels = mixedMoment B raw35283step0 raw35283step0Labels := by
      have ha : raw35283step0 = (fun i j => raw35283 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35283step0 raw35283; decide +kernel
      have hl : raw35283step0Labels = raw35283Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35283 raw35283Labels permutation583 permutation2
    mixedMoment B raw35283step0 raw35283step0Labels = mixedMoment B raw35283step1 raw35283step1Labels := by
      have ha : raw35283step1 = -raw35283step0 := by apply Matrix.ext; change ∀ i j, raw35283step1 i j = -(raw35283step0 i j); unfold raw35283step1 raw35283step0; decide +kernel
      have hl : raw35283step1Labels = raw35283step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5337 node5337Labels := by rfl

def raw35284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35284 raw35284Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw35284 raw35284Labels = mixedMoment B raw35284step0 raw35284step0Labels := by
      have ha : raw35284step0 = (fun i j => raw35284 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35284step0 raw35284; decide +kernel
      have hl : raw35284step0Labels = raw35284Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35284 raw35284Labels permutation583 permutation2
    mixedMoment B raw35284step0 raw35284step0Labels = mixedMoment B raw35284step1 raw35284step1Labels := by
      have ha : raw35284step1 = -raw35284step0 := by apply Matrix.ext; change ∀ i j, raw35284step1 i j = -(raw35284step0 i j); unfold raw35284step1 raw35284step0; decide +kernel
      have hl : raw35284step1Labels = raw35284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw35285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35285step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35285 raw35285Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw35285 raw35285Labels = mixedMoment B raw35285step0 raw35285step0Labels := by
      have hz : ∀ j, raw35285 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35285step0 = (fun i j => raw35285 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35285step0 raw35285; decide +kernel
      have hl : raw35285step0Labels = raw35285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35285 raw35285Labels permutation346 hz
    mixedMoment B raw35285step0 raw35285step0Labels = mixedMoment B raw35285step1 raw35285step1Labels := by
      have ha : raw35285step1 = (fun i j => raw35285step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35285step1 raw35285step0; decide +kernel
      have hl : raw35285step1Labels = raw35285step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35285step0 raw35285step0Labels permutation56 permutation3
    mixedMoment B raw35285step1 raw35285step1Labels = mixedMoment B raw35285step2 raw35285step2Labels := by
      have ha : raw35285step2 = raw35285step1 := by apply Matrix.ext; unfold raw35285step2 raw35285step1; decide +kernel
      have hl : raw35285step1Labels = labelEmbedding6 ∘ raw35285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35285step1 raw35285step1Labels raw35285step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4951 node4951Labels := by rfl

def raw35286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35286 raw35286Labels = mixedMoment B node5340 node5340Labels := by
  calc
    mixedMoment B raw35286 raw35286Labels = mixedMoment B raw35286step0 raw35286step0Labels := by
      have ha : raw35286step0 = (fun i j => raw35286 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35286step0 raw35286; decide +kernel
      have hl : raw35286step0Labels = raw35286Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35286 raw35286Labels permutation588 permutation2
    mixedMoment B raw35286step0 raw35286step0Labels = mixedMoment B raw35286step1 raw35286step1Labels := by
      have ha : raw35286step1 = -raw35286step0 := by apply Matrix.ext; change ∀ i j, raw35286step1 i j = -(raw35286step0 i j); unfold raw35286step1 raw35286step0; decide +kernel
      have hl : raw35286step1Labels = raw35286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5340 node5340Labels := by rfl

def raw35287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35287 raw35287Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw35287 raw35287Labels = mixedMoment B raw35287step0 raw35287step0Labels := by
      have hz : ∀ j, raw35287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35287step0 = (fun i j => raw35287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35287step0 raw35287; decide +kernel
      have hl : raw35287step0Labels = raw35287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35287 raw35287Labels permutation346 hz
    mixedMoment B raw35287step0 raw35287step0Labels = mixedMoment B raw35287step1 raw35287step1Labels := by
      have ha : raw35287step1 = (fun i j => raw35287step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35287step1 raw35287step0; decide +kernel
      have hl : raw35287step1Labels = raw35287step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35287step0 raw35287step0Labels permutation126 permutation2
    mixedMoment B raw35287step1 raw35287step1Labels = mixedMoment B raw35287step2 raw35287step2Labels := by
      have ha : raw35287step2 = -raw35287step1 := by apply Matrix.ext; change ∀ i j, raw35287step2 i j = -(raw35287step1 i j); unfold raw35287step2 raw35287step1; decide +kernel
      have hl : raw35287step2Labels = raw35287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw35288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw35288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw35288step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35288 raw35288Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw35288 raw35288Labels = mixedMoment B raw35288step0 raw35288step0Labels := by
      have hz : ∀ j, raw35288 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35288step0 = (fun i j => raw35288 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35288step0 raw35288; decide +kernel
      have hl : raw35288step0Labels = raw35288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35288 raw35288Labels permutation346 hz
    mixedMoment B raw35288step0 raw35288step0Labels = mixedMoment B raw35288step1 raw35288step1Labels := by
      have ha : raw35288step1 = (fun i j => raw35288step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35288step1 raw35288step0; decide +kernel
      have hl : raw35288step1Labels = raw35288step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35288step0 raw35288step0Labels permutation126 permutation2
    mixedMoment B raw35288step1 raw35288step1Labels = mixedMoment B raw35288step2 raw35288step2Labels := by
      have ha : raw35288step2 = -raw35288step1 := by apply Matrix.ext; change ∀ i j, raw35288step2 i j = -(raw35288step1 i j); unfold raw35288step2 raw35288step1; decide +kernel
      have hl : raw35288step2Labels = raw35288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4935 node4935Labels := by rfl

def raw35289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35289 raw35289Labels = mixedMoment B node4932 node4932Labels := by
  calc
    mixedMoment B raw35289 raw35289Labels = mixedMoment B raw35289step0 raw35289step0Labels := by
      have ha : raw35289step0 = (fun i j => raw35289 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35289step0 raw35289; decide +kernel
      have hl : raw35289step0Labels = raw35289Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35289 raw35289Labels permutation588 permutation2
    mixedMoment B raw35289step0 raw35289step0Labels = mixedMoment B raw35289step1 raw35289step1Labels := by
      have ha : raw35289step1 = -raw35289step0 := by apply Matrix.ext; change ∀ i j, raw35289step1 i j = -(raw35289step0 i j); unfold raw35289step1 raw35289step0; decide +kernel
      have hl : raw35289step1Labels = raw35289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4932 node4932Labels := by rfl

def raw35290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35290step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35290 raw35290Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw35290 raw35290Labels = mixedMoment B raw35290step0 raw35290step0Labels := by
      have hz : ∀ j, raw35290 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35290step0 = (fun i j => raw35290 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35290step0 raw35290; decide +kernel
      have hl : raw35290step0Labels = raw35290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35290 raw35290Labels permutation346 hz
    mixedMoment B raw35290step0 raw35290step0Labels = mixedMoment B raw35290step1 raw35290step1Labels := by
      have ha : raw35290step1 = (fun i j => raw35290step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35290step1 raw35290step0; decide +kernel
      have hl : raw35290step1Labels = raw35290step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35290step0 raw35290step0Labels permutation126 permutation2
    mixedMoment B raw35290step1 raw35290step1Labels = mixedMoment B raw35290step2 raw35290step2Labels := by
      have ha : raw35290step2 = -raw35290step1 := by apply Matrix.ext; change ∀ i j, raw35290step2 i j = -(raw35290step1 i j); unfold raw35290step2 raw35290step1; decide +kernel
      have hl : raw35290step2Labels = raw35290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw35291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35291 raw35291Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw35291 raw35291Labels = mixedMoment B raw35291step0 raw35291step0Labels := by
      have hz : ∀ j, raw35291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35291step0 = (fun i j => raw35291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35291step0 raw35291; decide +kernel
      have hl : raw35291step0Labels = raw35291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35291 raw35291Labels permutation346 hz
    mixedMoment B raw35291step0 raw35291step0Labels = mixedMoment B raw35291step1 raw35291step1Labels := by
      have ha : raw35291step1 = (fun i j => raw35291step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35291step1 raw35291step0; decide +kernel
      have hl : raw35291step1Labels = raw35291step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35291step0 raw35291step0Labels permutation126 permutation2
    mixedMoment B raw35291step1 raw35291step1Labels = mixedMoment B raw35291step2 raw35291step2Labels := by
      have ha : raw35291step2 = -raw35291step1 := by apply Matrix.ext; change ∀ i j, raw35291step2 i j = -(raw35291step1 i j); unfold raw35291step2 raw35291step1; decide +kernel
      have hl : raw35291step2Labels = raw35291step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw35292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35292step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35292step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35292 raw35292Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw35292 raw35292Labels = mixedMoment B raw35292step0 raw35292step0Labels := by
      have hz : ∀ j, raw35292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35292step0 = (fun i j => raw35292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35292step0 raw35292; decide +kernel
      have hl : raw35292step0Labels = raw35292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35292 raw35292Labels permutation346 hz
    mixedMoment B raw35292step0 raw35292step0Labels = mixedMoment B raw35292step1 raw35292step1Labels := by
      have ha : raw35292step1 = (fun i j => raw35292step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35292step1 raw35292step0; decide +kernel
      have hl : raw35292step1Labels = raw35292step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35292step0 raw35292step0Labels permutation56 permutation3
    mixedMoment B raw35292step1 raw35292step1Labels = mixedMoment B raw35292step2 raw35292step2Labels := by
      have ha : raw35292step2 = raw35292step1 := by apply Matrix.ext; unfold raw35292step2 raw35292step1; decide +kernel
      have hl : raw35292step1Labels = labelEmbedding6 ∘ raw35292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35292step1 raw35292step1Labels raw35292step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4934 node4934Labels := by rfl

def raw35293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35293step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35293step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35293step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35293 raw35293Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw35293 raw35293Labels = mixedMoment B raw35293step0 raw35293step0Labels := by
      have ha : raw35293step0 = (fun i j => raw35293 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35293step0 raw35293; decide +kernel
      have hl : raw35293step0Labels = raw35293Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35293 raw35293Labels permutation687 permutation3
    mixedMoment B raw35293step0 raw35293step0Labels = mixedMoment B raw35293step1 raw35293step1Labels := by
      have ha : raw35293step1 = -raw35293step0 := by apply Matrix.ext; change ∀ i j, raw35293step1 i j = -(raw35293step0 i j); unfold raw35293step1 raw35293step0; decide +kernel
      have hl : raw35293step1Labels = raw35293step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35293step1 raw35293step1Labels = mixedMoment B raw35293step2 raw35293step2Labels := by
      have ha : raw35293step2 = raw35293step1 := by apply Matrix.ext; unfold raw35293step2 raw35293step1; decide +kernel
      have hl : raw35293step1Labels = labelEmbedding6 ∘ raw35293step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35293step1 raw35293step1Labels raw35293step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4958 node4958Labels := by rfl

def raw35294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35294step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35294step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35294 raw35294Labels = mixedMoment B node4974 node4974Labels := by
  calc
    mixedMoment B raw35294 raw35294Labels = mixedMoment B raw35294step0 raw35294step0Labels := by
      have hz : ∀ j, raw35294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35294step0 = (fun i j => raw35294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35294step0 raw35294; decide +kernel
      have hl : raw35294step0Labels = raw35294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35294 raw35294Labels permutation346 hz
    mixedMoment B raw35294step0 raw35294step0Labels = mixedMoment B raw35294step1 raw35294step1Labels := by
      have ha : raw35294step1 = (fun i j => raw35294step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35294step1 raw35294step0; decide +kernel
      have hl : raw35294step1Labels = raw35294step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35294step0 raw35294step0Labels permutation150 permutation3
    mixedMoment B raw35294step1 raw35294step1Labels = mixedMoment B raw35294step2 raw35294step2Labels := by
      have ha : raw35294step2 = -raw35294step1 := by apply Matrix.ext; change ∀ i j, raw35294step2 i j = -(raw35294step1 i j); unfold raw35294step2 raw35294step1; decide +kernel
      have hl : raw35294step2Labels = raw35294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35294step2 raw35294step2Labels = mixedMoment B raw35294step3 raw35294step3Labels := by
      have ha : raw35294step3 = raw35294step2 := by apply Matrix.ext; unfold raw35294step3 raw35294step2; decide +kernel
      have hl : raw35294step2Labels = labelEmbedding6 ∘ raw35294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35294step2 raw35294step2Labels raw35294step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4974 node4974Labels := by rfl

def raw35295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35295 raw35295Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw35295 raw35295Labels = mixedMoment B raw35295step0 raw35295step0Labels := by
      have hz : ∀ j, raw35295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35295step0 = (fun i j => raw35295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35295step0 raw35295; decide +kernel
      have hl : raw35295step0Labels = raw35295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35295 raw35295Labels permutation346 hz
    mixedMoment B raw35295step0 raw35295step0Labels = mixedMoment B raw35295step1 raw35295step1Labels := by
      have ha : raw35295step1 = (fun i j => raw35295step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35295step1 raw35295step0; decide +kernel
      have hl : raw35295step1Labels = raw35295step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35295step0 raw35295step0Labels permutation56 permutation3
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw35296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35296 raw35296Labels = mixedMoment B node3936 node3936Labels := by
  calc
    mixedMoment B raw35296 raw35296Labels = mixedMoment B raw35296step0 raw35296step0Labels := by
      have ha : raw35296step0 = (fun i j => raw35296 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35296step0 raw35296; decide +kernel
      have hl : raw35296step0Labels = raw35296Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35296 raw35296Labels permutation684 permutation3
    mixedMoment B raw35296step0 raw35296step0Labels = mixedMoment B raw35296step1 raw35296step1Labels := by
      have ha : raw35296step1 = -raw35296step0 := by apply Matrix.ext; change ∀ i j, raw35296step1 i j = -(raw35296step0 i j); unfold raw35296step1 raw35296step0; decide +kernel
      have hl : raw35296step1Labels = raw35296step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3936 node3936Labels := by rfl

def raw35297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw35297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35297 raw35297Labels = mixedMoment B node3940 node3940Labels := by
  calc
    mixedMoment B raw35297 raw35297Labels = mixedMoment B raw35297step0 raw35297step0Labels := by
      have hz : ∀ j, raw35297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35297step0 = (fun i j => raw35297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35297step0 raw35297; decide +kernel
      have hl : raw35297step0Labels = raw35297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35297 raw35297Labels permutation346 hz
    mixedMoment B raw35297step0 raw35297step0Labels = mixedMoment B raw35297step1 raw35297step1Labels := by
      have ha : raw35297step1 = (fun i j => raw35297step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35297step1 raw35297step0; decide +kernel
      have hl : raw35297step1Labels = raw35297step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35297step0 raw35297step0Labels permutation147 permutation3
    mixedMoment B raw35297step1 raw35297step1Labels = mixedMoment B raw35297step2 raw35297step2Labels := by
      have ha : raw35297step2 = -raw35297step1 := by apply Matrix.ext; change ∀ i j, raw35297step2 i j = -(raw35297step1 i j); unfold raw35297step2 raw35297step1; decide +kernel
      have hl : raw35297step2Labels = raw35297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3940 node3940Labels := by rfl

def raw35298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35298 raw35298Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw35298 raw35298Labels = mixedMoment B raw35298step0 raw35298step0Labels := by
      have hz : ∀ j, raw35298 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35298step0 = (fun i j => raw35298 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35298step0 raw35298; decide +kernel
      have hl : raw35298step0Labels = raw35298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35298 raw35298Labels permutation346 hz
    mixedMoment B raw35298step0 raw35298step0Labels = mixedMoment B raw35298step1 raw35298step1Labels := by
      have ha : raw35298step1 = (fun i j => raw35298step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35298step1 raw35298step0; decide +kernel
      have hl : raw35298step1Labels = raw35298step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35298step0 raw35298step0Labels permutation56 permutation3
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw35299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw35299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35299 raw35299Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw35299 raw35299Labels = mixedMoment B raw35299step0 raw35299step0Labels := by
      have hz : ∀ j, raw35299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35299step0 = (fun i j => raw35299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35299step0 raw35299; decide +kernel
      have hl : raw35299step0Labels = raw35299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35299 raw35299Labels permutation346 hz
    mixedMoment B raw35299step0 raw35299step0Labels = mixedMoment B raw35299step1 raw35299step1Labels := by
      have ha : raw35299step1 = (fun i j => raw35299step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35299step1 raw35299step0; decide +kernel
      have hl : raw35299step1Labels = raw35299step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35299step0 raw35299step0Labels permutation57 permutation3
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw35300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35300 raw35300Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw35300 raw35300Labels = mixedMoment B raw35300step0 raw35300step0Labels := by
      have hz : ∀ j, raw35300 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35300step0 = (fun i j => raw35300 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35300step0 raw35300; decide +kernel
      have hl : raw35300step0Labels = raw35300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35300 raw35300Labels permutation346 hz
    mixedMoment B raw35300step0 raw35300step0Labels = mixedMoment B raw35300step1 raw35300step1Labels := by
      have ha : raw35300step1 = (fun i j => raw35300step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35300step1 raw35300step0; decide +kernel
      have hl : raw35300step1Labels = raw35300step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35300step0 raw35300step0Labels permutation32 permutation3
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw35301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35301step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35301 raw35301Labels = mixedMoment B node2324 node2324Labels := by
  calc
    mixedMoment B raw35301 raw35301Labels = mixedMoment B raw35301step0 raw35301step0Labels := by
      have ha : raw35301step0 = (fun i j => raw35301 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35301step0 raw35301; decide +kernel
      have hl : raw35301step0Labels = raw35301Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35301 raw35301Labels permutation271 permutation3
    _ = mixedMoment B node2324 node2324Labels := by rfl

def raw35302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35302 raw35302Labels = mixedMoment B node3919 node3919Labels := by
  calc
    mixedMoment B raw35302 raw35302Labels = mixedMoment B raw35302step0 raw35302step0Labels := by
      have ha : raw35302step0 = (fun i j => raw35302 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35302step0 raw35302; decide +kernel
      have hl : raw35302step0Labels = raw35302Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35302 raw35302Labels permutation158 permutation3
    _ = mixedMoment B node3919 node3919Labels := by rfl

def raw35303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw35303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35303 raw35303Labels = mixedMoment B node3923 node3923Labels := by
  calc
    mixedMoment B raw35303 raw35303Labels = mixedMoment B raw35303step0 raw35303step0Labels := by
      have ha : raw35303step0 = (fun i j => raw35303 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35303step0 raw35303; decide +kernel
      have hl : raw35303step0Labels = raw35303Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35303 raw35303Labels permutation160 permutation3
    _ = mixedMoment B node3923 node3923Labels := by rfl

def raw35304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35304 raw35304Labels = mixedMoment B node3925 node3925Labels := by
  calc
    mixedMoment B raw35304 raw35304Labels = mixedMoment B raw35304step0 raw35304step0Labels := by
      have ha : raw35304step0 = (fun i j => raw35304 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35304step0 raw35304; decide +kernel
      have hl : raw35304step0Labels = raw35304Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35304 raw35304Labels permutation162 permutation3
    _ = mixedMoment B node3925 node3925Labels := by rfl

def raw35305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35305step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35305 raw35305Labels = mixedMoment B node2343 node2343Labels := by
  calc
    mixedMoment B raw35305 raw35305Labels = mixedMoment B raw35305step0 raw35305step0Labels := by
      have hz : ∀ j, raw35305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35305step0 = (fun i j => raw35305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35305step0 raw35305; decide +kernel
      have hl : raw35305step0Labels = raw35305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35305 raw35305Labels permutation346 hz
    mixedMoment B raw35305step0 raw35305step0Labels = mixedMoment B raw35305step1 raw35305step1Labels := by
      have ha : raw35305step1 = (fun i j => raw35305step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35305step1 raw35305step0; decide +kernel
      have hl : raw35305step1Labels = raw35305step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35305step0 raw35305step0Labels permutation56 permutation3
    _ = mixedMoment B node2343 node2343Labels := by rfl

def raw35306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35306 raw35306Labels = mixedMoment B node3918 node3918Labels := by
  calc
    mixedMoment B raw35306 raw35306Labels = mixedMoment B raw35306step0 raw35306step0Labels := by
      have ha : raw35306step0 = (fun i j => raw35306 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35306step0 raw35306; decide +kernel
      have hl : raw35306step0Labels = raw35306Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35306 raw35306Labels permutation152 permutation3
    _ = mixedMoment B node3918 node3918Labels := by rfl

def raw35307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35307 raw35307Labels = mixedMoment B node3929 node3929Labels := by
  calc
    mixedMoment B raw35307 raw35307Labels = mixedMoment B raw35307step0 raw35307step0Labels := by
      have hz : ∀ j, raw35307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35307step0 = (fun i j => raw35307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35307step0 raw35307; decide +kernel
      have hl : raw35307step0Labels = raw35307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35307 raw35307Labels permutation346 hz
    mixedMoment B raw35307step0 raw35307step0Labels = mixedMoment B raw35307step1 raw35307step1Labels := by
      have ha : raw35307step1 = (fun i j => raw35307step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35307step1 raw35307step0; decide +kernel
      have hl : raw35307step1Labels = raw35307step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35307step0 raw35307step0Labels permutation34 permutation3
    _ = mixedMoment B node3929 node3929Labels := by rfl

def raw35308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35308step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35308 raw35308Labels = mixedMoment B node3932 node3932Labels := by
  calc
    mixedMoment B raw35308 raw35308Labels = mixedMoment B raw35308step0 raw35308step0Labels := by
      have hz : ∀ j, raw35308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35308step0 = (fun i j => raw35308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35308step0 raw35308; decide +kernel
      have hl : raw35308step0Labels = raw35308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35308 raw35308Labels permutation346 hz
    mixedMoment B raw35308step0 raw35308step0Labels = mixedMoment B raw35308step1 raw35308step1Labels := by
      have ha : raw35308step1 = (fun i j => raw35308step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35308step1 raw35308step0; decide +kernel
      have hl : raw35308step1Labels = raw35308step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35308step0 raw35308step0Labels permutation36 permutation3
    _ = mixedMoment B node3932 node3932Labels := by rfl

def raw35309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw35309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35309 raw35309Labels = mixedMoment B node2326 node2326Labels := by
  calc
    mixedMoment B raw35309 raw35309Labels = mixedMoment B raw35309step0 raw35309step0Labels := by
      have hz : ∀ j, raw35309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35309step0 = (fun i j => raw35309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35309step0 raw35309; decide +kernel
      have hl : raw35309step0Labels = raw35309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35309 raw35309Labels permutation346 hz
    mixedMoment B raw35309step0 raw35309step0Labels = mixedMoment B raw35309step1 raw35309step1Labels := by
      have ha : raw35309step1 = (fun i j => raw35309step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35309step1 raw35309step0; decide +kernel
      have hl : raw35309step1Labels = raw35309step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35309step0 raw35309step0Labels permutation57 permutation3
    _ = mixedMoment B node2326 node2326Labels := by rfl

def raw35310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35310 raw35310Labels = mixedMoment B node2825 node2825Labels := by
  calc
    mixedMoment B raw35310 raw35310Labels = mixedMoment B raw35310step0 raw35310step0Labels := by
      have ha : raw35310step0 = (fun i j => raw35310 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35310step0 raw35310; decide +kernel
      have hl : raw35310step0Labels = raw35310Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35310 raw35310Labels permutation588 permutation3
    mixedMoment B raw35310step0 raw35310step0Labels = mixedMoment B raw35310step1 raw35310step1Labels := by
      have ha : raw35310step1 = -raw35310step0 := by apply Matrix.ext; change ∀ i j, raw35310step1 i j = -(raw35310step0 i j); unfold raw35310step1 raw35310step0; decide +kernel
      have hl : raw35310step1Labels = raw35310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2825 node2825Labels := by rfl

def raw35311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35311 raw35311Labels = mixedMoment B node2830 node2830Labels := by
  calc
    mixedMoment B raw35311 raw35311Labels = mixedMoment B raw35311step0 raw35311step0Labels := by
      have hz : ∀ j, raw35311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35311step0 = (fun i j => raw35311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35311step0 raw35311; decide +kernel
      have hl : raw35311step0Labels = raw35311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35311 raw35311Labels permutation346 hz
    mixedMoment B raw35311step0 raw35311step0Labels = mixedMoment B raw35311step1 raw35311step1Labels := by
      have ha : raw35311step1 = (fun i j => raw35311step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35311step1 raw35311step0; decide +kernel
      have hl : raw35311step1Labels = raw35311step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35311step0 raw35311step0Labels permutation126 permutation3
    mixedMoment B raw35311step1 raw35311step1Labels = mixedMoment B raw35311step2 raw35311step2Labels := by
      have ha : raw35311step2 = -raw35311step1 := by apply Matrix.ext; change ∀ i j, raw35311step2 i j = -(raw35311step1 i j); unfold raw35311step2 raw35311step1; decide +kernel
      have hl : raw35311step2Labels = raw35311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2830 node2830Labels := by rfl

def raw35312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw35312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35312 raw35312Labels = mixedMoment B node2991 node2991Labels := by
  calc
    mixedMoment B raw35312 raw35312Labels = mixedMoment B raw35312step0 raw35312step0Labels := by
      have hz : ∀ j, raw35312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35312step0 = (fun i j => raw35312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35312step0 raw35312; decide +kernel
      have hl : raw35312step0Labels = raw35312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35312 raw35312Labels permutation346 hz
    mixedMoment B raw35312step0 raw35312step0Labels = mixedMoment B raw35312step1 raw35312step1Labels := by
      have ha : raw35312step1 = (fun i j => raw35312step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35312step1 raw35312step0; decide +kernel
      have hl : raw35312step1Labels = raw35312step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35312step0 raw35312step0Labels permutation126 permutation3
    mixedMoment B raw35312step1 raw35312step1Labels = mixedMoment B raw35312step2 raw35312step2Labels := by
      have ha : raw35312step2 = -raw35312step1 := by apply Matrix.ext; change ∀ i j, raw35312step2 i j = -(raw35312step1 i j); unfold raw35312step2 raw35312step1; decide +kernel
      have hl : raw35312step2Labels = raw35312step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2991 node2991Labels := by rfl

def raw35313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35313 raw35313Labels = mixedMoment B node2325 node2325Labels := by
  calc
    mixedMoment B raw35313 raw35313Labels = mixedMoment B raw35313step0 raw35313step0Labels := by
      have hz : ∀ j, raw35313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35313step0 = (fun i j => raw35313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35313step0 raw35313; decide +kernel
      have hl : raw35313step0Labels = raw35313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35313 raw35313Labels permutation346 hz
    mixedMoment B raw35313step0 raw35313step0Labels = mixedMoment B raw35313step1 raw35313step1Labels := by
      have ha : raw35313step1 = (fun i j => raw35313step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35313step1 raw35313step0; decide +kernel
      have hl : raw35313step1Labels = raw35313step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35313step0 raw35313step0Labels permutation56 permutation3
    _ = mixedMoment B node2325 node2325Labels := by rfl

def raw35314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35314 raw35314Labels = mixedMoment B node2351 node2351Labels := by
  calc
    mixedMoment B raw35314 raw35314Labels = mixedMoment B raw35314step0 raw35314step0Labels := by
      have ha : raw35314step0 = (fun i j => raw35314 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35314step0 raw35314; decide +kernel
      have hl : raw35314step0Labels = raw35314Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35314 raw35314Labels permutation687 permutation3
    mixedMoment B raw35314step0 raw35314step0Labels = mixedMoment B raw35314step1 raw35314step1Labels := by
      have ha : raw35314step1 = -raw35314step0 := by apply Matrix.ext; change ∀ i j, raw35314step1 i j = -(raw35314step0 i j); unfold raw35314step1 raw35314step0; decide +kernel
      have hl : raw35314step1Labels = raw35314step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2351 node2351Labels := by rfl

def raw35315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35315 raw35315Labels = mixedMoment B node2360 node2360Labels := by
  calc
    mixedMoment B raw35315 raw35315Labels = mixedMoment B raw35315step0 raw35315step0Labels := by
      have hz : ∀ j, raw35315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35315step0 = (fun i j => raw35315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35315step0 raw35315; decide +kernel
      have hl : raw35315step0Labels = raw35315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35315 raw35315Labels permutation346 hz
    mixedMoment B raw35315step0 raw35315step0Labels = mixedMoment B raw35315step1 raw35315step1Labels := by
      have ha : raw35315step1 = (fun i j => raw35315step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35315step1 raw35315step0; decide +kernel
      have hl : raw35315step1Labels = raw35315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35315step0 raw35315step0Labels permutation150 permutation3
    mixedMoment B raw35315step1 raw35315step1Labels = mixedMoment B raw35315step2 raw35315step2Labels := by
      have ha : raw35315step2 = -raw35315step1 := by apply Matrix.ext; change ∀ i j, raw35315step2 i j = -(raw35315step1 i j); unfold raw35315step2 raw35315step1; decide +kernel
      have hl : raw35315step2Labels = raw35315step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2360 node2360Labels := by rfl

def raw35316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw35316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw35316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw35316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35316 raw35316Labels = mixedMoment B node2621 node2621Labels := by
  calc
    mixedMoment B raw35316 raw35316Labels = mixedMoment B raw35316step0 raw35316step0Labels := by
      have hz : ∀ j, raw35316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35316step0 = (fun i j => raw35316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35316step0 raw35316; decide +kernel
      have hl : raw35316step0Labels = raw35316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35316 raw35316Labels permutation346 hz
    mixedMoment B raw35316step0 raw35316step0Labels = mixedMoment B raw35316step1 raw35316step1Labels := by
      have ha : raw35316step1 = (fun i j => raw35316step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35316step1 raw35316step0; decide +kernel
      have hl : raw35316step1Labels = raw35316step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35316step0 raw35316step0Labels permutation150 permutation3
    mixedMoment B raw35316step1 raw35316step1Labels = mixedMoment B raw35316step2 raw35316step2Labels := by
      have ha : raw35316step2 = -raw35316step1 := by apply Matrix.ext; change ∀ i j, raw35316step2 i j = -(raw35316step1 i j); unfold raw35316step2 raw35316step1; decide +kernel
      have hl : raw35316step2Labels = raw35316step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2621 node2621Labels := by rfl

def raw35317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw35317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw35317step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw35317step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35317 raw35317Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw35317 raw35317Labels = mixedMoment B raw35317step0 raw35317step0Labels := by
      have hz : ∀ j, raw35317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35317step0 = (fun i j => raw35317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35317step0 raw35317; decide +kernel
      have hl : raw35317step0Labels = raw35317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35317 raw35317Labels permutation346 hz
    mixedMoment B raw35317step0 raw35317step0Labels = mixedMoment B raw35317step1 raw35317step1Labels := by
      have ha : raw35317step1 = (fun i j => raw35317step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35317step1 raw35317step0; decide +kernel
      have hl : raw35317step1Labels = raw35317step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35317step0 raw35317step0Labels permutation58 permutation5
    mixedMoment B raw35317step1 raw35317step1Labels = mixedMoment B raw35317step2 raw35317step2Labels := by
      have ha : raw35317step2 = -raw35317step1 := by apply Matrix.ext; change ∀ i j, raw35317step2 i j = -(raw35317step1 i j); unfold raw35317step2 raw35317step1; decide +kernel
      have hl : raw35317step2Labels = raw35317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35317step2 raw35317step2Labels = mixedMoment B raw35317step3 raw35317step3Labels := by
      have ha : raw35317step3 = raw35317step2 := by apply Matrix.ext; unfold raw35317step3 raw35317step2; decide +kernel
      have hl : raw35317step2Labels = labelEmbedding1 ∘ raw35317step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35317step2 raw35317step2Labels raw35317step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw35318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35318 raw35318Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw35318 raw35318Labels = mixedMoment B raw35318step0 raw35318step0Labels := by
      have ha : raw35318step0 = (fun i j => raw35318 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35318step0 raw35318; decide +kernel
      have hl : raw35318step0Labels = raw35318Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35318 raw35318Labels permutation583 permutation7
    mixedMoment B raw35318step0 raw35318step0Labels = mixedMoment B raw35318step1 raw35318step1Labels := by
      have ha : raw35318step1 = raw35318step0 := by apply Matrix.ext; unfold raw35318step1 raw35318step0; decide +kernel
      have hl : raw35318step0Labels = labelEmbedding1 ∘ raw35318step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35318step0 raw35318step0Labels raw35318step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw35319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35319step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35319 raw35319Labels = mixedMoment B node3774 node3774Labels := by
  calc
    mixedMoment B raw35319 raw35319Labels = mixedMoment B raw35319step0 raw35319step0Labels := by
      have hz : ∀ j, raw35319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35319step0 = (fun i j => raw35319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35319step0 raw35319; decide +kernel
      have hl : raw35319step0Labels = raw35319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35319 raw35319Labels permutation346 hz
    mixedMoment B raw35319step0 raw35319step0Labels = mixedMoment B raw35319step1 raw35319step1Labels := by
      have ha : raw35319step1 = (fun i j => raw35319step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35319step1 raw35319step0; decide +kernel
      have hl : raw35319step1Labels = raw35319step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35319step0 raw35319step0Labels permutation123 permutation7
    mixedMoment B raw35319step1 raw35319step1Labels = mixedMoment B raw35319step2 raw35319step2Labels := by
      have ha : raw35319step2 = raw35319step1 := by apply Matrix.ext; unfold raw35319step2 raw35319step1; decide +kernel
      have hl : raw35319step1Labels = labelEmbedding1 ∘ raw35319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35319step1 raw35319step1Labels raw35319step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3774 node3774Labels := by rfl

def raw35320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35320step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35320step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35320 raw35320Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw35320 raw35320Labels = mixedMoment B raw35320step0 raw35320step0Labels := by
      have hz : ∀ j, raw35320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35320step0 = (fun i j => raw35320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35320step0 raw35320; decide +kernel
      have hl : raw35320step0Labels = raw35320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35320 raw35320Labels permutation346 hz
    mixedMoment B raw35320step0 raw35320step0Labels = mixedMoment B raw35320step1 raw35320step1Labels := by
      have ha : raw35320step1 = (fun i j => raw35320step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35320step1 raw35320step0; decide +kernel
      have hl : raw35320step1Labels = raw35320step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35320step0 raw35320step0Labels permutation126 permutation7
    mixedMoment B raw35320step1 raw35320step1Labels = mixedMoment B raw35320step2 raw35320step2Labels := by
      have ha : raw35320step2 = raw35320step1 := by apply Matrix.ext; unfold raw35320step2 raw35320step1; decide +kernel
      have hl : raw35320step1Labels = labelEmbedding1 ∘ raw35320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35320step1 raw35320step1Labels raw35320step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw35321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35321step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35321 raw35321Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw35321 raw35321Labels = mixedMoment B raw35321step0 raw35321step0Labels := by
      have ha : raw35321step0 = (fun i j => raw35321 (permutation279 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35321step0 raw35321; decide +kernel
      have hl : raw35321step0Labels = raw35321Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35321 raw35321Labels permutation279 permutation5
    mixedMoment B raw35321step0 raw35321step0Labels = mixedMoment B raw35321step1 raw35321step1Labels := by
      have ha : raw35321step1 = -raw35321step0 := by apply Matrix.ext; change ∀ i j, raw35321step1 i j = -(raw35321step0 i j); unfold raw35321step1 raw35321step0; decide +kernel
      have hl : raw35321step1Labels = raw35321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35321step1 raw35321step1Labels = mixedMoment B raw35321step2 raw35321step2Labels := by
      have ha : raw35321step2 = raw35321step1 := by apply Matrix.ext; unfold raw35321step2 raw35321step1; decide +kernel
      have hl : raw35321step1Labels = labelEmbedding1 ∘ raw35321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35321step1 raw35321step1Labels raw35321step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw35322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35322 raw35322Labels = mixedMoment B node3756 node3756Labels := by
  calc
    mixedMoment B raw35322 raw35322Labels = mixedMoment B raw35322step0 raw35322step0Labels := by
      have ha : raw35322step0 = (fun i j => raw35322 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35322step0 raw35322; decide +kernel
      have hl : raw35322step0Labels = raw35322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35322 raw35322Labels permutation583 permutation7
    mixedMoment B raw35322step0 raw35322step0Labels = mixedMoment B raw35322step1 raw35322step1Labels := by
      have ha : raw35322step1 = raw35322step0 := by apply Matrix.ext; unfold raw35322step1 raw35322step0; decide +kernel
      have hl : raw35322step0Labels = labelEmbedding1 ∘ raw35322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35322step0 raw35322step0Labels raw35322step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3756 node3756Labels := by rfl

def raw35323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35323step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35323 raw35323Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw35323 raw35323Labels = mixedMoment B raw35323step0 raw35323step0Labels := by
      have ha : raw35323step0 = (fun i j => raw35323 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35323step0 raw35323; decide +kernel
      have hl : raw35323step0Labels = raw35323Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35323 raw35323Labels permutation583 permutation7
    mixedMoment B raw35323step0 raw35323step0Labels = mixedMoment B raw35323step1 raw35323step1Labels := by
      have ha : raw35323step1 = raw35323step0 := by apply Matrix.ext; unfold raw35323step1 raw35323step0; decide +kernel
      have hl : raw35323step0Labels = labelEmbedding1 ∘ raw35323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35323step0 raw35323step0Labels raw35323step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

def raw35324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw35324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw35324step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35324step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw35324step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35324 raw35324Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw35324 raw35324Labels = mixedMoment B raw35324step0 raw35324step0Labels := by
      have hz : ∀ j, raw35324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35324step0 = (fun i j => raw35324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35324step0 raw35324; decide +kernel
      have hl : raw35324step0Labels = raw35324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35324 raw35324Labels permutation346 hz
    mixedMoment B raw35324step0 raw35324step0Labels = mixedMoment B raw35324step1 raw35324step1Labels := by
      have ha : raw35324step1 = (fun i j => raw35324step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35324step1 raw35324step0; decide +kernel
      have hl : raw35324step1Labels = raw35324step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35324step0 raw35324step0Labels permutation59 permutation5
    mixedMoment B raw35324step1 raw35324step1Labels = mixedMoment B raw35324step2 raw35324step2Labels := by
      have ha : raw35324step2 = -raw35324step1 := by apply Matrix.ext; change ∀ i j, raw35324step2 i j = -(raw35324step1 i j); unfold raw35324step2 raw35324step1; decide +kernel
      have hl : raw35324step2Labels = raw35324step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35324step2 raw35324step2Labels = mixedMoment B raw35324step3 raw35324step3Labels := by
      have ha : raw35324step3 = raw35324step2 := by apply Matrix.ext; unfold raw35324step3 raw35324step2; decide +kernel
      have hl : raw35324step2Labels = labelEmbedding1 ∘ raw35324step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35324step2 raw35324step2Labels raw35324step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

def raw35325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw35325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw35325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35325 raw35325Labels = mixedMoment B node3763 node3763Labels := by
  calc
    mixedMoment B raw35325 raw35325Labels = mixedMoment B raw35325step0 raw35325step0Labels := by
      have ha : raw35325step0 = (fun i j => raw35325 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35325step0 raw35325; decide +kernel
      have hl : raw35325step0Labels = raw35325Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35325 raw35325Labels permutation583 permutation7
    mixedMoment B raw35325step0 raw35325step0Labels = mixedMoment B raw35325step1 raw35325step1Labels := by
      have ha : raw35325step1 = raw35325step0 := by apply Matrix.ext; unfold raw35325step1 raw35325step0; decide +kernel
      have hl : raw35325step0Labels = labelEmbedding1 ∘ raw35325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35325step0 raw35325step0Labels raw35325step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3763 node3763Labels := by rfl

def raw35326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw35326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw35326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35326 raw35326Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw35326 raw35326Labels = mixedMoment B raw35326step0 raw35326step0Labels := by
      have hz : ∀ j, raw35326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35326step0 = (fun i j => raw35326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35326step0 raw35326; decide +kernel
      have hl : raw35326step0Labels = raw35326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35326 raw35326Labels permutation346 hz
    mixedMoment B raw35326step0 raw35326step0Labels = mixedMoment B raw35326step1 raw35326step1Labels := by
      have ha : raw35326step1 = (fun i j => raw35326step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35326step1 raw35326step0; decide +kernel
      have hl : raw35326step1Labels = raw35326step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35326step0 raw35326step0Labels permutation126 permutation7
    mixedMoment B raw35326step1 raw35326step1Labels = mixedMoment B raw35326step2 raw35326step2Labels := by
      have ha : raw35326step2 = raw35326step1 := by apply Matrix.ext; unfold raw35326step2 raw35326step1; decide +kernel
      have hl : raw35326step1Labels = labelEmbedding1 ∘ raw35326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35326step1 raw35326step1Labels raw35326step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

def raw35327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw35327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw35327step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35327step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw35327step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35327 raw35327Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw35327 raw35327Labels = mixedMoment B raw35327step0 raw35327step0Labels := by
      have hz : ∀ j, raw35327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35327step0 = (fun i j => raw35327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35327step0 raw35327; decide +kernel
      have hl : raw35327step0Labels = raw35327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35327 raw35327Labels permutation346 hz
    mixedMoment B raw35327step0 raw35327step0Labels = mixedMoment B raw35327step1 raw35327step1Labels := by
      have ha : raw35327step1 = (fun i j => raw35327step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35327step1 raw35327step0; decide +kernel
      have hl : raw35327step1Labels = raw35327step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35327step0 raw35327step0Labels permutation57 permutation5
    mixedMoment B raw35327step1 raw35327step1Labels = mixedMoment B raw35327step2 raw35327step2Labels := by
      have ha : raw35327step2 = -raw35327step1 := by apply Matrix.ext; change ∀ i j, raw35327step2 i j = -(raw35327step1 i j); unfold raw35327step2 raw35327step1; decide +kernel
      have hl : raw35327step2Labels = raw35327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35327step2 raw35327step2Labels = mixedMoment B raw35327step3 raw35327step3Labels := by
      have ha : raw35327step3 = raw35327step2 := by apply Matrix.ext; unfold raw35327step3 raw35327step2; decide +kernel
      have hl : raw35327step2Labels = labelEmbedding1 ∘ raw35327step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35327step2 raw35327step2Labels raw35327step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
