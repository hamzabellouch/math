import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -3, 3]]
def raw20480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw20480step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw20480step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20480 raw20480Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw20480 raw20480Labels = mixedMoment B raw20480step0 raw20480step0Labels := by
      have hz : ∀ j, raw20480 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20480step0 = (fun i j => raw20480 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20480step0 raw20480; decide +kernel
      have hl : raw20480step0Labels = raw20480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20480 raw20480Labels permutation434 hz
    mixedMoment B raw20480step0 raw20480step0Labels = mixedMoment B raw20480step1 raw20480step1Labels := by
      have hz : ∀ j, raw20480step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20480step1 = (fun i j => raw20480step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20480step1 raw20480step0; decide +kernel
      have hl : raw20480step1Labels = raw20480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20480step0 raw20480step0Labels permutation80 hz
    mixedMoment B raw20480step1 raw20480step1Labels = mixedMoment B raw20480step2 raw20480step2Labels := by
      have hz : ∀ j, raw20480step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20480step2 = (fun i j => raw20480step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20480step2 raw20480step1; decide +kernel
      have hl : raw20480step2Labels = raw20480step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20480step1 raw20480step1Labels permutation14 hz
    mixedMoment B raw20480step2 raw20480step2Labels = mixedMoment B raw20480step3 raw20480step3Labels := by
      have ha : raw20480step3 = (fun i j => raw20480step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20480step3 raw20480step2; decide +kernel
      have hl : raw20480step3Labels = raw20480step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20480step2 raw20480step2Labels permutation2 permutation4
    mixedMoment B raw20480step3 raw20480step3Labels = mixedMoment B raw20480step4 raw20480step4Labels := by
      have ha : raw20480step4 = -raw20480step3 := by apply Matrix.ext; change ∀ i j, raw20480step4 i j = -(raw20480step3 i j); unfold raw20480step4 raw20480step3; decide +kernel
      have hl : raw20480step4Labels = raw20480step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1730 node1730Labels := by rfl

def raw20481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20481step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20481 raw20481Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20481 raw20481Labels = mixedMoment B raw20481step0 raw20481step0Labels := by
      have hz : ∀ j, raw20481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20481step0 = (fun i j => raw20481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20481step0 raw20481; decide +kernel
      have hl : raw20481step0Labels = raw20481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20481 raw20481Labels permutation434 hz
    mixedMoment B raw20481step0 raw20481step0Labels = mixedMoment B raw20481step1 raw20481step1Labels := by
      have hz : ∀ j, raw20481step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20481step1 = (fun i j => raw20481step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20481step1 raw20481step0; decide +kernel
      have hl : raw20481step1Labels = raw20481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20481step0 raw20481step0Labels permutation56 hz
    mixedMoment B raw20481step1 raw20481step1Labels = mixedMoment B raw20481step2 raw20481step2Labels := by
      have ha : raw20481step2 = (fun i j => raw20481step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20481step2 raw20481step1; decide +kernel
      have hl : raw20481step2Labels = raw20481step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20481step1 raw20481step1Labels permutation8 permutation4
    mixedMoment B raw20481step2 raw20481step2Labels = mixedMoment B raw20481step3 raw20481step3Labels := by
      have ha : raw20481step3 = -raw20481step2 := by apply Matrix.ext; change ∀ i j, raw20481step3 i j = -(raw20481step2 i j); unfold raw20481step3 raw20481step2; decide +kernel
      have hl : raw20481step3Labels = raw20481step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw20482 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20482 raw20482Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20482 raw20482Labels = mixedMoment B raw20482step0 raw20482step0Labels := by
      have hz : ∀ j, raw20482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20482step0 = (fun i j => raw20482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20482step0 raw20482; decide +kernel
      have hl : raw20482step0Labels = raw20482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20482 raw20482Labels permutation346 hz
    mixedMoment B raw20482step0 raw20482step0Labels = mixedMoment B raw20482step1 raw20482step1Labels := by
      have hz : ∀ j, raw20482step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20482step1 = (fun i j => raw20482step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20482step1 raw20482step0; decide +kernel
      have hl : raw20482step1Labels = raw20482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20482step0 raw20482step0Labels permutation56 hz
    mixedMoment B raw20482step1 raw20482step1Labels = mixedMoment B raw20482step2 raw20482step2Labels := by
      have ha : raw20482step2 = (fun i j => raw20482step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20482step2 raw20482step1; decide +kernel
      have hl : raw20482step2Labels = raw20482step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20482step1 raw20482step1Labels permutation8 permutation4
    mixedMoment B raw20482step2 raw20482step2Labels = mixedMoment B raw20482step3 raw20482step3Labels := by
      have ha : raw20482step3 = -raw20482step2 := by apply Matrix.ext; change ∀ i j, raw20482step3 i j = -(raw20482step2 i j); unfold raw20482step3 raw20482step2; decide +kernel
      have hl : raw20482step3Labels = raw20482step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw20483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20483step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20483step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20483 raw20483Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw20483 raw20483Labels = mixedMoment B raw20483step0 raw20483step0Labels := by
      have hz : ∀ j, raw20483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20483step0 = (fun i j => raw20483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20483step0 raw20483; decide +kernel
      have hl : raw20483step0Labels = raw20483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20483 raw20483Labels permutation434 hz
    mixedMoment B raw20483step0 raw20483step0Labels = mixedMoment B raw20483step1 raw20483step1Labels := by
      have hz : ∀ j, raw20483step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20483step1 = (fun i j => raw20483step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20483step1 raw20483step0; decide +kernel
      have hl : raw20483step1Labels = raw20483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20483step0 raw20483step0Labels permutation80 hz
    mixedMoment B raw20483step1 raw20483step1Labels = mixedMoment B raw20483step2 raw20483step2Labels := by
      have ha : raw20483step2 = (fun i j => raw20483step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20483step2 raw20483step1; decide +kernel
      have hl : raw20483step2Labels = raw20483step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20483step1 raw20483step1Labels permutation8 permutation3
    mixedMoment B raw20483step2 raw20483step2Labels = mixedMoment B raw20483step3 raw20483step3Labels := by
      have ha : raw20483step3 = raw20483step2 := by apply Matrix.ext; unfold raw20483step3 raw20483step2; decide +kernel
      have hl : raw20483step2Labels = labelEmbedding6 ∘ raw20483step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20483step2 raw20483step2Labels raw20483step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4184 node4184Labels := by rfl

def raw20484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20484step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20484 raw20484Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20484 raw20484Labels = mixedMoment B raw20484step0 raw20484step0Labels := by
      have hz : ∀ j, raw20484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20484step0 = (fun i j => raw20484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20484step0 raw20484; decide +kernel
      have hl : raw20484step0Labels = raw20484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20484 raw20484Labels permutation434 hz
    mixedMoment B raw20484step0 raw20484step0Labels = mixedMoment B raw20484step1 raw20484step1Labels := by
      have ha : raw20484step1 = (fun i j => raw20484step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20484step1 raw20484step0; decide +kernel
      have hl : raw20484step1Labels = raw20484step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20484step0 raw20484step0Labels permutation38 permutation3
    mixedMoment B raw20484step1 raw20484step1Labels = mixedMoment B raw20484step2 raw20484step2Labels := by
      have ha : raw20484step2 = raw20484step1 := by apply Matrix.ext; unfold raw20484step2 raw20484step1; decide +kernel
      have hl : raw20484step1Labels = labelEmbedding6 ∘ raw20484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20484step1 raw20484step1Labels raw20484step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

def raw20485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20485 raw20485Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20485 raw20485Labels = mixedMoment B raw20485step0 raw20485step0Labels := by
      have hz : ∀ j, raw20485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20485step0 = (fun i j => raw20485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20485step0 raw20485; decide +kernel
      have hl : raw20485step0Labels = raw20485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20485 raw20485Labels permutation346 hz
    mixedMoment B raw20485step0 raw20485step0Labels = mixedMoment B raw20485step1 raw20485step1Labels := by
      have ha : raw20485step1 = (fun i j => raw20485step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20485step1 raw20485step0; decide +kernel
      have hl : raw20485step1Labels = raw20485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20485step0 raw20485step0Labels permutation38 permutation3
    mixedMoment B raw20485step1 raw20485step1Labels = mixedMoment B raw20485step2 raw20485step2Labels := by
      have ha : raw20485step2 = raw20485step1 := by apply Matrix.ext; unfold raw20485step2 raw20485step1; decide +kernel
      have hl : raw20485step1Labels = labelEmbedding6 ∘ raw20485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20485step1 raw20485step1Labels raw20485step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

def raw20486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20486step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20486step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20486step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20486 raw20486Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw20486 raw20486Labels = mixedMoment B raw20486step0 raw20486step0Labels := by
      have hz : ∀ j, raw20486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20486step0 = (fun i j => raw20486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20486step0 raw20486; decide +kernel
      have hl : raw20486step0Labels = raw20486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20486 raw20486Labels permutation434 hz
    mixedMoment B raw20486step0 raw20486step0Labels = mixedMoment B raw20486step1 raw20486step1Labels := by
      have hz : ∀ j, raw20486step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20486step1 = (fun i j => raw20486step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20486step1 raw20486step0; decide +kernel
      have hl : raw20486step1Labels = raw20486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20486step0 raw20486step0Labels permutation56 hz
    mixedMoment B raw20486step1 raw20486step1Labels = mixedMoment B raw20486step2 raw20486step2Labels := by
      have ha : raw20486step2 = (fun i j => raw20486step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20486step2 raw20486step1; decide +kernel
      have hl : raw20486step2Labels = raw20486step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20486step1 raw20486step1Labels permutation8 permutation3
    mixedMoment B raw20486step2 raw20486step2Labels = mixedMoment B raw20486step3 raw20486step3Labels := by
      have ha : raw20486step3 = raw20486step2 := by apply Matrix.ext; unfold raw20486step3 raw20486step2; decide +kernel
      have hl : raw20486step2Labels = labelEmbedding6 ∘ raw20486step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20486step2 raw20486step2Labels raw20486step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4184 node4184Labels := by rfl

def raw20487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20487step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20487step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20487 raw20487Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20487 raw20487Labels = mixedMoment B raw20487step0 raw20487step0Labels := by
      have hz : ∀ j, raw20487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20487step0 = (fun i j => raw20487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20487step0 raw20487; decide +kernel
      have hl : raw20487step0Labels = raw20487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20487 raw20487Labels permutation434 hz
    mixedMoment B raw20487step0 raw20487step0Labels = mixedMoment B raw20487step1 raw20487step1Labels := by
      have ha : raw20487step1 = (fun i j => raw20487step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20487step1 raw20487step0; decide +kernel
      have hl : raw20487step1Labels = raw20487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20487step0 raw20487step0Labels permutation32 permutation3
    mixedMoment B raw20487step1 raw20487step1Labels = mixedMoment B raw20487step2 raw20487step2Labels := by
      have ha : raw20487step2 = raw20487step1 := by apply Matrix.ext; unfold raw20487step2 raw20487step1; decide +kernel
      have hl : raw20487step1Labels = labelEmbedding6 ∘ raw20487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20487step1 raw20487step1Labels raw20487step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

def raw20488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20488step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20488step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20488 raw20488Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20488 raw20488Labels = mixedMoment B raw20488step0 raw20488step0Labels := by
      have hz : ∀ j, raw20488 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20488step0 = (fun i j => raw20488 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20488step0 raw20488; decide +kernel
      have hl : raw20488step0Labels = raw20488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20488 raw20488Labels permutation265 hz
    mixedMoment B raw20488step0 raw20488step0Labels = mixedMoment B raw20488step1 raw20488step1Labels := by
      have ha : raw20488step1 = (fun i j => raw20488step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20488step1 raw20488step0; decide +kernel
      have hl : raw20488step1Labels = raw20488step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20488step0 raw20488step0Labels permutation38 permutation3
    mixedMoment B raw20488step1 raw20488step1Labels = mixedMoment B raw20488step2 raw20488step2Labels := by
      have ha : raw20488step2 = raw20488step1 := by apply Matrix.ext; unfold raw20488step2 raw20488step1; decide +kernel
      have hl : raw20488step1Labels = labelEmbedding6 ∘ raw20488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20488step1 raw20488step1Labels raw20488step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

def raw20489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20489step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20489step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20489step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20489 raw20489Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw20489 raw20489Labels = mixedMoment B raw20489step0 raw20489step0Labels := by
      have hz : ∀ j, raw20489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20489step0 = (fun i j => raw20489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20489step0 raw20489; decide +kernel
      have hl : raw20489step0Labels = raw20489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20489 raw20489Labels permutation346 hz
    mixedMoment B raw20489step0 raw20489step0Labels = mixedMoment B raw20489step1 raw20489step1Labels := by
      have hz : ∀ j, raw20489step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20489step1 = (fun i j => raw20489step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20489step1 raw20489step0; decide +kernel
      have hl : raw20489step1Labels = raw20489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20489step0 raw20489step0Labels permutation56 hz
    mixedMoment B raw20489step1 raw20489step1Labels = mixedMoment B raw20489step2 raw20489step2Labels := by
      have ha : raw20489step2 = (fun i j => raw20489step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20489step2 raw20489step1; decide +kernel
      have hl : raw20489step2Labels = raw20489step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20489step1 raw20489step1Labels permutation8 permutation3
    mixedMoment B raw20489step2 raw20489step2Labels = mixedMoment B raw20489step3 raw20489step3Labels := by
      have ha : raw20489step3 = raw20489step2 := by apply Matrix.ext; unfold raw20489step3 raw20489step2; decide +kernel
      have hl : raw20489step2Labels = labelEmbedding6 ∘ raw20489step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20489step2 raw20489step2Labels raw20489step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4184 node4184Labels := by rfl

def raw20490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20490step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20490step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20490 raw20490Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20490 raw20490Labels = mixedMoment B raw20490step0 raw20490step0Labels := by
      have hz : ∀ j, raw20490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20490step0 = (fun i j => raw20490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20490step0 raw20490; decide +kernel
      have hl : raw20490step0Labels = raw20490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20490 raw20490Labels permutation346 hz
    mixedMoment B raw20490step0 raw20490step0Labels = mixedMoment B raw20490step1 raw20490step1Labels := by
      have ha : raw20490step1 = (fun i j => raw20490step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20490step1 raw20490step0; decide +kernel
      have hl : raw20490step1Labels = raw20490step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20490step0 raw20490step0Labels permutation32 permutation3
    mixedMoment B raw20490step1 raw20490step1Labels = mixedMoment B raw20490step2 raw20490step2Labels := by
      have ha : raw20490step2 = raw20490step1 := by apply Matrix.ext; unfold raw20490step2 raw20490step1; decide +kernel
      have hl : raw20490step1Labels = labelEmbedding6 ∘ raw20490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20490step1 raw20490step1Labels raw20490step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

def raw20491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20491step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20491step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20491 raw20491Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20491 raw20491Labels = mixedMoment B raw20491step0 raw20491step0Labels := by
      have hz : ∀ j, raw20491 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20491step0 = (fun i j => raw20491 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20491step0 raw20491; decide +kernel
      have hl : raw20491step0Labels = raw20491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20491 raw20491Labels permutation265 hz
    mixedMoment B raw20491step0 raw20491step0Labels = mixedMoment B raw20491step1 raw20491step1Labels := by
      have ha : raw20491step1 = (fun i j => raw20491step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20491step1 raw20491step0; decide +kernel
      have hl : raw20491step1Labels = raw20491step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20491step0 raw20491step0Labels permutation32 permutation3
    mixedMoment B raw20491step1 raw20491step1Labels = mixedMoment B raw20491step2 raw20491step2Labels := by
      have ha : raw20491step2 = raw20491step1 := by apply Matrix.ext; unfold raw20491step2 raw20491step1; decide +kernel
      have hl : raw20491step1Labels = labelEmbedding6 ∘ raw20491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20491step1 raw20491step1Labels raw20491step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

def raw20492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20492step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20492step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20492step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20492step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20492 raw20492Labels = mixedMoment B node4193 node4193Labels := by
  calc
    mixedMoment B raw20492 raw20492Labels = mixedMoment B raw20492step0 raw20492step0Labels := by
      have hz : ∀ j, raw20492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20492step0 = (fun i j => raw20492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20492step0 raw20492; decide +kernel
      have hl : raw20492step0Labels = raw20492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20492 raw20492Labels permutation434 hz
    mixedMoment B raw20492step0 raw20492step0Labels = mixedMoment B raw20492step1 raw20492step1Labels := by
      have hz : ∀ j, raw20492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20492step1 = (fun i j => raw20492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20492step1 raw20492step0; decide +kernel
      have hl : raw20492step1Labels = raw20492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20492step0 raw20492step0Labels permutation80 hz
    mixedMoment B raw20492step1 raw20492step1Labels = mixedMoment B raw20492step2 raw20492step2Labels := by
      have hz : ∀ j, raw20492step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20492step2 = (fun i j => raw20492step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20492step2 raw20492step1; decide +kernel
      have hl : raw20492step2Labels = raw20492step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20492step1 raw20492step1Labels permutation14 hz
    mixedMoment B raw20492step2 raw20492step2Labels = mixedMoment B raw20492step3 raw20492step3Labels := by
      have ha : raw20492step3 = (fun i j => raw20492step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20492step3 raw20492step2; decide +kernel
      have hl : raw20492step3Labels = raw20492step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20492step2 raw20492step2Labels permutation2 permutation3
    mixedMoment B raw20492step3 raw20492step3Labels = mixedMoment B raw20492step4 raw20492step4Labels := by
      have ha : raw20492step4 = raw20492step3 := by apply Matrix.ext; unfold raw20492step4 raw20492step3; decide +kernel
      have hl : raw20492step3Labels = labelEmbedding6 ∘ raw20492step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20492step3 raw20492step3Labels raw20492step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4193 node4193Labels := by rfl

def raw20493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20493step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20493step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20493step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20493 raw20493Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw20493 raw20493Labels = mixedMoment B raw20493step0 raw20493step0Labels := by
      have hz : ∀ j, raw20493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20493step0 = (fun i j => raw20493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20493step0 raw20493; decide +kernel
      have hl : raw20493step0Labels = raw20493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20493 raw20493Labels permutation434 hz
    mixedMoment B raw20493step0 raw20493step0Labels = mixedMoment B raw20493step1 raw20493step1Labels := by
      have hz : ∀ j, raw20493step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20493step1 = (fun i j => raw20493step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20493step1 raw20493step0; decide +kernel
      have hl : raw20493step1Labels = raw20493step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20493step0 raw20493step0Labels permutation80 hz
    mixedMoment B raw20493step1 raw20493step1Labels = mixedMoment B raw20493step2 raw20493step2Labels := by
      have ha : raw20493step2 = (fun i j => raw20493step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20493step2 raw20493step1; decide +kernel
      have hl : raw20493step2Labels = raw20493step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20493step1 raw20493step1Labels permutation8 permutation3
    mixedMoment B raw20493step2 raw20493step2Labels = mixedMoment B raw20493step3 raw20493step3Labels := by
      have ha : raw20493step3 = raw20493step2 := by apply Matrix.ext; unfold raw20493step3 raw20493step2; decide +kernel
      have hl : raw20493step2Labels = labelEmbedding6 ∘ raw20493step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20493step2 raw20493step2Labels raw20493step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4560 node4560Labels := by rfl

def raw20494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20494step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20494step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20494step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20494 raw20494Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw20494 raw20494Labels = mixedMoment B raw20494step0 raw20494step0Labels := by
      have hz : ∀ j, raw20494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20494step0 = (fun i j => raw20494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20494step0 raw20494; decide +kernel
      have hl : raw20494step0Labels = raw20494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20494 raw20494Labels permutation434 hz
    mixedMoment B raw20494step0 raw20494step0Labels = mixedMoment B raw20494step1 raw20494step1Labels := by
      have hz : ∀ j, raw20494step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20494step1 = (fun i j => raw20494step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20494step1 raw20494step0; decide +kernel
      have hl : raw20494step1Labels = raw20494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20494step0 raw20494step0Labels permutation56 hz
    mixedMoment B raw20494step1 raw20494step1Labels = mixedMoment B raw20494step2 raw20494step2Labels := by
      have ha : raw20494step2 = (fun i j => raw20494step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20494step2 raw20494step1; decide +kernel
      have hl : raw20494step2Labels = raw20494step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20494step1 raw20494step1Labels permutation8 permutation3
    mixedMoment B raw20494step2 raw20494step2Labels = mixedMoment B raw20494step3 raw20494step3Labels := by
      have ha : raw20494step3 = raw20494step2 := by apply Matrix.ext; unfold raw20494step3 raw20494step2; decide +kernel
      have hl : raw20494step2Labels = labelEmbedding6 ∘ raw20494step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20494step2 raw20494step2Labels raw20494step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4560 node4560Labels := by rfl

def raw20495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20495step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20495step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20495step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20495 raw20495Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw20495 raw20495Labels = mixedMoment B raw20495step0 raw20495step0Labels := by
      have hz : ∀ j, raw20495 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20495step0 = (fun i j => raw20495 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20495step0 raw20495; decide +kernel
      have hl : raw20495step0Labels = raw20495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20495 raw20495Labels permutation346 hz
    mixedMoment B raw20495step0 raw20495step0Labels = mixedMoment B raw20495step1 raw20495step1Labels := by
      have hz : ∀ j, raw20495step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20495step1 = (fun i j => raw20495step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20495step1 raw20495step0; decide +kernel
      have hl : raw20495step1Labels = raw20495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20495step0 raw20495step0Labels permutation56 hz
    mixedMoment B raw20495step1 raw20495step1Labels = mixedMoment B raw20495step2 raw20495step2Labels := by
      have ha : raw20495step2 = (fun i j => raw20495step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20495step2 raw20495step1; decide +kernel
      have hl : raw20495step2Labels = raw20495step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20495step1 raw20495step1Labels permutation8 permutation3
    mixedMoment B raw20495step2 raw20495step2Labels = mixedMoment B raw20495step3 raw20495step3Labels := by
      have ha : raw20495step3 = raw20495step2 := by apply Matrix.ext; unfold raw20495step3 raw20495step2; decide +kernel
      have hl : raw20495step2Labels = labelEmbedding6 ∘ raw20495step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20495step2 raw20495step2Labels raw20495step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4560 node4560Labels := by rfl

def raw20496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20496step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw20496step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw20496step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20496 raw20496Labels = mixedMoment B node3125 node3125Labels := by
  calc
    mixedMoment B raw20496 raw20496Labels = mixedMoment B raw20496step0 raw20496step0Labels := by
      have hz : ∀ j, raw20496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20496step0 = (fun i j => raw20496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20496step0 raw20496; decide +kernel
      have hl : raw20496step0Labels = raw20496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20496 raw20496Labels permutation434 hz
    mixedMoment B raw20496step0 raw20496step0Labels = mixedMoment B raw20496step1 raw20496step1Labels := by
      have hz : ∀ j, raw20496step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20496step1 = (fun i j => raw20496step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20496step1 raw20496step0; decide +kernel
      have hl : raw20496step1Labels = raw20496step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20496step0 raw20496step0Labels permutation80 hz
    mixedMoment B raw20496step1 raw20496step1Labels = mixedMoment B raw20496step2 raw20496step2Labels := by
      have hz : ∀ j, raw20496step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20496step2 = (fun i j => raw20496step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20496step2 raw20496step1; decide +kernel
      have hl : raw20496step2Labels = raw20496step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20496step1 raw20496step1Labels permutation14 hz
    mixedMoment B raw20496step2 raw20496step2Labels = mixedMoment B raw20496step3 raw20496step3Labels := by
      have ha : raw20496step3 = (fun i j => raw20496step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20496step3 raw20496step2; decide +kernel
      have hl : raw20496step3Labels = raw20496step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20496step2 raw20496step2Labels permutation2 permutation3
    _ = mixedMoment B node3125 node3125Labels := by rfl

def raw20497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20497step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20497 raw20497Labels = mixedMoment B node612 node612Labels := by
  calc
    mixedMoment B raw20497 raw20497Labels = mixedMoment B raw20497step0 raw20497step0Labels := by
      have hz : ∀ j, raw20497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20497step0 = (fun i j => raw20497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20497step0 raw20497; decide +kernel
      have hl : raw20497step0Labels = raw20497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20497 raw20497Labels permutation434 hz
    mixedMoment B raw20497step0 raw20497step0Labels = mixedMoment B raw20497step1 raw20497step1Labels := by
      have hz : ∀ j, raw20497step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20497step1 = (fun i j => raw20497step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20497step1 raw20497step0; decide +kernel
      have hl : raw20497step1Labels = raw20497step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20497step0 raw20497step0Labels permutation80 hz
    mixedMoment B raw20497step1 raw20497step1Labels = mixedMoment B raw20497step2 raw20497step2Labels := by
      have ha : raw20497step2 = (fun i j => raw20497step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20497step2 raw20497step1; decide +kernel
      have hl : raw20497step2Labels = raw20497step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20497step1 raw20497step1Labels permutation8 permutation3
    _ = mixedMoment B node612 node612Labels := by rfl

def raw20498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20498 raw20498Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw20498 raw20498Labels = mixedMoment B raw20498step0 raw20498step0Labels := by
      have hz : ∀ j, raw20498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20498step0 = (fun i j => raw20498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20498step0 raw20498; decide +kernel
      have hl : raw20498step0Labels = raw20498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20498 raw20498Labels permutation434 hz
    mixedMoment B raw20498step0 raw20498step0Labels = mixedMoment B raw20498step1 raw20498step1Labels := by
      have ha : raw20498step1 = (fun i j => raw20498step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20498step1 raw20498step0; decide +kernel
      have hl : raw20498step1Labels = raw20498step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20498step0 raw20498step0Labels permutation38 permutation3
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw20499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20499 raw20499Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw20499 raw20499Labels = mixedMoment B raw20499step0 raw20499step0Labels := by
      have hz : ∀ j, raw20499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20499step0 = (fun i j => raw20499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20499step0 raw20499; decide +kernel
      have hl : raw20499step0Labels = raw20499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20499 raw20499Labels permutation346 hz
    mixedMoment B raw20499step0 raw20499step0Labels = mixedMoment B raw20499step1 raw20499step1Labels := by
      have ha : raw20499step1 = (fun i j => raw20499step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20499step1 raw20499step0; decide +kernel
      have hl : raw20499step1Labels = raw20499step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20499step0 raw20499step0Labels permutation38 permutation3
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw20500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20500step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20500 raw20500Labels = mixedMoment B node612 node612Labels := by
  calc
    mixedMoment B raw20500 raw20500Labels = mixedMoment B raw20500step0 raw20500step0Labels := by
      have hz : ∀ j, raw20500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20500step0 = (fun i j => raw20500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20500step0 raw20500; decide +kernel
      have hl : raw20500step0Labels = raw20500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20500 raw20500Labels permutation434 hz
    mixedMoment B raw20500step0 raw20500step0Labels = mixedMoment B raw20500step1 raw20500step1Labels := by
      have hz : ∀ j, raw20500step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20500step1 = (fun i j => raw20500step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20500step1 raw20500step0; decide +kernel
      have hl : raw20500step1Labels = raw20500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20500step0 raw20500step0Labels permutation56 hz
    mixedMoment B raw20500step1 raw20500step1Labels = mixedMoment B raw20500step2 raw20500step2Labels := by
      have ha : raw20500step2 = (fun i j => raw20500step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20500step2 raw20500step1; decide +kernel
      have hl : raw20500step2Labels = raw20500step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20500step1 raw20500step1Labels permutation8 permutation3
    _ = mixedMoment B node612 node612Labels := by rfl

def raw20501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20501 raw20501Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw20501 raw20501Labels = mixedMoment B raw20501step0 raw20501step0Labels := by
      have hz : ∀ j, raw20501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20501step0 = (fun i j => raw20501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20501step0 raw20501; decide +kernel
      have hl : raw20501step0Labels = raw20501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20501 raw20501Labels permutation434 hz
    mixedMoment B raw20501step0 raw20501step0Labels = mixedMoment B raw20501step1 raw20501step1Labels := by
      have ha : raw20501step1 = (fun i j => raw20501step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20501step1 raw20501step0; decide +kernel
      have hl : raw20501step1Labels = raw20501step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20501step0 raw20501step0Labels permutation32 permutation3
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw20502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20502 raw20502Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw20502 raw20502Labels = mixedMoment B raw20502step0 raw20502step0Labels := by
      have hz : ∀ j, raw20502 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20502step0 = (fun i j => raw20502 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20502step0 raw20502; decide +kernel
      have hl : raw20502step0Labels = raw20502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20502 raw20502Labels permutation265 hz
    mixedMoment B raw20502step0 raw20502step0Labels = mixedMoment B raw20502step1 raw20502step1Labels := by
      have ha : raw20502step1 = (fun i j => raw20502step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20502step1 raw20502step0; decide +kernel
      have hl : raw20502step1Labels = raw20502step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20502step0 raw20502step0Labels permutation38 permutation3
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw20503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20503step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20503 raw20503Labels = mixedMoment B node612 node612Labels := by
  calc
    mixedMoment B raw20503 raw20503Labels = mixedMoment B raw20503step0 raw20503step0Labels := by
      have hz : ∀ j, raw20503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20503step0 = (fun i j => raw20503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20503step0 raw20503; decide +kernel
      have hl : raw20503step0Labels = raw20503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20503 raw20503Labels permutation346 hz
    mixedMoment B raw20503step0 raw20503step0Labels = mixedMoment B raw20503step1 raw20503step1Labels := by
      have hz : ∀ j, raw20503step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20503step1 = (fun i j => raw20503step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20503step1 raw20503step0; decide +kernel
      have hl : raw20503step1Labels = raw20503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20503step0 raw20503step0Labels permutation56 hz
    mixedMoment B raw20503step1 raw20503step1Labels = mixedMoment B raw20503step2 raw20503step2Labels := by
      have ha : raw20503step2 = (fun i j => raw20503step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20503step2 raw20503step1; decide +kernel
      have hl : raw20503step2Labels = raw20503step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20503step1 raw20503step1Labels permutation8 permutation3
    _ = mixedMoment B node612 node612Labels := by rfl

def raw20504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20504 raw20504Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw20504 raw20504Labels = mixedMoment B raw20504step0 raw20504step0Labels := by
      have hz : ∀ j, raw20504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20504step0 = (fun i j => raw20504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20504step0 raw20504; decide +kernel
      have hl : raw20504step0Labels = raw20504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20504 raw20504Labels permutation346 hz
    mixedMoment B raw20504step0 raw20504step0Labels = mixedMoment B raw20504step1 raw20504step1Labels := by
      have ha : raw20504step1 = (fun i j => raw20504step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20504step1 raw20504step0; decide +kernel
      have hl : raw20504step1Labels = raw20504step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20504step0 raw20504step0Labels permutation32 permutation3
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw20505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20505 raw20505Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw20505 raw20505Labels = mixedMoment B raw20505step0 raw20505step0Labels := by
      have hz : ∀ j, raw20505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20505step0 = (fun i j => raw20505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20505step0 raw20505; decide +kernel
      have hl : raw20505step0Labels = raw20505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20505 raw20505Labels permutation265 hz
    mixedMoment B raw20505step0 raw20505step0Labels = mixedMoment B raw20505step1 raw20505step1Labels := by
      have ha : raw20505step1 = (fun i j => raw20505step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20505step1 raw20505step0; decide +kernel
      have hl : raw20505step1Labels = raw20505step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20505step0 raw20505step0Labels permutation32 permutation3
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw20506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20506step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20506step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20506step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20506 raw20506Labels = mixedMoment B node621 node621Labels := by
  calc
    mixedMoment B raw20506 raw20506Labels = mixedMoment B raw20506step0 raw20506step0Labels := by
      have hz : ∀ j, raw20506 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20506step0 = (fun i j => raw20506 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20506step0 raw20506; decide +kernel
      have hl : raw20506step0Labels = raw20506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20506 raw20506Labels permutation434 hz
    mixedMoment B raw20506step0 raw20506step0Labels = mixedMoment B raw20506step1 raw20506step1Labels := by
      have hz : ∀ j, raw20506step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20506step1 = (fun i j => raw20506step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20506step1 raw20506step0; decide +kernel
      have hl : raw20506step1Labels = raw20506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20506step0 raw20506step0Labels permutation80 hz
    mixedMoment B raw20506step1 raw20506step1Labels = mixedMoment B raw20506step2 raw20506step2Labels := by
      have hz : ∀ j, raw20506step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20506step2 = (fun i j => raw20506step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20506step2 raw20506step1; decide +kernel
      have hl : raw20506step2Labels = raw20506step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20506step1 raw20506step1Labels permutation14 hz
    mixedMoment B raw20506step2 raw20506step2Labels = mixedMoment B raw20506step3 raw20506step3Labels := by
      have ha : raw20506step3 = (fun i j => raw20506step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20506step3 raw20506step2; decide +kernel
      have hl : raw20506step3Labels = raw20506step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20506step2 raw20506step2Labels permutation2 permutation3
    _ = mixedMoment B node621 node621Labels := by rfl

def raw20507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20507step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20507 raw20507Labels = mixedMoment B node1146 node1146Labels := by
  calc
    mixedMoment B raw20507 raw20507Labels = mixedMoment B raw20507step0 raw20507step0Labels := by
      have hz : ∀ j, raw20507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20507step0 = (fun i j => raw20507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20507step0 raw20507; decide +kernel
      have hl : raw20507step0Labels = raw20507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20507 raw20507Labels permutation434 hz
    mixedMoment B raw20507step0 raw20507step0Labels = mixedMoment B raw20507step1 raw20507step1Labels := by
      have hz : ∀ j, raw20507step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20507step1 = (fun i j => raw20507step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20507step1 raw20507step0; decide +kernel
      have hl : raw20507step1Labels = raw20507step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20507step0 raw20507step0Labels permutation80 hz
    mixedMoment B raw20507step1 raw20507step1Labels = mixedMoment B raw20507step2 raw20507step2Labels := by
      have ha : raw20507step2 = (fun i j => raw20507step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20507step2 raw20507step1; decide +kernel
      have hl : raw20507step2Labels = raw20507step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20507step1 raw20507step1Labels permutation8 permutation3
    _ = mixedMoment B node1146 node1146Labels := by rfl

def raw20508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20508step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20508 raw20508Labels = mixedMoment B node1146 node1146Labels := by
  calc
    mixedMoment B raw20508 raw20508Labels = mixedMoment B raw20508step0 raw20508step0Labels := by
      have hz : ∀ j, raw20508 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20508step0 = (fun i j => raw20508 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20508step0 raw20508; decide +kernel
      have hl : raw20508step0Labels = raw20508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20508 raw20508Labels permutation434 hz
    mixedMoment B raw20508step0 raw20508step0Labels = mixedMoment B raw20508step1 raw20508step1Labels := by
      have hz : ∀ j, raw20508step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20508step1 = (fun i j => raw20508step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20508step1 raw20508step0; decide +kernel
      have hl : raw20508step1Labels = raw20508step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20508step0 raw20508step0Labels permutation56 hz
    mixedMoment B raw20508step1 raw20508step1Labels = mixedMoment B raw20508step2 raw20508step2Labels := by
      have ha : raw20508step2 = (fun i j => raw20508step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20508step2 raw20508step1; decide +kernel
      have hl : raw20508step2Labels = raw20508step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20508step1 raw20508step1Labels permutation8 permutation3
    _ = mixedMoment B node1146 node1146Labels := by rfl

def raw20509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20509step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20509 raw20509Labels = mixedMoment B node1146 node1146Labels := by
  calc
    mixedMoment B raw20509 raw20509Labels = mixedMoment B raw20509step0 raw20509step0Labels := by
      have hz : ∀ j, raw20509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20509step0 = (fun i j => raw20509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20509step0 raw20509; decide +kernel
      have hl : raw20509step0Labels = raw20509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20509 raw20509Labels permutation346 hz
    mixedMoment B raw20509step0 raw20509step0Labels = mixedMoment B raw20509step1 raw20509step1Labels := by
      have hz : ∀ j, raw20509step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20509step1 = (fun i j => raw20509step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20509step1 raw20509step0; decide +kernel
      have hl : raw20509step1Labels = raw20509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20509step0 raw20509step0Labels permutation56 hz
    mixedMoment B raw20509step1 raw20509step1Labels = mixedMoment B raw20509step2 raw20509step2Labels := by
      have ha : raw20509step2 = (fun i j => raw20509step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20509step2 raw20509step1; decide +kernel
      have hl : raw20509step2Labels = raw20509step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20509step1 raw20509step1Labels permutation8 permutation3
    _ = mixedMoment B node1146 node1146Labels := by rfl

def raw20510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20510step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20510step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20510step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20510 raw20510Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw20510 raw20510Labels = mixedMoment B raw20510step0 raw20510step0Labels := by
      have hz : ∀ j, raw20510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20510step0 = (fun i j => raw20510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20510step0 raw20510; decide +kernel
      have hl : raw20510step0Labels = raw20510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20510 raw20510Labels permutation434 hz
    mixedMoment B raw20510step0 raw20510step0Labels = mixedMoment B raw20510step1 raw20510step1Labels := by
      have hz : ∀ j, raw20510step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20510step1 = (fun i j => raw20510step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20510step1 raw20510step0; decide +kernel
      have hl : raw20510step1Labels = raw20510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20510step0 raw20510step0Labels permutation80 hz
    mixedMoment B raw20510step1 raw20510step1Labels = mixedMoment B raw20510step2 raw20510step2Labels := by
      have hz : ∀ j, raw20510step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20510step2 = (fun i j => raw20510step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20510step2 raw20510step1; decide +kernel
      have hl : raw20510step2Labels = raw20510step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20510step1 raw20510step1Labels permutation14 hz
    mixedMoment B raw20510step2 raw20510step2Labels = mixedMoment B raw20510step3 raw20510step3Labels := by
      have ha : raw20510step3 = (fun i j => raw20510step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20510step3 raw20510step2; decide +kernel
      have hl : raw20510step3Labels = raw20510step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20510step2 raw20510step2Labels permutation2 permutation3
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw20511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20511step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20511step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20511step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20511step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20511step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20511 raw20511Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw20511 raw20511Labels = mixedMoment B raw20511step0 raw20511step0Labels := by
      have hz : ∀ j, raw20511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20511step0 = (fun i j => raw20511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20511step0 raw20511; decide +kernel
      have hl : raw20511step0Labels = raw20511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20511 raw20511Labels permutation434 hz
    mixedMoment B raw20511step0 raw20511step0Labels = mixedMoment B raw20511step1 raw20511step1Labels := by
      have hz : ∀ j, raw20511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20511step1 = (fun i j => raw20511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20511step1 raw20511step0; decide +kernel
      have hl : raw20511step1Labels = raw20511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20511step0 raw20511step0Labels permutation80 hz
    mixedMoment B raw20511step1 raw20511step1Labels = mixedMoment B raw20511step2 raw20511step2Labels := by
      have ha : raw20511step2 = (fun i j => raw20511step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20511step2 raw20511step1; decide +kernel
      have hl : raw20511step2Labels = raw20511step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20511step1 raw20511step1Labels permutation12 permutation5
    mixedMoment B raw20511step2 raw20511step2Labels = mixedMoment B raw20511step3 raw20511step3Labels := by
      have ha : raw20511step3 = -raw20511step2 := by apply Matrix.ext; change ∀ i j, raw20511step3 i j = -(raw20511step2 i j); unfold raw20511step3 raw20511step2; decide +kernel
      have hl : raw20511step3Labels = raw20511step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20511step3 raw20511step3Labels = mixedMoment B raw20511step4 raw20511step4Labels := by
      have ha : raw20511step4 = raw20511step3 := by apply Matrix.ext; unfold raw20511step4 raw20511step3; decide +kernel
      have hl : raw20511step3Labels = labelEmbedding1 ∘ raw20511step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20511step3 raw20511step3Labels raw20511step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

def raw20512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20512step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20512 raw20512Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20512 raw20512Labels = mixedMoment B raw20512step0 raw20512step0Labels := by
      have hz : ∀ j, raw20512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20512step0 = (fun i j => raw20512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20512step0 raw20512; decide +kernel
      have hl : raw20512step0Labels = raw20512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20512 raw20512Labels permutation434 hz
    mixedMoment B raw20512step0 raw20512step0Labels = mixedMoment B raw20512step1 raw20512step1Labels := by
      have ha : raw20512step1 = (fun i j => raw20512step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20512step1 raw20512step0; decide +kernel
      have hl : raw20512step1Labels = raw20512step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20512step0 raw20512step0Labels permutation137 permutation7
    mixedMoment B raw20512step1 raw20512step1Labels = mixedMoment B raw20512step2 raw20512step2Labels := by
      have ha : raw20512step2 = raw20512step1 := by apply Matrix.ext; unfold raw20512step2 raw20512step1; decide +kernel
      have hl : raw20512step1Labels = labelEmbedding1 ∘ raw20512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20512step1 raw20512step1Labels raw20512step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

def raw20513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20513step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20513step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20513 raw20513Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20513 raw20513Labels = mixedMoment B raw20513step0 raw20513step0Labels := by
      have hz : ∀ j, raw20513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20513step0 = (fun i j => raw20513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20513step0 raw20513; decide +kernel
      have hl : raw20513step0Labels = raw20513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20513 raw20513Labels permutation346 hz
    mixedMoment B raw20513step0 raw20513step0Labels = mixedMoment B raw20513step1 raw20513step1Labels := by
      have ha : raw20513step1 = (fun i j => raw20513step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20513step1 raw20513step0; decide +kernel
      have hl : raw20513step1Labels = raw20513step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20513step0 raw20513step0Labels permutation137 permutation7
    mixedMoment B raw20513step1 raw20513step1Labels = mixedMoment B raw20513step2 raw20513step2Labels := by
      have ha : raw20513step2 = raw20513step1 := by apply Matrix.ext; unfold raw20513step2 raw20513step1; decide +kernel
      have hl : raw20513step1Labels = labelEmbedding1 ∘ raw20513step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20513step1 raw20513step1Labels raw20513step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

def raw20514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20514step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20514step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20514step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20514step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20514 raw20514Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw20514 raw20514Labels = mixedMoment B raw20514step0 raw20514step0Labels := by
      have hz : ∀ j, raw20514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20514step0 = (fun i j => raw20514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20514step0 raw20514; decide +kernel
      have hl : raw20514step0Labels = raw20514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20514 raw20514Labels permutation434 hz
    mixedMoment B raw20514step0 raw20514step0Labels = mixedMoment B raw20514step1 raw20514step1Labels := by
      have hz : ∀ j, raw20514step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20514step1 = (fun i j => raw20514step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20514step1 raw20514step0; decide +kernel
      have hl : raw20514step1Labels = raw20514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20514step0 raw20514step0Labels permutation56 hz
    mixedMoment B raw20514step1 raw20514step1Labels = mixedMoment B raw20514step2 raw20514step2Labels := by
      have ha : raw20514step2 = (fun i j => raw20514step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20514step2 raw20514step1; decide +kernel
      have hl : raw20514step2Labels = raw20514step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20514step1 raw20514step1Labels permutation12 permutation5
    mixedMoment B raw20514step2 raw20514step2Labels = mixedMoment B raw20514step3 raw20514step3Labels := by
      have ha : raw20514step3 = -raw20514step2 := by apply Matrix.ext; change ∀ i j, raw20514step3 i j = -(raw20514step2 i j); unfold raw20514step3 raw20514step2; decide +kernel
      have hl : raw20514step3Labels = raw20514step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20514step3 raw20514step3Labels = mixedMoment B raw20514step4 raw20514step4Labels := by
      have ha : raw20514step4 = raw20514step3 := by apply Matrix.ext; unfold raw20514step4 raw20514step3; decide +kernel
      have hl : raw20514step3Labels = labelEmbedding1 ∘ raw20514step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20514step3 raw20514step3Labels raw20514step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

def raw20515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20515step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20515 raw20515Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20515 raw20515Labels = mixedMoment B raw20515step0 raw20515step0Labels := by
      have hz : ∀ j, raw20515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20515step0 = (fun i j => raw20515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20515step0 raw20515; decide +kernel
      have hl : raw20515step0Labels = raw20515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20515 raw20515Labels permutation434 hz
    mixedMoment B raw20515step0 raw20515step0Labels = mixedMoment B raw20515step1 raw20515step1Labels := by
      have ha : raw20515step1 = (fun i j => raw20515step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20515step1 raw20515step0; decide +kernel
      have hl : raw20515step1Labels = raw20515step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20515step0 raw20515step0Labels permutation143 permutation7
    mixedMoment B raw20515step1 raw20515step1Labels = mixedMoment B raw20515step2 raw20515step2Labels := by
      have ha : raw20515step2 = raw20515step1 := by apply Matrix.ext; unfold raw20515step2 raw20515step1; decide +kernel
      have hl : raw20515step1Labels = labelEmbedding1 ∘ raw20515step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20515step1 raw20515step1Labels raw20515step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

def raw20516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20516step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20516 raw20516Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20516 raw20516Labels = mixedMoment B raw20516step0 raw20516step0Labels := by
      have hz : ∀ j, raw20516 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20516step0 = (fun i j => raw20516 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20516step0 raw20516; decide +kernel
      have hl : raw20516step0Labels = raw20516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20516 raw20516Labels permutation265 hz
    mixedMoment B raw20516step0 raw20516step0Labels = mixedMoment B raw20516step1 raw20516step1Labels := by
      have ha : raw20516step1 = (fun i j => raw20516step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20516step1 raw20516step0; decide +kernel
      have hl : raw20516step1Labels = raw20516step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20516step0 raw20516step0Labels permutation137 permutation7
    mixedMoment B raw20516step1 raw20516step1Labels = mixedMoment B raw20516step2 raw20516step2Labels := by
      have ha : raw20516step2 = raw20516step1 := by apply Matrix.ext; unfold raw20516step2 raw20516step1; decide +kernel
      have hl : raw20516step1Labels = labelEmbedding1 ∘ raw20516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20516step1 raw20516step1Labels raw20516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

def raw20517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20517step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20517step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20517step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20517step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20517step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20517 raw20517Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw20517 raw20517Labels = mixedMoment B raw20517step0 raw20517step0Labels := by
      have hz : ∀ j, raw20517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20517step0 = (fun i j => raw20517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20517step0 raw20517; decide +kernel
      have hl : raw20517step0Labels = raw20517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20517 raw20517Labels permutation346 hz
    mixedMoment B raw20517step0 raw20517step0Labels = mixedMoment B raw20517step1 raw20517step1Labels := by
      have hz : ∀ j, raw20517step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20517step1 = (fun i j => raw20517step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20517step1 raw20517step0; decide +kernel
      have hl : raw20517step1Labels = raw20517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20517step0 raw20517step0Labels permutation56 hz
    mixedMoment B raw20517step1 raw20517step1Labels = mixedMoment B raw20517step2 raw20517step2Labels := by
      have ha : raw20517step2 = (fun i j => raw20517step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20517step2 raw20517step1; decide +kernel
      have hl : raw20517step2Labels = raw20517step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20517step1 raw20517step1Labels permutation12 permutation5
    mixedMoment B raw20517step2 raw20517step2Labels = mixedMoment B raw20517step3 raw20517step3Labels := by
      have ha : raw20517step3 = -raw20517step2 := by apply Matrix.ext; change ∀ i j, raw20517step3 i j = -(raw20517step2 i j); unfold raw20517step3 raw20517step2; decide +kernel
      have hl : raw20517step3Labels = raw20517step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20517step3 raw20517step3Labels = mixedMoment B raw20517step4 raw20517step4Labels := by
      have ha : raw20517step4 = raw20517step3 := by apply Matrix.ext; unfold raw20517step4 raw20517step3; decide +kernel
      have hl : raw20517step3Labels = labelEmbedding1 ∘ raw20517step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20517step3 raw20517step3Labels raw20517step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

def raw20518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20518 raw20518Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20518 raw20518Labels = mixedMoment B raw20518step0 raw20518step0Labels := by
      have hz : ∀ j, raw20518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20518step0 = (fun i j => raw20518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20518step0 raw20518; decide +kernel
      have hl : raw20518step0Labels = raw20518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20518 raw20518Labels permutation346 hz
    mixedMoment B raw20518step0 raw20518step0Labels = mixedMoment B raw20518step1 raw20518step1Labels := by
      have ha : raw20518step1 = (fun i j => raw20518step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20518step1 raw20518step0; decide +kernel
      have hl : raw20518step1Labels = raw20518step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20518step0 raw20518step0Labels permutation143 permutation7
    mixedMoment B raw20518step1 raw20518step1Labels = mixedMoment B raw20518step2 raw20518step2Labels := by
      have ha : raw20518step2 = raw20518step1 := by apply Matrix.ext; unfold raw20518step2 raw20518step1; decide +kernel
      have hl : raw20518step1Labels = labelEmbedding1 ∘ raw20518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20518step1 raw20518step1Labels raw20518step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

def raw20519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20519 raw20519Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20519 raw20519Labels = mixedMoment B raw20519step0 raw20519step0Labels := by
      have hz : ∀ j, raw20519 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20519step0 = (fun i j => raw20519 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20519step0 raw20519; decide +kernel
      have hl : raw20519step0Labels = raw20519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20519 raw20519Labels permutation265 hz
    mixedMoment B raw20519step0 raw20519step0Labels = mixedMoment B raw20519step1 raw20519step1Labels := by
      have ha : raw20519step1 = (fun i j => raw20519step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20519step1 raw20519step0; decide +kernel
      have hl : raw20519step1Labels = raw20519step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20519step0 raw20519step0Labels permutation143 permutation7
    mixedMoment B raw20519step1 raw20519step1Labels = mixedMoment B raw20519step2 raw20519step2Labels := by
      have ha : raw20519step2 = raw20519step1 := by apply Matrix.ext; unfold raw20519step2 raw20519step1; decide +kernel
      have hl : raw20519step1Labels = labelEmbedding1 ∘ raw20519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20519step1 raw20519step1Labels raw20519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

def raw20520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20520step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20520step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-3, 1, 2]]
def raw20520step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20520step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw20520step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20520step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw20520step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20520 raw20520Labels = mixedMoment B node1531 node1531Labels := by
  calc
    mixedMoment B raw20520 raw20520Labels = mixedMoment B raw20520step0 raw20520step0Labels := by
      have hz : ∀ j, raw20520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20520step0 = (fun i j => raw20520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20520step0 raw20520; decide +kernel
      have hl : raw20520step0Labels = raw20520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20520 raw20520Labels permutation434 hz
    mixedMoment B raw20520step0 raw20520step0Labels = mixedMoment B raw20520step1 raw20520step1Labels := by
      have hz : ∀ j, raw20520step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20520step1 = (fun i j => raw20520step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20520step1 raw20520step0; decide +kernel
      have hl : raw20520step1Labels = raw20520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20520step0 raw20520step0Labels permutation80 hz
    mixedMoment B raw20520step1 raw20520step1Labels = mixedMoment B raw20520step2 raw20520step2Labels := by
      have hz : ∀ j, raw20520step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20520step2 = (fun i j => raw20520step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20520step2 raw20520step1; decide +kernel
      have hl : raw20520step2Labels = raw20520step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20520step1 raw20520step1Labels permutation14 hz
    mixedMoment B raw20520step2 raw20520step2Labels = mixedMoment B raw20520step3 raw20520step3Labels := by
      have ha : raw20520step3 = (fun i j => raw20520step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20520step3 raw20520step2; decide +kernel
      have hl : raw20520step3Labels = raw20520step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20520step2 raw20520step2Labels permutation3 permutation5
    mixedMoment B raw20520step3 raw20520step3Labels = mixedMoment B raw20520step4 raw20520step4Labels := by
      have ha : raw20520step4 = -raw20520step3 := by apply Matrix.ext; change ∀ i j, raw20520step4 i j = -(raw20520step3 i j); unfold raw20520step4 raw20520step3; decide +kernel
      have hl : raw20520step4Labels = raw20520step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20520step4 raw20520step4Labels = mixedMoment B raw20520step5 raw20520step5Labels := by
      have ha : raw20520step5 = raw20520step4 := by apply Matrix.ext; unfold raw20520step5 raw20520step4; decide +kernel
      have hl : raw20520step4Labels = labelEmbedding1 ∘ raw20520step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20520step4 raw20520step4Labels raw20520step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1531 node1531Labels := by rfl

def raw20521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20521step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20521step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20521step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20521 raw20521Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw20521 raw20521Labels = mixedMoment B raw20521step0 raw20521step0Labels := by
      have hz : ∀ j, raw20521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20521step0 = (fun i j => raw20521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20521step0 raw20521; decide +kernel
      have hl : raw20521step0Labels = raw20521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20521 raw20521Labels permutation434 hz
    mixedMoment B raw20521step0 raw20521step0Labels = mixedMoment B raw20521step1 raw20521step1Labels := by
      have hz : ∀ j, raw20521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20521step1 = (fun i j => raw20521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20521step1 raw20521step0; decide +kernel
      have hl : raw20521step1Labels = raw20521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20521step0 raw20521step0Labels permutation80 hz
    mixedMoment B raw20521step1 raw20521step1Labels = mixedMoment B raw20521step2 raw20521step2Labels := by
      have ha : raw20521step2 = (fun i j => raw20521step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20521step2 raw20521step1; decide +kernel
      have hl : raw20521step2Labels = raw20521step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20521step1 raw20521step1Labels permutation29 permutation7
    mixedMoment B raw20521step2 raw20521step2Labels = mixedMoment B raw20521step3 raw20521step3Labels := by
      have ha : raw20521step3 = raw20521step2 := by apply Matrix.ext; unfold raw20521step3 raw20521step2; decide +kernel
      have hl : raw20521step2Labels = labelEmbedding1 ∘ raw20521step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20521step2 raw20521step2Labels raw20521step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2258 node2258Labels := by rfl

def raw20522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20522step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20522step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20522 raw20522Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw20522 raw20522Labels = mixedMoment B raw20522step0 raw20522step0Labels := by
      have hz : ∀ j, raw20522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20522step0 = (fun i j => raw20522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20522step0 raw20522; decide +kernel
      have hl : raw20522step0Labels = raw20522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20522 raw20522Labels permutation434 hz
    mixedMoment B raw20522step0 raw20522step0Labels = mixedMoment B raw20522step1 raw20522step1Labels := by
      have hz : ∀ j, raw20522step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20522step1 = (fun i j => raw20522step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20522step1 raw20522step0; decide +kernel
      have hl : raw20522step1Labels = raw20522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20522step0 raw20522step0Labels permutation56 hz
    mixedMoment B raw20522step1 raw20522step1Labels = mixedMoment B raw20522step2 raw20522step2Labels := by
      have ha : raw20522step2 = (fun i j => raw20522step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20522step2 raw20522step1; decide +kernel
      have hl : raw20522step2Labels = raw20522step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20522step1 raw20522step1Labels permutation29 permutation7
    mixedMoment B raw20522step2 raw20522step2Labels = mixedMoment B raw20522step3 raw20522step3Labels := by
      have ha : raw20522step3 = raw20522step2 := by apply Matrix.ext; unfold raw20522step3 raw20522step2; decide +kernel
      have hl : raw20522step2Labels = labelEmbedding1 ∘ raw20522step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20522step2 raw20522step2Labels raw20522step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2258 node2258Labels := by rfl

def raw20523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20523step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20523step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20523step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20523 raw20523Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw20523 raw20523Labels = mixedMoment B raw20523step0 raw20523step0Labels := by
      have hz : ∀ j, raw20523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20523step0 = (fun i j => raw20523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20523step0 raw20523; decide +kernel
      have hl : raw20523step0Labels = raw20523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20523 raw20523Labels permutation346 hz
    mixedMoment B raw20523step0 raw20523step0Labels = mixedMoment B raw20523step1 raw20523step1Labels := by
      have hz : ∀ j, raw20523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20523step1 = (fun i j => raw20523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20523step1 raw20523step0; decide +kernel
      have hl : raw20523step1Labels = raw20523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20523step0 raw20523step0Labels permutation56 hz
    mixedMoment B raw20523step1 raw20523step1Labels = mixedMoment B raw20523step2 raw20523step2Labels := by
      have ha : raw20523step2 = (fun i j => raw20523step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20523step2 raw20523step1; decide +kernel
      have hl : raw20523step2Labels = raw20523step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20523step1 raw20523step1Labels permutation29 permutation7
    mixedMoment B raw20523step2 raw20523step2Labels = mixedMoment B raw20523step3 raw20523step3Labels := by
      have ha : raw20523step3 = raw20523step2 := by apply Matrix.ext; unfold raw20523step3 raw20523step2; decide +kernel
      have hl : raw20523step2Labels = labelEmbedding1 ∘ raw20523step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20523step2 raw20523step2Labels raw20523step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2258 node2258Labels := by rfl

def raw20524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20524 raw20524Labels = mixedMoment B node639 node639Labels := by
  calc
    mixedMoment B raw20524 raw20524Labels = mixedMoment B raw20524step0 raw20524step0Labels := by
      have hz : ∀ j, raw20524 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20524step0 = (fun i j => raw20524 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20524step0 raw20524; decide +kernel
      have hl : raw20524step0Labels = raw20524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20524 raw20524Labels permutation434 hz
    mixedMoment B raw20524step0 raw20524step0Labels = mixedMoment B raw20524step1 raw20524step1Labels := by
      have hz : ∀ j, raw20524step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20524step1 = (fun i j => raw20524step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20524step1 raw20524step0; decide +kernel
      have hl : raw20524step1Labels = raw20524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20524step0 raw20524step0Labels permutation80 hz
    mixedMoment B raw20524step1 raw20524step1Labels = mixedMoment B raw20524step2 raw20524step2Labels := by
      have ha : raw20524step2 = (fun i j => raw20524step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20524step2 raw20524step1; decide +kernel
      have hl : raw20524step2Labels = raw20524step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20524step1 raw20524step1Labels permutation10 permutation2
    _ = mixedMoment B node639 node639Labels := by rfl

def raw20525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20525 raw20525Labels = mixedMoment B node639 node639Labels := by
  calc
    mixedMoment B raw20525 raw20525Labels = mixedMoment B raw20525step0 raw20525step0Labels := by
      have hz : ∀ j, raw20525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20525step0 = (fun i j => raw20525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20525step0 raw20525; decide +kernel
      have hl : raw20525step0Labels = raw20525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20525 raw20525Labels permutation434 hz
    mixedMoment B raw20525step0 raw20525step0Labels = mixedMoment B raw20525step1 raw20525step1Labels := by
      have hz : ∀ j, raw20525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20525step1 = (fun i j => raw20525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20525step1 raw20525step0; decide +kernel
      have hl : raw20525step1Labels = raw20525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20525step0 raw20525step0Labels permutation56 hz
    mixedMoment B raw20525step1 raw20525step1Labels = mixedMoment B raw20525step2 raw20525step2Labels := by
      have ha : raw20525step2 = (fun i j => raw20525step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20525step2 raw20525step1; decide +kernel
      have hl : raw20525step2Labels = raw20525step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20525step1 raw20525step1Labels permutation10 permutation2
    _ = mixedMoment B node639 node639Labels := by rfl

def raw20526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20526 raw20526Labels = mixedMoment B node639 node639Labels := by
  calc
    mixedMoment B raw20526 raw20526Labels = mixedMoment B raw20526step0 raw20526step0Labels := by
      have hz : ∀ j, raw20526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20526step0 = (fun i j => raw20526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20526step0 raw20526; decide +kernel
      have hl : raw20526step0Labels = raw20526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20526 raw20526Labels permutation346 hz
    mixedMoment B raw20526step0 raw20526step0Labels = mixedMoment B raw20526step1 raw20526step1Labels := by
      have hz : ∀ j, raw20526step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20526step1 = (fun i j => raw20526step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20526step1 raw20526step0; decide +kernel
      have hl : raw20526step1Labels = raw20526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20526step0 raw20526step0Labels permutation56 hz
    mixedMoment B raw20526step1 raw20526step1Labels = mixedMoment B raw20526step2 raw20526step2Labels := by
      have ha : raw20526step2 = (fun i j => raw20526step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20526step2 raw20526step1; decide +kernel
      have hl : raw20526step2Labels = raw20526step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20526step1 raw20526step1Labels permutation10 permutation2
    _ = mixedMoment B node639 node639Labels := by rfl

def raw20527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20527 raw20527Labels = mixedMoment B node654 node654Labels := by
  calc
    mixedMoment B raw20527 raw20527Labels = mixedMoment B raw20527step0 raw20527step0Labels := by
      have hz : ∀ j, raw20527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20527step0 = (fun i j => raw20527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20527step0 raw20527; decide +kernel
      have hl : raw20527step0Labels = raw20527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20527 raw20527Labels permutation434 hz
    mixedMoment B raw20527step0 raw20527step0Labels = mixedMoment B raw20527step1 raw20527step1Labels := by
      have hz : ∀ j, raw20527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20527step1 = (fun i j => raw20527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20527step1 raw20527step0; decide +kernel
      have hl : raw20527step1Labels = raw20527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20527step0 raw20527step0Labels permutation80 hz
    mixedMoment B raw20527step1 raw20527step1Labels = mixedMoment B raw20527step2 raw20527step2Labels := by
      have hz : ∀ j, raw20527step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20527step2 = (fun i j => raw20527step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20527step2 raw20527step1; decide +kernel
      have hl : raw20527step2Labels = raw20527step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20527step1 raw20527step1Labels permutation14 hz
    _ = mixedMoment B node654 node654Labels := by rfl

def raw20528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20528 raw20528Labels = mixedMoment B node1157 node1157Labels := by
  calc
    mixedMoment B raw20528 raw20528Labels = mixedMoment B raw20528step0 raw20528step0Labels := by
      have hz : ∀ j, raw20528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20528step0 = (fun i j => raw20528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20528step0 raw20528; decide +kernel
      have hl : raw20528step0Labels = raw20528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20528 raw20528Labels permutation434 hz
    mixedMoment B raw20528step0 raw20528step0Labels = mixedMoment B raw20528step1 raw20528step1Labels := by
      have ha : raw20528step1 = (fun i j => raw20528step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20528step1 raw20528step0; decide +kernel
      have hl : raw20528step1Labels = raw20528step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20528step0 raw20528step0Labels permutation40 permutation2
    _ = mixedMoment B node1157 node1157Labels := by rfl

def raw20529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20529 raw20529Labels = mixedMoment B node1157 node1157Labels := by
  calc
    mixedMoment B raw20529 raw20529Labels = mixedMoment B raw20529step0 raw20529step0Labels := by
      have hz : ∀ j, raw20529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20529step0 = (fun i j => raw20529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20529step0 raw20529; decide +kernel
      have hl : raw20529step0Labels = raw20529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20529 raw20529Labels permutation346 hz
    mixedMoment B raw20529step0 raw20529step0Labels = mixedMoment B raw20529step1 raw20529step1Labels := by
      have ha : raw20529step1 = (fun i j => raw20529step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20529step1 raw20529step0; decide +kernel
      have hl : raw20529step1Labels = raw20529step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20529step0 raw20529step0Labels permutation40 permutation2
    _ = mixedMoment B node1157 node1157Labels := by rfl

def raw20530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20530 raw20530Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw20530 raw20530Labels = mixedMoment B raw20530step0 raw20530step0Labels := by
      have hz : ∀ j, raw20530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20530step0 = (fun i j => raw20530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20530step0 raw20530; decide +kernel
      have hl : raw20530step0Labels = raw20530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20530 raw20530Labels permutation434 hz
    mixedMoment B raw20530step0 raw20530step0Labels = mixedMoment B raw20530step1 raw20530step1Labels := by
      have hz : ∀ j, raw20530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20530step1 = (fun i j => raw20530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20530step1 raw20530step0; decide +kernel
      have hl : raw20530step1Labels = raw20530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20530step0 raw20530step0Labels permutation80 hz
    mixedMoment B raw20530step1 raw20530step1Labels = mixedMoment B raw20530step2 raw20530step2Labels := by
      have ha : raw20530step2 = (fun i j => raw20530step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20530step2 raw20530step1; decide +kernel
      have hl : raw20530step2Labels = raw20530step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20530step1 raw20530step1Labels permutation10 permutation2
    _ = mixedMoment B node1292 node1292Labels := by rfl

def raw20531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20531 raw20531Labels = mixedMoment B node1157 node1157Labels := by
  calc
    mixedMoment B raw20531 raw20531Labels = mixedMoment B raw20531step0 raw20531step0Labels := by
      have hz : ∀ j, raw20531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20531step0 = (fun i j => raw20531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20531step0 raw20531; decide +kernel
      have hl : raw20531step0Labels = raw20531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20531 raw20531Labels permutation434 hz
    mixedMoment B raw20531step0 raw20531step0Labels = mixedMoment B raw20531step1 raw20531step1Labels := by
      have ha : raw20531step1 = (fun i j => raw20531step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20531step1 raw20531step0; decide +kernel
      have hl : raw20531step1Labels = raw20531step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20531step0 raw20531step0Labels permutation34 permutation2
    _ = mixedMoment B node1157 node1157Labels := by rfl

def raw20532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20532 raw20532Labels = mixedMoment B node1157 node1157Labels := by
  calc
    mixedMoment B raw20532 raw20532Labels = mixedMoment B raw20532step0 raw20532step0Labels := by
      have hz : ∀ j, raw20532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20532step0 = (fun i j => raw20532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20532step0 raw20532; decide +kernel
      have hl : raw20532step0Labels = raw20532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20532 raw20532Labels permutation346 hz
    mixedMoment B raw20532step0 raw20532step0Labels = mixedMoment B raw20532step1 raw20532step1Labels := by
      have ha : raw20532step1 = (fun i j => raw20532step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20532step1 raw20532step0; decide +kernel
      have hl : raw20532step1Labels = raw20532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20532step0 raw20532step0Labels permutation34 permutation2
    _ = mixedMoment B node1157 node1157Labels := by rfl

def raw20533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20533 raw20533Labels = mixedMoment B node1174 node1174Labels := by
  calc
    mixedMoment B raw20533 raw20533Labels = mixedMoment B raw20533step0 raw20533step0Labels := by
      have hz : ∀ j, raw20533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20533step0 = (fun i j => raw20533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20533step0 raw20533; decide +kernel
      have hl : raw20533step0Labels = raw20533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20533 raw20533Labels permutation434 hz
    mixedMoment B raw20533step0 raw20533step0Labels = mixedMoment B raw20533step1 raw20533step1Labels := by
      have hz : ∀ j, raw20533step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20533step1 = (fun i j => raw20533step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20533step1 raw20533step0; decide +kernel
      have hl : raw20533step1Labels = raw20533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20533step0 raw20533step0Labels permutation80 hz
    _ = mixedMoment B node1174 node1174Labels := by rfl

def raw20534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20534step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20534step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20534 raw20534Labels = mixedMoment B node4166 node4166Labels := by
  calc
    mixedMoment B raw20534 raw20534Labels = mixedMoment B raw20534step0 raw20534step0Labels := by
      have hz : ∀ j, raw20534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20534step0 = (fun i j => raw20534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20534step0 raw20534; decide +kernel
      have hl : raw20534step0Labels = raw20534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20534 raw20534Labels permutation434 hz
    mixedMoment B raw20534step0 raw20534step0Labels = mixedMoment B raw20534step1 raw20534step1Labels := by
      have hz : ∀ j, raw20534step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20534step1 = (fun i j => raw20534step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20534step1 raw20534step0; decide +kernel
      have hl : raw20534step1Labels = raw20534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20534step0 raw20534step0Labels permutation80 hz
    mixedMoment B raw20534step1 raw20534step1Labels = mixedMoment B raw20534step2 raw20534step2Labels := by
      have ha : raw20534step2 = (fun i j => raw20534step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20534step2 raw20534step1; decide +kernel
      have hl : raw20534step2Labels = raw20534step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20534step1 raw20534step1Labels permutation10 permutation3
    mixedMoment B raw20534step2 raw20534step2Labels = mixedMoment B raw20534step3 raw20534step3Labels := by
      have ha : raw20534step3 = raw20534step2 := by apply Matrix.ext; unfold raw20534step3 raw20534step2; decide +kernel
      have hl : raw20534step2Labels = labelEmbedding6 ∘ raw20534step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20534step2 raw20534step2Labels raw20534step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4166 node4166Labels := by rfl

def raw20535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20535step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20535 raw20535Labels = mixedMoment B node4538 node4538Labels := by
  calc
    mixedMoment B raw20535 raw20535Labels = mixedMoment B raw20535step0 raw20535step0Labels := by
      have hz : ∀ j, raw20535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20535step0 = (fun i j => raw20535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20535step0 raw20535; decide +kernel
      have hl : raw20535step0Labels = raw20535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20535 raw20535Labels permutation434 hz
    mixedMoment B raw20535step0 raw20535step0Labels = mixedMoment B raw20535step1 raw20535step1Labels := by
      have ha : raw20535step1 = (fun i j => raw20535step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20535step1 raw20535step0; decide +kernel
      have hl : raw20535step1Labels = raw20535step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20535step0 raw20535step0Labels permutation40 permutation3
    mixedMoment B raw20535step1 raw20535step1Labels = mixedMoment B raw20535step2 raw20535step2Labels := by
      have ha : raw20535step2 = raw20535step1 := by apply Matrix.ext; unfold raw20535step2 raw20535step1; decide +kernel
      have hl : raw20535step1Labels = labelEmbedding6 ∘ raw20535step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20535step1 raw20535step1Labels raw20535step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4538 node4538Labels := by rfl

def raw20536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20536step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20536step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20536 raw20536Labels = mixedMoment B node4538 node4538Labels := by
  calc
    mixedMoment B raw20536 raw20536Labels = mixedMoment B raw20536step0 raw20536step0Labels := by
      have hz : ∀ j, raw20536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20536step0 = (fun i j => raw20536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20536step0 raw20536; decide +kernel
      have hl : raw20536step0Labels = raw20536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20536 raw20536Labels permutation346 hz
    mixedMoment B raw20536step0 raw20536step0Labels = mixedMoment B raw20536step1 raw20536step1Labels := by
      have ha : raw20536step1 = (fun i j => raw20536step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20536step1 raw20536step0; decide +kernel
      have hl : raw20536step1Labels = raw20536step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20536step0 raw20536step0Labels permutation40 permutation3
    mixedMoment B raw20536step1 raw20536step1Labels = mixedMoment B raw20536step2 raw20536step2Labels := by
      have ha : raw20536step2 = raw20536step1 := by apply Matrix.ext; unfold raw20536step2 raw20536step1; decide +kernel
      have hl : raw20536step1Labels = labelEmbedding6 ∘ raw20536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20536step1 raw20536step1Labels raw20536step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4538 node4538Labels := by rfl

def raw20537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20537step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20537step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20537step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20537 raw20537Labels = mixedMoment B node4166 node4166Labels := by
  calc
    mixedMoment B raw20537 raw20537Labels = mixedMoment B raw20537step0 raw20537step0Labels := by
      have hz : ∀ j, raw20537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20537step0 = (fun i j => raw20537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20537step0 raw20537; decide +kernel
      have hl : raw20537step0Labels = raw20537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20537 raw20537Labels permutation434 hz
    mixedMoment B raw20537step0 raw20537step0Labels = mixedMoment B raw20537step1 raw20537step1Labels := by
      have hz : ∀ j, raw20537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20537step1 = (fun i j => raw20537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20537step1 raw20537step0; decide +kernel
      have hl : raw20537step1Labels = raw20537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20537step0 raw20537step0Labels permutation56 hz
    mixedMoment B raw20537step1 raw20537step1Labels = mixedMoment B raw20537step2 raw20537step2Labels := by
      have ha : raw20537step2 = (fun i j => raw20537step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20537step2 raw20537step1; decide +kernel
      have hl : raw20537step2Labels = raw20537step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20537step1 raw20537step1Labels permutation10 permutation3
    mixedMoment B raw20537step2 raw20537step2Labels = mixedMoment B raw20537step3 raw20537step3Labels := by
      have ha : raw20537step3 = raw20537step2 := by apply Matrix.ext; unfold raw20537step3 raw20537step2; decide +kernel
      have hl : raw20537step2Labels = labelEmbedding6 ∘ raw20537step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20537step2 raw20537step2Labels raw20537step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4166 node4166Labels := by rfl

def raw20538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20538step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20538step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20538 raw20538Labels = mixedMoment B node4538 node4538Labels := by
  calc
    mixedMoment B raw20538 raw20538Labels = mixedMoment B raw20538step0 raw20538step0Labels := by
      have hz : ∀ j, raw20538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20538step0 = (fun i j => raw20538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20538step0 raw20538; decide +kernel
      have hl : raw20538step0Labels = raw20538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20538 raw20538Labels permutation434 hz
    mixedMoment B raw20538step0 raw20538step0Labels = mixedMoment B raw20538step1 raw20538step1Labels := by
      have ha : raw20538step1 = (fun i j => raw20538step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20538step1 raw20538step0; decide +kernel
      have hl : raw20538step1Labels = raw20538step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20538step0 raw20538step0Labels permutation34 permutation3
    mixedMoment B raw20538step1 raw20538step1Labels = mixedMoment B raw20538step2 raw20538step2Labels := by
      have ha : raw20538step2 = raw20538step1 := by apply Matrix.ext; unfold raw20538step2 raw20538step1; decide +kernel
      have hl : raw20538step1Labels = labelEmbedding6 ∘ raw20538step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20538step1 raw20538step1Labels raw20538step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4538 node4538Labels := by rfl

def raw20539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20539step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20539 raw20539Labels = mixedMoment B node4538 node4538Labels := by
  calc
    mixedMoment B raw20539 raw20539Labels = mixedMoment B raw20539step0 raw20539step0Labels := by
      have hz : ∀ j, raw20539 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20539step0 = (fun i j => raw20539 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20539step0 raw20539; decide +kernel
      have hl : raw20539step0Labels = raw20539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20539 raw20539Labels permutation265 hz
    mixedMoment B raw20539step0 raw20539step0Labels = mixedMoment B raw20539step1 raw20539step1Labels := by
      have ha : raw20539step1 = (fun i j => raw20539step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20539step1 raw20539step0; decide +kernel
      have hl : raw20539step1Labels = raw20539step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20539step0 raw20539step0Labels permutation40 permutation3
    mixedMoment B raw20539step1 raw20539step1Labels = mixedMoment B raw20539step2 raw20539step2Labels := by
      have ha : raw20539step2 = raw20539step1 := by apply Matrix.ext; unfold raw20539step2 raw20539step1; decide +kernel
      have hl : raw20539step1Labels = labelEmbedding6 ∘ raw20539step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20539step1 raw20539step1Labels raw20539step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4538 node4538Labels := by rfl

def raw20540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20540step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20540step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20540step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20540 raw20540Labels = mixedMoment B node4166 node4166Labels := by
  calc
    mixedMoment B raw20540 raw20540Labels = mixedMoment B raw20540step0 raw20540step0Labels := by
      have hz : ∀ j, raw20540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20540step0 = (fun i j => raw20540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20540step0 raw20540; decide +kernel
      have hl : raw20540step0Labels = raw20540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20540 raw20540Labels permutation346 hz
    mixedMoment B raw20540step0 raw20540step0Labels = mixedMoment B raw20540step1 raw20540step1Labels := by
      have hz : ∀ j, raw20540step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20540step1 = (fun i j => raw20540step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20540step1 raw20540step0; decide +kernel
      have hl : raw20540step1Labels = raw20540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20540step0 raw20540step0Labels permutation56 hz
    mixedMoment B raw20540step1 raw20540step1Labels = mixedMoment B raw20540step2 raw20540step2Labels := by
      have ha : raw20540step2 = (fun i j => raw20540step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20540step2 raw20540step1; decide +kernel
      have hl : raw20540step2Labels = raw20540step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20540step1 raw20540step1Labels permutation10 permutation3
    mixedMoment B raw20540step2 raw20540step2Labels = mixedMoment B raw20540step3 raw20540step3Labels := by
      have ha : raw20540step3 = raw20540step2 := by apply Matrix.ext; unfold raw20540step3 raw20540step2; decide +kernel
      have hl : raw20540step2Labels = labelEmbedding6 ∘ raw20540step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20540step2 raw20540step2Labels raw20540step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4166 node4166Labels := by rfl

def raw20541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20541step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20541step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20541 raw20541Labels = mixedMoment B node4538 node4538Labels := by
  calc
    mixedMoment B raw20541 raw20541Labels = mixedMoment B raw20541step0 raw20541step0Labels := by
      have hz : ∀ j, raw20541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20541step0 = (fun i j => raw20541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20541step0 raw20541; decide +kernel
      have hl : raw20541step0Labels = raw20541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20541 raw20541Labels permutation346 hz
    mixedMoment B raw20541step0 raw20541step0Labels = mixedMoment B raw20541step1 raw20541step1Labels := by
      have ha : raw20541step1 = (fun i j => raw20541step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20541step1 raw20541step0; decide +kernel
      have hl : raw20541step1Labels = raw20541step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20541step0 raw20541step0Labels permutation34 permutation3
    mixedMoment B raw20541step1 raw20541step1Labels = mixedMoment B raw20541step2 raw20541step2Labels := by
      have ha : raw20541step2 = raw20541step1 := by apply Matrix.ext; unfold raw20541step2 raw20541step1; decide +kernel
      have hl : raw20541step1Labels = labelEmbedding6 ∘ raw20541step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20541step1 raw20541step1Labels raw20541step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4538 node4538Labels := by rfl

def raw20542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20542step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20542step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20542 raw20542Labels = mixedMoment B node4538 node4538Labels := by
  calc
    mixedMoment B raw20542 raw20542Labels = mixedMoment B raw20542step0 raw20542step0Labels := by
      have hz : ∀ j, raw20542 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20542step0 = (fun i j => raw20542 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20542step0 raw20542; decide +kernel
      have hl : raw20542step0Labels = raw20542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20542 raw20542Labels permutation265 hz
    mixedMoment B raw20542step0 raw20542step0Labels = mixedMoment B raw20542step1 raw20542step1Labels := by
      have ha : raw20542step1 = (fun i j => raw20542step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20542step1 raw20542step0; decide +kernel
      have hl : raw20542step1Labels = raw20542step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20542step0 raw20542step0Labels permutation34 permutation3
    mixedMoment B raw20542step1 raw20542step1Labels = mixedMoment B raw20542step2 raw20542step2Labels := by
      have ha : raw20542step2 = raw20542step1 := by apply Matrix.ext; unfold raw20542step2 raw20542step1; decide +kernel
      have hl : raw20542step1Labels = labelEmbedding6 ∘ raw20542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20542step1 raw20542step1Labels raw20542step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4538 node4538Labels := by rfl

def raw20543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw20543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw20543step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20543step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw20543step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20543 raw20543Labels = mixedMoment B node4190 node4190Labels := by
  calc
    mixedMoment B raw20543 raw20543Labels = mixedMoment B raw20543step0 raw20543step0Labels := by
      have hz : ∀ j, raw20543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20543step0 = (fun i j => raw20543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20543step0 raw20543; decide +kernel
      have hl : raw20543step0Labels = raw20543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20543 raw20543Labels permutation434 hz
    mixedMoment B raw20543step0 raw20543step0Labels = mixedMoment B raw20543step1 raw20543step1Labels := by
      have hz : ∀ j, raw20543step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20543step1 = (fun i j => raw20543step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20543step1 raw20543step0; decide +kernel
      have hl : raw20543step1Labels = raw20543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20543step0 raw20543step0Labels permutation80 hz
    mixedMoment B raw20543step1 raw20543step1Labels = mixedMoment B raw20543step2 raw20543step2Labels := by
      have hz : ∀ j, raw20543step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20543step2 = (fun i j => raw20543step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20543step2 raw20543step1; decide +kernel
      have hl : raw20543step2Labels = raw20543step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20543step1 raw20543step1Labels permutation14 hz
    mixedMoment B raw20543step2 raw20543step2Labels = mixedMoment B raw20543step3 raw20543step3Labels := by
      have ha : raw20543step3 = (fun i j => raw20543step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20543step3 raw20543step2; decide +kernel
      have hl : raw20543step3Labels = raw20543step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20543step2 raw20543step2Labels permutation2 permutation3
    mixedMoment B raw20543step3 raw20543step3Labels = mixedMoment B raw20543step4 raw20543step4Labels := by
      have ha : raw20543step4 = raw20543step3 := by apply Matrix.ext; unfold raw20543step4 raw20543step3; decide +kernel
      have hl : raw20543step3Labels = labelEmbedding6 ∘ raw20543step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20543step3 raw20543step3Labels raw20543step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4190 node4190Labels := by rfl

def raw20544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20544step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20544step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20544step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20544 raw20544Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw20544 raw20544Labels = mixedMoment B raw20544step0 raw20544step0Labels := by
      have hz : ∀ j, raw20544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20544step0 = (fun i j => raw20544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20544step0 raw20544; decide +kernel
      have hl : raw20544step0Labels = raw20544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20544 raw20544Labels permutation434 hz
    mixedMoment B raw20544step0 raw20544step0Labels = mixedMoment B raw20544step1 raw20544step1Labels := by
      have hz : ∀ j, raw20544step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20544step1 = (fun i j => raw20544step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20544step1 raw20544step0; decide +kernel
      have hl : raw20544step1Labels = raw20544step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20544step0 raw20544step0Labels permutation80 hz
    mixedMoment B raw20544step1 raw20544step1Labels = mixedMoment B raw20544step2 raw20544step2Labels := by
      have ha : raw20544step2 = (fun i j => raw20544step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20544step2 raw20544step1; decide +kernel
      have hl : raw20544step2Labels = raw20544step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20544step1 raw20544step1Labels permutation8 permutation3
    mixedMoment B raw20544step2 raw20544step2Labels = mixedMoment B raw20544step3 raw20544step3Labels := by
      have ha : raw20544step3 = raw20544step2 := by apply Matrix.ext; unfold raw20544step3 raw20544step2; decide +kernel
      have hl : raw20544step2Labels = labelEmbedding6 ∘ raw20544step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20544step2 raw20544step2Labels raw20544step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4557 node4557Labels := by rfl

def raw20545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20545step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20545step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20545 raw20545Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw20545 raw20545Labels = mixedMoment B raw20545step0 raw20545step0Labels := by
      have hz : ∀ j, raw20545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20545step0 = (fun i j => raw20545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20545step0 raw20545; decide +kernel
      have hl : raw20545step0Labels = raw20545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20545 raw20545Labels permutation434 hz
    mixedMoment B raw20545step0 raw20545step0Labels = mixedMoment B raw20545step1 raw20545step1Labels := by
      have hz : ∀ j, raw20545step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20545step1 = (fun i j => raw20545step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20545step1 raw20545step0; decide +kernel
      have hl : raw20545step1Labels = raw20545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20545step0 raw20545step0Labels permutation56 hz
    mixedMoment B raw20545step1 raw20545step1Labels = mixedMoment B raw20545step2 raw20545step2Labels := by
      have ha : raw20545step2 = (fun i j => raw20545step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20545step2 raw20545step1; decide +kernel
      have hl : raw20545step2Labels = raw20545step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20545step1 raw20545step1Labels permutation8 permutation3
    mixedMoment B raw20545step2 raw20545step2Labels = mixedMoment B raw20545step3 raw20545step3Labels := by
      have ha : raw20545step3 = raw20545step2 := by apply Matrix.ext; unfold raw20545step3 raw20545step2; decide +kernel
      have hl : raw20545step2Labels = labelEmbedding6 ∘ raw20545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20545step2 raw20545step2Labels raw20545step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4557 node4557Labels := by rfl

def raw20546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20546step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20546step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20546 raw20546Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw20546 raw20546Labels = mixedMoment B raw20546step0 raw20546step0Labels := by
      have hz : ∀ j, raw20546 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20546step0 = (fun i j => raw20546 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20546step0 raw20546; decide +kernel
      have hl : raw20546step0Labels = raw20546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20546 raw20546Labels permutation346 hz
    mixedMoment B raw20546step0 raw20546step0Labels = mixedMoment B raw20546step1 raw20546step1Labels := by
      have hz : ∀ j, raw20546step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20546step1 = (fun i j => raw20546step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20546step1 raw20546step0; decide +kernel
      have hl : raw20546step1Labels = raw20546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20546step0 raw20546step0Labels permutation56 hz
    mixedMoment B raw20546step1 raw20546step1Labels = mixedMoment B raw20546step2 raw20546step2Labels := by
      have ha : raw20546step2 = (fun i j => raw20546step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20546step2 raw20546step1; decide +kernel
      have hl : raw20546step2Labels = raw20546step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20546step1 raw20546step1Labels permutation8 permutation3
    mixedMoment B raw20546step2 raw20546step2Labels = mixedMoment B raw20546step3 raw20546step3Labels := by
      have ha : raw20546step3 = raw20546step2 := by apply Matrix.ext; unfold raw20546step3 raw20546step2; decide +kernel
      have hl : raw20546step2Labels = labelEmbedding6 ∘ raw20546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20546step2 raw20546step2Labels raw20546step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4557 node4557Labels := by rfl

def raw20547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 1, -2], ![4, -4, 0]]
def raw20547step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20547step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20547step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20547step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20547 raw20547Labels = mixedMoment B node4168 node4168Labels := by
  calc
    mixedMoment B raw20547 raw20547Labels = mixedMoment B raw20547step0 raw20547step0Labels := by
      have hz : ∀ j, raw20547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20547step0 = (fun i j => raw20547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20547step0 raw20547; decide +kernel
      have hl : raw20547step0Labels = raw20547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20547 raw20547Labels permutation434 hz
    mixedMoment B raw20547step0 raw20547step0Labels = mixedMoment B raw20547step1 raw20547step1Labels := by
      have hz : ∀ j, raw20547step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20547step1 = (fun i j => raw20547step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20547step1 raw20547step0; decide +kernel
      have hl : raw20547step1Labels = raw20547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20547step0 raw20547step0Labels permutation80 hz
    mixedMoment B raw20547step1 raw20547step1Labels = mixedMoment B raw20547step2 raw20547step2Labels := by
      have hz : ∀ j, raw20547step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20547step2 = (fun i j => raw20547step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20547step2 raw20547step1; decide +kernel
      have hl : raw20547step2Labels = raw20547step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20547step1 raw20547step1Labels permutation14 hz
    mixedMoment B raw20547step2 raw20547step2Labels = mixedMoment B raw20547step3 raw20547step3Labels := by
      have ha : raw20547step3 = (fun i j => raw20547step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20547step3 raw20547step2; decide +kernel
      have hl : raw20547step3Labels = raw20547step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20547step2 raw20547step2Labels permutation2 permutation3
    mixedMoment B raw20547step3 raw20547step3Labels = mixedMoment B raw20547step4 raw20547step4Labels := by
      have ha : raw20547step4 = raw20547step3 := by apply Matrix.ext; unfold raw20547step4 raw20547step3; decide +kernel
      have hl : raw20547step3Labels = labelEmbedding6 ∘ raw20547step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20547step3 raw20547step3Labels raw20547step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4168 node4168Labels := by rfl

def raw20548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20548step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20548step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20548step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20548step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20548step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20548 raw20548Labels = mixedMoment B node4240 node4240Labels := by
  calc
    mixedMoment B raw20548 raw20548Labels = mixedMoment B raw20548step0 raw20548step0Labels := by
      have hz : ∀ j, raw20548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20548step0 = (fun i j => raw20548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20548step0 raw20548; decide +kernel
      have hl : raw20548step0Labels = raw20548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20548 raw20548Labels permutation434 hz
    mixedMoment B raw20548step0 raw20548step0Labels = mixedMoment B raw20548step1 raw20548step1Labels := by
      have hz : ∀ j, raw20548step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20548step1 = (fun i j => raw20548step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20548step1 raw20548step0; decide +kernel
      have hl : raw20548step1Labels = raw20548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20548step0 raw20548step0Labels permutation80 hz
    mixedMoment B raw20548step1 raw20548step1Labels = mixedMoment B raw20548step2 raw20548step2Labels := by
      have ha : raw20548step2 = (fun i j => raw20548step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20548step2 raw20548step1; decide +kernel
      have hl : raw20548step2Labels = raw20548step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20548step1 raw20548step1Labels permutation31 permutation3
    mixedMoment B raw20548step2 raw20548step2Labels = mixedMoment B raw20548step3 raw20548step3Labels := by
      have ha : raw20548step3 = -raw20548step2 := by apply Matrix.ext; change ∀ i j, raw20548step3 i j = -(raw20548step2 i j); unfold raw20548step3 raw20548step2; decide +kernel
      have hl : raw20548step3Labels = raw20548step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20548step3 raw20548step3Labels = mixedMoment B raw20548step4 raw20548step4Labels := by
      have ha : raw20548step4 = raw20548step3 := by apply Matrix.ext; unfold raw20548step4 raw20548step3; decide +kernel
      have hl : raw20548step3Labels = labelEmbedding6 ∘ raw20548step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20548step3 raw20548step3Labels raw20548step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4240 node4240Labels := by rfl

def raw20549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20549step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20549step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20549step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20549step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20549step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20549 raw20549Labels = mixedMoment B node4240 node4240Labels := by
  calc
    mixedMoment B raw20549 raw20549Labels = mixedMoment B raw20549step0 raw20549step0Labels := by
      have hz : ∀ j, raw20549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20549step0 = (fun i j => raw20549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20549step0 raw20549; decide +kernel
      have hl : raw20549step0Labels = raw20549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20549 raw20549Labels permutation434 hz
    mixedMoment B raw20549step0 raw20549step0Labels = mixedMoment B raw20549step1 raw20549step1Labels := by
      have hz : ∀ j, raw20549step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20549step1 = (fun i j => raw20549step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20549step1 raw20549step0; decide +kernel
      have hl : raw20549step1Labels = raw20549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20549step0 raw20549step0Labels permutation56 hz
    mixedMoment B raw20549step1 raw20549step1Labels = mixedMoment B raw20549step2 raw20549step2Labels := by
      have ha : raw20549step2 = (fun i j => raw20549step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20549step2 raw20549step1; decide +kernel
      have hl : raw20549step2Labels = raw20549step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20549step1 raw20549step1Labels permutation31 permutation3
    mixedMoment B raw20549step2 raw20549step2Labels = mixedMoment B raw20549step3 raw20549step3Labels := by
      have ha : raw20549step3 = -raw20549step2 := by apply Matrix.ext; change ∀ i j, raw20549step3 i j = -(raw20549step2 i j); unfold raw20549step3 raw20549step2; decide +kernel
      have hl : raw20549step3Labels = raw20549step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20549step3 raw20549step3Labels = mixedMoment B raw20549step4 raw20549step4Labels := by
      have ha : raw20549step4 = raw20549step3 := by apply Matrix.ext; unfold raw20549step4 raw20549step3; decide +kernel
      have hl : raw20549step3Labels = labelEmbedding6 ∘ raw20549step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20549step3 raw20549step3Labels raw20549step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4240 node4240Labels := by rfl

def raw20550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20550step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20550step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20550step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20550step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20550 raw20550Labels = mixedMoment B node4240 node4240Labels := by
  calc
    mixedMoment B raw20550 raw20550Labels = mixedMoment B raw20550step0 raw20550step0Labels := by
      have hz : ∀ j, raw20550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20550step0 = (fun i j => raw20550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20550step0 raw20550; decide +kernel
      have hl : raw20550step0Labels = raw20550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20550 raw20550Labels permutation346 hz
    mixedMoment B raw20550step0 raw20550step0Labels = mixedMoment B raw20550step1 raw20550step1Labels := by
      have hz : ∀ j, raw20550step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20550step1 = (fun i j => raw20550step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20550step1 raw20550step0; decide +kernel
      have hl : raw20550step1Labels = raw20550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20550step0 raw20550step0Labels permutation56 hz
    mixedMoment B raw20550step1 raw20550step1Labels = mixedMoment B raw20550step2 raw20550step2Labels := by
      have ha : raw20550step2 = (fun i j => raw20550step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20550step2 raw20550step1; decide +kernel
      have hl : raw20550step2Labels = raw20550step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20550step1 raw20550step1Labels permutation31 permutation3
    mixedMoment B raw20550step2 raw20550step2Labels = mixedMoment B raw20550step3 raw20550step3Labels := by
      have ha : raw20550step3 = -raw20550step2 := by apply Matrix.ext; change ∀ i j, raw20550step3 i j = -(raw20550step2 i j); unfold raw20550step3 raw20550step2; decide +kernel
      have hl : raw20550step3Labels = raw20550step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20550step3 raw20550step3Labels = mixedMoment B raw20550step4 raw20550step4Labels := by
      have ha : raw20550step4 = raw20550step3 := by apply Matrix.ext; unfold raw20550step4 raw20550step3; decide +kernel
      have hl : raw20550step3Labels = labelEmbedding6 ∘ raw20550step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20550step3 raw20550step3Labels raw20550step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4240 node4240Labels := by rfl

def raw20551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20551 raw20551Labels = mixedMoment B node594 node594Labels := by
  calc
    mixedMoment B raw20551 raw20551Labels = mixedMoment B raw20551step0 raw20551step0Labels := by
      have hz : ∀ j, raw20551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20551step0 = (fun i j => raw20551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20551step0 raw20551; decide +kernel
      have hl : raw20551step0Labels = raw20551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20551 raw20551Labels permutation434 hz
    mixedMoment B raw20551step0 raw20551step0Labels = mixedMoment B raw20551step1 raw20551step1Labels := by
      have hz : ∀ j, raw20551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20551step1 = (fun i j => raw20551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20551step1 raw20551step0; decide +kernel
      have hl : raw20551step1Labels = raw20551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20551step0 raw20551step0Labels permutation80 hz
    mixedMoment B raw20551step1 raw20551step1Labels = mixedMoment B raw20551step2 raw20551step2Labels := by
      have ha : raw20551step2 = (fun i j => raw20551step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20551step2 raw20551step1; decide +kernel
      have hl : raw20551step2Labels = raw20551step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20551step1 raw20551step1Labels permutation10 permutation3
    _ = mixedMoment B node594 node594Labels := by rfl

def raw20552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20552 raw20552Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw20552 raw20552Labels = mixedMoment B raw20552step0 raw20552step0Labels := by
      have hz : ∀ j, raw20552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20552step0 = (fun i j => raw20552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20552step0 raw20552; decide +kernel
      have hl : raw20552step0Labels = raw20552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20552 raw20552Labels permutation434 hz
    mixedMoment B raw20552step0 raw20552step0Labels = mixedMoment B raw20552step1 raw20552step1Labels := by
      have ha : raw20552step1 = (fun i j => raw20552step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20552step1 raw20552step0; decide +kernel
      have hl : raw20552step1Labels = raw20552step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20552step0 raw20552step0Labels permutation40 permutation3
    _ = mixedMoment B node1123 node1123Labels := by rfl

def raw20553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20553 raw20553Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw20553 raw20553Labels = mixedMoment B raw20553step0 raw20553step0Labels := by
      have hz : ∀ j, raw20553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20553step0 = (fun i j => raw20553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20553step0 raw20553; decide +kernel
      have hl : raw20553step0Labels = raw20553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20553 raw20553Labels permutation346 hz
    mixedMoment B raw20553step0 raw20553step0Labels = mixedMoment B raw20553step1 raw20553step1Labels := by
      have ha : raw20553step1 = (fun i j => raw20553step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20553step1 raw20553step0; decide +kernel
      have hl : raw20553step1Labels = raw20553step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20553step0 raw20553step0Labels permutation40 permutation3
    _ = mixedMoment B node1123 node1123Labels := by rfl

def raw20554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20554step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20554 raw20554Labels = mixedMoment B node594 node594Labels := by
  calc
    mixedMoment B raw20554 raw20554Labels = mixedMoment B raw20554step0 raw20554step0Labels := by
      have hz : ∀ j, raw20554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20554step0 = (fun i j => raw20554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20554step0 raw20554; decide +kernel
      have hl : raw20554step0Labels = raw20554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20554 raw20554Labels permutation434 hz
    mixedMoment B raw20554step0 raw20554step0Labels = mixedMoment B raw20554step1 raw20554step1Labels := by
      have hz : ∀ j, raw20554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20554step1 = (fun i j => raw20554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20554step1 raw20554step0; decide +kernel
      have hl : raw20554step1Labels = raw20554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20554step0 raw20554step0Labels permutation56 hz
    mixedMoment B raw20554step1 raw20554step1Labels = mixedMoment B raw20554step2 raw20554step2Labels := by
      have ha : raw20554step2 = (fun i j => raw20554step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20554step2 raw20554step1; decide +kernel
      have hl : raw20554step2Labels = raw20554step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20554step1 raw20554step1Labels permutation10 permutation3
    _ = mixedMoment B node594 node594Labels := by rfl

def raw20555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20555 raw20555Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw20555 raw20555Labels = mixedMoment B raw20555step0 raw20555step0Labels := by
      have hz : ∀ j, raw20555 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20555step0 = (fun i j => raw20555 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20555step0 raw20555; decide +kernel
      have hl : raw20555step0Labels = raw20555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20555 raw20555Labels permutation434 hz
    mixedMoment B raw20555step0 raw20555step0Labels = mixedMoment B raw20555step1 raw20555step1Labels := by
      have ha : raw20555step1 = (fun i j => raw20555step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20555step1 raw20555step0; decide +kernel
      have hl : raw20555step1Labels = raw20555step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20555step0 raw20555step0Labels permutation34 permutation3
    _ = mixedMoment B node1123 node1123Labels := by rfl

def raw20556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20556 raw20556Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw20556 raw20556Labels = mixedMoment B raw20556step0 raw20556step0Labels := by
      have hz : ∀ j, raw20556 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20556step0 = (fun i j => raw20556 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20556step0 raw20556; decide +kernel
      have hl : raw20556step0Labels = raw20556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20556 raw20556Labels permutation265 hz
    mixedMoment B raw20556step0 raw20556step0Labels = mixedMoment B raw20556step1 raw20556step1Labels := by
      have ha : raw20556step1 = (fun i j => raw20556step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20556step1 raw20556step0; decide +kernel
      have hl : raw20556step1Labels = raw20556step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20556step0 raw20556step0Labels permutation40 permutation3
    _ = mixedMoment B node1123 node1123Labels := by rfl

def raw20557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20557step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20557step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20557 raw20557Labels = mixedMoment B node594 node594Labels := by
  calc
    mixedMoment B raw20557 raw20557Labels = mixedMoment B raw20557step0 raw20557step0Labels := by
      have hz : ∀ j, raw20557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20557step0 = (fun i j => raw20557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20557step0 raw20557; decide +kernel
      have hl : raw20557step0Labels = raw20557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20557 raw20557Labels permutation346 hz
    mixedMoment B raw20557step0 raw20557step0Labels = mixedMoment B raw20557step1 raw20557step1Labels := by
      have hz : ∀ j, raw20557step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20557step1 = (fun i j => raw20557step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20557step1 raw20557step0; decide +kernel
      have hl : raw20557step1Labels = raw20557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20557step0 raw20557step0Labels permutation56 hz
    mixedMoment B raw20557step1 raw20557step1Labels = mixedMoment B raw20557step2 raw20557step2Labels := by
      have ha : raw20557step2 = (fun i j => raw20557step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20557step2 raw20557step1; decide +kernel
      have hl : raw20557step2Labels = raw20557step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20557step1 raw20557step1Labels permutation10 permutation3
    _ = mixedMoment B node594 node594Labels := by rfl

def raw20558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20558 raw20558Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw20558 raw20558Labels = mixedMoment B raw20558step0 raw20558step0Labels := by
      have hz : ∀ j, raw20558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20558step0 = (fun i j => raw20558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20558step0 raw20558; decide +kernel
      have hl : raw20558step0Labels = raw20558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20558 raw20558Labels permutation346 hz
    mixedMoment B raw20558step0 raw20558step0Labels = mixedMoment B raw20558step1 raw20558step1Labels := by
      have ha : raw20558step1 = (fun i j => raw20558step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20558step1 raw20558step0; decide +kernel
      have hl : raw20558step1Labels = raw20558step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20558step0 raw20558step0Labels permutation34 permutation3
    _ = mixedMoment B node1123 node1123Labels := by rfl

def raw20559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20559 raw20559Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw20559 raw20559Labels = mixedMoment B raw20559step0 raw20559step0Labels := by
      have hz : ∀ j, raw20559 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20559step0 = (fun i j => raw20559 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20559step0 raw20559; decide +kernel
      have hl : raw20559step0Labels = raw20559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20559 raw20559Labels permutation265 hz
    mixedMoment B raw20559step0 raw20559step0Labels = mixedMoment B raw20559step1 raw20559step1Labels := by
      have ha : raw20559step1 = (fun i j => raw20559step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20559step1 raw20559step0; decide +kernel
      have hl : raw20559step1Labels = raw20559step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20559step0 raw20559step0Labels permutation34 permutation3
    _ = mixedMoment B node1123 node1123Labels := by rfl

def raw20560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20560step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw20560step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw20560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20560 raw20560Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw20560 raw20560Labels = mixedMoment B raw20560step0 raw20560step0Labels := by
      have hz : ∀ j, raw20560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20560step0 = (fun i j => raw20560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20560step0 raw20560; decide +kernel
      have hl : raw20560step0Labels = raw20560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20560 raw20560Labels permutation434 hz
    mixedMoment B raw20560step0 raw20560step0Labels = mixedMoment B raw20560step1 raw20560step1Labels := by
      have hz : ∀ j, raw20560step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20560step1 = (fun i j => raw20560step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20560step1 raw20560step0; decide +kernel
      have hl : raw20560step1Labels = raw20560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20560step0 raw20560step0Labels permutation80 hz
    mixedMoment B raw20560step1 raw20560step1Labels = mixedMoment B raw20560step2 raw20560step2Labels := by
      have hz : ∀ j, raw20560step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20560step2 = (fun i j => raw20560step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20560step2 raw20560step1; decide +kernel
      have hl : raw20560step2Labels = raw20560step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20560step1 raw20560step1Labels permutation14 hz
    mixedMoment B raw20560step2 raw20560step2Labels = mixedMoment B raw20560step3 raw20560step3Labels := by
      have ha : raw20560step3 = (fun i j => raw20560step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20560step3 raw20560step2; decide +kernel
      have hl : raw20560step3Labels = raw20560step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20560step2 raw20560step2Labels permutation2 permutation3
    _ = mixedMoment B node618 node618Labels := by rfl

def raw20561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20561step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20561 raw20561Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw20561 raw20561Labels = mixedMoment B raw20561step0 raw20561step0Labels := by
      have hz : ∀ j, raw20561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20561step0 = (fun i j => raw20561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20561step0 raw20561; decide +kernel
      have hl : raw20561step0Labels = raw20561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20561 raw20561Labels permutation434 hz
    mixedMoment B raw20561step0 raw20561step0Labels = mixedMoment B raw20561step1 raw20561step1Labels := by
      have hz : ∀ j, raw20561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20561step1 = (fun i j => raw20561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20561step1 raw20561step0; decide +kernel
      have hl : raw20561step1Labels = raw20561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20561step0 raw20561step0Labels permutation80 hz
    mixedMoment B raw20561step1 raw20561step1Labels = mixedMoment B raw20561step2 raw20561step2Labels := by
      have ha : raw20561step2 = (fun i j => raw20561step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20561step2 raw20561step1; decide +kernel
      have hl : raw20561step2Labels = raw20561step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20561step1 raw20561step1Labels permutation8 permutation3
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw20562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20562step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20562 raw20562Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw20562 raw20562Labels = mixedMoment B raw20562step0 raw20562step0Labels := by
      have hz : ∀ j, raw20562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20562step0 = (fun i j => raw20562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20562step0 raw20562; decide +kernel
      have hl : raw20562step0Labels = raw20562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20562 raw20562Labels permutation434 hz
    mixedMoment B raw20562step0 raw20562step0Labels = mixedMoment B raw20562step1 raw20562step1Labels := by
      have hz : ∀ j, raw20562step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20562step1 = (fun i j => raw20562step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20562step1 raw20562step0; decide +kernel
      have hl : raw20562step1Labels = raw20562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20562step0 raw20562step0Labels permutation56 hz
    mixedMoment B raw20562step1 raw20562step1Labels = mixedMoment B raw20562step2 raw20562step2Labels := by
      have ha : raw20562step2 = (fun i j => raw20562step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20562step2 raw20562step1; decide +kernel
      have hl : raw20562step2Labels = raw20562step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20562step1 raw20562step1Labels permutation8 permutation3
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw20563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20563step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20563 raw20563Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw20563 raw20563Labels = mixedMoment B raw20563step0 raw20563step0Labels := by
      have hz : ∀ j, raw20563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20563step0 = (fun i j => raw20563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20563step0 raw20563; decide +kernel
      have hl : raw20563step0Labels = raw20563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20563 raw20563Labels permutation346 hz
    mixedMoment B raw20563step0 raw20563step0Labels = mixedMoment B raw20563step1 raw20563step1Labels := by
      have hz : ∀ j, raw20563step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20563step1 = (fun i j => raw20563step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20563step1 raw20563step0; decide +kernel
      have hl : raw20563step1Labels = raw20563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20563step0 raw20563step0Labels permutation56 hz
    mixedMoment B raw20563step1 raw20563step1Labels = mixedMoment B raw20563step2 raw20563step2Labels := by
      have ha : raw20563step2 = (fun i j => raw20563step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20563step2 raw20563step1; decide +kernel
      have hl : raw20563step2Labels = raw20563step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20563step1 raw20563step1Labels permutation8 permutation3
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw20564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20564step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 1, -2], ![4, -4, 0]]
def raw20564step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20564 raw20564Labels = mixedMoment B node596 node596Labels := by
  calc
    mixedMoment B raw20564 raw20564Labels = mixedMoment B raw20564step0 raw20564step0Labels := by
      have hz : ∀ j, raw20564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20564step0 = (fun i j => raw20564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20564step0 raw20564; decide +kernel
      have hl : raw20564step0Labels = raw20564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20564 raw20564Labels permutation434 hz
    mixedMoment B raw20564step0 raw20564step0Labels = mixedMoment B raw20564step1 raw20564step1Labels := by
      have hz : ∀ j, raw20564step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20564step1 = (fun i j => raw20564step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20564step1 raw20564step0; decide +kernel
      have hl : raw20564step1Labels = raw20564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20564step0 raw20564step0Labels permutation80 hz
    mixedMoment B raw20564step1 raw20564step1Labels = mixedMoment B raw20564step2 raw20564step2Labels := by
      have hz : ∀ j, raw20564step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20564step2 = (fun i j => raw20564step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20564step2 raw20564step1; decide +kernel
      have hl : raw20564step2Labels = raw20564step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20564step1 raw20564step1Labels permutation14 hz
    mixedMoment B raw20564step2 raw20564step2Labels = mixedMoment B raw20564step3 raw20564step3Labels := by
      have ha : raw20564step3 = (fun i j => raw20564step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20564step3 raw20564step2; decide +kernel
      have hl : raw20564step3Labels = raw20564step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20564step2 raw20564step2Labels permutation2 permutation3
    _ = mixedMoment B node596 node596Labels := by rfl

def raw20565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20565step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20565step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20565 raw20565Labels = mixedMoment B node740 node740Labels := by
  calc
    mixedMoment B raw20565 raw20565Labels = mixedMoment B raw20565step0 raw20565step0Labels := by
      have hz : ∀ j, raw20565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20565step0 = (fun i j => raw20565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20565step0 raw20565; decide +kernel
      have hl : raw20565step0Labels = raw20565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20565 raw20565Labels permutation434 hz
    mixedMoment B raw20565step0 raw20565step0Labels = mixedMoment B raw20565step1 raw20565step1Labels := by
      have hz : ∀ j, raw20565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20565step1 = (fun i j => raw20565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20565step1 raw20565step0; decide +kernel
      have hl : raw20565step1Labels = raw20565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20565step0 raw20565step0Labels permutation80 hz
    mixedMoment B raw20565step1 raw20565step1Labels = mixedMoment B raw20565step2 raw20565step2Labels := by
      have ha : raw20565step2 = (fun i j => raw20565step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20565step2 raw20565step1; decide +kernel
      have hl : raw20565step2Labels = raw20565step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20565step1 raw20565step1Labels permutation31 permutation3
    mixedMoment B raw20565step2 raw20565step2Labels = mixedMoment B raw20565step3 raw20565step3Labels := by
      have ha : raw20565step3 = -raw20565step2 := by apply Matrix.ext; change ∀ i j, raw20565step3 i j = -(raw20565step2 i j); unfold raw20565step3 raw20565step2; decide +kernel
      have hl : raw20565step3Labels = raw20565step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node740 node740Labels := by rfl

def raw20566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20566step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20566step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20566 raw20566Labels = mixedMoment B node740 node740Labels := by
  calc
    mixedMoment B raw20566 raw20566Labels = mixedMoment B raw20566step0 raw20566step0Labels := by
      have hz : ∀ j, raw20566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20566step0 = (fun i j => raw20566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20566step0 raw20566; decide +kernel
      have hl : raw20566step0Labels = raw20566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20566 raw20566Labels permutation434 hz
    mixedMoment B raw20566step0 raw20566step0Labels = mixedMoment B raw20566step1 raw20566step1Labels := by
      have hz : ∀ j, raw20566step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20566step1 = (fun i j => raw20566step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20566step1 raw20566step0; decide +kernel
      have hl : raw20566step1Labels = raw20566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20566step0 raw20566step0Labels permutation56 hz
    mixedMoment B raw20566step1 raw20566step1Labels = mixedMoment B raw20566step2 raw20566step2Labels := by
      have ha : raw20566step2 = (fun i j => raw20566step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20566step2 raw20566step1; decide +kernel
      have hl : raw20566step2Labels = raw20566step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20566step1 raw20566step1Labels permutation31 permutation3
    mixedMoment B raw20566step2 raw20566step2Labels = mixedMoment B raw20566step3 raw20566step3Labels := by
      have ha : raw20566step3 = -raw20566step2 := by apply Matrix.ext; change ∀ i j, raw20566step3 i j = -(raw20566step2 i j); unfold raw20566step3 raw20566step2; decide +kernel
      have hl : raw20566step3Labels = raw20566step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node740 node740Labels := by rfl

def raw20567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20567step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20567step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20567 raw20567Labels = mixedMoment B node740 node740Labels := by
  calc
    mixedMoment B raw20567 raw20567Labels = mixedMoment B raw20567step0 raw20567step0Labels := by
      have hz : ∀ j, raw20567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20567step0 = (fun i j => raw20567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20567step0 raw20567; decide +kernel
      have hl : raw20567step0Labels = raw20567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20567 raw20567Labels permutation346 hz
    mixedMoment B raw20567step0 raw20567step0Labels = mixedMoment B raw20567step1 raw20567step1Labels := by
      have hz : ∀ j, raw20567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20567step1 = (fun i j => raw20567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20567step1 raw20567step0; decide +kernel
      have hl : raw20567step1Labels = raw20567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20567step0 raw20567step0Labels permutation56 hz
    mixedMoment B raw20567step1 raw20567step1Labels = mixedMoment B raw20567step2 raw20567step2Labels := by
      have ha : raw20567step2 = (fun i j => raw20567step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20567step2 raw20567step1; decide +kernel
      have hl : raw20567step2Labels = raw20567step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20567step1 raw20567step1Labels permutation31 permutation3
    mixedMoment B raw20567step2 raw20567step2Labels = mixedMoment B raw20567step3 raw20567step3Labels := by
      have ha : raw20567step3 = -raw20567step2 := by apply Matrix.ext; change ∀ i j, raw20567step3 i j = -(raw20567step2 i j); unfold raw20567step3 raw20567step2; decide +kernel
      have hl : raw20567step3Labels = raw20567step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node740 node740Labels := by rfl

def raw20568 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20568step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20568step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20568 raw20568Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw20568 raw20568Labels = mixedMoment B raw20568step0 raw20568step0Labels := by
      have hz : ∀ j, raw20568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20568step0 = (fun i j => raw20568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20568step0 raw20568; decide +kernel
      have hl : raw20568step0Labels = raw20568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20568 raw20568Labels permutation434 hz
    mixedMoment B raw20568step0 raw20568step0Labels = mixedMoment B raw20568step1 raw20568step1Labels := by
      have hz : ∀ j, raw20568step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20568step1 = (fun i j => raw20568step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20568step1 raw20568step0; decide +kernel
      have hl : raw20568step1Labels = raw20568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20568step0 raw20568step0Labels permutation80 hz
    mixedMoment B raw20568step1 raw20568step1Labels = mixedMoment B raw20568step2 raw20568step2Labels := by
      have ha : raw20568step2 = (fun i j => raw20568step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20568step2 raw20568step1; decide +kernel
      have hl : raw20568step2Labels = raw20568step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20568step1 raw20568step1Labels permutation8 permutation7
    mixedMoment B raw20568step2 raw20568step2Labels = mixedMoment B raw20568step3 raw20568step3Labels := by
      have ha : raw20568step3 = raw20568step2 := by apply Matrix.ext; unfold raw20568step3 raw20568step2; decide +kernel
      have hl : raw20568step2Labels = labelEmbedding10 ∘ raw20568step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20568step2 raw20568step2Labels raw20568step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw20569 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20569step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20569 raw20569Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw20569 raw20569Labels = mixedMoment B raw20569step0 raw20569step0Labels := by
      have hz : ∀ j, raw20569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20569step0 = (fun i j => raw20569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20569step0 raw20569; decide +kernel
      have hl : raw20569step0Labels = raw20569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20569 raw20569Labels permutation434 hz
    mixedMoment B raw20569step0 raw20569step0Labels = mixedMoment B raw20569step1 raw20569step1Labels := by
      have hz : ∀ j, raw20569step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20569step1 = (fun i j => raw20569step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20569step1 raw20569step0; decide +kernel
      have hl : raw20569step1Labels = raw20569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20569step0 raw20569step0Labels permutation56 hz
    mixedMoment B raw20569step1 raw20569step1Labels = mixedMoment B raw20569step2 raw20569step2Labels := by
      have ha : raw20569step2 = (fun i j => raw20569step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20569step2 raw20569step1; decide +kernel
      have hl : raw20569step2Labels = raw20569step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20569step1 raw20569step1Labels permutation8 permutation7
    mixedMoment B raw20569step2 raw20569step2Labels = mixedMoment B raw20569step3 raw20569step3Labels := by
      have ha : raw20569step3 = raw20569step2 := by apply Matrix.ext; unfold raw20569step3 raw20569step2; decide +kernel
      have hl : raw20569step2Labels = labelEmbedding10 ∘ raw20569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20569step2 raw20569step2Labels raw20569step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw20570 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20570step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20570step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20570 raw20570Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw20570 raw20570Labels = mixedMoment B raw20570step0 raw20570step0Labels := by
      have hz : ∀ j, raw20570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20570step0 = (fun i j => raw20570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20570step0 raw20570; decide +kernel
      have hl : raw20570step0Labels = raw20570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20570 raw20570Labels permutation346 hz
    mixedMoment B raw20570step0 raw20570step0Labels = mixedMoment B raw20570step1 raw20570step1Labels := by
      have hz : ∀ j, raw20570step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20570step1 = (fun i j => raw20570step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20570step1 raw20570step0; decide +kernel
      have hl : raw20570step1Labels = raw20570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20570step0 raw20570step0Labels permutation56 hz
    mixedMoment B raw20570step1 raw20570step1Labels = mixedMoment B raw20570step2 raw20570step2Labels := by
      have ha : raw20570step2 = (fun i j => raw20570step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20570step2 raw20570step1; decide +kernel
      have hl : raw20570step2Labels = raw20570step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20570step1 raw20570step1Labels permutation8 permutation7
    mixedMoment B raw20570step2 raw20570step2Labels = mixedMoment B raw20570step3 raw20570step3Labels := by
      have ha : raw20570step3 = raw20570step2 := by apply Matrix.ext; unfold raw20570step3 raw20570step2; decide +kernel
      have hl : raw20570step2Labels = labelEmbedding10 ∘ raw20570step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20570step2 raw20570step2Labels raw20570step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw20571 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20571step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![0, -3, 3]]
def raw20571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20571step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw20571step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20571step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw20571step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20571 raw20571Labels = mixedMoment B node4508 node4508Labels := by
  calc
    mixedMoment B raw20571 raw20571Labels = mixedMoment B raw20571step0 raw20571step0Labels := by
      have hz : ∀ j, raw20571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20571step0 = (fun i j => raw20571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20571step0 raw20571; decide +kernel
      have hl : raw20571step0Labels = raw20571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20571 raw20571Labels permutation434 hz
    mixedMoment B raw20571step0 raw20571step0Labels = mixedMoment B raw20571step1 raw20571step1Labels := by
      have hz : ∀ j, raw20571step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20571step1 = (fun i j => raw20571step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20571step1 raw20571step0; decide +kernel
      have hl : raw20571step1Labels = raw20571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20571step0 raw20571step0Labels permutation80 hz
    mixedMoment B raw20571step1 raw20571step1Labels = mixedMoment B raw20571step2 raw20571step2Labels := by
      have hz : ∀ j, raw20571step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20571step2 = (fun i j => raw20571step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20571step2 raw20571step1; decide +kernel
      have hl : raw20571step2Labels = raw20571step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20571step1 raw20571step1Labels permutation14 hz
    mixedMoment B raw20571step2 raw20571step2Labels = mixedMoment B raw20571step3 raw20571step3Labels := by
      have ha : raw20571step3 = (fun i j => raw20571step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20571step3 raw20571step2; decide +kernel
      have hl : raw20571step3Labels = raw20571step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20571step2 raw20571step2Labels permutation2 permutation7
    mixedMoment B raw20571step3 raw20571step3Labels = mixedMoment B raw20571step4 raw20571step4Labels := by
      have ha : raw20571step4 = raw20571step3 := by apply Matrix.ext; unfold raw20571step4 raw20571step3; decide +kernel
      have hl : raw20571step3Labels = labelEmbedding10 ∘ raw20571step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20571step3 raw20571step3Labels raw20571step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4508 node4508Labels := by rfl

def raw20572 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20572step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20572step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20572step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20572 raw20572Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw20572 raw20572Labels = mixedMoment B raw20572step0 raw20572step0Labels := by
      have hz : ∀ j, raw20572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20572step0 = (fun i j => raw20572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20572step0 raw20572; decide +kernel
      have hl : raw20572step0Labels = raw20572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20572 raw20572Labels permutation434 hz
    mixedMoment B raw20572step0 raw20572step0Labels = mixedMoment B raw20572step1 raw20572step1Labels := by
      have hz : ∀ j, raw20572step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20572step1 = (fun i j => raw20572step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20572step1 raw20572step0; decide +kernel
      have hl : raw20572step1Labels = raw20572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20572step0 raw20572step0Labels permutation80 hz
    mixedMoment B raw20572step1 raw20572step1Labels = mixedMoment B raw20572step2 raw20572step2Labels := by
      have ha : raw20572step2 = (fun i j => raw20572step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20572step2 raw20572step1; decide +kernel
      have hl : raw20572step2Labels = raw20572step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20572step1 raw20572step1Labels permutation8 permutation6
    mixedMoment B raw20572step2 raw20572step2Labels = mixedMoment B raw20572step3 raw20572step3Labels := by
      have ha : raw20572step3 = raw20572step2 := by apply Matrix.ext; unfold raw20572step3 raw20572step2; decide +kernel
      have hl : raw20572step2Labels = labelEmbedding9 ∘ raw20572step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20572step2 raw20572step2Labels raw20572step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

def raw20573 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20573step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20573 raw20573Labels = mixedMoment B node4588 node4588Labels := by
  calc
    mixedMoment B raw20573 raw20573Labels = mixedMoment B raw20573step0 raw20573step0Labels := by
      have hz : ∀ j, raw20573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20573step0 = (fun i j => raw20573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20573step0 raw20573; decide +kernel
      have hl : raw20573step0Labels = raw20573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20573 raw20573Labels permutation434 hz
    mixedMoment B raw20573step0 raw20573step0Labels = mixedMoment B raw20573step1 raw20573step1Labels := by
      have ha : raw20573step1 = (fun i j => raw20573step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20573step1 raw20573step0; decide +kernel
      have hl : raw20573step1Labels = raw20573step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20573step0 raw20573step0Labels permutation38 permutation6
    mixedMoment B raw20573step1 raw20573step1Labels = mixedMoment B raw20573step2 raw20573step2Labels := by
      have ha : raw20573step2 = raw20573step1 := by apply Matrix.ext; unfold raw20573step2 raw20573step1; decide +kernel
      have hl : raw20573step1Labels = labelEmbedding9 ∘ raw20573step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20573step1 raw20573step1Labels raw20573step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4588 node4588Labels := by rfl

def raw20574 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20574step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20574 raw20574Labels = mixedMoment B node4588 node4588Labels := by
  calc
    mixedMoment B raw20574 raw20574Labels = mixedMoment B raw20574step0 raw20574step0Labels := by
      have hz : ∀ j, raw20574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20574step0 = (fun i j => raw20574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20574step0 raw20574; decide +kernel
      have hl : raw20574step0Labels = raw20574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20574 raw20574Labels permutation346 hz
    mixedMoment B raw20574step0 raw20574step0Labels = mixedMoment B raw20574step1 raw20574step1Labels := by
      have ha : raw20574step1 = (fun i j => raw20574step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20574step1 raw20574step0; decide +kernel
      have hl : raw20574step1Labels = raw20574step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20574step0 raw20574step0Labels permutation38 permutation6
    mixedMoment B raw20574step1 raw20574step1Labels = mixedMoment B raw20574step2 raw20574step2Labels := by
      have ha : raw20574step2 = raw20574step1 := by apply Matrix.ext; unfold raw20574step2 raw20574step1; decide +kernel
      have hl : raw20574step1Labels = labelEmbedding9 ∘ raw20574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20574step1 raw20574step1Labels raw20574step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4588 node4588Labels := by rfl

def raw20575 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20575step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20575step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20575step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20575step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20575 raw20575Labels = mixedMoment B node4610 node4610Labels := by
  calc
    mixedMoment B raw20575 raw20575Labels = mixedMoment B raw20575step0 raw20575step0Labels := by
      have hz : ∀ j, raw20575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20575step0 = (fun i j => raw20575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20575step0 raw20575; decide +kernel
      have hl : raw20575step0Labels = raw20575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20575 raw20575Labels permutation434 hz
    mixedMoment B raw20575step0 raw20575step0Labels = mixedMoment B raw20575step1 raw20575step1Labels := by
      have hz : ∀ j, raw20575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20575step1 = (fun i j => raw20575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20575step1 raw20575step0; decide +kernel
      have hl : raw20575step1Labels = raw20575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20575step0 raw20575step0Labels permutation80 hz
    mixedMoment B raw20575step1 raw20575step1Labels = mixedMoment B raw20575step2 raw20575step2Labels := by
      have ha : raw20575step2 = (fun i j => raw20575step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20575step2 raw20575step1; decide +kernel
      have hl : raw20575step2Labels = raw20575step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20575step1 raw20575step1Labels permutation8 permutation7
    mixedMoment B raw20575step2 raw20575step2Labels = mixedMoment B raw20575step3 raw20575step3Labels := by
      have ha : raw20575step3 = raw20575step2 := by apply Matrix.ext; unfold raw20575step3 raw20575step2; decide +kernel
      have hl : raw20575step2Labels = labelEmbedding10 ∘ raw20575step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20575step2 raw20575step2Labels raw20575step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4610 node4610Labels := by rfl

def raw20576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20576step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20576step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20576 raw20576Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw20576 raw20576Labels = mixedMoment B raw20576step0 raw20576step0Labels := by
      have hz : ∀ j, raw20576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20576step0 = (fun i j => raw20576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20576step0 raw20576; decide +kernel
      have hl : raw20576step0Labels = raw20576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20576 raw20576Labels permutation434 hz
    mixedMoment B raw20576step0 raw20576step0Labels = mixedMoment B raw20576step1 raw20576step1Labels := by
      have hz : ∀ j, raw20576step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20576step1 = (fun i j => raw20576step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20576step1 raw20576step0; decide +kernel
      have hl : raw20576step1Labels = raw20576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20576step0 raw20576step0Labels permutation56 hz
    mixedMoment B raw20576step1 raw20576step1Labels = mixedMoment B raw20576step2 raw20576step2Labels := by
      have ha : raw20576step2 = (fun i j => raw20576step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20576step2 raw20576step1; decide +kernel
      have hl : raw20576step2Labels = raw20576step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20576step1 raw20576step1Labels permutation8 permutation6
    mixedMoment B raw20576step2 raw20576step2Labels = mixedMoment B raw20576step3 raw20576step3Labels := by
      have ha : raw20576step3 = raw20576step2 := by apply Matrix.ext; unfold raw20576step3 raw20576step2; decide +kernel
      have hl : raw20576step2Labels = labelEmbedding9 ∘ raw20576step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20576step2 raw20576step2Labels raw20576step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

def raw20577 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20577step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20577 raw20577Labels = mixedMoment B node4588 node4588Labels := by
  calc
    mixedMoment B raw20577 raw20577Labels = mixedMoment B raw20577step0 raw20577step0Labels := by
      have hz : ∀ j, raw20577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20577step0 = (fun i j => raw20577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20577step0 raw20577; decide +kernel
      have hl : raw20577step0Labels = raw20577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20577 raw20577Labels permutation434 hz
    mixedMoment B raw20577step0 raw20577step0Labels = mixedMoment B raw20577step1 raw20577step1Labels := by
      have ha : raw20577step1 = (fun i j => raw20577step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20577step1 raw20577step0; decide +kernel
      have hl : raw20577step1Labels = raw20577step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20577step0 raw20577step0Labels permutation32 permutation6
    mixedMoment B raw20577step1 raw20577step1Labels = mixedMoment B raw20577step2 raw20577step2Labels := by
      have ha : raw20577step2 = raw20577step1 := by apply Matrix.ext; unfold raw20577step2 raw20577step1; decide +kernel
      have hl : raw20577step1Labels = labelEmbedding9 ∘ raw20577step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20577step1 raw20577step1Labels raw20577step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4588 node4588Labels := by rfl

def raw20578 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20578step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20578 raw20578Labels = mixedMoment B node4588 node4588Labels := by
  calc
    mixedMoment B raw20578 raw20578Labels = mixedMoment B raw20578step0 raw20578step0Labels := by
      have hz : ∀ j, raw20578 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20578step0 = (fun i j => raw20578 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20578step0 raw20578; decide +kernel
      have hl : raw20578step0Labels = raw20578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20578 raw20578Labels permutation265 hz
    mixedMoment B raw20578step0 raw20578step0Labels = mixedMoment B raw20578step1 raw20578step1Labels := by
      have ha : raw20578step1 = (fun i j => raw20578step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20578step1 raw20578step0; decide +kernel
      have hl : raw20578step1Labels = raw20578step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20578step0 raw20578step0Labels permutation38 permutation6
    mixedMoment B raw20578step1 raw20578step1Labels = mixedMoment B raw20578step2 raw20578step2Labels := by
      have ha : raw20578step2 = raw20578step1 := by apply Matrix.ext; unfold raw20578step2 raw20578step1; decide +kernel
      have hl : raw20578step1Labels = labelEmbedding9 ∘ raw20578step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20578step1 raw20578step1Labels raw20578step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4588 node4588Labels := by rfl

def raw20579 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20579step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20579step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20579step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20579 raw20579Labels = mixedMoment B node4610 node4610Labels := by
  calc
    mixedMoment B raw20579 raw20579Labels = mixedMoment B raw20579step0 raw20579step0Labels := by
      have hz : ∀ j, raw20579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20579step0 = (fun i j => raw20579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20579step0 raw20579; decide +kernel
      have hl : raw20579step0Labels = raw20579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20579 raw20579Labels permutation434 hz
    mixedMoment B raw20579step0 raw20579step0Labels = mixedMoment B raw20579step1 raw20579step1Labels := by
      have hz : ∀ j, raw20579step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20579step1 = (fun i j => raw20579step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20579step1 raw20579step0; decide +kernel
      have hl : raw20579step1Labels = raw20579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20579step0 raw20579step0Labels permutation56 hz
    mixedMoment B raw20579step1 raw20579step1Labels = mixedMoment B raw20579step2 raw20579step2Labels := by
      have ha : raw20579step2 = (fun i j => raw20579step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20579step2 raw20579step1; decide +kernel
      have hl : raw20579step2Labels = raw20579step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20579step1 raw20579step1Labels permutation8 permutation7
    mixedMoment B raw20579step2 raw20579step2Labels = mixedMoment B raw20579step3 raw20579step3Labels := by
      have ha : raw20579step3 = raw20579step2 := by apply Matrix.ext; unfold raw20579step3 raw20579step2; decide +kernel
      have hl : raw20579step2Labels = labelEmbedding10 ∘ raw20579step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20579step2 raw20579step2Labels raw20579step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4610 node4610Labels := by rfl

def raw20580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20580step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20580step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20580step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20580 raw20580Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw20580 raw20580Labels = mixedMoment B raw20580step0 raw20580step0Labels := by
      have hz : ∀ j, raw20580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20580step0 = (fun i j => raw20580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20580step0 raw20580; decide +kernel
      have hl : raw20580step0Labels = raw20580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20580 raw20580Labels permutation346 hz
    mixedMoment B raw20580step0 raw20580step0Labels = mixedMoment B raw20580step1 raw20580step1Labels := by
      have hz : ∀ j, raw20580step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20580step1 = (fun i j => raw20580step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20580step1 raw20580step0; decide +kernel
      have hl : raw20580step1Labels = raw20580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20580step0 raw20580step0Labels permutation56 hz
    mixedMoment B raw20580step1 raw20580step1Labels = mixedMoment B raw20580step2 raw20580step2Labels := by
      have ha : raw20580step2 = (fun i j => raw20580step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20580step2 raw20580step1; decide +kernel
      have hl : raw20580step2Labels = raw20580step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20580step1 raw20580step1Labels permutation8 permutation6
    mixedMoment B raw20580step2 raw20580step2Labels = mixedMoment B raw20580step3 raw20580step3Labels := by
      have ha : raw20580step3 = raw20580step2 := by apply Matrix.ext; unfold raw20580step3 raw20580step2; decide +kernel
      have hl : raw20580step2Labels = labelEmbedding9 ∘ raw20580step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20580step2 raw20580step2Labels raw20580step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

def raw20581 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20581step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20581 raw20581Labels = mixedMoment B node4588 node4588Labels := by
  calc
    mixedMoment B raw20581 raw20581Labels = mixedMoment B raw20581step0 raw20581step0Labels := by
      have hz : ∀ j, raw20581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20581step0 = (fun i j => raw20581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20581step0 raw20581; decide +kernel
      have hl : raw20581step0Labels = raw20581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20581 raw20581Labels permutation346 hz
    mixedMoment B raw20581step0 raw20581step0Labels = mixedMoment B raw20581step1 raw20581step1Labels := by
      have ha : raw20581step1 = (fun i j => raw20581step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20581step1 raw20581step0; decide +kernel
      have hl : raw20581step1Labels = raw20581step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20581step0 raw20581step0Labels permutation32 permutation6
    mixedMoment B raw20581step1 raw20581step1Labels = mixedMoment B raw20581step2 raw20581step2Labels := by
      have ha : raw20581step2 = raw20581step1 := by apply Matrix.ext; unfold raw20581step2 raw20581step1; decide +kernel
      have hl : raw20581step1Labels = labelEmbedding9 ∘ raw20581step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20581step1 raw20581step1Labels raw20581step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4588 node4588Labels := by rfl

def raw20582 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20582step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20582 raw20582Labels = mixedMoment B node4588 node4588Labels := by
  calc
    mixedMoment B raw20582 raw20582Labels = mixedMoment B raw20582step0 raw20582step0Labels := by
      have hz : ∀ j, raw20582 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20582step0 = (fun i j => raw20582 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20582step0 raw20582; decide +kernel
      have hl : raw20582step0Labels = raw20582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20582 raw20582Labels permutation265 hz
    mixedMoment B raw20582step0 raw20582step0Labels = mixedMoment B raw20582step1 raw20582step1Labels := by
      have ha : raw20582step1 = (fun i j => raw20582step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20582step1 raw20582step0; decide +kernel
      have hl : raw20582step1Labels = raw20582step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20582step0 raw20582step0Labels permutation32 permutation6
    mixedMoment B raw20582step1 raw20582step1Labels = mixedMoment B raw20582step2 raw20582step2Labels := by
      have ha : raw20582step2 = raw20582step1 := by apply Matrix.ext; unfold raw20582step2 raw20582step1; decide +kernel
      have hl : raw20582step1Labels = labelEmbedding9 ∘ raw20582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20582step1 raw20582step1Labels raw20582step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4588 node4588Labels := by rfl

def raw20583 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20583step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20583step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20583 raw20583Labels = mixedMoment B node4610 node4610Labels := by
  calc
    mixedMoment B raw20583 raw20583Labels = mixedMoment B raw20583step0 raw20583step0Labels := by
      have hz : ∀ j, raw20583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20583step0 = (fun i j => raw20583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20583step0 raw20583; decide +kernel
      have hl : raw20583step0Labels = raw20583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20583 raw20583Labels permutation346 hz
    mixedMoment B raw20583step0 raw20583step0Labels = mixedMoment B raw20583step1 raw20583step1Labels := by
      have hz : ∀ j, raw20583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20583step1 = (fun i j => raw20583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20583step1 raw20583step0; decide +kernel
      have hl : raw20583step1Labels = raw20583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20583step0 raw20583step0Labels permutation56 hz
    mixedMoment B raw20583step1 raw20583step1Labels = mixedMoment B raw20583step2 raw20583step2Labels := by
      have ha : raw20583step2 = (fun i j => raw20583step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20583step2 raw20583step1; decide +kernel
      have hl : raw20583step2Labels = raw20583step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20583step1 raw20583step1Labels permutation8 permutation7
    mixedMoment B raw20583step2 raw20583step2Labels = mixedMoment B raw20583step3 raw20583step3Labels := by
      have ha : raw20583step3 = raw20583step2 := by apply Matrix.ext; unfold raw20583step3 raw20583step2; decide +kernel
      have hl : raw20583step2Labels = labelEmbedding10 ∘ raw20583step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20583step2 raw20583step2Labels raw20583step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4610 node4610Labels := by rfl

def raw20584 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20584step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, -2, 3]]
def raw20584step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20584step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20584step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20584step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20584step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20584 raw20584Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw20584 raw20584Labels = mixedMoment B raw20584step0 raw20584step0Labels := by
      have hz : ∀ j, raw20584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20584step0 = (fun i j => raw20584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20584step0 raw20584; decide +kernel
      have hl : raw20584step0Labels = raw20584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20584 raw20584Labels permutation434 hz
    mixedMoment B raw20584step0 raw20584step0Labels = mixedMoment B raw20584step1 raw20584step1Labels := by
      have hz : ∀ j, raw20584step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20584step1 = (fun i j => raw20584step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20584step1 raw20584step0; decide +kernel
      have hl : raw20584step1Labels = raw20584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20584step0 raw20584step0Labels permutation80 hz
    mixedMoment B raw20584step1 raw20584step1Labels = mixedMoment B raw20584step2 raw20584step2Labels := by
      have hz : ∀ j, raw20584step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20584step2 = (fun i j => raw20584step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20584step2 raw20584step1; decide +kernel
      have hl : raw20584step2Labels = raw20584step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20584step1 raw20584step1Labels permutation14 hz
    mixedMoment B raw20584step2 raw20584step2Labels = mixedMoment B raw20584step3 raw20584step3Labels := by
      have ha : raw20584step3 = (fun i j => raw20584step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20584step3 raw20584step2; decide +kernel
      have hl : raw20584step3Labels = raw20584step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20584step2 raw20584step2Labels permutation2 permutation6
    mixedMoment B raw20584step3 raw20584step3Labels = mixedMoment B raw20584step4 raw20584step4Labels := by
      have ha : raw20584step4 = raw20584step3 := by apply Matrix.ext; unfold raw20584step4 raw20584step3; decide +kernel
      have hl : raw20584step3Labels = labelEmbedding9 ∘ raw20584step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20584step3 raw20584step3Labels raw20584step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw20585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20585step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20585step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -4, 3]]
def raw20585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20585step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20585step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20585step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20585step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20585 raw20585Labels = mixedMoment B node4493 node4493Labels := by
  calc
    mixedMoment B raw20585 raw20585Labels = mixedMoment B raw20585step0 raw20585step0Labels := by
      have hz : ∀ j, raw20585 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20585step0 = (fun i j => raw20585 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20585step0 raw20585; decide +kernel
      have hl : raw20585step0Labels = raw20585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20585 raw20585Labels permutation434 hz
    mixedMoment B raw20585step0 raw20585step0Labels = mixedMoment B raw20585step1 raw20585step1Labels := by
      have hz : ∀ j, raw20585step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20585step1 = (fun i j => raw20585step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20585step1 raw20585step0; decide +kernel
      have hl : raw20585step1Labels = raw20585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20585step0 raw20585step0Labels permutation80 hz
    mixedMoment B raw20585step1 raw20585step1Labels = mixedMoment B raw20585step2 raw20585step2Labels := by
      have hz : ∀ j, raw20585step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20585step2 = (fun i j => raw20585step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20585step2 raw20585step1; decide +kernel
      have hl : raw20585step2Labels = raw20585step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20585step1 raw20585step1Labels permutation14 hz
    mixedMoment B raw20585step2 raw20585step2Labels = mixedMoment B raw20585step3 raw20585step3Labels := by
      have ha : raw20585step3 = (fun i j => raw20585step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20585step3 raw20585step2; decide +kernel
      have hl : raw20585step3Labels = raw20585step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20585step2 raw20585step2Labels permutation7 permutation4
    mixedMoment B raw20585step3 raw20585step3Labels = mixedMoment B raw20585step4 raw20585step4Labels := by
      have ha : raw20585step4 = raw20585step3 := by apply Matrix.ext; unfold raw20585step4 raw20585step3; decide +kernel
      have hl : raw20585step3Labels = labelEmbedding7 ∘ raw20585step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20585step3 raw20585step3Labels raw20585step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4493 node4493Labels := by rfl

def raw20586 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20586step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20586step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20586 raw20586Labels = mixedMoment B node4488 node4488Labels := by
  calc
    mixedMoment B raw20586 raw20586Labels = mixedMoment B raw20586step0 raw20586step0Labels := by
      have hz : ∀ j, raw20586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20586step0 = (fun i j => raw20586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20586step0 raw20586; decide +kernel
      have hl : raw20586step0Labels = raw20586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20586 raw20586Labels permutation434 hz
    mixedMoment B raw20586step0 raw20586step0Labels = mixedMoment B raw20586step1 raw20586step1Labels := by
      have hz : ∀ j, raw20586step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20586step1 = (fun i j => raw20586step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20586step1 raw20586step0; decide +kernel
      have hl : raw20586step1Labels = raw20586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20586step0 raw20586step0Labels permutation80 hz
    mixedMoment B raw20586step1 raw20586step1Labels = mixedMoment B raw20586step2 raw20586step2Labels := by
      have ha : raw20586step2 = (fun i j => raw20586step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20586step2 raw20586step1; decide +kernel
      have hl : raw20586step2Labels = raw20586step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20586step1 raw20586step1Labels permutation31 permutation4
    mixedMoment B raw20586step2 raw20586step2Labels = mixedMoment B raw20586step3 raw20586step3Labels := by
      have ha : raw20586step3 = raw20586step2 := by apply Matrix.ext; unfold raw20586step3 raw20586step2; decide +kernel
      have hl : raw20586step2Labels = labelEmbedding7 ∘ raw20586step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20586step2 raw20586step2Labels raw20586step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4488 node4488Labels := by rfl

def raw20587 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20587step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20587 raw20587Labels = mixedMoment B node4488 node4488Labels := by
  calc
    mixedMoment B raw20587 raw20587Labels = mixedMoment B raw20587step0 raw20587step0Labels := by
      have hz : ∀ j, raw20587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20587step0 = (fun i j => raw20587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20587step0 raw20587; decide +kernel
      have hl : raw20587step0Labels = raw20587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20587 raw20587Labels permutation434 hz
    mixedMoment B raw20587step0 raw20587step0Labels = mixedMoment B raw20587step1 raw20587step1Labels := by
      have hz : ∀ j, raw20587step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20587step1 = (fun i j => raw20587step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20587step1 raw20587step0; decide +kernel
      have hl : raw20587step1Labels = raw20587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20587step0 raw20587step0Labels permutation56 hz
    mixedMoment B raw20587step1 raw20587step1Labels = mixedMoment B raw20587step2 raw20587step2Labels := by
      have ha : raw20587step2 = (fun i j => raw20587step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20587step2 raw20587step1; decide +kernel
      have hl : raw20587step2Labels = raw20587step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20587step1 raw20587step1Labels permutation31 permutation4
    mixedMoment B raw20587step2 raw20587step2Labels = mixedMoment B raw20587step3 raw20587step3Labels := by
      have ha : raw20587step3 = raw20587step2 := by apply Matrix.ext; unfold raw20587step3 raw20587step2; decide +kernel
      have hl : raw20587step2Labels = labelEmbedding7 ∘ raw20587step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20587step2 raw20587step2Labels raw20587step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4488 node4488Labels := by rfl

def raw20588 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20588step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20588step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20588 raw20588Labels = mixedMoment B node4488 node4488Labels := by
  calc
    mixedMoment B raw20588 raw20588Labels = mixedMoment B raw20588step0 raw20588step0Labels := by
      have hz : ∀ j, raw20588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20588step0 = (fun i j => raw20588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20588step0 raw20588; decide +kernel
      have hl : raw20588step0Labels = raw20588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20588 raw20588Labels permutation346 hz
    mixedMoment B raw20588step0 raw20588step0Labels = mixedMoment B raw20588step1 raw20588step1Labels := by
      have hz : ∀ j, raw20588step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20588step1 = (fun i j => raw20588step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20588step1 raw20588step0; decide +kernel
      have hl : raw20588step1Labels = raw20588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20588step0 raw20588step0Labels permutation56 hz
    mixedMoment B raw20588step1 raw20588step1Labels = mixedMoment B raw20588step2 raw20588step2Labels := by
      have ha : raw20588step2 = (fun i j => raw20588step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20588step2 raw20588step1; decide +kernel
      have hl : raw20588step2Labels = raw20588step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20588step1 raw20588step1Labels permutation31 permutation4
    mixedMoment B raw20588step2 raw20588step2Labels = mixedMoment B raw20588step3 raw20588step3Labels := by
      have ha : raw20588step3 = raw20588step2 := by apply Matrix.ext; unfold raw20588step3 raw20588step2; decide +kernel
      have hl : raw20588step2Labels = labelEmbedding7 ∘ raw20588step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20588step2 raw20588step2Labels raw20588step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4488 node4488Labels := by rfl

def raw20589 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20589step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![1, -4, 3]]
def raw20589step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20589step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw20589step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20589step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw20589step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20589 raw20589Labels = mixedMoment B node4509 node4509Labels := by
  calc
    mixedMoment B raw20589 raw20589Labels = mixedMoment B raw20589step0 raw20589step0Labels := by
      have hz : ∀ j, raw20589 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20589step0 = (fun i j => raw20589 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20589step0 raw20589; decide +kernel
      have hl : raw20589step0Labels = raw20589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20589 raw20589Labels permutation434 hz
    mixedMoment B raw20589step0 raw20589step0Labels = mixedMoment B raw20589step1 raw20589step1Labels := by
      have hz : ∀ j, raw20589step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20589step1 = (fun i j => raw20589step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20589step1 raw20589step0; decide +kernel
      have hl : raw20589step1Labels = raw20589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20589step0 raw20589step0Labels permutation80 hz
    mixedMoment B raw20589step1 raw20589step1Labels = mixedMoment B raw20589step2 raw20589step2Labels := by
      have hz : ∀ j, raw20589step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20589step2 = (fun i j => raw20589step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20589step2 raw20589step1; decide +kernel
      have hl : raw20589step2Labels = raw20589step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20589step1 raw20589step1Labels permutation14 hz
    mixedMoment B raw20589step2 raw20589step2Labels = mixedMoment B raw20589step3 raw20589step3Labels := by
      have ha : raw20589step3 = (fun i j => raw20589step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20589step3 raw20589step2; decide +kernel
      have hl : raw20589step3Labels = raw20589step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20589step2 raw20589step2Labels permutation7 permutation4
    mixedMoment B raw20589step3 raw20589step3Labels = mixedMoment B raw20589step4 raw20589step4Labels := by
      have ha : raw20589step4 = raw20589step3 := by apply Matrix.ext; unfold raw20589step4 raw20589step3; decide +kernel
      have hl : raw20589step3Labels = labelEmbedding7 ∘ raw20589step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20589step3 raw20589step3Labels raw20589step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4509 node4509Labels := by rfl

def raw20590 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20590 raw20590Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw20590 raw20590Labels = mixedMoment B raw20590step0 raw20590step0Labels := by
      have hz : ∀ j, raw20590 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20590step0 = (fun i j => raw20590 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20590step0 raw20590; decide +kernel
      have hl : raw20590step0Labels = raw20590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20590 raw20590Labels permutation434 hz
    mixedMoment B raw20590step0 raw20590step0Labels = mixedMoment B raw20590step1 raw20590step1Labels := by
      have hz : ∀ j, raw20590step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20590step1 = (fun i j => raw20590step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20590step1 raw20590step0; decide +kernel
      have hl : raw20590step1Labels = raw20590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20590step0 raw20590step0Labels permutation80 hz
    mixedMoment B raw20590step1 raw20590step1Labels = mixedMoment B raw20590step2 raw20590step2Labels := by
      have ha : raw20590step2 = (fun i j => raw20590step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20590step2 raw20590step1; decide +kernel
      have hl : raw20590step2Labels = raw20590step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20590step1 raw20590step1Labels permutation8 permutation6
    _ = mixedMoment B node1408 node1408Labels := by rfl

def raw20591 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20591step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20591 raw20591Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw20591 raw20591Labels = mixedMoment B raw20591step0 raw20591step0Labels := by
      have hz : ∀ j, raw20591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20591step0 = (fun i j => raw20591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20591step0 raw20591; decide +kernel
      have hl : raw20591step0Labels = raw20591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20591 raw20591Labels permutation434 hz
    mixedMoment B raw20591step0 raw20591step0Labels = mixedMoment B raw20591step1 raw20591step1Labels := by
      have hz : ∀ j, raw20591step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20591step1 = (fun i j => raw20591step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20591step1 raw20591step0; decide +kernel
      have hl : raw20591step1Labels = raw20591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20591step0 raw20591step0Labels permutation56 hz
    mixedMoment B raw20591step1 raw20591step1Labels = mixedMoment B raw20591step2 raw20591step2Labels := by
      have ha : raw20591step2 = (fun i j => raw20591step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20591step2 raw20591step1; decide +kernel
      have hl : raw20591step2Labels = raw20591step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20591step1 raw20591step1Labels permutation8 permutation6
    _ = mixedMoment B node1408 node1408Labels := by rfl

def raw20592 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20592step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20592 raw20592Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw20592 raw20592Labels = mixedMoment B raw20592step0 raw20592step0Labels := by
      have hz : ∀ j, raw20592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20592step0 = (fun i j => raw20592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20592step0 raw20592; decide +kernel
      have hl : raw20592step0Labels = raw20592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20592 raw20592Labels permutation346 hz
    mixedMoment B raw20592step0 raw20592step0Labels = mixedMoment B raw20592step1 raw20592step1Labels := by
      have hz : ∀ j, raw20592step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20592step1 = (fun i j => raw20592step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20592step1 raw20592step0; decide +kernel
      have hl : raw20592step1Labels = raw20592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20592step0 raw20592step0Labels permutation56 hz
    mixedMoment B raw20592step1 raw20592step1Labels = mixedMoment B raw20592step2 raw20592step2Labels := by
      have ha : raw20592step2 = (fun i j => raw20592step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20592step2 raw20592step1; decide +kernel
      have hl : raw20592step2Labels = raw20592step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20592step1 raw20592step1Labels permutation8 permutation6
    _ = mixedMoment B node1408 node1408Labels := by rfl

def raw20593 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![0, -3, 3]]
def raw20593step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw20593step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20593 raw20593Labels = mixedMoment B node1438 node1438Labels := by
  calc
    mixedMoment B raw20593 raw20593Labels = mixedMoment B raw20593step0 raw20593step0Labels := by
      have hz : ∀ j, raw20593 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20593step0 = (fun i j => raw20593 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20593step0 raw20593; decide +kernel
      have hl : raw20593step0Labels = raw20593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20593 raw20593Labels permutation434 hz
    mixedMoment B raw20593step0 raw20593step0Labels = mixedMoment B raw20593step1 raw20593step1Labels := by
      have hz : ∀ j, raw20593step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20593step1 = (fun i j => raw20593step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20593step1 raw20593step0; decide +kernel
      have hl : raw20593step1Labels = raw20593step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20593step0 raw20593step0Labels permutation80 hz
    mixedMoment B raw20593step1 raw20593step1Labels = mixedMoment B raw20593step2 raw20593step2Labels := by
      have hz : ∀ j, raw20593step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20593step2 = (fun i j => raw20593step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20593step2 raw20593step1; decide +kernel
      have hl : raw20593step2Labels = raw20593step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20593step1 raw20593step1Labels permutation14 hz
    mixedMoment B raw20593step2 raw20593step2Labels = mixedMoment B raw20593step3 raw20593step3Labels := by
      have ha : raw20593step3 = (fun i j => raw20593step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20593step3 raw20593step2; decide +kernel
      have hl : raw20593step3Labels = raw20593step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20593step2 raw20593step2Labels permutation2 permutation6
    _ = mixedMoment B node1438 node1438Labels := by rfl

def raw20594 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw20594step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20594 raw20594Labels = mixedMoment B node1445 node1445Labels := by
  calc
    mixedMoment B raw20594 raw20594Labels = mixedMoment B raw20594step0 raw20594step0Labels := by
      have hz : ∀ j, raw20594 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20594step0 = (fun i j => raw20594 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20594step0 raw20594; decide +kernel
      have hl : raw20594step0Labels = raw20594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20594 raw20594Labels permutation434 hz
    mixedMoment B raw20594step0 raw20594step0Labels = mixedMoment B raw20594step1 raw20594step1Labels := by
      have hz : ∀ j, raw20594step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20594step1 = (fun i j => raw20594step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20594step1 raw20594step0; decide +kernel
      have hl : raw20594step1Labels = raw20594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20594step0 raw20594step0Labels permutation80 hz
    mixedMoment B raw20594step1 raw20594step1Labels = mixedMoment B raw20594step2 raw20594step2Labels := by
      have hz : ∀ j, raw20594step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20594step2 = (fun i j => raw20594step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20594step2 raw20594step1; decide +kernel
      have hl : raw20594step2Labels = raw20594step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20594step1 raw20594step1Labels permutation14 hz
    mixedMoment B raw20594step2 raw20594step2Labels = mixedMoment B raw20594step3 raw20594step3Labels := by
      have ha : raw20594step3 = (fun i j => raw20594step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20594step3 raw20594step2; decide +kernel
      have hl : raw20594step3Labels = raw20594step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20594step2 raw20594step2Labels permutation2 permutation6
    _ = mixedMoment B node1445 node1445Labels := by rfl

def raw20595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20595 raw20595Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw20595 raw20595Labels = mixedMoment B raw20595step0 raw20595step0Labels := by
      have hz : ∀ j, raw20595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20595step0 = (fun i j => raw20595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20595step0 raw20595; decide +kernel
      have hl : raw20595step0Labels = raw20595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20595 raw20595Labels permutation434 hz
    mixedMoment B raw20595step0 raw20595step0Labels = mixedMoment B raw20595step1 raw20595step1Labels := by
      have hz : ∀ j, raw20595step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20595step1 = (fun i j => raw20595step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20595step1 raw20595step0; decide +kernel
      have hl : raw20595step1Labels = raw20595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20595step0 raw20595step0Labels permutation80 hz
    mixedMoment B raw20595step1 raw20595step1Labels = mixedMoment B raw20595step2 raw20595step2Labels := by
      have ha : raw20595step2 = (fun i j => raw20595step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20595step2 raw20595step1; decide +kernel
      have hl : raw20595step2Labels = raw20595step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20595step1 raw20595step1Labels permutation8 permutation6
    _ = mixedMoment B node1037 node1037Labels := by rfl

def raw20596 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20596 raw20596Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw20596 raw20596Labels = mixedMoment B raw20596step0 raw20596step0Labels := by
      have hz : ∀ j, raw20596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20596step0 = (fun i j => raw20596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20596step0 raw20596; decide +kernel
      have hl : raw20596step0Labels = raw20596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20596 raw20596Labels permutation434 hz
    mixedMoment B raw20596step0 raw20596step0Labels = mixedMoment B raw20596step1 raw20596step1Labels := by
      have ha : raw20596step1 = (fun i j => raw20596step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20596step1 raw20596step0; decide +kernel
      have hl : raw20596step1Labels = raw20596step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20596step0 raw20596step0Labels permutation38 permutation6
    _ = mixedMoment B node1211 node1211Labels := by rfl

def raw20597 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20597 raw20597Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw20597 raw20597Labels = mixedMoment B raw20597step0 raw20597step0Labels := by
      have hz : ∀ j, raw20597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20597step0 = (fun i j => raw20597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20597step0 raw20597; decide +kernel
      have hl : raw20597step0Labels = raw20597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20597 raw20597Labels permutation346 hz
    mixedMoment B raw20597step0 raw20597step0Labels = mixedMoment B raw20597step1 raw20597step1Labels := by
      have ha : raw20597step1 = (fun i j => raw20597step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20597step1 raw20597step0; decide +kernel
      have hl : raw20597step1Labels = raw20597step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20597step0 raw20597step0Labels permutation38 permutation6
    _ = mixedMoment B node1211 node1211Labels := by rfl

def raw20598 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20598step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20598 raw20598Labels = mixedMoment B node1258 node1258Labels := by
  calc
    mixedMoment B raw20598 raw20598Labels = mixedMoment B raw20598step0 raw20598step0Labels := by
      have hz : ∀ j, raw20598 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20598step0 = (fun i j => raw20598 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20598step0 raw20598; decide +kernel
      have hl : raw20598step0Labels = raw20598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20598 raw20598Labels permutation434 hz
    mixedMoment B raw20598step0 raw20598step0Labels = mixedMoment B raw20598step1 raw20598step1Labels := by
      have hz : ∀ j, raw20598step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20598step1 = (fun i j => raw20598step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20598step1 raw20598step0; decide +kernel
      have hl : raw20598step1Labels = raw20598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20598step0 raw20598step0Labels permutation80 hz
    mixedMoment B raw20598step1 raw20598step1Labels = mixedMoment B raw20598step2 raw20598step2Labels := by
      have ha : raw20598step2 = (fun i j => raw20598step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20598step2 raw20598step1; decide +kernel
      have hl : raw20598step2Labels = raw20598step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20598step1 raw20598step1Labels permutation8 permutation6
    _ = mixedMoment B node1258 node1258Labels := by rfl

def raw20599 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20599step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20599 raw20599Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw20599 raw20599Labels = mixedMoment B raw20599step0 raw20599step0Labels := by
      have hz : ∀ j, raw20599 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20599step0 = (fun i j => raw20599 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20599step0 raw20599; decide +kernel
      have hl : raw20599step0Labels = raw20599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20599 raw20599Labels permutation434 hz
    mixedMoment B raw20599step0 raw20599step0Labels = mixedMoment B raw20599step1 raw20599step1Labels := by
      have hz : ∀ j, raw20599step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20599step1 = (fun i j => raw20599step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20599step1 raw20599step0; decide +kernel
      have hl : raw20599step1Labels = raw20599step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20599step0 raw20599step0Labels permutation80 hz
    mixedMoment B raw20599step1 raw20599step1Labels = mixedMoment B raw20599step2 raw20599step2Labels := by
      have ha : raw20599step2 = (fun i j => raw20599step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20599step2 raw20599step1; decide +kernel
      have hl : raw20599step2Labels = raw20599step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20599step1 raw20599step1Labels permutation8 permutation6
    _ = mixedMoment B node1264 node1264Labels := by rfl

def raw20600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20600step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20600step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20600 raw20600Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw20600 raw20600Labels = mixedMoment B raw20600step0 raw20600step0Labels := by
      have hz : ∀ j, raw20600 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20600step0 = (fun i j => raw20600 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20600step0 raw20600; decide +kernel
      have hl : raw20600step0Labels = raw20600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20600 raw20600Labels permutation434 hz
    mixedMoment B raw20600step0 raw20600step0Labels = mixedMoment B raw20600step1 raw20600step1Labels := by
      have hz : ∀ j, raw20600step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20600step1 = (fun i j => raw20600step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20600step1 raw20600step0; decide +kernel
      have hl : raw20600step1Labels = raw20600step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20600step0 raw20600step0Labels permutation56 hz
    mixedMoment B raw20600step1 raw20600step1Labels = mixedMoment B raw20600step2 raw20600step2Labels := by
      have ha : raw20600step2 = (fun i j => raw20600step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20600step2 raw20600step1; decide +kernel
      have hl : raw20600step2Labels = raw20600step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20600step1 raw20600step1Labels permutation8 permutation6
    _ = mixedMoment B node1037 node1037Labels := by rfl

def raw20601 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20601 raw20601Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw20601 raw20601Labels = mixedMoment B raw20601step0 raw20601step0Labels := by
      have hz : ∀ j, raw20601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20601step0 = (fun i j => raw20601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20601step0 raw20601; decide +kernel
      have hl : raw20601step0Labels = raw20601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20601 raw20601Labels permutation434 hz
    mixedMoment B raw20601step0 raw20601step0Labels = mixedMoment B raw20601step1 raw20601step1Labels := by
      have ha : raw20601step1 = (fun i j => raw20601step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20601step1 raw20601step0; decide +kernel
      have hl : raw20601step1Labels = raw20601step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20601step0 raw20601step0Labels permutation32 permutation6
    _ = mixedMoment B node1211 node1211Labels := by rfl

def raw20602 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20602 raw20602Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw20602 raw20602Labels = mixedMoment B raw20602step0 raw20602step0Labels := by
      have hz : ∀ j, raw20602 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20602step0 = (fun i j => raw20602 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20602step0 raw20602; decide +kernel
      have hl : raw20602step0Labels = raw20602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20602 raw20602Labels permutation265 hz
    mixedMoment B raw20602step0 raw20602step0Labels = mixedMoment B raw20602step1 raw20602step1Labels := by
      have ha : raw20602step1 = (fun i j => raw20602step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20602step1 raw20602step0; decide +kernel
      have hl : raw20602step1Labels = raw20602step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20602step0 raw20602step0Labels permutation38 permutation6
    _ = mixedMoment B node1211 node1211Labels := by rfl

def raw20603 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20603step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20603 raw20603Labels = mixedMoment B node1258 node1258Labels := by
  calc
    mixedMoment B raw20603 raw20603Labels = mixedMoment B raw20603step0 raw20603step0Labels := by
      have hz : ∀ j, raw20603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20603step0 = (fun i j => raw20603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20603step0 raw20603; decide +kernel
      have hl : raw20603step0Labels = raw20603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20603 raw20603Labels permutation434 hz
    mixedMoment B raw20603step0 raw20603step0Labels = mixedMoment B raw20603step1 raw20603step1Labels := by
      have hz : ∀ j, raw20603step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20603step1 = (fun i j => raw20603step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20603step1 raw20603step0; decide +kernel
      have hl : raw20603step1Labels = raw20603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20603step0 raw20603step0Labels permutation56 hz
    mixedMoment B raw20603step1 raw20603step1Labels = mixedMoment B raw20603step2 raw20603step2Labels := by
      have ha : raw20603step2 = (fun i j => raw20603step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20603step2 raw20603step1; decide +kernel
      have hl : raw20603step2Labels = raw20603step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20603step1 raw20603step1Labels permutation8 permutation6
    _ = mixedMoment B node1258 node1258Labels := by rfl

def raw20604 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20604step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20604 raw20604Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw20604 raw20604Labels = mixedMoment B raw20604step0 raw20604step0Labels := by
      have hz : ∀ j, raw20604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20604step0 = (fun i j => raw20604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20604step0 raw20604; decide +kernel
      have hl : raw20604step0Labels = raw20604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20604 raw20604Labels permutation434 hz
    mixedMoment B raw20604step0 raw20604step0Labels = mixedMoment B raw20604step1 raw20604step1Labels := by
      have hz : ∀ j, raw20604step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20604step1 = (fun i j => raw20604step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20604step1 raw20604step0; decide +kernel
      have hl : raw20604step1Labels = raw20604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20604step0 raw20604step0Labels permutation56 hz
    mixedMoment B raw20604step1 raw20604step1Labels = mixedMoment B raw20604step2 raw20604step2Labels := by
      have ha : raw20604step2 = (fun i j => raw20604step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20604step2 raw20604step1; decide +kernel
      have hl : raw20604step2Labels = raw20604step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20604step1 raw20604step1Labels permutation8 permutation6
    _ = mixedMoment B node1264 node1264Labels := by rfl

def raw20605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20605step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20605 raw20605Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw20605 raw20605Labels = mixedMoment B raw20605step0 raw20605step0Labels := by
      have hz : ∀ j, raw20605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20605step0 = (fun i j => raw20605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20605step0 raw20605; decide +kernel
      have hl : raw20605step0Labels = raw20605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20605 raw20605Labels permutation346 hz
    mixedMoment B raw20605step0 raw20605step0Labels = mixedMoment B raw20605step1 raw20605step1Labels := by
      have hz : ∀ j, raw20605step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20605step1 = (fun i j => raw20605step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20605step1 raw20605step0; decide +kernel
      have hl : raw20605step1Labels = raw20605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20605step0 raw20605step0Labels permutation56 hz
    mixedMoment B raw20605step1 raw20605step1Labels = mixedMoment B raw20605step2 raw20605step2Labels := by
      have ha : raw20605step2 = (fun i j => raw20605step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20605step2 raw20605step1; decide +kernel
      have hl : raw20605step2Labels = raw20605step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20605step1 raw20605step1Labels permutation8 permutation6
    _ = mixedMoment B node1037 node1037Labels := by rfl

def raw20606 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20606 raw20606Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw20606 raw20606Labels = mixedMoment B raw20606step0 raw20606step0Labels := by
      have hz : ∀ j, raw20606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20606step0 = (fun i j => raw20606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20606step0 raw20606; decide +kernel
      have hl : raw20606step0Labels = raw20606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20606 raw20606Labels permutation346 hz
    mixedMoment B raw20606step0 raw20606step0Labels = mixedMoment B raw20606step1 raw20606step1Labels := by
      have ha : raw20606step1 = (fun i j => raw20606step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20606step1 raw20606step0; decide +kernel
      have hl : raw20606step1Labels = raw20606step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20606step0 raw20606step0Labels permutation32 permutation6
    _ = mixedMoment B node1211 node1211Labels := by rfl

def raw20607 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20607step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20607 raw20607Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw20607 raw20607Labels = mixedMoment B raw20607step0 raw20607step0Labels := by
      have hz : ∀ j, raw20607 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20607step0 = (fun i j => raw20607 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20607step0 raw20607; decide +kernel
      have hl : raw20607step0Labels = raw20607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20607 raw20607Labels permutation265 hz
    mixedMoment B raw20607step0 raw20607step0Labels = mixedMoment B raw20607step1 raw20607step1Labels := by
      have ha : raw20607step1 = (fun i j => raw20607step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20607step1 raw20607step0; decide +kernel
      have hl : raw20607step1Labels = raw20607step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20607step0 raw20607step0Labels permutation32 permutation6
    _ = mixedMoment B node1211 node1211Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
