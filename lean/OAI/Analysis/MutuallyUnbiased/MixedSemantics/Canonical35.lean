import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4480step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw4480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4480 raw4480Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw4480 raw4480Labels = mixedMoment B raw4480step0 raw4480step0Labels := by
      have hz : ∀ j, raw4480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4480step0 = (fun i j => raw4480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4480step0 raw4480; decide +kernel
      have hl : raw4480step0Labels = raw4480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4480 raw4480Labels permutation346 hz
    mixedMoment B raw4480step0 raw4480step0Labels = mixedMoment B raw4480step1 raw4480step1Labels := by
      have hz : ∀ j, raw4480step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4480step1 = (fun i j => raw4480step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4480step1 raw4480step0; decide +kernel
      have hl : raw4480step1Labels = raw4480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4480step0 raw4480step0Labels permutation56 hz
    mixedMoment B raw4480step1 raw4480step1Labels = mixedMoment B raw4480step2 raw4480step2Labels := by
      have ha : raw4480step2 = (fun i j => raw4480step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4480step2 raw4480step1; decide +kernel
      have hl : raw4480step2Labels = raw4480step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4480step1 raw4480step1Labels permutation10 permutation3
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw4481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4481step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4481step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw4481step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4481step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw4481step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4481 raw4481Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw4481 raw4481Labels = mixedMoment B raw4481step0 raw4481step0Labels := by
      have hz : ∀ j, raw4481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4481step0 = (fun i j => raw4481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4481step0 raw4481; decide +kernel
      have hl : raw4481step0Labels = raw4481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4481 raw4481Labels permutation434 hz
    mixedMoment B raw4481step0 raw4481step0Labels = mixedMoment B raw4481step1 raw4481step1Labels := by
      have hz : ∀ j, raw4481step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4481step1 = (fun i j => raw4481step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4481step1 raw4481step0; decide +kernel
      have hl : raw4481step1Labels = raw4481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4481step0 raw4481step0Labels permutation80 hz
    mixedMoment B raw4481step1 raw4481step1Labels = mixedMoment B raw4481step2 raw4481step2Labels := by
      have hz : ∀ j, raw4481step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4481step2 = (fun i j => raw4481step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4481step2 raw4481step1; decide +kernel
      have hl : raw4481step2Labels = raw4481step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4481step1 raw4481step1Labels permutation14 hz
    mixedMoment B raw4481step2 raw4481step2Labels = mixedMoment B raw4481step3 raw4481step3Labels := by
      have ha : raw4481step3 = (fun i j => raw4481step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4481step3 raw4481step2; decide +kernel
      have hl : raw4481step3Labels = raw4481step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4481step2 raw4481step2Labels permutation2 permutation3
    _ = mixedMoment B node1092 node1092Labels := by rfl

def raw4482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4482step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw4482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4482 raw4482Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw4482 raw4482Labels = mixedMoment B raw4482step0 raw4482step0Labels := by
      have hz : ∀ j, raw4482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4482step0 = (fun i j => raw4482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4482step0 raw4482; decide +kernel
      have hl : raw4482step0Labels = raw4482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4482 raw4482Labels permutation434 hz
    mixedMoment B raw4482step0 raw4482step0Labels = mixedMoment B raw4482step1 raw4482step1Labels := by
      have hz : ∀ j, raw4482step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4482step1 = (fun i j => raw4482step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4482step1 raw4482step0; decide +kernel
      have hl : raw4482step1Labels = raw4482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4482step0 raw4482step0Labels permutation80 hz
    mixedMoment B raw4482step1 raw4482step1Labels = mixedMoment B raw4482step2 raw4482step2Labels := by
      have ha : raw4482step2 = (fun i j => raw4482step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4482step2 raw4482step1; decide +kernel
      have hl : raw4482step2Labels = raw4482step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4482step1 raw4482step1Labels permutation8 permutation3
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw4483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw4483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4483 raw4483Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw4483 raw4483Labels = mixedMoment B raw4483step0 raw4483step0Labels := by
      have hz : ∀ j, raw4483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4483step0 = (fun i j => raw4483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4483step0 raw4483; decide +kernel
      have hl : raw4483step0Labels = raw4483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4483 raw4483Labels permutation434 hz
    mixedMoment B raw4483step0 raw4483step0Labels = mixedMoment B raw4483step1 raw4483step1Labels := by
      have hz : ∀ j, raw4483step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4483step1 = (fun i j => raw4483step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4483step1 raw4483step0; decide +kernel
      have hl : raw4483step1Labels = raw4483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4483step0 raw4483step0Labels permutation56 hz
    mixedMoment B raw4483step1 raw4483step1Labels = mixedMoment B raw4483step2 raw4483step2Labels := by
      have ha : raw4483step2 = (fun i j => raw4483step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4483step2 raw4483step1; decide +kernel
      have hl : raw4483step2Labels = raw4483step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4483step1 raw4483step1Labels permutation8 permutation3
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw4484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw4484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4484 raw4484Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw4484 raw4484Labels = mixedMoment B raw4484step0 raw4484step0Labels := by
      have hz : ∀ j, raw4484 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4484step0 = (fun i j => raw4484 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4484step0 raw4484; decide +kernel
      have hl : raw4484step0Labels = raw4484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4484 raw4484Labels permutation346 hz
    mixedMoment B raw4484step0 raw4484step0Labels = mixedMoment B raw4484step1 raw4484step1Labels := by
      have hz : ∀ j, raw4484step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4484step1 = (fun i j => raw4484step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4484step1 raw4484step0; decide +kernel
      have hl : raw4484step1Labels = raw4484step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4484step0 raw4484step0Labels permutation56 hz
    mixedMoment B raw4484step1 raw4484step1Labels = mixedMoment B raw4484step2 raw4484step2Labels := by
      have ha : raw4484step2 = (fun i j => raw4484step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4484step2 raw4484step1; decide +kernel
      have hl : raw4484step2Labels = raw4484step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4484step1 raw4484step1Labels permutation8 permutation3
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw4485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4485step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4485step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw4485step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4485step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4485step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4485 raw4485Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw4485 raw4485Labels = mixedMoment B raw4485step0 raw4485step0Labels := by
      have hz : ∀ j, raw4485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4485step0 = (fun i j => raw4485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4485step0 raw4485; decide +kernel
      have hl : raw4485step0Labels = raw4485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4485 raw4485Labels permutation434 hz
    mixedMoment B raw4485step0 raw4485step0Labels = mixedMoment B raw4485step1 raw4485step1Labels := by
      have hz : ∀ j, raw4485step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4485step1 = (fun i j => raw4485step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4485step1 raw4485step0; decide +kernel
      have hl : raw4485step1Labels = raw4485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4485step0 raw4485step0Labels permutation80 hz
    mixedMoment B raw4485step1 raw4485step1Labels = mixedMoment B raw4485step2 raw4485step2Labels := by
      have hz : ∀ j, raw4485step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4485step2 = (fun i j => raw4485step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4485step2 raw4485step1; decide +kernel
      have hl : raw4485step2Labels = raw4485step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4485step1 raw4485step1Labels permutation14 hz
    mixedMoment B raw4485step2 raw4485step2Labels = mixedMoment B raw4485step3 raw4485step3Labels := by
      have ha : raw4485step3 = (fun i j => raw4485step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4485step3 raw4485step2; decide +kernel
      have hl : raw4485step3Labels = raw4485step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4485step2 raw4485step2Labels permutation2 permutation3
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw4486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4486step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4486step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![4, -1, -3]]
def raw4486step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4486step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw4486step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4486 raw4486Labels = mixedMoment B node1064 node1064Labels := by
  calc
    mixedMoment B raw4486 raw4486Labels = mixedMoment B raw4486step0 raw4486step0Labels := by
      have hz : ∀ j, raw4486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4486step0 = (fun i j => raw4486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4486step0 raw4486; decide +kernel
      have hl : raw4486step0Labels = raw4486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4486 raw4486Labels permutation434 hz
    mixedMoment B raw4486step0 raw4486step0Labels = mixedMoment B raw4486step1 raw4486step1Labels := by
      have hz : ∀ j, raw4486step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4486step1 = (fun i j => raw4486step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4486step1 raw4486step0; decide +kernel
      have hl : raw4486step1Labels = raw4486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4486step0 raw4486step0Labels permutation80 hz
    mixedMoment B raw4486step1 raw4486step1Labels = mixedMoment B raw4486step2 raw4486step2Labels := by
      have hz : ∀ j, raw4486step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4486step2 = (fun i j => raw4486step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4486step2 raw4486step1; decide +kernel
      have hl : raw4486step2Labels = raw4486step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4486step1 raw4486step1Labels permutation14 hz
    mixedMoment B raw4486step2 raw4486step2Labels = mixedMoment B raw4486step3 raw4486step3Labels := by
      have ha : raw4486step3 = (fun i j => raw4486step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4486step3 raw4486step2; decide +kernel
      have hl : raw4486step3Labels = raw4486step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4486step2 raw4486step2Labels permutation2 permutation3
    _ = mixedMoment B node1064 node1064Labels := by rfl

def raw4487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4487step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-3, 1, 2]]
def raw4487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4487step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw4487step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4487 raw4487Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw4487 raw4487Labels = mixedMoment B raw4487step0 raw4487step0Labels := by
      have hz : ∀ j, raw4487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4487step0 = (fun i j => raw4487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4487step0 raw4487; decide +kernel
      have hl : raw4487step0Labels = raw4487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4487 raw4487Labels permutation434 hz
    mixedMoment B raw4487step0 raw4487step0Labels = mixedMoment B raw4487step1 raw4487step1Labels := by
      have hz : ∀ j, raw4487step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4487step1 = (fun i j => raw4487step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4487step1 raw4487step0; decide +kernel
      have hl : raw4487step1Labels = raw4487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4487step0 raw4487step0Labels permutation80 hz
    mixedMoment B raw4487step1 raw4487step1Labels = mixedMoment B raw4487step2 raw4487step2Labels := by
      have ha : raw4487step2 = (fun i j => raw4487step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4487step2 raw4487step1; decide +kernel
      have hl : raw4487step2Labels = raw4487step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4487step1 raw4487step1Labels permutation31 permutation3
    mixedMoment B raw4487step2 raw4487step2Labels = mixedMoment B raw4487step3 raw4487step3Labels := by
      have ha : raw4487step3 = -raw4487step2 := by apply Matrix.ext; change ∀ i j, raw4487step3 i j = -(raw4487step2 i j); unfold raw4487step3 raw4487step2; decide +kernel
      have hl : raw4487step3Labels = raw4487step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1372 node1372Labels := by rfl

def raw4488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4488step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-3, 1, 2]]
def raw4488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4488step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw4488step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4488 raw4488Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw4488 raw4488Labels = mixedMoment B raw4488step0 raw4488step0Labels := by
      have hz : ∀ j, raw4488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4488step0 = (fun i j => raw4488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4488step0 raw4488; decide +kernel
      have hl : raw4488step0Labels = raw4488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4488 raw4488Labels permutation434 hz
    mixedMoment B raw4488step0 raw4488step0Labels = mixedMoment B raw4488step1 raw4488step1Labels := by
      have hz : ∀ j, raw4488step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4488step1 = (fun i j => raw4488step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4488step1 raw4488step0; decide +kernel
      have hl : raw4488step1Labels = raw4488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4488step0 raw4488step0Labels permutation56 hz
    mixedMoment B raw4488step1 raw4488step1Labels = mixedMoment B raw4488step2 raw4488step2Labels := by
      have ha : raw4488step2 = (fun i j => raw4488step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4488step2 raw4488step1; decide +kernel
      have hl : raw4488step2Labels = raw4488step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4488step1 raw4488step1Labels permutation31 permutation3
    mixedMoment B raw4488step2 raw4488step2Labels = mixedMoment B raw4488step3 raw4488step3Labels := by
      have ha : raw4488step3 = -raw4488step2 := by apply Matrix.ext; change ∀ i j, raw4488step3 i j = -(raw4488step2 i j); unfold raw4488step3 raw4488step2; decide +kernel
      have hl : raw4488step3Labels = raw4488step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1372 node1372Labels := by rfl

def raw4489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4489step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-3, 1, 2]]
def raw4489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4489step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw4489step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4489 raw4489Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw4489 raw4489Labels = mixedMoment B raw4489step0 raw4489step0Labels := by
      have hz : ∀ j, raw4489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4489step0 = (fun i j => raw4489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4489step0 raw4489; decide +kernel
      have hl : raw4489step0Labels = raw4489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4489 raw4489Labels permutation346 hz
    mixedMoment B raw4489step0 raw4489step0Labels = mixedMoment B raw4489step1 raw4489step1Labels := by
      have hz : ∀ j, raw4489step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4489step1 = (fun i j => raw4489step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4489step1 raw4489step0; decide +kernel
      have hl : raw4489step1Labels = raw4489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4489step0 raw4489step0Labels permutation56 hz
    mixedMoment B raw4489step1 raw4489step1Labels = mixedMoment B raw4489step2 raw4489step2Labels := by
      have ha : raw4489step2 = (fun i j => raw4489step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4489step2 raw4489step1; decide +kernel
      have hl : raw4489step2Labels = raw4489step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4489step1 raw4489step1Labels permutation31 permutation3
    mixedMoment B raw4489step2 raw4489step2Labels = mixedMoment B raw4489step3 raw4489step3Labels := by
      have ha : raw4489step3 = -raw4489step2 := by apply Matrix.ext; change ∀ i j, raw4489step3 i j = -(raw4489step2 i j); unfold raw4489step3 raw4489step2; decide +kernel
      have hl : raw4489step3Labels = raw4489step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1372 node1372Labels := by rfl

def raw4490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4490step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw4490step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4490step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4490step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4490step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw4490step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4490 raw4490Labels = mixedMoment B node1445 node1445Labels := by
  calc
    mixedMoment B raw4490 raw4490Labels = mixedMoment B raw4490step0 raw4490step0Labels := by
      have hz : ∀ j, raw4490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4490step0 = (fun i j => raw4490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4490step0 raw4490; decide +kernel
      have hl : raw4490step0Labels = raw4490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4490 raw4490Labels permutation434 hz
    mixedMoment B raw4490step0 raw4490step0Labels = mixedMoment B raw4490step1 raw4490step1Labels := by
      have hz : ∀ j, raw4490step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4490step1 = (fun i j => raw4490step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4490step1 raw4490step0; decide +kernel
      have hl : raw4490step1Labels = raw4490step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4490step0 raw4490step0Labels permutation80 hz
    mixedMoment B raw4490step1 raw4490step1Labels = mixedMoment B raw4490step2 raw4490step2Labels := by
      have hz : ∀ j, raw4490step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4490step2 = (fun i j => raw4490step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4490step2 raw4490step1; decide +kernel
      have hl : raw4490step2Labels = raw4490step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4490step1 raw4490step1Labels permutation14 hz
    mixedMoment B raw4490step2 raw4490step2Labels = mixedMoment B raw4490step3 raw4490step3Labels := by
      have ha : raw4490step3 = (fun i j => raw4490step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4490step3 raw4490step2; decide +kernel
      have hl : raw4490step3Labels = raw4490step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4490step2 raw4490step2Labels permutation7 permutation3
    mixedMoment B raw4490step3 raw4490step3Labels = mixedMoment B raw4490step4 raw4490step4Labels := by
      have ha : raw4490step4 = -raw4490step3 := by apply Matrix.ext; change ∀ i j, raw4490step4 i j = -(raw4490step3 i j); unfold raw4490step4 raw4490step3; decide +kernel
      have hl : raw4490step4Labels = raw4490step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1445 node1445Labels := by rfl

def raw4491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4491step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4491step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4491step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4491step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4491step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4491step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4491step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4491 raw4491Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw4491 raw4491Labels = mixedMoment B raw4491step0 raw4491step0Labels := by
      have hz : ∀ j, raw4491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4491step0 = (fun i j => raw4491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4491step0 raw4491; decide +kernel
      have hl : raw4491step0Labels = raw4491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4491 raw4491Labels permutation434 hz
    mixedMoment B raw4491step0 raw4491step0Labels = mixedMoment B raw4491step1 raw4491step1Labels := by
      have hz : ∀ j, raw4491step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4491step1 = (fun i j => raw4491step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4491step1 raw4491step0; decide +kernel
      have hl : raw4491step1Labels = raw4491step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4491step0 raw4491step0Labels permutation80 hz
    mixedMoment B raw4491step1 raw4491step1Labels = mixedMoment B raw4491step2 raw4491step2Labels := by
      have ha : raw4491step2 = (fun i j => raw4491step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4491step2 raw4491step1; decide +kernel
      have hl : raw4491step2Labels = raw4491step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4491step1 raw4491step1Labels permutation28 permutation7
    mixedMoment B raw4491step2 raw4491step2Labels = mixedMoment B raw4491step3 raw4491step3Labels := by
      have ha : raw4491step3 = raw4491step2 := by apply Matrix.ext; unfold raw4491step3 raw4491step2; decide +kernel
      have hl : raw4491step2Labels = labelEmbedding1 ∘ raw4491step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4491step2 raw4491step2Labels raw4491step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw4492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4492step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4492step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4492step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4492step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4492step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4492 raw4492Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw4492 raw4492Labels = mixedMoment B raw4492step0 raw4492step0Labels := by
      have hz : ∀ j, raw4492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4492step0 = (fun i j => raw4492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4492step0 raw4492; decide +kernel
      have hl : raw4492step0Labels = raw4492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4492 raw4492Labels permutation434 hz
    mixedMoment B raw4492step0 raw4492step0Labels = mixedMoment B raw4492step1 raw4492step1Labels := by
      have hz : ∀ j, raw4492step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4492step1 = (fun i j => raw4492step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4492step1 raw4492step0; decide +kernel
      have hl : raw4492step1Labels = raw4492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4492step0 raw4492step0Labels permutation56 hz
    mixedMoment B raw4492step1 raw4492step1Labels = mixedMoment B raw4492step2 raw4492step2Labels := by
      have ha : raw4492step2 = (fun i j => raw4492step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4492step2 raw4492step1; decide +kernel
      have hl : raw4492step2Labels = raw4492step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4492step1 raw4492step1Labels permutation28 permutation7
    mixedMoment B raw4492step2 raw4492step2Labels = mixedMoment B raw4492step3 raw4492step3Labels := by
      have ha : raw4492step3 = raw4492step2 := by apply Matrix.ext; unfold raw4492step3 raw4492step2; decide +kernel
      have hl : raw4492step2Labels = labelEmbedding1 ∘ raw4492step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4492step2 raw4492step2Labels raw4492step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw4493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4493step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4493step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4493step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4493step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4493step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4493 raw4493Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw4493 raw4493Labels = mixedMoment B raw4493step0 raw4493step0Labels := by
      have hz : ∀ j, raw4493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4493step0 = (fun i j => raw4493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4493step0 raw4493; decide +kernel
      have hl : raw4493step0Labels = raw4493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4493 raw4493Labels permutation346 hz
    mixedMoment B raw4493step0 raw4493step0Labels = mixedMoment B raw4493step1 raw4493step1Labels := by
      have hz : ∀ j, raw4493step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4493step1 = (fun i j => raw4493step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4493step1 raw4493step0; decide +kernel
      have hl : raw4493step1Labels = raw4493step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4493step0 raw4493step0Labels permutation56 hz
    mixedMoment B raw4493step1 raw4493step1Labels = mixedMoment B raw4493step2 raw4493step2Labels := by
      have ha : raw4493step2 = (fun i j => raw4493step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4493step2 raw4493step1; decide +kernel
      have hl : raw4493step2Labels = raw4493step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4493step1 raw4493step1Labels permutation28 permutation7
    mixedMoment B raw4493step2 raw4493step2Labels = mixedMoment B raw4493step3 raw4493step3Labels := by
      have ha : raw4493step3 = raw4493step2 := by apply Matrix.ext; unfold raw4493step3 raw4493step2; decide +kernel
      have hl : raw4493step2Labels = labelEmbedding1 ∘ raw4493step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4493step2 raw4493step2Labels raw4493step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw4494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4494step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4494step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4494step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw4494step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4494step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw4494step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4494step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw4494step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4494 raw4494Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw4494 raw4494Labels = mixedMoment B raw4494step0 raw4494step0Labels := by
      have hz : ∀ j, raw4494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4494step0 = (fun i j => raw4494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4494step0 raw4494; decide +kernel
      have hl : raw4494step0Labels = raw4494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4494 raw4494Labels permutation434 hz
    mixedMoment B raw4494step0 raw4494step0Labels = mixedMoment B raw4494step1 raw4494step1Labels := by
      have hz : ∀ j, raw4494step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4494step1 = (fun i j => raw4494step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4494step1 raw4494step0; decide +kernel
      have hl : raw4494step1Labels = raw4494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4494step0 raw4494step0Labels permutation80 hz
    mixedMoment B raw4494step1 raw4494step1Labels = mixedMoment B raw4494step2 raw4494step2Labels := by
      have hz : ∀ j, raw4494step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4494step2 = (fun i j => raw4494step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4494step2 raw4494step1; decide +kernel
      have hl : raw4494step2Labels = raw4494step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4494step1 raw4494step1Labels permutation14 hz
    mixedMoment B raw4494step2 raw4494step2Labels = mixedMoment B raw4494step3 raw4494step3Labels := by
      have ha : raw4494step3 = (fun i j => raw4494step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4494step3 raw4494step2; decide +kernel
      have hl : raw4494step3Labels = raw4494step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4494step2 raw4494step2Labels permutation6 permutation7
    mixedMoment B raw4494step3 raw4494step3Labels = mixedMoment B raw4494step4 raw4494step4Labels := by
      have ha : raw4494step4 = raw4494step3 := by apply Matrix.ext; unfold raw4494step4 raw4494step3; decide +kernel
      have hl : raw4494step3Labels = labelEmbedding1 ∘ raw4494step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4494step3 raw4494step3Labels raw4494step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw4495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4495step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4495step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4495step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw4495step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4495step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4495step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4495step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4495step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4495 raw4495Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw4495 raw4495Labels = mixedMoment B raw4495step0 raw4495step0Labels := by
      have hz : ∀ j, raw4495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4495step0 = (fun i j => raw4495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4495step0 raw4495; decide +kernel
      have hl : raw4495step0Labels = raw4495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4495 raw4495Labels permutation434 hz
    mixedMoment B raw4495step0 raw4495step0Labels = mixedMoment B raw4495step1 raw4495step1Labels := by
      have hz : ∀ j, raw4495step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4495step1 = (fun i j => raw4495step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4495step1 raw4495step0; decide +kernel
      have hl : raw4495step1Labels = raw4495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4495step0 raw4495step0Labels permutation80 hz
    mixedMoment B raw4495step1 raw4495step1Labels = mixedMoment B raw4495step2 raw4495step2Labels := by
      have hz : ∀ j, raw4495step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4495step2 = (fun i j => raw4495step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4495step2 raw4495step1; decide +kernel
      have hl : raw4495step2Labels = raw4495step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4495step1 raw4495step1Labels permutation14 hz
    mixedMoment B raw4495step2 raw4495step2Labels = mixedMoment B raw4495step3 raw4495step3Labels := by
      have ha : raw4495step3 = (fun i j => raw4495step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4495step3 raw4495step2; decide +kernel
      have hl : raw4495step3Labels = raw4495step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4495step2 raw4495step2Labels permutation6 permutation7
    mixedMoment B raw4495step3 raw4495step3Labels = mixedMoment B raw4495step4 raw4495step4Labels := by
      have ha : raw4495step4 = raw4495step3 := by apply Matrix.ext; unfold raw4495step4 raw4495step3; decide +kernel
      have hl : raw4495step3Labels = labelEmbedding1 ∘ raw4495step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4495step3 raw4495step3Labels raw4495step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw4496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4496step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4496step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4496step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw4496step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4496step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4496step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4496step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4496step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4496 raw4496Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw4496 raw4496Labels = mixedMoment B raw4496step0 raw4496step0Labels := by
      have hz : ∀ j, raw4496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4496step0 = (fun i j => raw4496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4496step0 raw4496; decide +kernel
      have hl : raw4496step0Labels = raw4496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4496 raw4496Labels permutation434 hz
    mixedMoment B raw4496step0 raw4496step0Labels = mixedMoment B raw4496step1 raw4496step1Labels := by
      have hz : ∀ j, raw4496step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4496step1 = (fun i j => raw4496step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4496step1 raw4496step0; decide +kernel
      have hl : raw4496step1Labels = raw4496step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4496step0 raw4496step0Labels permutation80 hz
    mixedMoment B raw4496step1 raw4496step1Labels = mixedMoment B raw4496step2 raw4496step2Labels := by
      have ha : raw4496step2 = (fun i j => raw4496step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4496step2 raw4496step1; decide +kernel
      have hl : raw4496step2Labels = raw4496step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4496step1 raw4496step1Labels permutation12 permutation5
    mixedMoment B raw4496step2 raw4496step2Labels = mixedMoment B raw4496step3 raw4496step3Labels := by
      have ha : raw4496step3 = -raw4496step2 := by apply Matrix.ext; change ∀ i j, raw4496step3 i j = -(raw4496step2 i j); unfold raw4496step3 raw4496step2; decide +kernel
      have hl : raw4496step3Labels = raw4496step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4496step3 raw4496step3Labels = mixedMoment B raw4496step4 raw4496step4Labels := by
      have ha : raw4496step4 = raw4496step3 := by apply Matrix.ext; unfold raw4496step4 raw4496step3; decide +kernel
      have hl : raw4496step3Labels = labelEmbedding1 ∘ raw4496step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4496step3 raw4496step3Labels raw4496step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw4497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4497step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4497 raw4497Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4497 raw4497Labels = mixedMoment B raw4497step0 raw4497step0Labels := by
      have hz : ∀ j, raw4497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4497step0 = (fun i j => raw4497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4497step0 raw4497; decide +kernel
      have hl : raw4497step0Labels = raw4497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4497 raw4497Labels permutation434 hz
    mixedMoment B raw4497step0 raw4497step0Labels = mixedMoment B raw4497step1 raw4497step1Labels := by
      have ha : raw4497step1 = (fun i j => raw4497step0 (permutation136 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4497step1 raw4497step0; decide +kernel
      have hl : raw4497step1Labels = raw4497step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4497step0 raw4497step0Labels permutation136 permutation7
    mixedMoment B raw4497step1 raw4497step1Labels = mixedMoment B raw4497step2 raw4497step2Labels := by
      have ha : raw4497step2 = raw4497step1 := by apply Matrix.ext; unfold raw4497step2 raw4497step1; decide +kernel
      have hl : raw4497step1Labels = labelEmbedding1 ∘ raw4497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4497step1 raw4497step1Labels raw4497step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw4498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4498step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4498 raw4498Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4498 raw4498Labels = mixedMoment B raw4498step0 raw4498step0Labels := by
      have hz : ∀ j, raw4498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4498step0 = (fun i j => raw4498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4498step0 raw4498; decide +kernel
      have hl : raw4498step0Labels = raw4498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4498 raw4498Labels permutation346 hz
    mixedMoment B raw4498step0 raw4498step0Labels = mixedMoment B raw4498step1 raw4498step1Labels := by
      have ha : raw4498step1 = (fun i j => raw4498step0 (permutation136 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4498step1 raw4498step0; decide +kernel
      have hl : raw4498step1Labels = raw4498step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4498step0 raw4498step0Labels permutation136 permutation7
    mixedMoment B raw4498step1 raw4498step1Labels = mixedMoment B raw4498step2 raw4498step2Labels := by
      have ha : raw4498step2 = raw4498step1 := by apply Matrix.ext; unfold raw4498step2 raw4498step1; decide +kernel
      have hl : raw4498step1Labels = labelEmbedding1 ∘ raw4498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4498step1 raw4498step1Labels raw4498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw4499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4499step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4499step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4499step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4499step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4499 raw4499Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw4499 raw4499Labels = mixedMoment B raw4499step0 raw4499step0Labels := by
      have hz : ∀ j, raw4499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4499step0 = (fun i j => raw4499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4499step0 raw4499; decide +kernel
      have hl : raw4499step0Labels = raw4499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4499 raw4499Labels permutation434 hz
    mixedMoment B raw4499step0 raw4499step0Labels = mixedMoment B raw4499step1 raw4499step1Labels := by
      have hz : ∀ j, raw4499step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4499step1 = (fun i j => raw4499step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4499step1 raw4499step0; decide +kernel
      have hl : raw4499step1Labels = raw4499step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4499step0 raw4499step0Labels permutation80 hz
    mixedMoment B raw4499step1 raw4499step1Labels = mixedMoment B raw4499step2 raw4499step2Labels := by
      have ha : raw4499step2 = (fun i j => raw4499step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4499step2 raw4499step1; decide +kernel
      have hl : raw4499step2Labels = raw4499step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4499step1 raw4499step1Labels permutation28 permutation7
    mixedMoment B raw4499step2 raw4499step2Labels = mixedMoment B raw4499step3 raw4499step3Labels := by
      have ha : raw4499step3 = raw4499step2 := by apply Matrix.ext; unfold raw4499step3 raw4499step2; decide +kernel
      have hl : raw4499step2Labels = labelEmbedding1 ∘ raw4499step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4499step2 raw4499step2Labels raw4499step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw4500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4500step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4500step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4500step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4500step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4500 raw4500Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw4500 raw4500Labels = mixedMoment B raw4500step0 raw4500step0Labels := by
      have hz : ∀ j, raw4500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4500step0 = (fun i j => raw4500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4500step0 raw4500; decide +kernel
      have hl : raw4500step0Labels = raw4500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4500 raw4500Labels permutation434 hz
    mixedMoment B raw4500step0 raw4500step0Labels = mixedMoment B raw4500step1 raw4500step1Labels := by
      have hz : ∀ j, raw4500step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4500step1 = (fun i j => raw4500step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4500step1 raw4500step0; decide +kernel
      have hl : raw4500step1Labels = raw4500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4500step0 raw4500step0Labels permutation80 hz
    mixedMoment B raw4500step1 raw4500step1Labels = mixedMoment B raw4500step2 raw4500step2Labels := by
      have ha : raw4500step2 = (fun i j => raw4500step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4500step2 raw4500step1; decide +kernel
      have hl : raw4500step2Labels = raw4500step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4500step1 raw4500step1Labels permutation28 permutation7
    mixedMoment B raw4500step2 raw4500step2Labels = mixedMoment B raw4500step3 raw4500step3Labels := by
      have ha : raw4500step3 = raw4500step2 := by apply Matrix.ext; unfold raw4500step3 raw4500step2; decide +kernel
      have hl : raw4500step2Labels = labelEmbedding1 ∘ raw4500step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4500step2 raw4500step2Labels raw4500step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw4501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4501step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4501step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4501step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw4501step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4501step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4501step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4501step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4501step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4501 raw4501Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw4501 raw4501Labels = mixedMoment B raw4501step0 raw4501step0Labels := by
      have hz : ∀ j, raw4501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4501step0 = (fun i j => raw4501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4501step0 raw4501; decide +kernel
      have hl : raw4501step0Labels = raw4501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4501 raw4501Labels permutation434 hz
    mixedMoment B raw4501step0 raw4501step0Labels = mixedMoment B raw4501step1 raw4501step1Labels := by
      have hz : ∀ j, raw4501step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4501step1 = (fun i j => raw4501step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4501step1 raw4501step0; decide +kernel
      have hl : raw4501step1Labels = raw4501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4501step0 raw4501step0Labels permutation56 hz
    mixedMoment B raw4501step1 raw4501step1Labels = mixedMoment B raw4501step2 raw4501step2Labels := by
      have ha : raw4501step2 = (fun i j => raw4501step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4501step2 raw4501step1; decide +kernel
      have hl : raw4501step2Labels = raw4501step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4501step1 raw4501step1Labels permutation12 permutation5
    mixedMoment B raw4501step2 raw4501step2Labels = mixedMoment B raw4501step3 raw4501step3Labels := by
      have ha : raw4501step3 = -raw4501step2 := by apply Matrix.ext; change ∀ i j, raw4501step3 i j = -(raw4501step2 i j); unfold raw4501step3 raw4501step2; decide +kernel
      have hl : raw4501step3Labels = raw4501step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4501step3 raw4501step3Labels = mixedMoment B raw4501step4 raw4501step4Labels := by
      have ha : raw4501step4 = raw4501step3 := by apply Matrix.ext; unfold raw4501step4 raw4501step3; decide +kernel
      have hl : raw4501step3Labels = labelEmbedding1 ∘ raw4501step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4501step3 raw4501step3Labels raw4501step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw4502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4502 raw4502Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4502 raw4502Labels = mixedMoment B raw4502step0 raw4502step0Labels := by
      have hz : ∀ j, raw4502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4502step0 = (fun i j => raw4502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4502step0 raw4502; decide +kernel
      have hl : raw4502step0Labels = raw4502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4502 raw4502Labels permutation434 hz
    mixedMoment B raw4502step0 raw4502step0Labels = mixedMoment B raw4502step1 raw4502step1Labels := by
      have ha : raw4502step1 = (fun i j => raw4502step0 (permutation142 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4502step1 raw4502step0; decide +kernel
      have hl : raw4502step1Labels = raw4502step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4502step0 raw4502step0Labels permutation142 permutation7
    mixedMoment B raw4502step1 raw4502step1Labels = mixedMoment B raw4502step2 raw4502step2Labels := by
      have ha : raw4502step2 = raw4502step1 := by apply Matrix.ext; unfold raw4502step2 raw4502step1; decide +kernel
      have hl : raw4502step1Labels = labelEmbedding1 ∘ raw4502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4502step1 raw4502step1Labels raw4502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw4503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4503 raw4503Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4503 raw4503Labels = mixedMoment B raw4503step0 raw4503step0Labels := by
      have hz : ∀ j, raw4503 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4503step0 = (fun i j => raw4503 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4503step0 raw4503; decide +kernel
      have hl : raw4503step0Labels = raw4503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4503 raw4503Labels permutation265 hz
    mixedMoment B raw4503step0 raw4503step0Labels = mixedMoment B raw4503step1 raw4503step1Labels := by
      have ha : raw4503step1 = (fun i j => raw4503step0 (permutation136 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4503step1 raw4503step0; decide +kernel
      have hl : raw4503step1Labels = raw4503step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4503step0 raw4503step0Labels permutation136 permutation7
    mixedMoment B raw4503step1 raw4503step1Labels = mixedMoment B raw4503step2 raw4503step2Labels := by
      have ha : raw4503step2 = raw4503step1 := by apply Matrix.ext; unfold raw4503step2 raw4503step1; decide +kernel
      have hl : raw4503step1Labels = labelEmbedding1 ∘ raw4503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4503step1 raw4503step1Labels raw4503step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw4504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4504step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4504step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4504step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4504step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4504step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4504step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4504 raw4504Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw4504 raw4504Labels = mixedMoment B raw4504step0 raw4504step0Labels := by
      have hz : ∀ j, raw4504 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4504step0 = (fun i j => raw4504 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4504step0 raw4504; decide +kernel
      have hl : raw4504step0Labels = raw4504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4504 raw4504Labels permutation434 hz
    mixedMoment B raw4504step0 raw4504step0Labels = mixedMoment B raw4504step1 raw4504step1Labels := by
      have hz : ∀ j, raw4504step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4504step1 = (fun i j => raw4504step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4504step1 raw4504step0; decide +kernel
      have hl : raw4504step1Labels = raw4504step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4504step0 raw4504step0Labels permutation56 hz
    mixedMoment B raw4504step1 raw4504step1Labels = mixedMoment B raw4504step2 raw4504step2Labels := by
      have ha : raw4504step2 = (fun i j => raw4504step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4504step2 raw4504step1; decide +kernel
      have hl : raw4504step2Labels = raw4504step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4504step1 raw4504step1Labels permutation28 permutation7
    mixedMoment B raw4504step2 raw4504step2Labels = mixedMoment B raw4504step3 raw4504step3Labels := by
      have ha : raw4504step3 = raw4504step2 := by apply Matrix.ext; unfold raw4504step3 raw4504step2; decide +kernel
      have hl : raw4504step2Labels = labelEmbedding1 ∘ raw4504step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4504step2 raw4504step2Labels raw4504step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw4505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4505step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4505step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4505 raw4505Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw4505 raw4505Labels = mixedMoment B raw4505step0 raw4505step0Labels := by
      have hz : ∀ j, raw4505 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4505step0 = (fun i j => raw4505 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4505step0 raw4505; decide +kernel
      have hl : raw4505step0Labels = raw4505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4505 raw4505Labels permutation434 hz
    mixedMoment B raw4505step0 raw4505step0Labels = mixedMoment B raw4505step1 raw4505step1Labels := by
      have hz : ∀ j, raw4505step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4505step1 = (fun i j => raw4505step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4505step1 raw4505step0; decide +kernel
      have hl : raw4505step1Labels = raw4505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4505step0 raw4505step0Labels permutation56 hz
    mixedMoment B raw4505step1 raw4505step1Labels = mixedMoment B raw4505step2 raw4505step2Labels := by
      have ha : raw4505step2 = (fun i j => raw4505step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4505step2 raw4505step1; decide +kernel
      have hl : raw4505step2Labels = raw4505step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4505step1 raw4505step1Labels permutation28 permutation7
    mixedMoment B raw4505step2 raw4505step2Labels = mixedMoment B raw4505step3 raw4505step3Labels := by
      have ha : raw4505step3 = raw4505step2 := by apply Matrix.ext; unfold raw4505step3 raw4505step2; decide +kernel
      have hl : raw4505step2Labels = labelEmbedding1 ∘ raw4505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4505step2 raw4505step2Labels raw4505step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw4506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4506step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4506step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw4506step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4506step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4506step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4506step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4506step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4506 raw4506Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw4506 raw4506Labels = mixedMoment B raw4506step0 raw4506step0Labels := by
      have hz : ∀ j, raw4506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4506step0 = (fun i j => raw4506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4506step0 raw4506; decide +kernel
      have hl : raw4506step0Labels = raw4506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4506 raw4506Labels permutation346 hz
    mixedMoment B raw4506step0 raw4506step0Labels = mixedMoment B raw4506step1 raw4506step1Labels := by
      have hz : ∀ j, raw4506step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4506step1 = (fun i j => raw4506step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4506step1 raw4506step0; decide +kernel
      have hl : raw4506step1Labels = raw4506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4506step0 raw4506step0Labels permutation56 hz
    mixedMoment B raw4506step1 raw4506step1Labels = mixedMoment B raw4506step2 raw4506step2Labels := by
      have ha : raw4506step2 = (fun i j => raw4506step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4506step2 raw4506step1; decide +kernel
      have hl : raw4506step2Labels = raw4506step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4506step1 raw4506step1Labels permutation12 permutation5
    mixedMoment B raw4506step2 raw4506step2Labels = mixedMoment B raw4506step3 raw4506step3Labels := by
      have ha : raw4506step3 = -raw4506step2 := by apply Matrix.ext; change ∀ i j, raw4506step3 i j = -(raw4506step2 i j); unfold raw4506step3 raw4506step2; decide +kernel
      have hl : raw4506step3Labels = raw4506step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4506step3 raw4506step3Labels = mixedMoment B raw4506step4 raw4506step4Labels := by
      have ha : raw4506step4 = raw4506step3 := by apply Matrix.ext; unfold raw4506step4 raw4506step3; decide +kernel
      have hl : raw4506step3Labels = labelEmbedding1 ∘ raw4506step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4506step3 raw4506step3Labels raw4506step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw4507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4507 raw4507Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4507 raw4507Labels = mixedMoment B raw4507step0 raw4507step0Labels := by
      have hz : ∀ j, raw4507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4507step0 = (fun i j => raw4507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4507step0 raw4507; decide +kernel
      have hl : raw4507step0Labels = raw4507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4507 raw4507Labels permutation346 hz
    mixedMoment B raw4507step0 raw4507step0Labels = mixedMoment B raw4507step1 raw4507step1Labels := by
      have ha : raw4507step1 = (fun i j => raw4507step0 (permutation142 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4507step1 raw4507step0; decide +kernel
      have hl : raw4507step1Labels = raw4507step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4507step0 raw4507step0Labels permutation142 permutation7
    mixedMoment B raw4507step1 raw4507step1Labels = mixedMoment B raw4507step2 raw4507step2Labels := by
      have ha : raw4507step2 = raw4507step1 := by apply Matrix.ext; unfold raw4507step2 raw4507step1; decide +kernel
      have hl : raw4507step1Labels = labelEmbedding1 ∘ raw4507step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4507step1 raw4507step1Labels raw4507step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw4508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4508step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4508 raw4508Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4508 raw4508Labels = mixedMoment B raw4508step0 raw4508step0Labels := by
      have hz : ∀ j, raw4508 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4508step0 = (fun i j => raw4508 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4508step0 raw4508; decide +kernel
      have hl : raw4508step0Labels = raw4508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4508 raw4508Labels permutation265 hz
    mixedMoment B raw4508step0 raw4508step0Labels = mixedMoment B raw4508step1 raw4508step1Labels := by
      have ha : raw4508step1 = (fun i j => raw4508step0 (permutation142 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4508step1 raw4508step0; decide +kernel
      have hl : raw4508step1Labels = raw4508step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4508step0 raw4508step0Labels permutation142 permutation7
    mixedMoment B raw4508step1 raw4508step1Labels = mixedMoment B raw4508step2 raw4508step2Labels := by
      have ha : raw4508step2 = raw4508step1 := by apply Matrix.ext; unfold raw4508step2 raw4508step1; decide +kernel
      have hl : raw4508step1Labels = labelEmbedding1 ∘ raw4508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4508step1 raw4508step1Labels raw4508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw4509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4509step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4509step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4509step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4509step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4509 raw4509Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw4509 raw4509Labels = mixedMoment B raw4509step0 raw4509step0Labels := by
      have hz : ∀ j, raw4509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4509step0 = (fun i j => raw4509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4509step0 raw4509; decide +kernel
      have hl : raw4509step0Labels = raw4509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4509 raw4509Labels permutation346 hz
    mixedMoment B raw4509step0 raw4509step0Labels = mixedMoment B raw4509step1 raw4509step1Labels := by
      have hz : ∀ j, raw4509step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4509step1 = (fun i j => raw4509step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4509step1 raw4509step0; decide +kernel
      have hl : raw4509step1Labels = raw4509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4509step0 raw4509step0Labels permutation56 hz
    mixedMoment B raw4509step1 raw4509step1Labels = mixedMoment B raw4509step2 raw4509step2Labels := by
      have ha : raw4509step2 = (fun i j => raw4509step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4509step2 raw4509step1; decide +kernel
      have hl : raw4509step2Labels = raw4509step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4509step1 raw4509step1Labels permutation28 permutation7
    mixedMoment B raw4509step2 raw4509step2Labels = mixedMoment B raw4509step3 raw4509step3Labels := by
      have ha : raw4509step3 = raw4509step2 := by apply Matrix.ext; unfold raw4509step3 raw4509step2; decide +kernel
      have hl : raw4509step2Labels = labelEmbedding1 ∘ raw4509step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4509step2 raw4509step2Labels raw4509step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw4510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4510step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4510step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4510step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4510step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4510 raw4510Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw4510 raw4510Labels = mixedMoment B raw4510step0 raw4510step0Labels := by
      have hz : ∀ j, raw4510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4510step0 = (fun i j => raw4510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4510step0 raw4510; decide +kernel
      have hl : raw4510step0Labels = raw4510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4510 raw4510Labels permutation346 hz
    mixedMoment B raw4510step0 raw4510step0Labels = mixedMoment B raw4510step1 raw4510step1Labels := by
      have hz : ∀ j, raw4510step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4510step1 = (fun i j => raw4510step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4510step1 raw4510step0; decide +kernel
      have hl : raw4510step1Labels = raw4510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4510step0 raw4510step0Labels permutation56 hz
    mixedMoment B raw4510step1 raw4510step1Labels = mixedMoment B raw4510step2 raw4510step2Labels := by
      have ha : raw4510step2 = (fun i j => raw4510step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4510step2 raw4510step1; decide +kernel
      have hl : raw4510step2Labels = raw4510step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4510step1 raw4510step1Labels permutation28 permutation7
    mixedMoment B raw4510step2 raw4510step2Labels = mixedMoment B raw4510step3 raw4510step3Labels := by
      have ha : raw4510step3 = raw4510step2 := by apply Matrix.ext; unfold raw4510step3 raw4510step2; decide +kernel
      have hl : raw4510step2Labels = labelEmbedding1 ∘ raw4510step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4510step2 raw4510step2Labels raw4510step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw4511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4511step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4511step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw4511step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4511step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw4511step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4511step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw4511step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4511step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw4511step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4511 raw4511Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw4511 raw4511Labels = mixedMoment B raw4511step0 raw4511step0Labels := by
      have hz : ∀ j, raw4511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4511step0 = (fun i j => raw4511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4511step0 raw4511; decide +kernel
      have hl : raw4511step0Labels = raw4511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4511 raw4511Labels permutation434 hz
    mixedMoment B raw4511step0 raw4511step0Labels = mixedMoment B raw4511step1 raw4511step1Labels := by
      have hz : ∀ j, raw4511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4511step1 = (fun i j => raw4511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4511step1 raw4511step0; decide +kernel
      have hl : raw4511step1Labels = raw4511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4511step0 raw4511step0Labels permutation80 hz
    mixedMoment B raw4511step1 raw4511step1Labels = mixedMoment B raw4511step2 raw4511step2Labels := by
      have hz : ∀ j, raw4511step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4511step2 = (fun i j => raw4511step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4511step2 raw4511step1; decide +kernel
      have hl : raw4511step2Labels = raw4511step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4511step1 raw4511step1Labels permutation14 hz
    mixedMoment B raw4511step2 raw4511step2Labels = mixedMoment B raw4511step3 raw4511step3Labels := by
      have ha : raw4511step3 = (fun i j => raw4511step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4511step3 raw4511step2; decide +kernel
      have hl : raw4511step3Labels = raw4511step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4511step2 raw4511step2Labels permutation3 permutation5
    mixedMoment B raw4511step3 raw4511step3Labels = mixedMoment B raw4511step4 raw4511step4Labels := by
      have ha : raw4511step4 = -raw4511step3 := by apply Matrix.ext; change ∀ i j, raw4511step4 i j = -(raw4511step3 i j); unfold raw4511step4 raw4511step3; decide +kernel
      have hl : raw4511step4Labels = raw4511step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4511step4 raw4511step4Labels = mixedMoment B raw4511step5 raw4511step5Labels := by
      have ha : raw4511step5 = raw4511step4 := by apply Matrix.ext; unfold raw4511step5 raw4511step4; decide +kernel
      have hl : raw4511step4Labels = labelEmbedding1 ∘ raw4511step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4511step4 raw4511step4Labels raw4511step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1747 node1747Labels := by rfl

def raw4512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4512step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4512step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4512step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4512step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4512step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4512 raw4512Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw4512 raw4512Labels = mixedMoment B raw4512step0 raw4512step0Labels := by
      have hz : ∀ j, raw4512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4512step0 = (fun i j => raw4512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4512step0 raw4512; decide +kernel
      have hl : raw4512step0Labels = raw4512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4512 raw4512Labels permutation434 hz
    mixedMoment B raw4512step0 raw4512step0Labels = mixedMoment B raw4512step1 raw4512step1Labels := by
      have hz : ∀ j, raw4512step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4512step1 = (fun i j => raw4512step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4512step1 raw4512step0; decide +kernel
      have hl : raw4512step1Labels = raw4512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4512step0 raw4512step0Labels permutation80 hz
    mixedMoment B raw4512step1 raw4512step1Labels = mixedMoment B raw4512step2 raw4512step2Labels := by
      have ha : raw4512step2 = (fun i j => raw4512step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4512step2 raw4512step1; decide +kernel
      have hl : raw4512step2Labels = raw4512step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4512step1 raw4512step1Labels permutation28 permutation7
    mixedMoment B raw4512step2 raw4512step2Labels = mixedMoment B raw4512step3 raw4512step3Labels := by
      have ha : raw4512step3 = raw4512step2 := by apply Matrix.ext; unfold raw4512step3 raw4512step2; decide +kernel
      have hl : raw4512step2Labels = labelEmbedding1 ∘ raw4512step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4512step2 raw4512step2Labels raw4512step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw4513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4513step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4513step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4513step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4513step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4513 raw4513Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw4513 raw4513Labels = mixedMoment B raw4513step0 raw4513step0Labels := by
      have hz : ∀ j, raw4513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4513step0 = (fun i j => raw4513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4513step0 raw4513; decide +kernel
      have hl : raw4513step0Labels = raw4513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4513 raw4513Labels permutation434 hz
    mixedMoment B raw4513step0 raw4513step0Labels = mixedMoment B raw4513step1 raw4513step1Labels := by
      have hz : ∀ j, raw4513step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4513step1 = (fun i j => raw4513step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4513step1 raw4513step0; decide +kernel
      have hl : raw4513step1Labels = raw4513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4513step0 raw4513step0Labels permutation56 hz
    mixedMoment B raw4513step1 raw4513step1Labels = mixedMoment B raw4513step2 raw4513step2Labels := by
      have ha : raw4513step2 = (fun i j => raw4513step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4513step2 raw4513step1; decide +kernel
      have hl : raw4513step2Labels = raw4513step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4513step1 raw4513step1Labels permutation28 permutation7
    mixedMoment B raw4513step2 raw4513step2Labels = mixedMoment B raw4513step3 raw4513step3Labels := by
      have ha : raw4513step3 = raw4513step2 := by apply Matrix.ext; unfold raw4513step3 raw4513step2; decide +kernel
      have hl : raw4513step2Labels = labelEmbedding1 ∘ raw4513step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4513step2 raw4513step2Labels raw4513step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw4514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4514step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4514step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4514 raw4514Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw4514 raw4514Labels = mixedMoment B raw4514step0 raw4514step0Labels := by
      have hz : ∀ j, raw4514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4514step0 = (fun i j => raw4514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4514step0 raw4514; decide +kernel
      have hl : raw4514step0Labels = raw4514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4514 raw4514Labels permutation346 hz
    mixedMoment B raw4514step0 raw4514step0Labels = mixedMoment B raw4514step1 raw4514step1Labels := by
      have hz : ∀ j, raw4514step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4514step1 = (fun i j => raw4514step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4514step1 raw4514step0; decide +kernel
      have hl : raw4514step1Labels = raw4514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4514step0 raw4514step0Labels permutation56 hz
    mixedMoment B raw4514step1 raw4514step1Labels = mixedMoment B raw4514step2 raw4514step2Labels := by
      have ha : raw4514step2 = (fun i j => raw4514step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4514step2 raw4514step1; decide +kernel
      have hl : raw4514step2Labels = raw4514step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4514step1 raw4514step1Labels permutation28 permutation7
    mixedMoment B raw4514step2 raw4514step2Labels = mixedMoment B raw4514step3 raw4514step3Labels := by
      have ha : raw4514step3 = raw4514step2 := by apply Matrix.ext; unfold raw4514step3 raw4514step2; decide +kernel
      have hl : raw4514step2Labels = labelEmbedding1 ∘ raw4514step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4514step2 raw4514step2Labels raw4514step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw4515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4515step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4515step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4515step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw4515step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4515step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4515step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4515step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4515step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4515 raw4515Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw4515 raw4515Labels = mixedMoment B raw4515step0 raw4515step0Labels := by
      have hz : ∀ j, raw4515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4515step0 = (fun i j => raw4515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4515step0 raw4515; decide +kernel
      have hl : raw4515step0Labels = raw4515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4515 raw4515Labels permutation434 hz
    mixedMoment B raw4515step0 raw4515step0Labels = mixedMoment B raw4515step1 raw4515step1Labels := by
      have hz : ∀ j, raw4515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4515step1 = (fun i j => raw4515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4515step1 raw4515step0; decide +kernel
      have hl : raw4515step1Labels = raw4515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4515step0 raw4515step0Labels permutation80 hz
    mixedMoment B raw4515step1 raw4515step1Labels = mixedMoment B raw4515step2 raw4515step2Labels := by
      have hz : ∀ j, raw4515step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4515step2 = (fun i j => raw4515step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4515step2 raw4515step1; decide +kernel
      have hl : raw4515step2Labels = raw4515step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4515step1 raw4515step1Labels permutation14 hz
    mixedMoment B raw4515step2 raw4515step2Labels = mixedMoment B raw4515step3 raw4515step3Labels := by
      have ha : raw4515step3 = (fun i j => raw4515step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4515step3 raw4515step2; decide +kernel
      have hl : raw4515step3Labels = raw4515step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4515step2 raw4515step2Labels permutation6 permutation7
    mixedMoment B raw4515step3 raw4515step3Labels = mixedMoment B raw4515step4 raw4515step4Labels := by
      have ha : raw4515step4 = raw4515step3 := by apply Matrix.ext; unfold raw4515step4 raw4515step3; decide +kernel
      have hl : raw4515step3Labels = labelEmbedding1 ∘ raw4515step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4515step3 raw4515step3Labels raw4515step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw4516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4516step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4516step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4516step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![4, -1, -3]]
def raw4516step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4516step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -3, 4], ![-2, 2, 0]]
def raw4516step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4516step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw4516step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4516step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw4516step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4516 raw4516Labels = mixedMoment B node1757 node1757Labels := by
  calc
    mixedMoment B raw4516 raw4516Labels = mixedMoment B raw4516step0 raw4516step0Labels := by
      have hz : ∀ j, raw4516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4516step0 = (fun i j => raw4516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4516step0 raw4516; decide +kernel
      have hl : raw4516step0Labels = raw4516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4516 raw4516Labels permutation434 hz
    mixedMoment B raw4516step0 raw4516step0Labels = mixedMoment B raw4516step1 raw4516step1Labels := by
      have hz : ∀ j, raw4516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4516step1 = (fun i j => raw4516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4516step1 raw4516step0; decide +kernel
      have hl : raw4516step1Labels = raw4516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4516step0 raw4516step0Labels permutation80 hz
    mixedMoment B raw4516step1 raw4516step1Labels = mixedMoment B raw4516step2 raw4516step2Labels := by
      have hz : ∀ j, raw4516step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4516step2 = (fun i j => raw4516step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4516step2 raw4516step1; decide +kernel
      have hl : raw4516step2Labels = raw4516step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4516step1 raw4516step1Labels permutation14 hz
    mixedMoment B raw4516step2 raw4516step2Labels = mixedMoment B raw4516step3 raw4516step3Labels := by
      have ha : raw4516step3 = (fun i j => raw4516step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4516step3 raw4516step2; decide +kernel
      have hl : raw4516step3Labels = raw4516step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4516step2 raw4516step2Labels permutation3 permutation5
    mixedMoment B raw4516step3 raw4516step3Labels = mixedMoment B raw4516step4 raw4516step4Labels := by
      have ha : raw4516step4 = -raw4516step3 := by apply Matrix.ext; change ∀ i j, raw4516step4 i j = -(raw4516step3 i j); unfold raw4516step4 raw4516step3; decide +kernel
      have hl : raw4516step4Labels = raw4516step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4516step4 raw4516step4Labels = mixedMoment B raw4516step5 raw4516step5Labels := by
      have ha : raw4516step5 = raw4516step4 := by apply Matrix.ext; unfold raw4516step5 raw4516step4; decide +kernel
      have hl : raw4516step4Labels = labelEmbedding1 ∘ raw4516step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4516step4 raw4516step4Labels raw4516step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1757 node1757Labels := by rfl

def raw4517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4517step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4517step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4517 raw4517Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw4517 raw4517Labels = mixedMoment B raw4517step0 raw4517step0Labels := by
      have hz : ∀ j, raw4517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4517step0 = (fun i j => raw4517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4517step0 raw4517; decide +kernel
      have hl : raw4517step0Labels = raw4517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4517 raw4517Labels permutation434 hz
    mixedMoment B raw4517step0 raw4517step0Labels = mixedMoment B raw4517step1 raw4517step1Labels := by
      have hz : ∀ j, raw4517step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4517step1 = (fun i j => raw4517step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4517step1 raw4517step0; decide +kernel
      have hl : raw4517step1Labels = raw4517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4517step0 raw4517step0Labels permutation80 hz
    mixedMoment B raw4517step1 raw4517step1Labels = mixedMoment B raw4517step2 raw4517step2Labels := by
      have ha : raw4517step2 = (fun i j => raw4517step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4517step2 raw4517step1; decide +kernel
      have hl : raw4517step2Labels = raw4517step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4517step1 raw4517step1Labels permutation28 permutation7
    mixedMoment B raw4517step2 raw4517step2Labels = mixedMoment B raw4517step3 raw4517step3Labels := by
      have ha : raw4517step3 = raw4517step2 := by apply Matrix.ext; unfold raw4517step3 raw4517step2; decide +kernel
      have hl : raw4517step2Labels = labelEmbedding1 ∘ raw4517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4517step2 raw4517step2Labels raw4517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw4518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4518step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4518 raw4518Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw4518 raw4518Labels = mixedMoment B raw4518step0 raw4518step0Labels := by
      have hz : ∀ j, raw4518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4518step0 = (fun i j => raw4518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4518step0 raw4518; decide +kernel
      have hl : raw4518step0Labels = raw4518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4518 raw4518Labels permutation434 hz
    mixedMoment B raw4518step0 raw4518step0Labels = mixedMoment B raw4518step1 raw4518step1Labels := by
      have hz : ∀ j, raw4518step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4518step1 = (fun i j => raw4518step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4518step1 raw4518step0; decide +kernel
      have hl : raw4518step1Labels = raw4518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4518step0 raw4518step0Labels permutation56 hz
    mixedMoment B raw4518step1 raw4518step1Labels = mixedMoment B raw4518step2 raw4518step2Labels := by
      have ha : raw4518step2 = (fun i j => raw4518step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4518step2 raw4518step1; decide +kernel
      have hl : raw4518step2Labels = raw4518step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4518step1 raw4518step1Labels permutation28 permutation7
    mixedMoment B raw4518step2 raw4518step2Labels = mixedMoment B raw4518step3 raw4518step3Labels := by
      have ha : raw4518step3 = raw4518step2 := by apply Matrix.ext; unfold raw4518step3 raw4518step2; decide +kernel
      have hl : raw4518step2Labels = labelEmbedding1 ∘ raw4518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4518step2 raw4518step2Labels raw4518step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw4519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4519step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4519step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4519step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4519 raw4519Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw4519 raw4519Labels = mixedMoment B raw4519step0 raw4519step0Labels := by
      have hz : ∀ j, raw4519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4519step0 = (fun i j => raw4519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4519step0 raw4519; decide +kernel
      have hl : raw4519step0Labels = raw4519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4519 raw4519Labels permutation346 hz
    mixedMoment B raw4519step0 raw4519step0Labels = mixedMoment B raw4519step1 raw4519step1Labels := by
      have hz : ∀ j, raw4519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4519step1 = (fun i j => raw4519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4519step1 raw4519step0; decide +kernel
      have hl : raw4519step1Labels = raw4519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4519step0 raw4519step0Labels permutation56 hz
    mixedMoment B raw4519step1 raw4519step1Labels = mixedMoment B raw4519step2 raw4519step2Labels := by
      have ha : raw4519step2 = (fun i j => raw4519step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4519step2 raw4519step1; decide +kernel
      have hl : raw4519step2Labels = raw4519step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4519step1 raw4519step1Labels permutation28 permutation7
    mixedMoment B raw4519step2 raw4519step2Labels = mixedMoment B raw4519step3 raw4519step3Labels := by
      have ha : raw4519step3 = raw4519step2 := by apply Matrix.ext; unfold raw4519step3 raw4519step2; decide +kernel
      have hl : raw4519step2Labels = labelEmbedding1 ∘ raw4519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4519step2 raw4519step2Labels raw4519step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw4520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4520step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4520step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw4520step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4520step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw4520step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4520step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw4520step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4520 raw4520Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw4520 raw4520Labels = mixedMoment B raw4520step0 raw4520step0Labels := by
      have hz : ∀ j, raw4520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4520step0 = (fun i j => raw4520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4520step0 raw4520; decide +kernel
      have hl : raw4520step0Labels = raw4520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4520 raw4520Labels permutation434 hz
    mixedMoment B raw4520step0 raw4520step0Labels = mixedMoment B raw4520step1 raw4520step1Labels := by
      have hz : ∀ j, raw4520step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4520step1 = (fun i j => raw4520step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4520step1 raw4520step0; decide +kernel
      have hl : raw4520step1Labels = raw4520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4520step0 raw4520step0Labels permutation80 hz
    mixedMoment B raw4520step1 raw4520step1Labels = mixedMoment B raw4520step2 raw4520step2Labels := by
      have hz : ∀ j, raw4520step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4520step2 = (fun i j => raw4520step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4520step2 raw4520step1; decide +kernel
      have hl : raw4520step2Labels = raw4520step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4520step1 raw4520step1Labels permutation14 hz
    mixedMoment B raw4520step2 raw4520step2Labels = mixedMoment B raw4520step3 raw4520step3Labels := by
      have ha : raw4520step3 = (fun i j => raw4520step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4520step3 raw4520step2; decide +kernel
      have hl : raw4520step3Labels = raw4520step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4520step2 raw4520step2Labels permutation6 permutation7
    mixedMoment B raw4520step3 raw4520step3Labels = mixedMoment B raw4520step4 raw4520step4Labels := by
      have ha : raw4520step4 = raw4520step3 := by apply Matrix.ext; unfold raw4520step4 raw4520step3; decide +kernel
      have hl : raw4520step3Labels = labelEmbedding1 ∘ raw4520step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4520step3 raw4520step3Labels raw4520step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

def raw4521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![3, 0, -3]]
def raw4521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4521step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4521 raw4521Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw4521 raw4521Labels = mixedMoment B raw4521step0 raw4521step0Labels := by
      have hz : ∀ j, raw4521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4521step0 = (fun i j => raw4521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4521step0 raw4521; decide +kernel
      have hl : raw4521step0Labels = raw4521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4521 raw4521Labels permutation434 hz
    mixedMoment B raw4521step0 raw4521step0Labels = mixedMoment B raw4521step1 raw4521step1Labels := by
      have hz : ∀ j, raw4521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4521step1 = (fun i j => raw4521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4521step1 raw4521step0; decide +kernel
      have hl : raw4521step1Labels = raw4521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4521step0 raw4521step0Labels permutation80 hz
    mixedMoment B raw4521step1 raw4521step1Labels = mixedMoment B raw4521step2 raw4521step2Labels := by
      have hz : ∀ j, raw4521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4521step2 = (fun i j => raw4521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4521step2 raw4521step1; decide +kernel
      have hl : raw4521step2Labels = raw4521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4521step1 raw4521step1Labels permutation14 hz
    mixedMoment B raw4521step2 raw4521step2Labels = mixedMoment B raw4521step3 raw4521step3Labels := by
      have ha : raw4521step3 = (fun i j => raw4521step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4521step3 raw4521step2; decide +kernel
      have hl : raw4521step3Labels = raw4521step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4521step2 raw4521step2Labels permutation7 permutation2
    mixedMoment B raw4521step3 raw4521step3Labels = mixedMoment B raw4521step4 raw4521step4Labels := by
      have ha : raw4521step4 = -raw4521step3 := by apply Matrix.ext; change ∀ i j, raw4521step4 i j = -(raw4521step3 i j); unfold raw4521step4 raw4521step3; decide +kernel
      have hl : raw4521step4Labels = raw4521step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw4522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw4522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4522step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4522 raw4522Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw4522 raw4522Labels = mixedMoment B raw4522step0 raw4522step0Labels := by
      have hz : ∀ j, raw4522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4522step0 = (fun i j => raw4522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4522step0 raw4522; decide +kernel
      have hl : raw4522step0Labels = raw4522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4522 raw4522Labels permutation434 hz
    mixedMoment B raw4522step0 raw4522step0Labels = mixedMoment B raw4522step1 raw4522step1Labels := by
      have hz : ∀ j, raw4522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4522step1 = (fun i j => raw4522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4522step1 raw4522step0; decide +kernel
      have hl : raw4522step1Labels = raw4522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4522step0 raw4522step0Labels permutation80 hz
    mixedMoment B raw4522step1 raw4522step1Labels = mixedMoment B raw4522step2 raw4522step2Labels := by
      have ha : raw4522step2 = (fun i j => raw4522step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4522step2 raw4522step1; decide +kernel
      have hl : raw4522step2Labels = raw4522step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4522step1 raw4522step1Labels permutation31 permutation2
    mixedMoment B raw4522step2 raw4522step2Labels = mixedMoment B raw4522step3 raw4522step3Labels := by
      have ha : raw4522step3 = -raw4522step2 := by apply Matrix.ext; change ∀ i j, raw4522step3 i j = -(raw4522step2 i j); unfold raw4522step3 raw4522step2; decide +kernel
      have hl : raw4522step3Labels = raw4522step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw4523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw4523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4523step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4523 raw4523Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw4523 raw4523Labels = mixedMoment B raw4523step0 raw4523step0Labels := by
      have hz : ∀ j, raw4523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4523step0 = (fun i j => raw4523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4523step0 raw4523; decide +kernel
      have hl : raw4523step0Labels = raw4523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4523 raw4523Labels permutation434 hz
    mixedMoment B raw4523step0 raw4523step0Labels = mixedMoment B raw4523step1 raw4523step1Labels := by
      have hz : ∀ j, raw4523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4523step1 = (fun i j => raw4523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4523step1 raw4523step0; decide +kernel
      have hl : raw4523step1Labels = raw4523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4523step0 raw4523step0Labels permutation56 hz
    mixedMoment B raw4523step1 raw4523step1Labels = mixedMoment B raw4523step2 raw4523step2Labels := by
      have ha : raw4523step2 = (fun i j => raw4523step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4523step2 raw4523step1; decide +kernel
      have hl : raw4523step2Labels = raw4523step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4523step1 raw4523step1Labels permutation31 permutation2
    mixedMoment B raw4523step2 raw4523step2Labels = mixedMoment B raw4523step3 raw4523step3Labels := by
      have ha : raw4523step3 = -raw4523step2 := by apply Matrix.ext; change ∀ i j, raw4523step3 i j = -(raw4523step2 i j); unfold raw4523step3 raw4523step2; decide +kernel
      have hl : raw4523step3Labels = raw4523step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw4524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw4524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4524step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4524 raw4524Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw4524 raw4524Labels = mixedMoment B raw4524step0 raw4524step0Labels := by
      have hz : ∀ j, raw4524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4524step0 = (fun i j => raw4524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4524step0 raw4524; decide +kernel
      have hl : raw4524step0Labels = raw4524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4524 raw4524Labels permutation346 hz
    mixedMoment B raw4524step0 raw4524step0Labels = mixedMoment B raw4524step1 raw4524step1Labels := by
      have hz : ∀ j, raw4524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4524step1 = (fun i j => raw4524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4524step1 raw4524step0; decide +kernel
      have hl : raw4524step1Labels = raw4524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4524step0 raw4524step0Labels permutation56 hz
    mixedMoment B raw4524step1 raw4524step1Labels = mixedMoment B raw4524step2 raw4524step2Labels := by
      have ha : raw4524step2 = (fun i j => raw4524step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4524step2 raw4524step1; decide +kernel
      have hl : raw4524step2Labels = raw4524step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4524step1 raw4524step1Labels permutation31 permutation2
    mixedMoment B raw4524step2 raw4524step2Labels = mixedMoment B raw4524step3 raw4524step3Labels := by
      have ha : raw4524step3 = -raw4524step2 := by apply Matrix.ext; change ∀ i j, raw4524step3 i j = -(raw4524step2 i j); unfold raw4524step3 raw4524step2; decide +kernel
      have hl : raw4524step3Labels = raw4524step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw4525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw4525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw4525step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw4525step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4525 raw4525Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw4525 raw4525Labels = mixedMoment B raw4525step0 raw4525step0Labels := by
      have hz : ∀ j, raw4525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4525step0 = (fun i j => raw4525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4525step0 raw4525; decide +kernel
      have hl : raw4525step0Labels = raw4525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4525 raw4525Labels permutation434 hz
    mixedMoment B raw4525step0 raw4525step0Labels = mixedMoment B raw4525step1 raw4525step1Labels := by
      have hz : ∀ j, raw4525step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4525step1 = (fun i j => raw4525step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4525step1 raw4525step0; decide +kernel
      have hl : raw4525step1Labels = raw4525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4525step0 raw4525step0Labels permutation80 hz
    mixedMoment B raw4525step1 raw4525step1Labels = mixedMoment B raw4525step2 raw4525step2Labels := by
      have hz : ∀ j, raw4525step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4525step2 = (fun i j => raw4525step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4525step2 raw4525step1; decide +kernel
      have hl : raw4525step2Labels = raw4525step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4525step1 raw4525step1Labels permutation14 hz
    mixedMoment B raw4525step2 raw4525step2Labels = mixedMoment B raw4525step3 raw4525step3Labels := by
      have ha : raw4525step3 = (fun i j => raw4525step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4525step3 raw4525step2; decide +kernel
      have hl : raw4525step3Labels = raw4525step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4525step2 raw4525step2Labels permutation7 permutation2
    mixedMoment B raw4525step3 raw4525step3Labels = mixedMoment B raw4525step4 raw4525step4Labels := by
      have ha : raw4525step4 = -raw4525step3 := by apply Matrix.ext; change ∀ i j, raw4525step4 i j = -(raw4525step3 i j); unfold raw4525step4 raw4525step3; decide +kernel
      have hl : raw4525step4Labels = raw4525step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw4526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw4526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw4526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw4526step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4526 raw4526Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw4526 raw4526Labels = mixedMoment B raw4526step0 raw4526step0Labels := by
      have hz : ∀ j, raw4526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4526step0 = (fun i j => raw4526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4526step0 raw4526; decide +kernel
      have hl : raw4526step0Labels = raw4526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4526 raw4526Labels permutation434 hz
    mixedMoment B raw4526step0 raw4526step0Labels = mixedMoment B raw4526step1 raw4526step1Labels := by
      have hz : ∀ j, raw4526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4526step1 = (fun i j => raw4526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4526step1 raw4526step0; decide +kernel
      have hl : raw4526step1Labels = raw4526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4526step0 raw4526step0Labels permutation80 hz
    mixedMoment B raw4526step1 raw4526step1Labels = mixedMoment B raw4526step2 raw4526step2Labels := by
      have hz : ∀ j, raw4526step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4526step2 = (fun i j => raw4526step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4526step2 raw4526step1; decide +kernel
      have hl : raw4526step2Labels = raw4526step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4526step1 raw4526step1Labels permutation14 hz
    mixedMoment B raw4526step2 raw4526step2Labels = mixedMoment B raw4526step3 raw4526step3Labels := by
      have ha : raw4526step3 = (fun i j => raw4526step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4526step3 raw4526step2; decide +kernel
      have hl : raw4526step3Labels = raw4526step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4526step2 raw4526step2Labels permutation7 permutation2
    mixedMoment B raw4526step3 raw4526step3Labels = mixedMoment B raw4526step4 raw4526step4Labels := by
      have ha : raw4526step4 = -raw4526step3 := by apply Matrix.ext; change ∀ i j, raw4526step4 i j = -(raw4526step3 i j); unfold raw4526step4 raw4526step3; decide +kernel
      have hl : raw4526step4Labels = raw4526step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3633 node3633Labels := by rfl

def raw4527 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![-2, 2], ![3, -3]]
def raw4527Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4527step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-2, 2], ![3, -3]]
def raw4527step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4527step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![3, -3]]
def raw4527step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4527step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]
def raw4527step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4527step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw4527step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4527step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw4527step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical4527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4527 raw4527Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw4527 raw4527Labels = mixedMoment B raw4527step0 raw4527step0Labels := by
      have hz : ∀ j, raw4527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4527step0 = (fun i j => raw4527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4527step0 raw4527; decide +kernel
      have hl : raw4527step0Labels = raw4527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4527 raw4527Labels permutation434 hz
    mixedMoment B raw4527step0 raw4527step0Labels = mixedMoment B raw4527step1 raw4527step1Labels := by
      have hz : ∀ j, raw4527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4527step1 = (fun i j => raw4527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4527step1 raw4527step0; decide +kernel
      have hl : raw4527step1Labels = raw4527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4527step0 raw4527step0Labels permutation80 hz
    mixedMoment B raw4527step1 raw4527step1Labels = mixedMoment B raw4527step2 raw4527step2Labels := by
      have hz : ∀ j, raw4527step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4527step2 = (fun i j => raw4527step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4527step2 raw4527step1; decide +kernel
      have hl : raw4527step2Labels = raw4527step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4527step1 raw4527step1Labels permutation14 hz
    mixedMoment B raw4527step2 raw4527step2Labels = mixedMoment B raw4527step3 raw4527step3Labels := by
      have ha : raw4527step3 = (fun i j => raw4527step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4527step3 raw4527step2; decide +kernel
      have hl : raw4527step3Labels = raw4527step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4527step2 raw4527step2Labels permutation6 permutation0
    mixedMoment B raw4527step3 raw4527step3Labels = mixedMoment B raw4527step4 raw4527step4Labels := by
      have ha : raw4527step4 = -raw4527step3 := by apply Matrix.ext; change ∀ i j, raw4527step4 i j = -(raw4527step3 i j); unfold raw4527step4 raw4527step3; decide +kernel
      have hl : raw4527step4Labels = raw4527step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw4528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw4528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4528 raw4528Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw4528 raw4528Labels = mixedMoment B raw4528step0 raw4528step0Labels := by
      have hz : ∀ j, raw4528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4528step0 = (fun i j => raw4528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4528step0 raw4528; decide +kernel
      have hl : raw4528step0Labels = raw4528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4528 raw4528Labels permutation434 hz
    mixedMoment B raw4528step0 raw4528step0Labels = mixedMoment B raw4528step1 raw4528step1Labels := by
      have hz : ∀ j, raw4528step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4528step1 = (fun i j => raw4528step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4528step1 raw4528step0; decide +kernel
      have hl : raw4528step1Labels = raw4528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4528step0 raw4528step0Labels permutation80 hz
    mixedMoment B raw4528step1 raw4528step1Labels = mixedMoment B raw4528step2 raw4528step2Labels := by
      have ha : raw4528step2 = (fun i j => raw4528step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4528step2 raw4528step1; decide +kernel
      have hl : raw4528step2Labels = raw4528step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4528step1 raw4528step1Labels permutation10 permutation2
    _ = mixedMoment B node1369 node1369Labels := by rfl

def raw4529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw4529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4529 raw4529Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw4529 raw4529Labels = mixedMoment B raw4529step0 raw4529step0Labels := by
      have hz : ∀ j, raw4529 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4529step0 = (fun i j => raw4529 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4529step0 raw4529; decide +kernel
      have hl : raw4529step0Labels = raw4529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4529 raw4529Labels permutation434 hz
    mixedMoment B raw4529step0 raw4529step0Labels = mixedMoment B raw4529step1 raw4529step1Labels := by
      have hz : ∀ j, raw4529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4529step1 = (fun i j => raw4529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4529step1 raw4529step0; decide +kernel
      have hl : raw4529step1Labels = raw4529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4529step0 raw4529step0Labels permutation56 hz
    mixedMoment B raw4529step1 raw4529step1Labels = mixedMoment B raw4529step2 raw4529step2Labels := by
      have ha : raw4529step2 = (fun i j => raw4529step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4529step2 raw4529step1; decide +kernel
      have hl : raw4529step2Labels = raw4529step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4529step1 raw4529step1Labels permutation10 permutation2
    _ = mixedMoment B node1369 node1369Labels := by rfl

def raw4530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw4530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4530 raw4530Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw4530 raw4530Labels = mixedMoment B raw4530step0 raw4530step0Labels := by
      have hz : ∀ j, raw4530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4530step0 = (fun i j => raw4530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4530step0 raw4530; decide +kernel
      have hl : raw4530step0Labels = raw4530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4530 raw4530Labels permutation346 hz
    mixedMoment B raw4530step0 raw4530step0Labels = mixedMoment B raw4530step1 raw4530step1Labels := by
      have hz : ∀ j, raw4530step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4530step1 = (fun i j => raw4530step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4530step1 raw4530step0; decide +kernel
      have hl : raw4530step1Labels = raw4530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4530step0 raw4530step0Labels permutation56 hz
    mixedMoment B raw4530step1 raw4530step1Labels = mixedMoment B raw4530step2 raw4530step2Labels := by
      have ha : raw4530step2 = (fun i j => raw4530step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4530step2 raw4530step1; decide +kernel
      have hl : raw4530step2Labels = raw4530step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4530step1 raw4530step1Labels permutation10 permutation2
    _ = mixedMoment B node1369 node1369Labels := by rfl

def raw4531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4531step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw4531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4531 raw4531Labels = mixedMoment B node1438 node1438Labels := by
  calc
    mixedMoment B raw4531 raw4531Labels = mixedMoment B raw4531step0 raw4531step0Labels := by
      have hz : ∀ j, raw4531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4531step0 = (fun i j => raw4531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4531step0 raw4531; decide +kernel
      have hl : raw4531step0Labels = raw4531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4531 raw4531Labels permutation434 hz
    mixedMoment B raw4531step0 raw4531step0Labels = mixedMoment B raw4531step1 raw4531step1Labels := by
      have hz : ∀ j, raw4531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4531step1 = (fun i j => raw4531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4531step1 raw4531step0; decide +kernel
      have hl : raw4531step1Labels = raw4531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4531step0 raw4531step0Labels permutation80 hz
    mixedMoment B raw4531step1 raw4531step1Labels = mixedMoment B raw4531step2 raw4531step2Labels := by
      have hz : ∀ j, raw4531step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4531step2 = (fun i j => raw4531step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4531step2 raw4531step1; decide +kernel
      have hl : raw4531step2Labels = raw4531step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4531step1 raw4531step1Labels permutation14 hz
    _ = mixedMoment B node1438 node1438Labels := by rfl

def raw4532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![4, -1, -3]]
def raw4532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-4, 3, 1]]
def raw4532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw4532step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4532 raw4532Labels = mixedMoment B node1064 node1064Labels := by
  calc
    mixedMoment B raw4532 raw4532Labels = mixedMoment B raw4532step0 raw4532step0Labels := by
      have hz : ∀ j, raw4532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4532step0 = (fun i j => raw4532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4532step0 raw4532; decide +kernel
      have hl : raw4532step0Labels = raw4532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4532 raw4532Labels permutation434 hz
    mixedMoment B raw4532step0 raw4532step0Labels = mixedMoment B raw4532step1 raw4532step1Labels := by
      have hz : ∀ j, raw4532step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4532step1 = (fun i j => raw4532step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4532step1 raw4532step0; decide +kernel
      have hl : raw4532step1Labels = raw4532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4532step0 raw4532step0Labels permutation80 hz
    mixedMoment B raw4532step1 raw4532step1Labels = mixedMoment B raw4532step2 raw4532step2Labels := by
      have hz : ∀ j, raw4532step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4532step2 = (fun i j => raw4532step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4532step2 raw4532step1; decide +kernel
      have hl : raw4532step2Labels = raw4532step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4532step1 raw4532step1Labels permutation14 hz
    mixedMoment B raw4532step2 raw4532step2Labels = mixedMoment B raw4532step3 raw4532step3Labels := by
      have ha : raw4532step3 = (fun i j => raw4532step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4532step3 raw4532step2; decide +kernel
      have hl : raw4532step3Labels = raw4532step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4532step2 raw4532step2Labels permutation7 permutation2
    mixedMoment B raw4532step3 raw4532step3Labels = mixedMoment B raw4532step4 raw4532step4Labels := by
      have ha : raw4532step4 = -raw4532step3 := by apply Matrix.ext; change ∀ i j, raw4532step4 i j = -(raw4532step3 i j); unfold raw4532step4 raw4532step3; decide +kernel
      have hl : raw4532step4Labels = raw4532step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1064 node1064Labels := by rfl

def raw4533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4533 raw4533Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw4533 raw4533Labels = mixedMoment B raw4533step0 raw4533step0Labels := by
      have hz : ∀ j, raw4533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4533step0 = (fun i j => raw4533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4533step0 raw4533; decide +kernel
      have hl : raw4533step0Labels = raw4533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4533 raw4533Labels permutation434 hz
    mixedMoment B raw4533step0 raw4533step0Labels = mixedMoment B raw4533step1 raw4533step1Labels := by
      have ha : raw4533step1 = (fun i j => raw4533step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4533step1 raw4533step0; decide +kernel
      have hl : raw4533step1Labels = raw4533step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4533step0 raw4533step0Labels permutation139 permutation2
    mixedMoment B raw4533step1 raw4533step1Labels = mixedMoment B raw4533step2 raw4533step2Labels := by
      have ha : raw4533step2 = -raw4533step1 := by apply Matrix.ext; change ∀ i j, raw4533step2 i j = -(raw4533step1 i j); unfold raw4533step2 raw4533step1; decide +kernel
      have hl : raw4533step2Labels = raw4533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

def raw4534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4534 raw4534Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw4534 raw4534Labels = mixedMoment B raw4534step0 raw4534step0Labels := by
      have hz : ∀ j, raw4534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4534step0 = (fun i j => raw4534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4534step0 raw4534; decide +kernel
      have hl : raw4534step0Labels = raw4534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4534 raw4534Labels permutation346 hz
    mixedMoment B raw4534step0 raw4534step0Labels = mixedMoment B raw4534step1 raw4534step1Labels := by
      have ha : raw4534step1 = (fun i j => raw4534step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4534step1 raw4534step0; decide +kernel
      have hl : raw4534step1Labels = raw4534step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4534step0 raw4534step0Labels permutation139 permutation2
    mixedMoment B raw4534step1 raw4534step1Labels = mixedMoment B raw4534step2 raw4534step2Labels := by
      have ha : raw4534step2 = -raw4534step1 := by apply Matrix.ext; change ∀ i j, raw4534step2 i j = -(raw4534step1 i j); unfold raw4534step2 raw4534step1; decide +kernel
      have hl : raw4534step2Labels = raw4534step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

def raw4535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4535step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4535 raw4535Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw4535 raw4535Labels = mixedMoment B raw4535step0 raw4535step0Labels := by
      have hz : ∀ j, raw4535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4535step0 = (fun i j => raw4535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4535step0 raw4535; decide +kernel
      have hl : raw4535step0Labels = raw4535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4535 raw4535Labels permutation434 hz
    mixedMoment B raw4535step0 raw4535step0Labels = mixedMoment B raw4535step1 raw4535step1Labels := by
      have hz : ∀ j, raw4535step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4535step1 = (fun i j => raw4535step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4535step1 raw4535step0; decide +kernel
      have hl : raw4535step1Labels = raw4535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4535step0 raw4535step0Labels permutation80 hz
    mixedMoment B raw4535step1 raw4535step1Labels = mixedMoment B raw4535step2 raw4535step2Labels := by
      have ha : raw4535step2 = (fun i j => raw4535step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4535step2 raw4535step1; decide +kernel
      have hl : raw4535step2Labels = raw4535step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4535step1 raw4535step1Labels permutation29 permutation2
    mixedMoment B raw4535step2 raw4535step2Labels = mixedMoment B raw4535step3 raw4535step3Labels := by
      have ha : raw4535step3 = -raw4535step2 := by apply Matrix.ext; change ∀ i j, raw4535step3 i j = -(raw4535step2 i j); unfold raw4535step3 raw4535step2; decide +kernel
      have hl : raw4535step3Labels = raw4535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw4536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw4536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4536 raw4536Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw4536 raw4536Labels = mixedMoment B raw4536step0 raw4536step0Labels := by
      have hz : ∀ j, raw4536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4536step0 = (fun i j => raw4536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4536step0 raw4536; decide +kernel
      have hl : raw4536step0Labels = raw4536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4536 raw4536Labels permutation434 hz
    mixedMoment B raw4536step0 raw4536step0Labels = mixedMoment B raw4536step1 raw4536step1Labels := by
      have hz : ∀ j, raw4536step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4536step1 = (fun i j => raw4536step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4536step1 raw4536step0; decide +kernel
      have hl : raw4536step1Labels = raw4536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4536step0 raw4536step0Labels permutation80 hz
    mixedMoment B raw4536step1 raw4536step1Labels = mixedMoment B raw4536step2 raw4536step2Labels := by
      have ha : raw4536step2 = (fun i j => raw4536step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4536step2 raw4536step1; decide +kernel
      have hl : raw4536step2Labels = raw4536step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4536step1 raw4536step1Labels permutation10 permutation2
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw4537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4537step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4537 raw4537Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw4537 raw4537Labels = mixedMoment B raw4537step0 raw4537step0Labels := by
      have hz : ∀ j, raw4537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4537step0 = (fun i j => raw4537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4537step0 raw4537; decide +kernel
      have hl : raw4537step0Labels = raw4537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4537 raw4537Labels permutation434 hz
    mixedMoment B raw4537step0 raw4537step0Labels = mixedMoment B raw4537step1 raw4537step1Labels := by
      have ha : raw4537step1 = (fun i j => raw4537step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4537step1 raw4537step0; decide +kernel
      have hl : raw4537step1Labels = raw4537step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4537step0 raw4537step0Labels permutation145 permutation2
    mixedMoment B raw4537step1 raw4537step1Labels = mixedMoment B raw4537step2 raw4537step2Labels := by
      have ha : raw4537step2 = -raw4537step1 := by apply Matrix.ext; change ∀ i j, raw4537step2 i j = -(raw4537step1 i j); unfold raw4537step2 raw4537step1; decide +kernel
      have hl : raw4537step2Labels = raw4537step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

def raw4538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4538 raw4538Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw4538 raw4538Labels = mixedMoment B raw4538step0 raw4538step0Labels := by
      have hz : ∀ j, raw4538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4538step0 = (fun i j => raw4538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4538step0 raw4538; decide +kernel
      have hl : raw4538step0Labels = raw4538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4538 raw4538Labels permutation346 hz
    mixedMoment B raw4538step0 raw4538step0Labels = mixedMoment B raw4538step1 raw4538step1Labels := by
      have ha : raw4538step1 = (fun i j => raw4538step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4538step1 raw4538step0; decide +kernel
      have hl : raw4538step1Labels = raw4538step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4538step0 raw4538step0Labels permutation145 permutation2
    mixedMoment B raw4538step1 raw4538step1Labels = mixedMoment B raw4538step2 raw4538step2Labels := by
      have ha : raw4538step2 = -raw4538step1 := by apply Matrix.ext; change ∀ i j, raw4538step2 i j = -(raw4538step1 i j); unfold raw4538step2 raw4538step1; decide +kernel
      have hl : raw4538step2Labels = raw4538step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

def raw4539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4539step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4539step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4539 raw4539Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw4539 raw4539Labels = mixedMoment B raw4539step0 raw4539step0Labels := by
      have hz : ∀ j, raw4539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4539step0 = (fun i j => raw4539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4539step0 raw4539; decide +kernel
      have hl : raw4539step0Labels = raw4539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4539 raw4539Labels permutation434 hz
    mixedMoment B raw4539step0 raw4539step0Labels = mixedMoment B raw4539step1 raw4539step1Labels := by
      have hz : ∀ j, raw4539step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4539step1 = (fun i j => raw4539step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4539step1 raw4539step0; decide +kernel
      have hl : raw4539step1Labels = raw4539step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4539step0 raw4539step0Labels permutation80 hz
    mixedMoment B raw4539step1 raw4539step1Labels = mixedMoment B raw4539step2 raw4539step2Labels := by
      have ha : raw4539step2 = (fun i j => raw4539step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4539step2 raw4539step1; decide +kernel
      have hl : raw4539step2Labels = raw4539step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4539step1 raw4539step1Labels permutation31 permutation2
    mixedMoment B raw4539step2 raw4539step2Labels = mixedMoment B raw4539step3 raw4539step3Labels := by
      have ha : raw4539step3 = -raw4539step2 := by apply Matrix.ext; change ∀ i j, raw4539step3 i j = -(raw4539step2 i j); unfold raw4539step3 raw4539step2; decide +kernel
      have hl : raw4539step3Labels = raw4539step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

def raw4540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4540step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4540 raw4540Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw4540 raw4540Labels = mixedMoment B raw4540step0 raw4540step0Labels := by
      have hz : ∀ j, raw4540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4540step0 = (fun i j => raw4540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4540step0 raw4540; decide +kernel
      have hl : raw4540step0Labels = raw4540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4540 raw4540Labels permutation434 hz
    mixedMoment B raw4540step0 raw4540step0Labels = mixedMoment B raw4540step1 raw4540step1Labels := by
      have hz : ∀ j, raw4540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4540step1 = (fun i j => raw4540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4540step1 raw4540step0; decide +kernel
      have hl : raw4540step1Labels = raw4540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4540step0 raw4540step0Labels permutation80 hz
    mixedMoment B raw4540step1 raw4540step1Labels = mixedMoment B raw4540step2 raw4540step2Labels := by
      have ha : raw4540step2 = (fun i j => raw4540step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4540step2 raw4540step1; decide +kernel
      have hl : raw4540step2Labels = raw4540step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4540step1 raw4540step1Labels permutation31 permutation2
    mixedMoment B raw4540step2 raw4540step2Labels = mixedMoment B raw4540step3 raw4540step3Labels := by
      have ha : raw4540step3 = -raw4540step2 := by apply Matrix.ext; change ∀ i j, raw4540step3 i j = -(raw4540step2 i j); unfold raw4540step3 raw4540step2; decide +kernel
      have hl : raw4540step3Labels = raw4540step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1059 node1059Labels := by rfl

def raw4541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4541step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4541step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4541 raw4541Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw4541 raw4541Labels = mixedMoment B raw4541step0 raw4541step0Labels := by
      have hz : ∀ j, raw4541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4541step0 = (fun i j => raw4541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4541step0 raw4541; decide +kernel
      have hl : raw4541step0Labels = raw4541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4541 raw4541Labels permutation434 hz
    mixedMoment B raw4541step0 raw4541step0Labels = mixedMoment B raw4541step1 raw4541step1Labels := by
      have hz : ∀ j, raw4541step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4541step1 = (fun i j => raw4541step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4541step1 raw4541step0; decide +kernel
      have hl : raw4541step1Labels = raw4541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4541step0 raw4541step0Labels permutation56 hz
    mixedMoment B raw4541step1 raw4541step1Labels = mixedMoment B raw4541step2 raw4541step2Labels := by
      have ha : raw4541step2 = (fun i j => raw4541step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4541step2 raw4541step1; decide +kernel
      have hl : raw4541step2Labels = raw4541step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4541step1 raw4541step1Labels permutation31 permutation2
    mixedMoment B raw4541step2 raw4541step2Labels = mixedMoment B raw4541step3 raw4541step3Labels := by
      have ha : raw4541step3 = -raw4541step2 := by apply Matrix.ext; change ∀ i j, raw4541step3 i j = -(raw4541step2 i j); unfold raw4541step3 raw4541step2; decide +kernel
      have hl : raw4541step3Labels = raw4541step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

def raw4542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4542step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4542step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4542 raw4542Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw4542 raw4542Labels = mixedMoment B raw4542step0 raw4542step0Labels := by
      have hz : ∀ j, raw4542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4542step0 = (fun i j => raw4542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4542step0 raw4542; decide +kernel
      have hl : raw4542step0Labels = raw4542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4542 raw4542Labels permutation346 hz
    mixedMoment B raw4542step0 raw4542step0Labels = mixedMoment B raw4542step1 raw4542step1Labels := by
      have hz : ∀ j, raw4542step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4542step1 = (fun i j => raw4542step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4542step1 raw4542step0; decide +kernel
      have hl : raw4542step1Labels = raw4542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4542step0 raw4542step0Labels permutation56 hz
    mixedMoment B raw4542step1 raw4542step1Labels = mixedMoment B raw4542step2 raw4542step2Labels := by
      have ha : raw4542step2 = (fun i j => raw4542step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4542step2 raw4542step1; decide +kernel
      have hl : raw4542step2Labels = raw4542step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4542step1 raw4542step1Labels permutation31 permutation2
    mixedMoment B raw4542step2 raw4542step2Labels = mixedMoment B raw4542step3 raw4542step3Labels := by
      have ha : raw4542step3 = -raw4542step2 := by apply Matrix.ext; change ∀ i j, raw4542step3 i j = -(raw4542step2 i j); unfold raw4542step3 raw4542step2; decide +kernel
      have hl : raw4542step3Labels = raw4542step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

def raw4543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4543step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw4543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4543step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4543step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4543 raw4543Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw4543 raw4543Labels = mixedMoment B raw4543step0 raw4543step0Labels := by
      have hz : ∀ j, raw4543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4543step0 = (fun i j => raw4543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4543step0 raw4543; decide +kernel
      have hl : raw4543step0Labels = raw4543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4543 raw4543Labels permutation434 hz
    mixedMoment B raw4543step0 raw4543step0Labels = mixedMoment B raw4543step1 raw4543step1Labels := by
      have hz : ∀ j, raw4543step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4543step1 = (fun i j => raw4543step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4543step1 raw4543step0; decide +kernel
      have hl : raw4543step1Labels = raw4543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4543step0 raw4543step0Labels permutation80 hz
    mixedMoment B raw4543step1 raw4543step1Labels = mixedMoment B raw4543step2 raw4543step2Labels := by
      have hz : ∀ j, raw4543step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4543step2 = (fun i j => raw4543step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4543step2 raw4543step1; decide +kernel
      have hl : raw4543step2Labels = raw4543step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4543step1 raw4543step1Labels permutation14 hz
    mixedMoment B raw4543step2 raw4543step2Labels = mixedMoment B raw4543step3 raw4543step3Labels := by
      have ha : raw4543step3 = (fun i j => raw4543step2 (permutation5 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4543step3 raw4543step2; decide +kernel
      have hl : raw4543step3Labels = raw4543step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4543step2 raw4543step2Labels permutation5 permutation4
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw4544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4544step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4544 raw4544Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw4544 raw4544Labels = mixedMoment B raw4544step0 raw4544step0Labels := by
      have hz : ∀ j, raw4544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4544step0 = (fun i j => raw4544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4544step0 raw4544; decide +kernel
      have hl : raw4544step0Labels = raw4544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4544 raw4544Labels permutation434 hz
    mixedMoment B raw4544step0 raw4544step0Labels = mixedMoment B raw4544step1 raw4544step1Labels := by
      have hz : ∀ j, raw4544step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4544step1 = (fun i j => raw4544step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4544step1 raw4544step0; decide +kernel
      have hl : raw4544step1Labels = raw4544step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4544step0 raw4544step0Labels permutation56 hz
    mixedMoment B raw4544step1 raw4544step1Labels = mixedMoment B raw4544step2 raw4544step2Labels := by
      have ha : raw4544step2 = (fun i j => raw4544step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4544step2 raw4544step1; decide +kernel
      have hl : raw4544step2Labels = raw4544step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4544step1 raw4544step1Labels permutation29 permutation2
    mixedMoment B raw4544step2 raw4544step2Labels = mixedMoment B raw4544step3 raw4544step3Labels := by
      have ha : raw4544step3 = -raw4544step2 := by apply Matrix.ext; change ∀ i j, raw4544step3 i j = -(raw4544step2 i j); unfold raw4544step3 raw4544step2; decide +kernel
      have hl : raw4544step3Labels = raw4544step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw4545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4545 raw4545Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw4545 raw4545Labels = mixedMoment B raw4545step0 raw4545step0Labels := by
      have hz : ∀ j, raw4545 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4545step0 = (fun i j => raw4545 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4545step0 raw4545; decide +kernel
      have hl : raw4545step0Labels = raw4545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4545 raw4545Labels permutation346 hz
    mixedMoment B raw4545step0 raw4545step0Labels = mixedMoment B raw4545step1 raw4545step1Labels := by
      have hz : ∀ j, raw4545step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4545step1 = (fun i j => raw4545step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4545step1 raw4545step0; decide +kernel
      have hl : raw4545step1Labels = raw4545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4545step0 raw4545step0Labels permutation56 hz
    mixedMoment B raw4545step1 raw4545step1Labels = mixedMoment B raw4545step2 raw4545step2Labels := by
      have ha : raw4545step2 = (fun i j => raw4545step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4545step2 raw4545step1; decide +kernel
      have hl : raw4545step2Labels = raw4545step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4545step1 raw4545step1Labels permutation29 permutation2
    mixedMoment B raw4545step2 raw4545step2Labels = mixedMoment B raw4545step3 raw4545step3Labels := by
      have ha : raw4545step3 = -raw4545step2 := by apply Matrix.ext; change ∀ i j, raw4545step3 i j = -(raw4545step2 i j); unfold raw4545step3 raw4545step2; decide +kernel
      have hl : raw4545step3Labels = raw4545step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw4546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw4546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw4546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw4546step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4546 raw4546Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw4546 raw4546Labels = mixedMoment B raw4546step0 raw4546step0Labels := by
      have hz : ∀ j, raw4546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4546step0 = (fun i j => raw4546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4546step0 raw4546; decide +kernel
      have hl : raw4546step0Labels = raw4546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4546 raw4546Labels permutation434 hz
    mixedMoment B raw4546step0 raw4546step0Labels = mixedMoment B raw4546step1 raw4546step1Labels := by
      have hz : ∀ j, raw4546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4546step1 = (fun i j => raw4546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4546step1 raw4546step0; decide +kernel
      have hl : raw4546step1Labels = raw4546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4546step0 raw4546step0Labels permutation80 hz
    mixedMoment B raw4546step1 raw4546step1Labels = mixedMoment B raw4546step2 raw4546step2Labels := by
      have hz : ∀ j, raw4546step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4546step2 = (fun i j => raw4546step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4546step2 raw4546step1; decide +kernel
      have hl : raw4546step2Labels = raw4546step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4546step1 raw4546step1Labels permutation14 hz
    mixedMoment B raw4546step2 raw4546step2Labels = mixedMoment B raw4546step3 raw4546step3Labels := by
      have ha : raw4546step3 = (fun i j => raw4546step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4546step3 raw4546step2; decide +kernel
      have hl : raw4546step3Labels = raw4546step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4546step2 raw4546step2Labels permutation7 permutation2
    mixedMoment B raw4546step3 raw4546step3Labels = mixedMoment B raw4546step4 raw4546step4Labels := by
      have ha : raw4546step4 = -raw4546step3 := by apply Matrix.ext; change ∀ i j, raw4546step4 i j = -(raw4546step3 i j); unfold raw4546step4 raw4546step3; decide +kernel
      have hl : raw4546step4Labels = raw4546step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw4547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4547step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4547step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4547 raw4547Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw4547 raw4547Labels = mixedMoment B raw4547step0 raw4547step0Labels := by
      have hz : ∀ j, raw4547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4547step0 = (fun i j => raw4547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4547step0 raw4547; decide +kernel
      have hl : raw4547step0Labels = raw4547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4547 raw4547Labels permutation434 hz
    mixedMoment B raw4547step0 raw4547step0Labels = mixedMoment B raw4547step1 raw4547step1Labels := by
      have hz : ∀ j, raw4547step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4547step1 = (fun i j => raw4547step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4547step1 raw4547step0; decide +kernel
      have hl : raw4547step1Labels = raw4547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4547step0 raw4547step0Labels permutation56 hz
    mixedMoment B raw4547step1 raw4547step1Labels = mixedMoment B raw4547step2 raw4547step2Labels := by
      have ha : raw4547step2 = (fun i j => raw4547step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4547step2 raw4547step1; decide +kernel
      have hl : raw4547step2Labels = raw4547step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4547step1 raw4547step1Labels permutation31 permutation2
    mixedMoment B raw4547step2 raw4547step2Labels = mixedMoment B raw4547step3 raw4547step3Labels := by
      have ha : raw4547step3 = -raw4547step2 := by apply Matrix.ext; change ∀ i j, raw4547step3 i j = -(raw4547step2 i j); unfold raw4547step3 raw4547step2; decide +kernel
      have hl : raw4547step3Labels = raw4547step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1059 node1059Labels := by rfl

def raw4548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4548step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4548step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4548 raw4548Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw4548 raw4548Labels = mixedMoment B raw4548step0 raw4548step0Labels := by
      have hz : ∀ j, raw4548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4548step0 = (fun i j => raw4548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4548step0 raw4548; decide +kernel
      have hl : raw4548step0Labels = raw4548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4548 raw4548Labels permutation346 hz
    mixedMoment B raw4548step0 raw4548step0Labels = mixedMoment B raw4548step1 raw4548step1Labels := by
      have hz : ∀ j, raw4548step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4548step1 = (fun i j => raw4548step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4548step1 raw4548step0; decide +kernel
      have hl : raw4548step1Labels = raw4548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4548step0 raw4548step0Labels permutation56 hz
    mixedMoment B raw4548step1 raw4548step1Labels = mixedMoment B raw4548step2 raw4548step2Labels := by
      have ha : raw4548step2 = (fun i j => raw4548step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4548step2 raw4548step1; decide +kernel
      have hl : raw4548step2Labels = raw4548step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4548step1 raw4548step1Labels permutation31 permutation2
    mixedMoment B raw4548step2 raw4548step2Labels = mixedMoment B raw4548step3 raw4548step3Labels := by
      have ha : raw4548step3 = -raw4548step2 := by apply Matrix.ext; change ∀ i j, raw4548step3 i j = -(raw4548step2 i j); unfold raw4548step3 raw4548step2; decide +kernel
      have hl : raw4548step3Labels = raw4548step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1059 node1059Labels := by rfl

def raw4549 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4549step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4549 raw4549Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw4549 raw4549Labels = mixedMoment B raw4549step0 raw4549step0Labels := by
      have hz : ∀ j, raw4549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4549step0 = (fun i j => raw4549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4549step0 raw4549; decide +kernel
      have hl : raw4549step0Labels = raw4549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4549 raw4549Labels permutation434 hz
    mixedMoment B raw4549step0 raw4549step0Labels = mixedMoment B raw4549step1 raw4549step1Labels := by
      have hz : ∀ j, raw4549step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4549step1 = (fun i j => raw4549step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4549step1 raw4549step0; decide +kernel
      have hl : raw4549step1Labels = raw4549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4549step0 raw4549step0Labels permutation56 hz
    mixedMoment B raw4549step1 raw4549step1Labels = mixedMoment B raw4549step2 raw4549step2Labels := by
      have ha : raw4549step2 = (fun i j => raw4549step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4549step2 raw4549step1; decide +kernel
      have hl : raw4549step2Labels = raw4549step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4549step1 raw4549step1Labels permutation29 permutation2
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw4550 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4550step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4550 raw4550Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw4550 raw4550Labels = mixedMoment B raw4550step0 raw4550step0Labels := by
      have hz : ∀ j, raw4550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4550step0 = (fun i j => raw4550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4550step0 raw4550; decide +kernel
      have hl : raw4550step0Labels = raw4550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4550 raw4550Labels permutation346 hz
    mixedMoment B raw4550step0 raw4550step0Labels = mixedMoment B raw4550step1 raw4550step1Labels := by
      have hz : ∀ j, raw4550step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4550step1 = (fun i j => raw4550step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4550step1 raw4550step0; decide +kernel
      have hl : raw4550step1Labels = raw4550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4550step0 raw4550step0Labels permutation56 hz
    mixedMoment B raw4550step1 raw4550step1Labels = mixedMoment B raw4550step2 raw4550step2Labels := by
      have ha : raw4550step2 = (fun i j => raw4550step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4550step2 raw4550step1; decide +kernel
      have hl : raw4550step2Labels = raw4550step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4550step1 raw4550step1Labels permutation29 permutation2
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw4551 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4551step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4551step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-4, 1, 3]]
def raw4551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4551step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw4551step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4551 raw4551Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw4551 raw4551Labels = mixedMoment B raw4551step0 raw4551step0Labels := by
      have hz : ∀ j, raw4551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4551step0 = (fun i j => raw4551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4551step0 raw4551; decide +kernel
      have hl : raw4551step0Labels = raw4551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4551 raw4551Labels permutation434 hz
    mixedMoment B raw4551step0 raw4551step0Labels = mixedMoment B raw4551step1 raw4551step1Labels := by
      have hz : ∀ j, raw4551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4551step1 = (fun i j => raw4551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4551step1 raw4551step0; decide +kernel
      have hl : raw4551step1Labels = raw4551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4551step0 raw4551step0Labels permutation80 hz
    mixedMoment B raw4551step1 raw4551step1Labels = mixedMoment B raw4551step2 raw4551step2Labels := by
      have hz : ∀ j, raw4551step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4551step2 = (fun i j => raw4551step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4551step2 raw4551step1; decide +kernel
      have hl : raw4551step2Labels = raw4551step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4551step1 raw4551step1Labels permutation14 hz
    mixedMoment B raw4551step2 raw4551step2Labels = mixedMoment B raw4551step3 raw4551step3Labels := by
      have ha : raw4551step3 = (fun i j => raw4551step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4551step3 raw4551step2; decide +kernel
      have hl : raw4551step3Labels = raw4551step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4551step2 raw4551step2Labels permutation7 permutation2
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw4552 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4552step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4552 raw4552Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw4552 raw4552Labels = mixedMoment B raw4552step0 raw4552step0Labels := by
      have hz : ∀ j, raw4552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4552step0 = (fun i j => raw4552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4552step0 raw4552; decide +kernel
      have hl : raw4552step0Labels = raw4552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4552 raw4552Labels permutation434 hz
    mixedMoment B raw4552step0 raw4552step0Labels = mixedMoment B raw4552step1 raw4552step1Labels := by
      have ha : raw4552step1 = (fun i j => raw4552step0 (permutation142 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4552step1 raw4552step0; decide +kernel
      have hl : raw4552step1Labels = raw4552step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4552step0 raw4552step0Labels permutation142 permutation2
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw4553 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4553 raw4553Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw4553 raw4553Labels = mixedMoment B raw4553step0 raw4553step0Labels := by
      have hz : ∀ j, raw4553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4553step0 = (fun i j => raw4553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4553step0 raw4553; decide +kernel
      have hl : raw4553step0Labels = raw4553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4553 raw4553Labels permutation346 hz
    mixedMoment B raw4553step0 raw4553step0Labels = mixedMoment B raw4553step1 raw4553step1Labels := by
      have ha : raw4553step1 = (fun i j => raw4553step0 (permutation142 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4553step1 raw4553step0; decide +kernel
      have hl : raw4553step1Labels = raw4553step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4553step0 raw4553step0Labels permutation142 permutation2
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw4554 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4554step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4554 raw4554Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw4554 raw4554Labels = mixedMoment B raw4554step0 raw4554step0Labels := by
      have hz : ∀ j, raw4554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4554step0 = (fun i j => raw4554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4554step0 raw4554; decide +kernel
      have hl : raw4554step0Labels = raw4554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4554 raw4554Labels permutation434 hz
    mixedMoment B raw4554step0 raw4554step0Labels = mixedMoment B raw4554step1 raw4554step1Labels := by
      have hz : ∀ j, raw4554step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4554step1 = (fun i j => raw4554step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4554step1 raw4554step0; decide +kernel
      have hl : raw4554step1Labels = raw4554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4554step0 raw4554step0Labels permutation80 hz
    mixedMoment B raw4554step1 raw4554step1Labels = mixedMoment B raw4554step2 raw4554step2Labels := by
      have ha : raw4554step2 = (fun i j => raw4554step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4554step2 raw4554step1; decide +kernel
      have hl : raw4554step2Labels = raw4554step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4554step1 raw4554step1Labels permutation28 permutation2
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw4555 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4555 raw4555Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw4555 raw4555Labels = mixedMoment B raw4555step0 raw4555step0Labels := by
      have hz : ∀ j, raw4555 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4555step0 = (fun i j => raw4555 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4555step0 raw4555; decide +kernel
      have hl : raw4555step0Labels = raw4555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4555 raw4555Labels permutation265 hz
    mixedMoment B raw4555step0 raw4555step0Labels = mixedMoment B raw4555step1 raw4555step1Labels := by
      have ha : raw4555step1 = (fun i j => raw4555step0 (permutation142 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4555step1 raw4555step0; decide +kernel
      have hl : raw4555step1Labels = raw4555step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4555step0 raw4555step0Labels permutation142 permutation2
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw4556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4556 raw4556Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw4556 raw4556Labels = mixedMoment B raw4556step0 raw4556step0Labels := by
      have hz : ∀ j, raw4556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4556step0 = (fun i j => raw4556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4556step0 raw4556; decide +kernel
      have hl : raw4556step0Labels = raw4556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4556 raw4556Labels permutation434 hz
    mixedMoment B raw4556step0 raw4556step0Labels = mixedMoment B raw4556step1 raw4556step1Labels := by
      have hz : ∀ j, raw4556step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4556step1 = (fun i j => raw4556step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4556step1 raw4556step0; decide +kernel
      have hl : raw4556step1Labels = raw4556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4556step0 raw4556step0Labels permutation56 hz
    mixedMoment B raw4556step1 raw4556step1Labels = mixedMoment B raw4556step2 raw4556step2Labels := by
      have ha : raw4556step2 = (fun i j => raw4556step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4556step2 raw4556step1; decide +kernel
      have hl : raw4556step2Labels = raw4556step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4556step1 raw4556step1Labels permutation28 permutation2
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw4557 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4557step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4557 raw4557Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw4557 raw4557Labels = mixedMoment B raw4557step0 raw4557step0Labels := by
      have hz : ∀ j, raw4557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4557step0 = (fun i j => raw4557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4557step0 raw4557; decide +kernel
      have hl : raw4557step0Labels = raw4557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4557 raw4557Labels permutation434 hz
    mixedMoment B raw4557step0 raw4557step0Labels = mixedMoment B raw4557step1 raw4557step1Labels := by
      have hz : ∀ j, raw4557step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4557step1 = (fun i j => raw4557step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4557step1 raw4557step0; decide +kernel
      have hl : raw4557step1Labels = raw4557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4557step0 raw4557step0Labels permutation56 hz
    mixedMoment B raw4557step1 raw4557step1Labels = mixedMoment B raw4557step2 raw4557step2Labels := by
      have ha : raw4557step2 = (fun i j => raw4557step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4557step2 raw4557step1; decide +kernel
      have hl : raw4557step2Labels = raw4557step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4557step1 raw4557step1Labels permutation28 permutation2
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw4558 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4558step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4558 raw4558Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw4558 raw4558Labels = mixedMoment B raw4558step0 raw4558step0Labels := by
      have hz : ∀ j, raw4558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4558step0 = (fun i j => raw4558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4558step0 raw4558; decide +kernel
      have hl : raw4558step0Labels = raw4558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4558 raw4558Labels permutation346 hz
    mixedMoment B raw4558step0 raw4558step0Labels = mixedMoment B raw4558step1 raw4558step1Labels := by
      have hz : ∀ j, raw4558step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4558step1 = (fun i j => raw4558step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4558step1 raw4558step0; decide +kernel
      have hl : raw4558step1Labels = raw4558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4558step0 raw4558step0Labels permutation56 hz
    mixedMoment B raw4558step1 raw4558step1Labels = mixedMoment B raw4558step2 raw4558step2Labels := by
      have ha : raw4558step2 = (fun i j => raw4558step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4558step2 raw4558step1; decide +kernel
      have hl : raw4558step2Labels = raw4558step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4558step1 raw4558step1Labels permutation28 permutation2
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw4559 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4559step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-4, 1, 3]]
def raw4559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4559step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw4559step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4559 raw4559Labels = mixedMoment B node4508 node4508Labels := by
  calc
    mixedMoment B raw4559 raw4559Labels = mixedMoment B raw4559step0 raw4559step0Labels := by
      have hz : ∀ j, raw4559 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4559step0 = (fun i j => raw4559 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4559step0 raw4559; decide +kernel
      have hl : raw4559step0Labels = raw4559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4559 raw4559Labels permutation434 hz
    mixedMoment B raw4559step0 raw4559step0Labels = mixedMoment B raw4559step1 raw4559step1Labels := by
      have hz : ∀ j, raw4559step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4559step1 = (fun i j => raw4559step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4559step1 raw4559step0; decide +kernel
      have hl : raw4559step1Labels = raw4559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4559step0 raw4559step0Labels permutation80 hz
    mixedMoment B raw4559step1 raw4559step1Labels = mixedMoment B raw4559step2 raw4559step2Labels := by
      have hz : ∀ j, raw4559step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4559step2 = (fun i j => raw4559step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4559step2 raw4559step1; decide +kernel
      have hl : raw4559step2Labels = raw4559step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4559step1 raw4559step1Labels permutation14 hz
    mixedMoment B raw4559step2 raw4559step2Labels = mixedMoment B raw4559step3 raw4559step3Labels := by
      have ha : raw4559step3 = (fun i j => raw4559step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4559step3 raw4559step2; decide +kernel
      have hl : raw4559step3Labels = raw4559step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4559step2 raw4559step2Labels permutation6 permutation2
    _ = mixedMoment B node4508 node4508Labels := by rfl

def raw4560 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4560step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw4560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4560 raw4560Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw4560 raw4560Labels = mixedMoment B raw4560step0 raw4560step0Labels := by
      have hz : ∀ j, raw4560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4560step0 = (fun i j => raw4560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4560step0 raw4560; decide +kernel
      have hl : raw4560step0Labels = raw4560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4560 raw4560Labels permutation434 hz
    mixedMoment B raw4560step0 raw4560step0Labels = mixedMoment B raw4560step1 raw4560step1Labels := by
      have hz : ∀ j, raw4560step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4560step1 = (fun i j => raw4560step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4560step1 raw4560step0; decide +kernel
      have hl : raw4560step1Labels = raw4560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4560step0 raw4560step0Labels permutation56 hz
    mixedMoment B raw4560step1 raw4560step1Labels = mixedMoment B raw4560step2 raw4560step2Labels := by
      have ha : raw4560step2 = (fun i j => raw4560step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4560step2 raw4560step1; decide +kernel
      have hl : raw4560step2Labels = raw4560step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4560step1 raw4560step1Labels permutation8 permutation6
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw4561 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4561step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw4561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4561 raw4561Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw4561 raw4561Labels = mixedMoment B raw4561step0 raw4561step0Labels := by
      have hz : ∀ j, raw4561 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4561step0 = (fun i j => raw4561 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4561step0 raw4561; decide +kernel
      have hl : raw4561step0Labels = raw4561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4561 raw4561Labels permutation346 hz
    mixedMoment B raw4561step0 raw4561step0Labels = mixedMoment B raw4561step1 raw4561step1Labels := by
      have hz : ∀ j, raw4561step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4561step1 = (fun i j => raw4561step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4561step1 raw4561step0; decide +kernel
      have hl : raw4561step1Labels = raw4561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4561step0 raw4561step0Labels permutation56 hz
    mixedMoment B raw4561step1 raw4561step1Labels = mixedMoment B raw4561step2 raw4561step2Labels := by
      have ha : raw4561step2 = (fun i j => raw4561step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4561step2 raw4561step1; decide +kernel
      have hl : raw4561step2Labels = raw4561step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4561step1 raw4561step1Labels permutation8 permutation6
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw4562 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4562step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4562step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-4, 1, 3]]
def raw4562step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4562step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw4562step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4562 raw4562Labels = mixedMoment B node1454 node1454Labels := by
  calc
    mixedMoment B raw4562 raw4562Labels = mixedMoment B raw4562step0 raw4562step0Labels := by
      have hz : ∀ j, raw4562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4562step0 = (fun i j => raw4562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4562step0 raw4562; decide +kernel
      have hl : raw4562step0Labels = raw4562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4562 raw4562Labels permutation434 hz
    mixedMoment B raw4562step0 raw4562step0Labels = mixedMoment B raw4562step1 raw4562step1Labels := by
      have hz : ∀ j, raw4562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4562step1 = (fun i j => raw4562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4562step1 raw4562step0; decide +kernel
      have hl : raw4562step1Labels = raw4562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4562step0 raw4562step0Labels permutation80 hz
    mixedMoment B raw4562step1 raw4562step1Labels = mixedMoment B raw4562step2 raw4562step2Labels := by
      have hz : ∀ j, raw4562step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4562step2 = (fun i j => raw4562step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4562step2 raw4562step1; decide +kernel
      have hl : raw4562step2Labels = raw4562step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4562step1 raw4562step1Labels permutation14 hz
    mixedMoment B raw4562step2 raw4562step2Labels = mixedMoment B raw4562step3 raw4562step3Labels := by
      have ha : raw4562step3 = (fun i j => raw4562step2 (permutation6 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4562step3 raw4562step2; decide +kernel
      have hl : raw4562step3Labels = raw4562step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4562step2 raw4562step2Labels permutation6 permutation3
    _ = mixedMoment B node1454 node1454Labels := by rfl

def raw4563 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4563 raw4563Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw4563 raw4563Labels = mixedMoment B raw4563step0 raw4563step0Labels := by
      have hz : ∀ j, raw4563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4563step0 = (fun i j => raw4563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4563step0 raw4563; decide +kernel
      have hl : raw4563step0Labels = raw4563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4563 raw4563Labels permutation434 hz
    mixedMoment B raw4563step0 raw4563step0Labels = mixedMoment B raw4563step1 raw4563step1Labels := by
      have ha : raw4563step1 = (fun i j => raw4563step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4563step1 raw4563step0; decide +kernel
      have hl : raw4563step1Labels = raw4563step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4563step0 raw4563step0Labels permutation38 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw4564 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4564 raw4564Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw4564 raw4564Labels = mixedMoment B raw4564step0 raw4564step0Labels := by
      have hz : ∀ j, raw4564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4564step0 = (fun i j => raw4564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4564step0 raw4564; decide +kernel
      have hl : raw4564step0Labels = raw4564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4564 raw4564Labels permutation346 hz
    mixedMoment B raw4564step0 raw4564step0Labels = mixedMoment B raw4564step1 raw4564step1Labels := by
      have ha : raw4564step1 = (fun i j => raw4564step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4564step1 raw4564step0; decide +kernel
      have hl : raw4564step1Labels = raw4564step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4564step0 raw4564step0Labels permutation38 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw4565 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4565step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4565 raw4565Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw4565 raw4565Labels = mixedMoment B raw4565step0 raw4565step0Labels := by
      have hz : ∀ j, raw4565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4565step0 = (fun i j => raw4565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4565step0 raw4565; decide +kernel
      have hl : raw4565step0Labels = raw4565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4565 raw4565Labels permutation434 hz
    mixedMoment B raw4565step0 raw4565step0Labels = mixedMoment B raw4565step1 raw4565step1Labels := by
      have hz : ∀ j, raw4565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4565step1 = (fun i j => raw4565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4565step1 raw4565step0; decide +kernel
      have hl : raw4565step1Labels = raw4565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4565step0 raw4565step0Labels permutation80 hz
    mixedMoment B raw4565step1 raw4565step1Labels = mixedMoment B raw4565step2 raw4565step2Labels := by
      have ha : raw4565step2 = (fun i j => raw4565step1 (permutation26 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4565step2 raw4565step1; decide +kernel
      have hl : raw4565step2Labels = raw4565step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4565step1 raw4565step1Labels permutation26 permutation3
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw4566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4566step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4566 raw4566Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw4566 raw4566Labels = mixedMoment B raw4566step0 raw4566step0Labels := by
      have hz : ∀ j, raw4566 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4566step0 = (fun i j => raw4566 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4566step0 raw4566; decide +kernel
      have hl : raw4566step0Labels = raw4566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4566 raw4566Labels permutation265 hz
    mixedMoment B raw4566step0 raw4566step0Labels = mixedMoment B raw4566step1 raw4566step1Labels := by
      have ha : raw4566step1 = (fun i j => raw4566step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4566step1 raw4566step0; decide +kernel
      have hl : raw4566step1Labels = raw4566step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4566step0 raw4566step0Labels permutation38 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw4567 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4567step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4567 raw4567Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw4567 raw4567Labels = mixedMoment B raw4567step0 raw4567step0Labels := by
      have hz : ∀ j, raw4567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4567step0 = (fun i j => raw4567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4567step0 raw4567; decide +kernel
      have hl : raw4567step0Labels = raw4567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4567 raw4567Labels permutation434 hz
    mixedMoment B raw4567step0 raw4567step0Labels = mixedMoment B raw4567step1 raw4567step1Labels := by
      have hz : ∀ j, raw4567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4567step1 = (fun i j => raw4567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4567step1 raw4567step0; decide +kernel
      have hl : raw4567step1Labels = raw4567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4567step0 raw4567step0Labels permutation56 hz
    mixedMoment B raw4567step1 raw4567step1Labels = mixedMoment B raw4567step2 raw4567step2Labels := by
      have ha : raw4567step2 = (fun i j => raw4567step1 (permutation26 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4567step2 raw4567step1; decide +kernel
      have hl : raw4567step2Labels = raw4567step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4567step1 raw4567step1Labels permutation26 permutation3
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw4568 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4568step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw4568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4568 raw4568Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw4568 raw4568Labels = mixedMoment B raw4568step0 raw4568step0Labels := by
      have hz : ∀ j, raw4568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4568step0 = (fun i j => raw4568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4568step0 raw4568; decide +kernel
      have hl : raw4568step0Labels = raw4568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4568 raw4568Labels permutation434 hz
    mixedMoment B raw4568step0 raw4568step0Labels = mixedMoment B raw4568step1 raw4568step1Labels := by
      have hz : ∀ j, raw4568step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4568step1 = (fun i j => raw4568step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4568step1 raw4568step0; decide +kernel
      have hl : raw4568step1Labels = raw4568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4568step0 raw4568step0Labels permutation56 hz
    mixedMoment B raw4568step1 raw4568step1Labels = mixedMoment B raw4568step2 raw4568step2Labels := by
      have ha : raw4568step2 = (fun i j => raw4568step1 (permutation20 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4568step2 raw4568step1; decide +kernel
      have hl : raw4568step2Labels = raw4568step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4568step1 raw4568step1Labels permutation20 permutation3
    mixedMoment B raw4568step2 raw4568step2Labels = mixedMoment B raw4568step3 raw4568step3Labels := by
      have ha : raw4568step3 = -raw4568step2 := by apply Matrix.ext; change ∀ i j, raw4568step3 i j = -(raw4568step2 i j); unfold raw4568step3 raw4568step2; decide +kernel
      have hl : raw4568step3Labels = raw4568step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2136 node2136Labels := by rfl

def raw4569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4569step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw4569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4569step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4569 raw4569Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw4569 raw4569Labels = mixedMoment B raw4569step0 raw4569step0Labels := by
      have hz : ∀ j, raw4569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4569step0 = (fun i j => raw4569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4569step0 raw4569; decide +kernel
      have hl : raw4569step0Labels = raw4569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4569 raw4569Labels permutation346 hz
    mixedMoment B raw4569step0 raw4569step0Labels = mixedMoment B raw4569step1 raw4569step1Labels := by
      have hz : ∀ j, raw4569step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4569step1 = (fun i j => raw4569step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4569step1 raw4569step0; decide +kernel
      have hl : raw4569step1Labels = raw4569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4569step0 raw4569step0Labels permutation56 hz
    mixedMoment B raw4569step1 raw4569step1Labels = mixedMoment B raw4569step2 raw4569step2Labels := by
      have ha : raw4569step2 = (fun i j => raw4569step1 (permutation20 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4569step2 raw4569step1; decide +kernel
      have hl : raw4569step2Labels = raw4569step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4569step1 raw4569step1Labels permutation20 permutation3
    mixedMoment B raw4569step2 raw4569step2Labels = mixedMoment B raw4569step3 raw4569step3Labels := by
      have ha : raw4569step3 = -raw4569step2 := by apply Matrix.ext; change ∀ i j, raw4569step3 i j = -(raw4569step2 i j); unfold raw4569step3 raw4569step2; decide +kernel
      have hl : raw4569step3Labels = raw4569step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2136 node2136Labels := by rfl

def raw4570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4570step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4570step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-4, 1, 3]]
def raw4570step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4570step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw4570step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4570 raw4570Labels = mixedMoment B node1438 node1438Labels := by
  calc
    mixedMoment B raw4570 raw4570Labels = mixedMoment B raw4570step0 raw4570step0Labels := by
      have hz : ∀ j, raw4570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4570step0 = (fun i j => raw4570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4570step0 raw4570; decide +kernel
      have hl : raw4570step0Labels = raw4570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4570 raw4570Labels permutation434 hz
    mixedMoment B raw4570step0 raw4570step0Labels = mixedMoment B raw4570step1 raw4570step1Labels := by
      have hz : ∀ j, raw4570step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4570step1 = (fun i j => raw4570step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4570step1 raw4570step0; decide +kernel
      have hl : raw4570step1Labels = raw4570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4570step0 raw4570step0Labels permutation80 hz
    mixedMoment B raw4570step1 raw4570step1Labels = mixedMoment B raw4570step2 raw4570step2Labels := by
      have hz : ∀ j, raw4570step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4570step2 = (fun i j => raw4570step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4570step2 raw4570step1; decide +kernel
      have hl : raw4570step2Labels = raw4570step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4570step1 raw4570step1Labels permutation14 hz
    mixedMoment B raw4570step2 raw4570step2Labels = mixedMoment B raw4570step3 raw4570step3Labels := by
      have ha : raw4570step3 = (fun i j => raw4570step2 (permutation6 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4570step3 raw4570step2; decide +kernel
      have hl : raw4570step3Labels = raw4570step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4570step2 raw4570step2Labels permutation6 permutation3
    _ = mixedMoment B node1438 node1438Labels := by rfl

def raw4571 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4571Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4571step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4571step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw4571step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4571step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4571step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4571step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4571step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4571 raw4571Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw4571 raw4571Labels = mixedMoment B raw4571step0 raw4571step0Labels := by
      have hz : ∀ j, raw4571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4571step0 = (fun i j => raw4571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4571step0 raw4571; decide +kernel
      have hl : raw4571step0Labels = raw4571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4571 raw4571Labels permutation434 hz
    mixedMoment B raw4571step0 raw4571step0Labels = mixedMoment B raw4571step1 raw4571step1Labels := by
      have hz : ∀ j, raw4571step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4571step1 = (fun i j => raw4571step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4571step1 raw4571step0; decide +kernel
      have hl : raw4571step1Labels = raw4571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4571step0 raw4571step0Labels permutation80 hz
    mixedMoment B raw4571step1 raw4571step1Labels = mixedMoment B raw4571step2 raw4571step2Labels := by
      have ha : raw4571step2 = (fun i j => raw4571step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4571step2 raw4571step1; decide +kernel
      have hl : raw4571step2Labels = raw4571step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4571step1 raw4571step1Labels permutation29 permutation7
    mixedMoment B raw4571step2 raw4571step2Labels = mixedMoment B raw4571step3 raw4571step3Labels := by
      have ha : raw4571step3 = -raw4571step2 := by apply Matrix.ext; change ∀ i j, raw4571step3 i j = -(raw4571step2 i j); unfold raw4571step3 raw4571step2; decide +kernel
      have hl : raw4571step3Labels = raw4571step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4571step3 raw4571step3Labels = mixedMoment B raw4571step4 raw4571step4Labels := by
      have ha : raw4571step4 = raw4571step3 := by apply Matrix.ext; unfold raw4571step4 raw4571step3; decide +kernel
      have hl : raw4571step3Labels = labelEmbedding1 ∘ raw4571step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4571step3 raw4571step3Labels raw4571step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw4572 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4572step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4572step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw4572step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4572step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4572step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4572step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4572step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4572 raw4572Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw4572 raw4572Labels = mixedMoment B raw4572step0 raw4572step0Labels := by
      have hz : ∀ j, raw4572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4572step0 = (fun i j => raw4572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4572step0 raw4572; decide +kernel
      have hl : raw4572step0Labels = raw4572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4572 raw4572Labels permutation434 hz
    mixedMoment B raw4572step0 raw4572step0Labels = mixedMoment B raw4572step1 raw4572step1Labels := by
      have hz : ∀ j, raw4572step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4572step1 = (fun i j => raw4572step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4572step1 raw4572step0; decide +kernel
      have hl : raw4572step1Labels = raw4572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4572step0 raw4572step0Labels permutation56 hz
    mixedMoment B raw4572step1 raw4572step1Labels = mixedMoment B raw4572step2 raw4572step2Labels := by
      have ha : raw4572step2 = (fun i j => raw4572step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4572step2 raw4572step1; decide +kernel
      have hl : raw4572step2Labels = raw4572step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4572step1 raw4572step1Labels permutation29 permutation7
    mixedMoment B raw4572step2 raw4572step2Labels = mixedMoment B raw4572step3 raw4572step3Labels := by
      have ha : raw4572step3 = -raw4572step2 := by apply Matrix.ext; change ∀ i j, raw4572step3 i j = -(raw4572step2 i j); unfold raw4572step3 raw4572step2; decide +kernel
      have hl : raw4572step3Labels = raw4572step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4572step3 raw4572step3Labels = mixedMoment B raw4572step4 raw4572step4Labels := by
      have ha : raw4572step4 = raw4572step3 := by apply Matrix.ext; unfold raw4572step4 raw4572step3; decide +kernel
      have hl : raw4572step3Labels = labelEmbedding1 ∘ raw4572step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4572step3 raw4572step3Labels raw4572step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw4573 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4573Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4573step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4573step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw4573step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4573step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4573step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4573step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4573 raw4573Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw4573 raw4573Labels = mixedMoment B raw4573step0 raw4573step0Labels := by
      have hz : ∀ j, raw4573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4573step0 = (fun i j => raw4573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4573step0 raw4573; decide +kernel
      have hl : raw4573step0Labels = raw4573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4573 raw4573Labels permutation346 hz
    mixedMoment B raw4573step0 raw4573step0Labels = mixedMoment B raw4573step1 raw4573step1Labels := by
      have hz : ∀ j, raw4573step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4573step1 = (fun i j => raw4573step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4573step1 raw4573step0; decide +kernel
      have hl : raw4573step1Labels = raw4573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4573step0 raw4573step0Labels permutation56 hz
    mixedMoment B raw4573step1 raw4573step1Labels = mixedMoment B raw4573step2 raw4573step2Labels := by
      have ha : raw4573step2 = (fun i j => raw4573step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4573step2 raw4573step1; decide +kernel
      have hl : raw4573step2Labels = raw4573step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4573step1 raw4573step1Labels permutation29 permutation7
    mixedMoment B raw4573step2 raw4573step2Labels = mixedMoment B raw4573step3 raw4573step3Labels := by
      have ha : raw4573step3 = -raw4573step2 := by apply Matrix.ext; change ∀ i j, raw4573step3 i j = -(raw4573step2 i j); unfold raw4573step3 raw4573step2; decide +kernel
      have hl : raw4573step3Labels = raw4573step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4573step3 raw4573step3Labels = mixedMoment B raw4573step4 raw4573step4Labels := by
      have ha : raw4573step4 = raw4573step3 := by apply Matrix.ext; unfold raw4573step4 raw4573step3; decide +kernel
      have hl : raw4573step3Labels = labelEmbedding1 ∘ raw4573step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4573step3 raw4573step3Labels raw4573step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw4574 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4574Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4574step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4574step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4574step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4574step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4574step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4574step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4574step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4574step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4574step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4574step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4574 raw4574Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw4574 raw4574Labels = mixedMoment B raw4574step0 raw4574step0Labels := by
      have hz : ∀ j, raw4574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4574step0 = (fun i j => raw4574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4574step0 raw4574; decide +kernel
      have hl : raw4574step0Labels = raw4574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4574 raw4574Labels permutation434 hz
    mixedMoment B raw4574step0 raw4574step0Labels = mixedMoment B raw4574step1 raw4574step1Labels := by
      have hz : ∀ j, raw4574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4574step1 = (fun i j => raw4574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4574step1 raw4574step0; decide +kernel
      have hl : raw4574step1Labels = raw4574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4574step0 raw4574step0Labels permutation80 hz
    mixedMoment B raw4574step1 raw4574step1Labels = mixedMoment B raw4574step2 raw4574step2Labels := by
      have hz : ∀ j, raw4574step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4574step2 = (fun i j => raw4574step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4574step2 raw4574step1; decide +kernel
      have hl : raw4574step2Labels = raw4574step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4574step1 raw4574step1Labels permutation14 hz
    mixedMoment B raw4574step2 raw4574step2Labels = mixedMoment B raw4574step3 raw4574step3Labels := by
      have ha : raw4574step3 = (fun i j => raw4574step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4574step3 raw4574step2; decide +kernel
      have hl : raw4574step3Labels = raw4574step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4574step2 raw4574step2Labels permutation7 permutation7
    mixedMoment B raw4574step3 raw4574step3Labels = mixedMoment B raw4574step4 raw4574step4Labels := by
      have ha : raw4574step4 = -raw4574step3 := by apply Matrix.ext; change ∀ i j, raw4574step4 i j = -(raw4574step3 i j); unfold raw4574step4 raw4574step3; decide +kernel
      have hl : raw4574step4Labels = raw4574step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4574step4 raw4574step4Labels = mixedMoment B raw4574step5 raw4574step5Labels := by
      have ha : raw4574step5 = raw4574step4 := by apply Matrix.ext; unfold raw4574step5 raw4574step4; decide +kernel
      have hl : raw4574step4Labels = labelEmbedding1 ∘ raw4574step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4574step4 raw4574step4Labels raw4574step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw4575 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4575Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4575step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4575step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4575step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-4, 1, 3]]
def raw4575step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4575step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw4575step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4575step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw4575step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4575step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw4575step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4575 raw4575Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw4575 raw4575Labels = mixedMoment B raw4575step0 raw4575step0Labels := by
      have hz : ∀ j, raw4575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4575step0 = (fun i j => raw4575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4575step0 raw4575; decide +kernel
      have hl : raw4575step0Labels = raw4575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4575 raw4575Labels permutation434 hz
    mixedMoment B raw4575step0 raw4575step0Labels = mixedMoment B raw4575step1 raw4575step1Labels := by
      have hz : ∀ j, raw4575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4575step1 = (fun i j => raw4575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4575step1 raw4575step0; decide +kernel
      have hl : raw4575step1Labels = raw4575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4575step0 raw4575step0Labels permutation80 hz
    mixedMoment B raw4575step1 raw4575step1Labels = mixedMoment B raw4575step2 raw4575step2Labels := by
      have hz : ∀ j, raw4575step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4575step2 = (fun i j => raw4575step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4575step2 raw4575step1; decide +kernel
      have hl : raw4575step2Labels = raw4575step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4575step1 raw4575step1Labels permutation14 hz
    mixedMoment B raw4575step2 raw4575step2Labels = mixedMoment B raw4575step3 raw4575step3Labels := by
      have ha : raw4575step3 = (fun i j => raw4575step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4575step3 raw4575step2; decide +kernel
      have hl : raw4575step3Labels = raw4575step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4575step2 raw4575step2Labels permutation7 permutation7
    mixedMoment B raw4575step3 raw4575step3Labels = mixedMoment B raw4575step4 raw4575step4Labels := by
      have ha : raw4575step4 = -raw4575step3 := by apply Matrix.ext; change ∀ i j, raw4575step4 i j = -(raw4575step3 i j); unfold raw4575step4 raw4575step3; decide +kernel
      have hl : raw4575step4Labels = raw4575step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4575step4 raw4575step4Labels = mixedMoment B raw4575step5 raw4575step5Labels := by
      have ha : raw4575step5 = raw4575step4 := by apply Matrix.ext; unfold raw4575step5 raw4575step4; decide +kernel
      have hl : raw4575step4Labels = labelEmbedding1 ∘ raw4575step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4575step4 raw4575step4Labels raw4575step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

def raw4576 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4576Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4576step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4576step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw4576step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4576step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4576step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4576step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4576 raw4576Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw4576 raw4576Labels = mixedMoment B raw4576step0 raw4576step0Labels := by
      have hz : ∀ j, raw4576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4576step0 = (fun i j => raw4576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4576step0 raw4576; decide +kernel
      have hl : raw4576step0Labels = raw4576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4576 raw4576Labels permutation434 hz
    mixedMoment B raw4576step0 raw4576step0Labels = mixedMoment B raw4576step1 raw4576step1Labels := by
      have hz : ∀ j, raw4576step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4576step1 = (fun i j => raw4576step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4576step1 raw4576step0; decide +kernel
      have hl : raw4576step1Labels = raw4576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4576step0 raw4576step0Labels permutation80 hz
    mixedMoment B raw4576step1 raw4576step1Labels = mixedMoment B raw4576step2 raw4576step2Labels := by
      have ha : raw4576step2 = (fun i j => raw4576step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4576step2 raw4576step1; decide +kernel
      have hl : raw4576step2Labels = raw4576step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4576step1 raw4576step1Labels permutation29 permutation7
    mixedMoment B raw4576step2 raw4576step2Labels = mixedMoment B raw4576step3 raw4576step3Labels := by
      have ha : raw4576step3 = -raw4576step2 := by apply Matrix.ext; change ∀ i j, raw4576step3 i j = -(raw4576step2 i j); unfold raw4576step3 raw4576step2; decide +kernel
      have hl : raw4576step3Labels = raw4576step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4576step3 raw4576step3Labels = mixedMoment B raw4576step4 raw4576step4Labels := by
      have ha : raw4576step4 = raw4576step3 := by apply Matrix.ext; unfold raw4576step4 raw4576step3; decide +kernel
      have hl : raw4576step3Labels = labelEmbedding1 ∘ raw4576step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4576step3 raw4576step3Labels raw4576step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw4577 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4577Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4577step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4577step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4577step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4577step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4577step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4577 raw4577Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw4577 raw4577Labels = mixedMoment B raw4577step0 raw4577step0Labels := by
      have hz : ∀ j, raw4577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4577step0 = (fun i j => raw4577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4577step0 raw4577; decide +kernel
      have hl : raw4577step0Labels = raw4577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4577 raw4577Labels permutation434 hz
    mixedMoment B raw4577step0 raw4577step0Labels = mixedMoment B raw4577step1 raw4577step1Labels := by
      have ha : raw4577step1 = (fun i j => raw4577step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4577step1 raw4577step0; decide +kernel
      have hl : raw4577step1Labels = raw4577step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4577step0 raw4577step0Labels permutation143 permutation7
    mixedMoment B raw4577step1 raw4577step1Labels = mixedMoment B raw4577step2 raw4577step2Labels := by
      have ha : raw4577step2 = -raw4577step1 := by apply Matrix.ext; change ∀ i j, raw4577step2 i j = -(raw4577step1 i j); unfold raw4577step2 raw4577step1; decide +kernel
      have hl : raw4577step2Labels = raw4577step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4577step2 raw4577step2Labels = mixedMoment B raw4577step3 raw4577step3Labels := by
      have ha : raw4577step3 = raw4577step2 := by apply Matrix.ext; unfold raw4577step3 raw4577step2; decide +kernel
      have hl : raw4577step2Labels = labelEmbedding1 ∘ raw4577step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4577step2 raw4577step2Labels raw4577step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw4578 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4578Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4578step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4578step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4578step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4578step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4578 raw4578Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw4578 raw4578Labels = mixedMoment B raw4578step0 raw4578step0Labels := by
      have hz : ∀ j, raw4578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4578step0 = (fun i j => raw4578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4578step0 raw4578; decide +kernel
      have hl : raw4578step0Labels = raw4578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4578 raw4578Labels permutation346 hz
    mixedMoment B raw4578step0 raw4578step0Labels = mixedMoment B raw4578step1 raw4578step1Labels := by
      have ha : raw4578step1 = (fun i j => raw4578step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4578step1 raw4578step0; decide +kernel
      have hl : raw4578step1Labels = raw4578step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4578step0 raw4578step0Labels permutation143 permutation7
    mixedMoment B raw4578step1 raw4578step1Labels = mixedMoment B raw4578step2 raw4578step2Labels := by
      have ha : raw4578step2 = -raw4578step1 := by apply Matrix.ext; change ∀ i j, raw4578step2 i j = -(raw4578step1 i j); unfold raw4578step2 raw4578step1; decide +kernel
      have hl : raw4578step2Labels = raw4578step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4578step2 raw4578step2Labels = mixedMoment B raw4578step3 raw4578step3Labels := by
      have ha : raw4578step3 = raw4578step2 := by apply Matrix.ext; unfold raw4578step3 raw4578step2; decide +kernel
      have hl : raw4578step2Labels = labelEmbedding1 ∘ raw4578step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4578step2 raw4578step2Labels raw4578step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw4579 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4579Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4579step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4579step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4579step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4579step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4579step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4579step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4579step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4579 raw4579Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw4579 raw4579Labels = mixedMoment B raw4579step0 raw4579step0Labels := by
      have hz : ∀ j, raw4579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4579step0 = (fun i j => raw4579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4579step0 raw4579; decide +kernel
      have hl : raw4579step0Labels = raw4579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4579 raw4579Labels permutation434 hz
    mixedMoment B raw4579step0 raw4579step0Labels = mixedMoment B raw4579step1 raw4579step1Labels := by
      have hz : ∀ j, raw4579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4579step1 = (fun i j => raw4579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4579step1 raw4579step0; decide +kernel
      have hl : raw4579step1Labels = raw4579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4579step0 raw4579step0Labels permutation80 hz
    mixedMoment B raw4579step1 raw4579step1Labels = mixedMoment B raw4579step2 raw4579step2Labels := by
      have ha : raw4579step2 = (fun i j => raw4579step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4579step2 raw4579step1; decide +kernel
      have hl : raw4579step2Labels = raw4579step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4579step1 raw4579step1Labels permutation29 permutation7
    mixedMoment B raw4579step2 raw4579step2Labels = mixedMoment B raw4579step3 raw4579step3Labels := by
      have ha : raw4579step3 = -raw4579step2 := by apply Matrix.ext; change ∀ i j, raw4579step3 i j = -(raw4579step2 i j); unfold raw4579step3 raw4579step2; decide +kernel
      have hl : raw4579step3Labels = raw4579step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4579step3 raw4579step3Labels = mixedMoment B raw4579step4 raw4579step4Labels := by
      have ha : raw4579step4 = raw4579step3 := by apply Matrix.ext; unfold raw4579step4 raw4579step3; decide +kernel
      have hl : raw4579step3Labels = labelEmbedding1 ∘ raw4579step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4579step3 raw4579step3Labels raw4579step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw4580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4580Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4580step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4580step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4580step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4580step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4580step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4580step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4580step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4580 raw4580Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw4580 raw4580Labels = mixedMoment B raw4580step0 raw4580step0Labels := by
      have hz : ∀ j, raw4580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4580step0 = (fun i j => raw4580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4580step0 raw4580; decide +kernel
      have hl : raw4580step0Labels = raw4580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4580 raw4580Labels permutation434 hz
    mixedMoment B raw4580step0 raw4580step0Labels = mixedMoment B raw4580step1 raw4580step1Labels := by
      have hz : ∀ j, raw4580step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4580step1 = (fun i j => raw4580step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4580step1 raw4580step0; decide +kernel
      have hl : raw4580step1Labels = raw4580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4580step0 raw4580step0Labels permutation80 hz
    mixedMoment B raw4580step1 raw4580step1Labels = mixedMoment B raw4580step2 raw4580step2Labels := by
      have ha : raw4580step2 = (fun i j => raw4580step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4580step2 raw4580step1; decide +kernel
      have hl : raw4580step2Labels = raw4580step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4580step1 raw4580step1Labels permutation29 permutation7
    mixedMoment B raw4580step2 raw4580step2Labels = mixedMoment B raw4580step3 raw4580step3Labels := by
      have ha : raw4580step3 = -raw4580step2 := by apply Matrix.ext; change ∀ i j, raw4580step3 i j = -(raw4580step2 i j); unfold raw4580step3 raw4580step2; decide +kernel
      have hl : raw4580step3Labels = raw4580step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4580step3 raw4580step3Labels = mixedMoment B raw4580step4 raw4580step4Labels := by
      have ha : raw4580step4 = raw4580step3 := by apply Matrix.ext; unfold raw4580step4 raw4580step3; decide +kernel
      have hl : raw4580step3Labels = labelEmbedding1 ∘ raw4580step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4580step3 raw4580step3Labels raw4580step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw4581 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4581Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4581step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4581step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw4581step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4581step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4581step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4581step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4581step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4581 raw4581Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw4581 raw4581Labels = mixedMoment B raw4581step0 raw4581step0Labels := by
      have hz : ∀ j, raw4581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4581step0 = (fun i j => raw4581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4581step0 raw4581; decide +kernel
      have hl : raw4581step0Labels = raw4581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4581 raw4581Labels permutation434 hz
    mixedMoment B raw4581step0 raw4581step0Labels = mixedMoment B raw4581step1 raw4581step1Labels := by
      have hz : ∀ j, raw4581step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4581step1 = (fun i j => raw4581step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4581step1 raw4581step0; decide +kernel
      have hl : raw4581step1Labels = raw4581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4581step0 raw4581step0Labels permutation56 hz
    mixedMoment B raw4581step1 raw4581step1Labels = mixedMoment B raw4581step2 raw4581step2Labels := by
      have ha : raw4581step2 = (fun i j => raw4581step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4581step2 raw4581step1; decide +kernel
      have hl : raw4581step2Labels = raw4581step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4581step1 raw4581step1Labels permutation29 permutation7
    mixedMoment B raw4581step2 raw4581step2Labels = mixedMoment B raw4581step3 raw4581step3Labels := by
      have ha : raw4581step3 = -raw4581step2 := by apply Matrix.ext; change ∀ i j, raw4581step3 i j = -(raw4581step2 i j); unfold raw4581step3 raw4581step2; decide +kernel
      have hl : raw4581step3Labels = raw4581step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4581step3 raw4581step3Labels = mixedMoment B raw4581step4 raw4581step4Labels := by
      have ha : raw4581step4 = raw4581step3 := by apply Matrix.ext; unfold raw4581step4 raw4581step3; decide +kernel
      have hl : raw4581step3Labels = labelEmbedding1 ∘ raw4581step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4581step3 raw4581step3Labels raw4581step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw4582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4582Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4582step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4582step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4582step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4582step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4582step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4582 raw4582Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw4582 raw4582Labels = mixedMoment B raw4582step0 raw4582step0Labels := by
      have hz : ∀ j, raw4582 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4582step0 = (fun i j => raw4582 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4582step0 raw4582; decide +kernel
      have hl : raw4582step0Labels = raw4582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4582 raw4582Labels permutation434 hz
    mixedMoment B raw4582step0 raw4582step0Labels = mixedMoment B raw4582step1 raw4582step1Labels := by
      have ha : raw4582step1 = (fun i j => raw4582step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4582step1 raw4582step0; decide +kernel
      have hl : raw4582step1Labels = raw4582step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4582step0 raw4582step0Labels permutation137 permutation7
    mixedMoment B raw4582step1 raw4582step1Labels = mixedMoment B raw4582step2 raw4582step2Labels := by
      have ha : raw4582step2 = -raw4582step1 := by apply Matrix.ext; change ∀ i j, raw4582step2 i j = -(raw4582step1 i j); unfold raw4582step2 raw4582step1; decide +kernel
      have hl : raw4582step2Labels = raw4582step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4582step2 raw4582step2Labels = mixedMoment B raw4582step3 raw4582step3Labels := by
      have ha : raw4582step3 = raw4582step2 := by apply Matrix.ext; unfold raw4582step3 raw4582step2; decide +kernel
      have hl : raw4582step2Labels = labelEmbedding1 ∘ raw4582step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4582step2 raw4582step2Labels raw4582step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw4583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4583Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4583step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4583step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4583step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4583step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4583step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4583step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4583 raw4583Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw4583 raw4583Labels = mixedMoment B raw4583step0 raw4583step0Labels := by
      have hz : ∀ j, raw4583 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4583step0 = (fun i j => raw4583 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4583step0 raw4583; decide +kernel
      have hl : raw4583step0Labels = raw4583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4583 raw4583Labels permutation265 hz
    mixedMoment B raw4583step0 raw4583step0Labels = mixedMoment B raw4583step1 raw4583step1Labels := by
      have ha : raw4583step1 = (fun i j => raw4583step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4583step1 raw4583step0; decide +kernel
      have hl : raw4583step1Labels = raw4583step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4583step0 raw4583step0Labels permutation143 permutation7
    mixedMoment B raw4583step1 raw4583step1Labels = mixedMoment B raw4583step2 raw4583step2Labels := by
      have ha : raw4583step2 = -raw4583step1 := by apply Matrix.ext; change ∀ i j, raw4583step2 i j = -(raw4583step1 i j); unfold raw4583step2 raw4583step1; decide +kernel
      have hl : raw4583step2Labels = raw4583step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4583step2 raw4583step2Labels = mixedMoment B raw4583step3 raw4583step3Labels := by
      have ha : raw4583step3 = raw4583step2 := by apply Matrix.ext; unfold raw4583step3 raw4583step2; decide +kernel
      have hl : raw4583step2Labels = labelEmbedding1 ∘ raw4583step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4583step2 raw4583step2Labels raw4583step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw4584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4584Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4584step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4584step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4584step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4584step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4584step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4584step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4584step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4584 raw4584Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw4584 raw4584Labels = mixedMoment B raw4584step0 raw4584step0Labels := by
      have hz : ∀ j, raw4584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4584step0 = (fun i j => raw4584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4584step0 raw4584; decide +kernel
      have hl : raw4584step0Labels = raw4584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4584 raw4584Labels permutation434 hz
    mixedMoment B raw4584step0 raw4584step0Labels = mixedMoment B raw4584step1 raw4584step1Labels := by
      have hz : ∀ j, raw4584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4584step1 = (fun i j => raw4584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4584step1 raw4584step0; decide +kernel
      have hl : raw4584step1Labels = raw4584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4584step0 raw4584step0Labels permutation56 hz
    mixedMoment B raw4584step1 raw4584step1Labels = mixedMoment B raw4584step2 raw4584step2Labels := by
      have ha : raw4584step2 = (fun i j => raw4584step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4584step2 raw4584step1; decide +kernel
      have hl : raw4584step2Labels = raw4584step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4584step1 raw4584step1Labels permutation29 permutation7
    mixedMoment B raw4584step2 raw4584step2Labels = mixedMoment B raw4584step3 raw4584step3Labels := by
      have ha : raw4584step3 = -raw4584step2 := by apply Matrix.ext; change ∀ i j, raw4584step3 i j = -(raw4584step2 i j); unfold raw4584step3 raw4584step2; decide +kernel
      have hl : raw4584step3Labels = raw4584step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4584step3 raw4584step3Labels = mixedMoment B raw4584step4 raw4584step4Labels := by
      have ha : raw4584step4 = raw4584step3 := by apply Matrix.ext; unfold raw4584step4 raw4584step3; decide +kernel
      have hl : raw4584step3Labels = labelEmbedding1 ∘ raw4584step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4584step3 raw4584step3Labels raw4584step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw4585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4585Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4585step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4585step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4585step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4585step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4585step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4585step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4585step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4585 raw4585Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw4585 raw4585Labels = mixedMoment B raw4585step0 raw4585step0Labels := by
      have hz : ∀ j, raw4585 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4585step0 = (fun i j => raw4585 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4585step0 raw4585; decide +kernel
      have hl : raw4585step0Labels = raw4585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4585 raw4585Labels permutation434 hz
    mixedMoment B raw4585step0 raw4585step0Labels = mixedMoment B raw4585step1 raw4585step1Labels := by
      have hz : ∀ j, raw4585step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4585step1 = (fun i j => raw4585step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4585step1 raw4585step0; decide +kernel
      have hl : raw4585step1Labels = raw4585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4585step0 raw4585step0Labels permutation56 hz
    mixedMoment B raw4585step1 raw4585step1Labels = mixedMoment B raw4585step2 raw4585step2Labels := by
      have ha : raw4585step2 = (fun i j => raw4585step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4585step2 raw4585step1; decide +kernel
      have hl : raw4585step2Labels = raw4585step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4585step1 raw4585step1Labels permutation29 permutation7
    mixedMoment B raw4585step2 raw4585step2Labels = mixedMoment B raw4585step3 raw4585step3Labels := by
      have ha : raw4585step3 = -raw4585step2 := by apply Matrix.ext; change ∀ i j, raw4585step3 i j = -(raw4585step2 i j); unfold raw4585step3 raw4585step2; decide +kernel
      have hl : raw4585step3Labels = raw4585step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4585step3 raw4585step3Labels = mixedMoment B raw4585step4 raw4585step4Labels := by
      have ha : raw4585step4 = raw4585step3 := by apply Matrix.ext; unfold raw4585step4 raw4585step3; decide +kernel
      have hl : raw4585step3Labels = labelEmbedding1 ∘ raw4585step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4585step3 raw4585step3Labels raw4585step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw4586 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4586Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4586step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4586step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw4586step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4586step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4586step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4586step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4586 raw4586Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw4586 raw4586Labels = mixedMoment B raw4586step0 raw4586step0Labels := by
      have hz : ∀ j, raw4586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4586step0 = (fun i j => raw4586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4586step0 raw4586; decide +kernel
      have hl : raw4586step0Labels = raw4586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4586 raw4586Labels permutation346 hz
    mixedMoment B raw4586step0 raw4586step0Labels = mixedMoment B raw4586step1 raw4586step1Labels := by
      have hz : ∀ j, raw4586step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4586step1 = (fun i j => raw4586step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4586step1 raw4586step0; decide +kernel
      have hl : raw4586step1Labels = raw4586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4586step0 raw4586step0Labels permutation56 hz
    mixedMoment B raw4586step1 raw4586step1Labels = mixedMoment B raw4586step2 raw4586step2Labels := by
      have ha : raw4586step2 = (fun i j => raw4586step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4586step2 raw4586step1; decide +kernel
      have hl : raw4586step2Labels = raw4586step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4586step1 raw4586step1Labels permutation29 permutation7
    mixedMoment B raw4586step2 raw4586step2Labels = mixedMoment B raw4586step3 raw4586step3Labels := by
      have ha : raw4586step3 = -raw4586step2 := by apply Matrix.ext; change ∀ i j, raw4586step3 i j = -(raw4586step2 i j); unfold raw4586step3 raw4586step2; decide +kernel
      have hl : raw4586step3Labels = raw4586step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4586step3 raw4586step3Labels = mixedMoment B raw4586step4 raw4586step4Labels := by
      have ha : raw4586step4 = raw4586step3 := by apply Matrix.ext; unfold raw4586step4 raw4586step3; decide +kernel
      have hl : raw4586step3Labels = labelEmbedding1 ∘ raw4586step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4586step3 raw4586step3Labels raw4586step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw4587 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4587Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4587step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4587step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4587step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4587step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4587step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4587 raw4587Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw4587 raw4587Labels = mixedMoment B raw4587step0 raw4587step0Labels := by
      have hz : ∀ j, raw4587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4587step0 = (fun i j => raw4587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4587step0 raw4587; decide +kernel
      have hl : raw4587step0Labels = raw4587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4587 raw4587Labels permutation346 hz
    mixedMoment B raw4587step0 raw4587step0Labels = mixedMoment B raw4587step1 raw4587step1Labels := by
      have ha : raw4587step1 = (fun i j => raw4587step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4587step1 raw4587step0; decide +kernel
      have hl : raw4587step1Labels = raw4587step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4587step0 raw4587step0Labels permutation137 permutation7
    mixedMoment B raw4587step1 raw4587step1Labels = mixedMoment B raw4587step2 raw4587step2Labels := by
      have ha : raw4587step2 = -raw4587step1 := by apply Matrix.ext; change ∀ i j, raw4587step2 i j = -(raw4587step1 i j); unfold raw4587step2 raw4587step1; decide +kernel
      have hl : raw4587step2Labels = raw4587step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4587step2 raw4587step2Labels = mixedMoment B raw4587step3 raw4587step3Labels := by
      have ha : raw4587step3 = raw4587step2 := by apply Matrix.ext; unfold raw4587step3 raw4587step2; decide +kernel
      have hl : raw4587step2Labels = labelEmbedding1 ∘ raw4587step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4587step2 raw4587step2Labels raw4587step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw4588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4588Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4588step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4588step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4588step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4588step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4588 raw4588Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw4588 raw4588Labels = mixedMoment B raw4588step0 raw4588step0Labels := by
      have hz : ∀ j, raw4588 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4588step0 = (fun i j => raw4588 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4588step0 raw4588; decide +kernel
      have hl : raw4588step0Labels = raw4588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4588 raw4588Labels permutation265 hz
    mixedMoment B raw4588step0 raw4588step0Labels = mixedMoment B raw4588step1 raw4588step1Labels := by
      have ha : raw4588step1 = (fun i j => raw4588step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4588step1 raw4588step0; decide +kernel
      have hl : raw4588step1Labels = raw4588step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4588step0 raw4588step0Labels permutation137 permutation7
    mixedMoment B raw4588step1 raw4588step1Labels = mixedMoment B raw4588step2 raw4588step2Labels := by
      have ha : raw4588step2 = -raw4588step1 := by apply Matrix.ext; change ∀ i j, raw4588step2 i j = -(raw4588step1 i j); unfold raw4588step2 raw4588step1; decide +kernel
      have hl : raw4588step2Labels = raw4588step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4588step2 raw4588step2Labels = mixedMoment B raw4588step3 raw4588step3Labels := by
      have ha : raw4588step3 = raw4588step2 := by apply Matrix.ext; unfold raw4588step3 raw4588step2; decide +kernel
      have hl : raw4588step2Labels = labelEmbedding1 ∘ raw4588step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4588step2 raw4588step2Labels raw4588step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw4589 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4589Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4589step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4589step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4589step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4589step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4589step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4589step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4589step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4589 raw4589Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw4589 raw4589Labels = mixedMoment B raw4589step0 raw4589step0Labels := by
      have hz : ∀ j, raw4589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4589step0 = (fun i j => raw4589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4589step0 raw4589; decide +kernel
      have hl : raw4589step0Labels = raw4589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4589 raw4589Labels permutation346 hz
    mixedMoment B raw4589step0 raw4589step0Labels = mixedMoment B raw4589step1 raw4589step1Labels := by
      have hz : ∀ j, raw4589step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4589step1 = (fun i j => raw4589step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4589step1 raw4589step0; decide +kernel
      have hl : raw4589step1Labels = raw4589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4589step0 raw4589step0Labels permutation56 hz
    mixedMoment B raw4589step1 raw4589step1Labels = mixedMoment B raw4589step2 raw4589step2Labels := by
      have ha : raw4589step2 = (fun i j => raw4589step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4589step2 raw4589step1; decide +kernel
      have hl : raw4589step2Labels = raw4589step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4589step1 raw4589step1Labels permutation29 permutation7
    mixedMoment B raw4589step2 raw4589step2Labels = mixedMoment B raw4589step3 raw4589step3Labels := by
      have ha : raw4589step3 = -raw4589step2 := by apply Matrix.ext; change ∀ i j, raw4589step3 i j = -(raw4589step2 i j); unfold raw4589step3 raw4589step2; decide +kernel
      have hl : raw4589step3Labels = raw4589step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4589step3 raw4589step3Labels = mixedMoment B raw4589step4 raw4589step4Labels := by
      have ha : raw4589step4 = raw4589step3 := by apply Matrix.ext; unfold raw4589step4 raw4589step3; decide +kernel
      have hl : raw4589step3Labels = labelEmbedding1 ∘ raw4589step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4589step3 raw4589step3Labels raw4589step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw4590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4590Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4590step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4590step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4590step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4590step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4590step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4590step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4590step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4590 raw4590Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw4590 raw4590Labels = mixedMoment B raw4590step0 raw4590step0Labels := by
      have hz : ∀ j, raw4590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4590step0 = (fun i j => raw4590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4590step0 raw4590; decide +kernel
      have hl : raw4590step0Labels = raw4590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4590 raw4590Labels permutation346 hz
    mixedMoment B raw4590step0 raw4590step0Labels = mixedMoment B raw4590step1 raw4590step1Labels := by
      have hz : ∀ j, raw4590step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4590step1 = (fun i j => raw4590step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4590step1 raw4590step0; decide +kernel
      have hl : raw4590step1Labels = raw4590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4590step0 raw4590step0Labels permutation56 hz
    mixedMoment B raw4590step1 raw4590step1Labels = mixedMoment B raw4590step2 raw4590step2Labels := by
      have ha : raw4590step2 = (fun i j => raw4590step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4590step2 raw4590step1; decide +kernel
      have hl : raw4590step2Labels = raw4590step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4590step1 raw4590step1Labels permutation29 permutation7
    mixedMoment B raw4590step2 raw4590step2Labels = mixedMoment B raw4590step3 raw4590step3Labels := by
      have ha : raw4590step3 = -raw4590step2 := by apply Matrix.ext; change ∀ i j, raw4590step3 i j = -(raw4590step2 i j); unfold raw4590step3 raw4590step2; decide +kernel
      have hl : raw4590step3Labels = raw4590step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4590step3 raw4590step3Labels = mixedMoment B raw4590step4 raw4590step4Labels := by
      have ha : raw4590step4 = raw4590step3 := by apply Matrix.ext; unfold raw4590step4 raw4590step3; decide +kernel
      have hl : raw4590step3Labels = labelEmbedding1 ∘ raw4590step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4590step3 raw4590step3Labels raw4590step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw4591 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4591step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4591step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4591step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-3, 0, 3]]
def raw4591step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4591step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw4591step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4591step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw4591step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4591 raw4591Labels = mixedMoment B node2285 node2285Labels := by
  calc
    mixedMoment B raw4591 raw4591Labels = mixedMoment B raw4591step0 raw4591step0Labels := by
      have hz : ∀ j, raw4591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4591step0 = (fun i j => raw4591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4591step0 raw4591; decide +kernel
      have hl : raw4591step0Labels = raw4591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4591 raw4591Labels permutation434 hz
    mixedMoment B raw4591step0 raw4591step0Labels = mixedMoment B raw4591step1 raw4591step1Labels := by
      have hz : ∀ j, raw4591step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4591step1 = (fun i j => raw4591step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4591step1 raw4591step0; decide +kernel
      have hl : raw4591step1Labels = raw4591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4591step0 raw4591step0Labels permutation80 hz
    mixedMoment B raw4591step1 raw4591step1Labels = mixedMoment B raw4591step2 raw4591step2Labels := by
      have hz : ∀ j, raw4591step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4591step2 = (fun i j => raw4591step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4591step2 raw4591step1; decide +kernel
      have hl : raw4591step2Labels = raw4591step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4591step1 raw4591step1Labels permutation14 hz
    mixedMoment B raw4591step2 raw4591step2Labels = mixedMoment B raw4591step3 raw4591step3Labels := by
      have ha : raw4591step3 = (fun i j => raw4591step2 (permutation5 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4591step3 raw4591step2; decide +kernel
      have hl : raw4591step3Labels = raw4591step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4591step2 raw4591step2Labels permutation5 permutation5
    mixedMoment B raw4591step3 raw4591step3Labels = mixedMoment B raw4591step4 raw4591step4Labels := by
      have ha : raw4591step4 = raw4591step3 := by apply Matrix.ext; unfold raw4591step4 raw4591step3; decide +kernel
      have hl : raw4591step3Labels = labelEmbedding1 ∘ raw4591step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4591step3 raw4591step3Labels raw4591step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2285 node2285Labels := by rfl

def raw4592 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4592step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw4592step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4592step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4592step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4592step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4592 raw4592Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw4592 raw4592Labels = mixedMoment B raw4592step0 raw4592step0Labels := by
      have hz : ∀ j, raw4592 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4592step0 = (fun i j => raw4592 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4592step0 raw4592; decide +kernel
      have hl : raw4592step0Labels = raw4592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4592 raw4592Labels permutation434 hz
    mixedMoment B raw4592step0 raw4592step0Labels = mixedMoment B raw4592step1 raw4592step1Labels := by
      have hz : ∀ j, raw4592step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4592step1 = (fun i j => raw4592step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4592step1 raw4592step0; decide +kernel
      have hl : raw4592step1Labels = raw4592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4592step0 raw4592step0Labels permutation80 hz
    mixedMoment B raw4592step1 raw4592step1Labels = mixedMoment B raw4592step2 raw4592step2Labels := by
      have ha : raw4592step2 = (fun i j => raw4592step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4592step2 raw4592step1; decide +kernel
      have hl : raw4592step2Labels = raw4592step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4592step1 raw4592step1Labels permutation29 permutation7
    mixedMoment B raw4592step2 raw4592step2Labels = mixedMoment B raw4592step3 raw4592step3Labels := by
      have ha : raw4592step3 = -raw4592step2 := by apply Matrix.ext; change ∀ i j, raw4592step3 i j = -(raw4592step2 i j); unfold raw4592step3 raw4592step2; decide +kernel
      have hl : raw4592step3Labels = raw4592step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4592step3 raw4592step3Labels = mixedMoment B raw4592step4 raw4592step4Labels := by
      have ha : raw4592step4 = raw4592step3 := by apply Matrix.ext; unfold raw4592step4 raw4592step3; decide +kernel
      have hl : raw4592step3Labels = labelEmbedding1 ∘ raw4592step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4592step3 raw4592step3Labels raw4592step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw4593 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4593step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw4593step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4593step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4593step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4593step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4593step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4593 raw4593Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw4593 raw4593Labels = mixedMoment B raw4593step0 raw4593step0Labels := by
      have hz : ∀ j, raw4593 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4593step0 = (fun i j => raw4593 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4593step0 raw4593; decide +kernel
      have hl : raw4593step0Labels = raw4593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4593 raw4593Labels permutation434 hz
    mixedMoment B raw4593step0 raw4593step0Labels = mixedMoment B raw4593step1 raw4593step1Labels := by
      have hz : ∀ j, raw4593step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4593step1 = (fun i j => raw4593step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4593step1 raw4593step0; decide +kernel
      have hl : raw4593step1Labels = raw4593step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4593step0 raw4593step0Labels permutation56 hz
    mixedMoment B raw4593step1 raw4593step1Labels = mixedMoment B raw4593step2 raw4593step2Labels := by
      have ha : raw4593step2 = (fun i j => raw4593step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4593step2 raw4593step1; decide +kernel
      have hl : raw4593step2Labels = raw4593step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4593step1 raw4593step1Labels permutation29 permutation7
    mixedMoment B raw4593step2 raw4593step2Labels = mixedMoment B raw4593step3 raw4593step3Labels := by
      have ha : raw4593step3 = -raw4593step2 := by apply Matrix.ext; change ∀ i j, raw4593step3 i j = -(raw4593step2 i j); unfold raw4593step3 raw4593step2; decide +kernel
      have hl : raw4593step3Labels = raw4593step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4593step3 raw4593step3Labels = mixedMoment B raw4593step4 raw4593step4Labels := by
      have ha : raw4593step4 = raw4593step3 := by apply Matrix.ext; unfold raw4593step4 raw4593step3; decide +kernel
      have hl : raw4593step3Labels = labelEmbedding1 ∘ raw4593step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4593step3 raw4593step3Labels raw4593step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw4594 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4594step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw4594step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4594step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4594step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4594step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4594step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4594 raw4594Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw4594 raw4594Labels = mixedMoment B raw4594step0 raw4594step0Labels := by
      have hz : ∀ j, raw4594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4594step0 = (fun i j => raw4594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4594step0 raw4594; decide +kernel
      have hl : raw4594step0Labels = raw4594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4594 raw4594Labels permutation346 hz
    mixedMoment B raw4594step0 raw4594step0Labels = mixedMoment B raw4594step1 raw4594step1Labels := by
      have hz : ∀ j, raw4594step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4594step1 = (fun i j => raw4594step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4594step1 raw4594step0; decide +kernel
      have hl : raw4594step1Labels = raw4594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4594step0 raw4594step0Labels permutation56 hz
    mixedMoment B raw4594step1 raw4594step1Labels = mixedMoment B raw4594step2 raw4594step2Labels := by
      have ha : raw4594step2 = (fun i j => raw4594step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4594step2 raw4594step1; decide +kernel
      have hl : raw4594step2Labels = raw4594step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4594step1 raw4594step1Labels permutation29 permutation7
    mixedMoment B raw4594step2 raw4594step2Labels = mixedMoment B raw4594step3 raw4594step3Labels := by
      have ha : raw4594step3 = -raw4594step2 := by apply Matrix.ext; change ∀ i j, raw4594step3 i j = -(raw4594step2 i j); unfold raw4594step3 raw4594step2; decide +kernel
      have hl : raw4594step3Labels = raw4594step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4594step3 raw4594step3Labels = mixedMoment B raw4594step4 raw4594step4Labels := by
      have ha : raw4594step4 = raw4594step3 := by apply Matrix.ext; unfold raw4594step4 raw4594step3; decide +kernel
      have hl : raw4594step3Labels = labelEmbedding1 ∘ raw4594step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4594step3 raw4594step3Labels raw4594step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw4595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4595step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4595step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-4, 1, 3]]
def raw4595step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4595step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw4595step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4595step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw4595step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4595step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw4595step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4595 raw4595Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw4595 raw4595Labels = mixedMoment B raw4595step0 raw4595step0Labels := by
      have hz : ∀ j, raw4595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4595step0 = (fun i j => raw4595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4595step0 raw4595; decide +kernel
      have hl : raw4595step0Labels = raw4595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4595 raw4595Labels permutation434 hz
    mixedMoment B raw4595step0 raw4595step0Labels = mixedMoment B raw4595step1 raw4595step1Labels := by
      have hz : ∀ j, raw4595step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4595step1 = (fun i j => raw4595step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4595step1 raw4595step0; decide +kernel
      have hl : raw4595step1Labels = raw4595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4595step0 raw4595step0Labels permutation80 hz
    mixedMoment B raw4595step1 raw4595step1Labels = mixedMoment B raw4595step2 raw4595step2Labels := by
      have hz : ∀ j, raw4595step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4595step2 = (fun i j => raw4595step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4595step2 raw4595step1; decide +kernel
      have hl : raw4595step2Labels = raw4595step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4595step1 raw4595step1Labels permutation14 hz
    mixedMoment B raw4595step2 raw4595step2Labels = mixedMoment B raw4595step3 raw4595step3Labels := by
      have ha : raw4595step3 = (fun i j => raw4595step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4595step3 raw4595step2; decide +kernel
      have hl : raw4595step3Labels = raw4595step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4595step2 raw4595step2Labels permutation7 permutation7
    mixedMoment B raw4595step3 raw4595step3Labels = mixedMoment B raw4595step4 raw4595step4Labels := by
      have ha : raw4595step4 = -raw4595step3 := by apply Matrix.ext; change ∀ i j, raw4595step4 i j = -(raw4595step3 i j); unfold raw4595step4 raw4595step3; decide +kernel
      have hl : raw4595step4Labels = raw4595step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4595step4 raw4595step4Labels = mixedMoment B raw4595step5 raw4595step5Labels := by
      have ha : raw4595step5 = raw4595step4 := by apply Matrix.ext; unfold raw4595step5 raw4595step4; decide +kernel
      have hl : raw4595step4Labels = labelEmbedding1 ∘ raw4595step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4595step4 raw4595step4Labels raw4595step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1747 node1747Labels := by rfl

def raw4596 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4596step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4596step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]
def raw4596step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4596step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-3, 3, 0]]
def raw4596step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4596step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw4596step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4596step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw4596step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4596 raw4596Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw4596 raw4596Labels = mixedMoment B raw4596step0 raw4596step0Labels := by
      have hz : ∀ j, raw4596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4596step0 = (fun i j => raw4596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4596step0 raw4596; decide +kernel
      have hl : raw4596step0Labels = raw4596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4596 raw4596Labels permutation434 hz
    mixedMoment B raw4596step0 raw4596step0Labels = mixedMoment B raw4596step1 raw4596step1Labels := by
      have hz : ∀ j, raw4596step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4596step1 = (fun i j => raw4596step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4596step1 raw4596step0; decide +kernel
      have hl : raw4596step1Labels = raw4596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4596step0 raw4596step0Labels permutation80 hz
    mixedMoment B raw4596step1 raw4596step1Labels = mixedMoment B raw4596step2 raw4596step2Labels := by
      have hz : ∀ j, raw4596step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4596step2 = (fun i j => raw4596step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4596step2 raw4596step1; decide +kernel
      have hl : raw4596step2Labels = raw4596step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4596step1 raw4596step1Labels permutation14 hz
    mixedMoment B raw4596step2 raw4596step2Labels = mixedMoment B raw4596step3 raw4596step3Labels := by
      have ha : raw4596step3 = (fun i j => raw4596step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4596step3 raw4596step2; decide +kernel
      have hl : raw4596step3Labels = raw4596step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4596step2 raw4596step2Labels permutation7 permutation7
    mixedMoment B raw4596step3 raw4596step3Labels = mixedMoment B raw4596step4 raw4596step4Labels := by
      have ha : raw4596step4 = -raw4596step3 := by apply Matrix.ext; change ∀ i j, raw4596step4 i j = -(raw4596step3 i j); unfold raw4596step4 raw4596step3; decide +kernel
      have hl : raw4596step4Labels = raw4596step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4596step4 raw4596step4Labels = mixedMoment B raw4596step5 raw4596step5Labels := by
      have ha : raw4596step5 = raw4596step4 := by apply Matrix.ext; unfold raw4596step5 raw4596step4; decide +kernel
      have hl : raw4596step4Labels = labelEmbedding1 ∘ raw4596step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4596step4 raw4596step4Labels raw4596step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw4597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4597step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4597step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw4597step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4597step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4597step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4597step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4597 raw4597Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4597 raw4597Labels = mixedMoment B raw4597step0 raw4597step0Labels := by
      have hz : ∀ j, raw4597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4597step0 = (fun i j => raw4597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4597step0 raw4597; decide +kernel
      have hl : raw4597step0Labels = raw4597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4597 raw4597Labels permutation434 hz
    mixedMoment B raw4597step0 raw4597step0Labels = mixedMoment B raw4597step1 raw4597step1Labels := by
      have hz : ∀ j, raw4597step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4597step1 = (fun i j => raw4597step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4597step1 raw4597step0; decide +kernel
      have hl : raw4597step1Labels = raw4597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4597step0 raw4597step0Labels permutation80 hz
    mixedMoment B raw4597step1 raw4597step1Labels = mixedMoment B raw4597step2 raw4597step2Labels := by
      have ha : raw4597step2 = (fun i j => raw4597step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4597step2 raw4597step1; decide +kernel
      have hl : raw4597step2Labels = raw4597step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4597step1 raw4597step1Labels permutation29 permutation7
    mixedMoment B raw4597step2 raw4597step2Labels = mixedMoment B raw4597step3 raw4597step3Labels := by
      have ha : raw4597step3 = -raw4597step2 := by apply Matrix.ext; change ∀ i j, raw4597step3 i j = -(raw4597step2 i j); unfold raw4597step3 raw4597step2; decide +kernel
      have hl : raw4597step3Labels = raw4597step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4597step3 raw4597step3Labels = mixedMoment B raw4597step4 raw4597step4Labels := by
      have ha : raw4597step4 = raw4597step3 := by apply Matrix.ext; unfold raw4597step4 raw4597step3; decide +kernel
      have hl : raw4597step3Labels = labelEmbedding1 ∘ raw4597step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4597step3 raw4597step3Labels raw4597step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw4598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4598step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4598step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw4598step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4598step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4598step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4598step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4598step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4598 raw4598Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4598 raw4598Labels = mixedMoment B raw4598step0 raw4598step0Labels := by
      have hz : ∀ j, raw4598 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4598step0 = (fun i j => raw4598 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4598step0 raw4598; decide +kernel
      have hl : raw4598step0Labels = raw4598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4598 raw4598Labels permutation434 hz
    mixedMoment B raw4598step0 raw4598step0Labels = mixedMoment B raw4598step1 raw4598step1Labels := by
      have hz : ∀ j, raw4598step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4598step1 = (fun i j => raw4598step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4598step1 raw4598step0; decide +kernel
      have hl : raw4598step1Labels = raw4598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4598step0 raw4598step0Labels permutation56 hz
    mixedMoment B raw4598step1 raw4598step1Labels = mixedMoment B raw4598step2 raw4598step2Labels := by
      have ha : raw4598step2 = (fun i j => raw4598step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4598step2 raw4598step1; decide +kernel
      have hl : raw4598step2Labels = raw4598step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4598step1 raw4598step1Labels permutation29 permutation7
    mixedMoment B raw4598step2 raw4598step2Labels = mixedMoment B raw4598step3 raw4598step3Labels := by
      have ha : raw4598step3 = -raw4598step2 := by apply Matrix.ext; change ∀ i j, raw4598step3 i j = -(raw4598step2 i j); unfold raw4598step3 raw4598step2; decide +kernel
      have hl : raw4598step3Labels = raw4598step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4598step3 raw4598step3Labels = mixedMoment B raw4598step4 raw4598step4Labels := by
      have ha : raw4598step4 = raw4598step3 := by apply Matrix.ext; unfold raw4598step4 raw4598step3; decide +kernel
      have hl : raw4598step3Labels = labelEmbedding1 ∘ raw4598step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4598step3 raw4598step3Labels raw4598step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw4599 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4599step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw4599step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4599step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4599step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4599step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4599step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4599 raw4599Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4599 raw4599Labels = mixedMoment B raw4599step0 raw4599step0Labels := by
      have hz : ∀ j, raw4599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4599step0 = (fun i j => raw4599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4599step0 raw4599; decide +kernel
      have hl : raw4599step0Labels = raw4599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4599 raw4599Labels permutation346 hz
    mixedMoment B raw4599step0 raw4599step0Labels = mixedMoment B raw4599step1 raw4599step1Labels := by
      have hz : ∀ j, raw4599step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4599step1 = (fun i j => raw4599step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4599step1 raw4599step0; decide +kernel
      have hl : raw4599step1Labels = raw4599step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4599step0 raw4599step0Labels permutation56 hz
    mixedMoment B raw4599step1 raw4599step1Labels = mixedMoment B raw4599step2 raw4599step2Labels := by
      have ha : raw4599step2 = (fun i j => raw4599step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4599step2 raw4599step1; decide +kernel
      have hl : raw4599step2Labels = raw4599step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4599step1 raw4599step1Labels permutation29 permutation7
    mixedMoment B raw4599step2 raw4599step2Labels = mixedMoment B raw4599step3 raw4599step3Labels := by
      have ha : raw4599step3 = -raw4599step2 := by apply Matrix.ext; change ∀ i j, raw4599step3 i j = -(raw4599step2 i j); unfold raw4599step3 raw4599step2; decide +kernel
      have hl : raw4599step3Labels = raw4599step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4599step3 raw4599step3Labels = mixedMoment B raw4599step4 raw4599step4Labels := by
      have ha : raw4599step4 = raw4599step3 := by apply Matrix.ext; unfold raw4599step4 raw4599step3; decide +kernel
      have hl : raw4599step3Labels = labelEmbedding1 ∘ raw4599step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4599step3 raw4599step3Labels raw4599step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw4600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4600step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4600step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4600step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4600step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw4600step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4600step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4600step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4600step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4600step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4600 raw4600Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw4600 raw4600Labels = mixedMoment B raw4600step0 raw4600step0Labels := by
      have hz : ∀ j, raw4600 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4600step0 = (fun i j => raw4600 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4600step0 raw4600; decide +kernel
      have hl : raw4600step0Labels = raw4600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4600 raw4600Labels permutation434 hz
    mixedMoment B raw4600step0 raw4600step0Labels = mixedMoment B raw4600step1 raw4600step1Labels := by
      have hz : ∀ j, raw4600step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4600step1 = (fun i j => raw4600step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4600step1 raw4600step0; decide +kernel
      have hl : raw4600step1Labels = raw4600step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4600step0 raw4600step0Labels permutation80 hz
    mixedMoment B raw4600step1 raw4600step1Labels = mixedMoment B raw4600step2 raw4600step2Labels := by
      have hz : ∀ j, raw4600step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4600step2 = (fun i j => raw4600step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4600step2 raw4600step1; decide +kernel
      have hl : raw4600step2Labels = raw4600step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4600step1 raw4600step1Labels permutation14 hz
    mixedMoment B raw4600step2 raw4600step2Labels = mixedMoment B raw4600step3 raw4600step3Labels := by
      have ha : raw4600step3 = (fun i j => raw4600step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4600step3 raw4600step2; decide +kernel
      have hl : raw4600step3Labels = raw4600step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4600step2 raw4600step2Labels permutation7 permutation7
    mixedMoment B raw4600step3 raw4600step3Labels = mixedMoment B raw4600step4 raw4600step4Labels := by
      have ha : raw4600step4 = -raw4600step3 := by apply Matrix.ext; change ∀ i j, raw4600step4 i j = -(raw4600step3 i j); unfold raw4600step4 raw4600step3; decide +kernel
      have hl : raw4600step4Labels = raw4600step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4600step4 raw4600step4Labels = mixedMoment B raw4600step5 raw4600step5Labels := by
      have ha : raw4600step5 = raw4600step4 := by apply Matrix.ext; unfold raw4600step5 raw4600step4; decide +kernel
      have hl : raw4600step4Labels = labelEmbedding1 ∘ raw4600step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4600step4 raw4600step4Labels raw4600step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw4601 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4601 raw4601Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw4601 raw4601Labels = mixedMoment B raw4601step0 raw4601step0Labels := by
      have hz : ∀ j, raw4601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4601step0 = (fun i j => raw4601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4601step0 raw4601; decide +kernel
      have hl : raw4601step0Labels = raw4601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4601 raw4601Labels permutation434 hz
    mixedMoment B raw4601step0 raw4601step0Labels = mixedMoment B raw4601step1 raw4601step1Labels := by
      have hz : ∀ j, raw4601step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4601step1 = (fun i j => raw4601step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4601step1 raw4601step0; decide +kernel
      have hl : raw4601step1Labels = raw4601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4601step0 raw4601step0Labels permutation56 hz
    mixedMoment B raw4601step1 raw4601step1Labels = mixedMoment B raw4601step2 raw4601step2Labels := by
      have ha : raw4601step2 = (fun i j => raw4601step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4601step2 raw4601step1; decide +kernel
      have hl : raw4601step2Labels = raw4601step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4601step1 raw4601step1Labels permutation29 permutation2
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw4602 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4602 raw4602Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw4602 raw4602Labels = mixedMoment B raw4602step0 raw4602step0Labels := by
      have hz : ∀ j, raw4602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4602step0 = (fun i j => raw4602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4602step0 raw4602; decide +kernel
      have hl : raw4602step0Labels = raw4602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4602 raw4602Labels permutation346 hz
    mixedMoment B raw4602step0 raw4602step0Labels = mixedMoment B raw4602step1 raw4602step1Labels := by
      have hz : ∀ j, raw4602step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4602step1 = (fun i j => raw4602step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4602step1 raw4602step0; decide +kernel
      have hl : raw4602step1Labels = raw4602step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4602step0 raw4602step0Labels permutation56 hz
    mixedMoment B raw4602step1 raw4602step1Labels = mixedMoment B raw4602step2 raw4602step2Labels := by
      have ha : raw4602step2 = (fun i j => raw4602step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4602step2 raw4602step1; decide +kernel
      have hl : raw4602step2Labels = raw4602step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4602step1 raw4602step1Labels permutation29 permutation2
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw4603 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4603step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4603step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-4, 1, 3]]
def raw4603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4603step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw4603step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4603 raw4603Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw4603 raw4603Labels = mixedMoment B raw4603step0 raw4603step0Labels := by
      have hz : ∀ j, raw4603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4603step0 = (fun i j => raw4603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4603step0 raw4603; decide +kernel
      have hl : raw4603step0Labels = raw4603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4603 raw4603Labels permutation434 hz
    mixedMoment B raw4603step0 raw4603step0Labels = mixedMoment B raw4603step1 raw4603step1Labels := by
      have hz : ∀ j, raw4603step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4603step1 = (fun i j => raw4603step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4603step1 raw4603step0; decide +kernel
      have hl : raw4603step1Labels = raw4603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4603step0 raw4603step0Labels permutation80 hz
    mixedMoment B raw4603step1 raw4603step1Labels = mixedMoment B raw4603step2 raw4603step2Labels := by
      have hz : ∀ j, raw4603step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4603step2 = (fun i j => raw4603step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4603step2 raw4603step1; decide +kernel
      have hl : raw4603step2Labels = raw4603step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4603step1 raw4603step1Labels permutation14 hz
    mixedMoment B raw4603step2 raw4603step2Labels = mixedMoment B raw4603step3 raw4603step3Labels := by
      have ha : raw4603step3 = (fun i j => raw4603step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4603step3 raw4603step2; decide +kernel
      have hl : raw4603step3Labels = raw4603step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4603step2 raw4603step2Labels permutation7 permutation2
    _ = mixedMoment B node1094 node1094Labels := by rfl

def raw4604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4604 raw4604Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw4604 raw4604Labels = mixedMoment B raw4604step0 raw4604step0Labels := by
      have hz : ∀ j, raw4604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4604step0 = (fun i j => raw4604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4604step0 raw4604; decide +kernel
      have hl : raw4604step0Labels = raw4604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4604 raw4604Labels permutation346 hz
    mixedMoment B raw4604step0 raw4604step0Labels = mixedMoment B raw4604step1 raw4604step1Labels := by
      have hz : ∀ j, raw4604step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4604step1 = (fun i j => raw4604step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4604step1 raw4604step0; decide +kernel
      have hl : raw4604step1Labels = raw4604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4604step0 raw4604step0Labels permutation56 hz
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw4605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4605 raw4605Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw4605 raw4605Labels = mixedMoment B raw4605step0 raw4605step0Labels := by
      have hz : ∀ j, raw4605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4605step0 = (fun i j => raw4605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4605step0 raw4605; decide +kernel
      have hl : raw4605step0Labels = raw4605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4605 raw4605Labels permutation346 hz
    mixedMoment B raw4605step0 raw4605step0Labels = mixedMoment B raw4605step1 raw4605step1Labels := by
      have ha : raw4605step1 = (fun i j => raw4605step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4605step1 raw4605step0; decide +kernel
      have hl : raw4605step1Labels = raw4605step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4605step0 raw4605step0Labels permutation40 permutation3
    mixedMoment B raw4605step1 raw4605step1Labels = mixedMoment B raw4605step2 raw4605step2Labels := by
      have ha : raw4605step2 = raw4605step1 := by apply Matrix.ext; unfold raw4605step2 raw4605step1; decide +kernel
      have hl : raw4605step1Labels = labelEmbedding6 ∘ raw4605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4605step1 raw4605step1Labels raw4605step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

def raw4606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4606step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4606step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4606step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4606 raw4606Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw4606 raw4606Labels = mixedMoment B raw4606step0 raw4606step0Labels := by
      have ha : raw4606step0 = (fun i j => raw4606 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4606step0 raw4606; decide +kernel
      have hl : raw4606step0Labels = raw4606Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4606 raw4606Labels permutation616 permutation3
    mixedMoment B raw4606step0 raw4606step0Labels = mixedMoment B raw4606step1 raw4606step1Labels := by
      have ha : raw4606step1 = -raw4606step0 := by apply Matrix.ext; change ∀ i j, raw4606step1 i j = -(raw4606step0 i j); unfold raw4606step1 raw4606step0; decide +kernel
      have hl : raw4606step1Labels = raw4606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4606step1 raw4606step1Labels = mixedMoment B raw4606step2 raw4606step2Labels := by
      have ha : raw4606step2 = raw4606step1 := by apply Matrix.ext; unfold raw4606step2 raw4606step1; decide +kernel
      have hl : raw4606step1Labels = labelEmbedding6 ∘ raw4606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4606step1 raw4606step1Labels raw4606step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

def raw4607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4607step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4607step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4607step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4607 raw4607Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw4607 raw4607Labels = mixedMoment B raw4607step0 raw4607step0Labels := by
      have hz : ∀ j, raw4607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4607step0 = (fun i j => raw4607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4607step0 raw4607; decide +kernel
      have hl : raw4607step0Labels = raw4607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4607 raw4607Labels permutation346 hz
    mixedMoment B raw4607step0 raw4607step0Labels = mixedMoment B raw4607step1 raw4607step1Labels := by
      have ha : raw4607step1 = (fun i j => raw4607step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4607step1 raw4607step0; decide +kernel
      have hl : raw4607step1Labels = raw4607step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4607step0 raw4607step0Labels permutation139 permutation3
    mixedMoment B raw4607step1 raw4607step1Labels = mixedMoment B raw4607step2 raw4607step2Labels := by
      have ha : raw4607step2 = -raw4607step1 := by apply Matrix.ext; change ∀ i j, raw4607step2 i j = -(raw4607step1 i j); unfold raw4607step2 raw4607step1; decide +kernel
      have hl : raw4607step2Labels = raw4607step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4607step2 raw4607step2Labels = mixedMoment B raw4607step3 raw4607step3Labels := by
      have ha : raw4607step3 = raw4607step2 := by apply Matrix.ext; unfold raw4607step3 raw4607step2; decide +kernel
      have hl : raw4607step2Labels = labelEmbedding6 ∘ raw4607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4607step2 raw4607step2Labels raw4607step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
