import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw21632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21632 raw21632Labels = mixedMoment B node698 node698Labels := by
  calc
    mixedMoment B raw21632 raw21632Labels = mixedMoment B raw21632step0 raw21632step0Labels := by
      have ha : raw21632step0 = (fun i j => raw21632 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21632step0 raw21632; decide +kernel
      have hl : raw21632step0Labels = raw21632Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21632 raw21632Labels permutation212 permutation4
    mixedMoment B raw21632step0 raw21632step0Labels = mixedMoment B raw21632step1 raw21632step1Labels := by
      have ha : raw21632step1 = -raw21632step0 := by apply Matrix.ext; change ∀ i j, raw21632step1 i j = -(raw21632step0 i j); unfold raw21632step1 raw21632step0; decide +kernel
      have hl : raw21632step1Labels = raw21632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node698 node698Labels := by rfl

def raw21633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw21633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw21633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21633 raw21633Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw21633 raw21633Labels = mixedMoment B raw21633step0 raw21633step0Labels := by
      have hz : ∀ j, raw21633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21633step0 = (fun i j => raw21633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21633step0 raw21633; decide +kernel
      have hl : raw21633step0Labels = raw21633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21633 raw21633Labels permutation346 hz
    mixedMoment B raw21633step0 raw21633step0Labels = mixedMoment B raw21633step1 raw21633step1Labels := by
      have ha : raw21633step1 = (fun i j => raw21633step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21633step1 raw21633step0; decide +kernel
      have hl : raw21633step1Labels = raw21633step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21633step0 raw21633step0Labels permutation40 permutation4
    mixedMoment B raw21633step1 raw21633step1Labels = mixedMoment B raw21633step2 raw21633step2Labels := by
      have ha : raw21633step2 = -raw21633step1 := by apply Matrix.ext; change ∀ i j, raw21633step2 i j = -(raw21633step1 i j); unfold raw21633step2 raw21633step1; decide +kernel
      have hl : raw21633step2Labels = raw21633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node701 node701Labels := by rfl

def raw21634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21634step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21634step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw21634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21634 raw21634Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw21634 raw21634Labels = mixedMoment B raw21634step0 raw21634step0Labels := by
      have hz : ∀ j, raw21634 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21634step0 = (fun i j => raw21634 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21634step0 raw21634; decide +kernel
      have hl : raw21634step0Labels = raw21634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21634 raw21634Labels permutation434 hz
    mixedMoment B raw21634step0 raw21634step0Labels = mixedMoment B raw21634step1 raw21634step1Labels := by
      have hz : ∀ j, raw21634step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21634step1 = (fun i j => raw21634step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21634step1 raw21634step0; decide +kernel
      have hl : raw21634step1Labels = raw21634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21634step0 raw21634step0Labels permutation80 hz
    mixedMoment B raw21634step1 raw21634step1Labels = mixedMoment B raw21634step2 raw21634step2Labels := by
      have hz : ∀ j, raw21634step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21634step2 = (fun i j => raw21634step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21634step2 raw21634step1; decide +kernel
      have hl : raw21634step2Labels = raw21634step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21634step1 raw21634step1Labels permutation14 hz
    _ = mixedMoment B node4901 node4901Labels := by rfl

def raw21635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21635 raw21635Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw21635 raw21635Labels = mixedMoment B raw21635step0 raw21635step0Labels := by
      have hz : ∀ j, raw21635 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21635step0 = (fun i j => raw21635 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21635step0 raw21635; decide +kernel
      have hl : raw21635step0Labels = raw21635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21635 raw21635Labels permutation434 hz
    mixedMoment B raw21635step0 raw21635step0Labels = mixedMoment B raw21635step1 raw21635step1Labels := by
      have hz : ∀ j, raw21635step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21635step1 = (fun i j => raw21635step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21635step1 raw21635step0; decide +kernel
      have hl : raw21635step1Labels = raw21635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21635step0 raw21635step0Labels permutation80 hz
    _ = mixedMoment B node4178 node4178Labels := by rfl

def raw21636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21636 raw21636Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw21636 raw21636Labels = mixedMoment B raw21636step0 raw21636step0Labels := by
      have hz : ∀ j, raw21636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21636step0 = (fun i j => raw21636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21636step0 raw21636; decide +kernel
      have hl : raw21636step0Labels = raw21636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21636 raw21636Labels permutation434 hz
    mixedMoment B raw21636step0 raw21636step0Labels = mixedMoment B raw21636step1 raw21636step1Labels := by
      have ha : raw21636step1 = (fun i j => raw21636step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21636step1 raw21636step0; decide +kernel
      have hl : raw21636step1Labels = raw21636step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21636step0 raw21636step0Labels permutation38 permutation2
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw21637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21637step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21637 raw21637Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw21637 raw21637Labels = mixedMoment B raw21637step0 raw21637step0Labels := by
      have hz : ∀ j, raw21637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21637step0 = (fun i j => raw21637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21637step0 raw21637; decide +kernel
      have hl : raw21637step0Labels = raw21637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21637 raw21637Labels permutation346 hz
    mixedMoment B raw21637step0 raw21637step0Labels = mixedMoment B raw21637step1 raw21637step1Labels := by
      have ha : raw21637step1 = (fun i j => raw21637step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21637step1 raw21637step0; decide +kernel
      have hl : raw21637step1Labels = raw21637step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21637step0 raw21637step0Labels permutation38 permutation2
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw21638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21638 raw21638Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw21638 raw21638Labels = mixedMoment B raw21638step0 raw21638step0Labels := by
      have hz : ∀ j, raw21638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21638step0 = (fun i j => raw21638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21638step0 raw21638; decide +kernel
      have hl : raw21638step0Labels = raw21638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21638 raw21638Labels permutation434 hz
    mixedMoment B raw21638step0 raw21638step0Labels = mixedMoment B raw21638step1 raw21638step1Labels := by
      have hz : ∀ j, raw21638step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21638step1 = (fun i j => raw21638step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21638step1 raw21638step0; decide +kernel
      have hl : raw21638step1Labels = raw21638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21638step0 raw21638step0Labels permutation80 hz
    mixedMoment B raw21638step1 raw21638step1Labels = mixedMoment B raw21638step2 raw21638step2Labels := by
      have ha : raw21638step2 = (fun i j => raw21638step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21638step2 raw21638step1; decide +kernel
      have hl : raw21638step2Labels = raw21638step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21638step1 raw21638step1Labels permutation10 permutation2
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw21639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21639 raw21639Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw21639 raw21639Labels = mixedMoment B raw21639step0 raw21639step0Labels := by
      have hz : ∀ j, raw21639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21639step0 = (fun i j => raw21639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21639step0 raw21639; decide +kernel
      have hl : raw21639step0Labels = raw21639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21639 raw21639Labels permutation434 hz
    mixedMoment B raw21639step0 raw21639step0Labels = mixedMoment B raw21639step1 raw21639step1Labels := by
      have hz : ∀ j, raw21639step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21639step1 = (fun i j => raw21639step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21639step1 raw21639step0; decide +kernel
      have hl : raw21639step1Labels = raw21639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21639step0 raw21639step0Labels permutation56 hz
    _ = mixedMoment B node4178 node4178Labels := by rfl

def raw21640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21640 raw21640Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw21640 raw21640Labels = mixedMoment B raw21640step0 raw21640step0Labels := by
      have hz : ∀ j, raw21640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21640step0 = (fun i j => raw21640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21640step0 raw21640; decide +kernel
      have hl : raw21640step0Labels = raw21640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21640 raw21640Labels permutation434 hz
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw21641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21641 raw21641Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw21641 raw21641Labels = mixedMoment B raw21641step0 raw21641step0Labels := by
      have hz : ∀ j, raw21641 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21641step0 = (fun i j => raw21641 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21641step0 raw21641; decide +kernel
      have hl : raw21641step0Labels = raw21641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21641 raw21641Labels permutation265 hz
    mixedMoment B raw21641step0 raw21641step0Labels = mixedMoment B raw21641step1 raw21641step1Labels := by
      have ha : raw21641step1 = (fun i j => raw21641step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21641step1 raw21641step0; decide +kernel
      have hl : raw21641step1Labels = raw21641step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21641step0 raw21641step0Labels permutation38 permutation2
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw21642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21642step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21642 raw21642Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw21642 raw21642Labels = mixedMoment B raw21642step0 raw21642step0Labels := by
      have hz : ∀ j, raw21642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21642step0 = (fun i j => raw21642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21642step0 raw21642; decide +kernel
      have hl : raw21642step0Labels = raw21642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21642 raw21642Labels permutation434 hz
    mixedMoment B raw21642step0 raw21642step0Labels = mixedMoment B raw21642step1 raw21642step1Labels := by
      have hz : ∀ j, raw21642step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21642step1 = (fun i j => raw21642step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21642step1 raw21642step0; decide +kernel
      have hl : raw21642step1Labels = raw21642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21642step0 raw21642step0Labels permutation56 hz
    mixedMoment B raw21642step1 raw21642step1Labels = mixedMoment B raw21642step2 raw21642step2Labels := by
      have ha : raw21642step2 = (fun i j => raw21642step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21642step2 raw21642step1; decide +kernel
      have hl : raw21642step2Labels = raw21642step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21642step1 raw21642step1Labels permutation10 permutation2
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw21643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21643step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21643 raw21643Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw21643 raw21643Labels = mixedMoment B raw21643step0 raw21643step0Labels := by
      have hz : ∀ j, raw21643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21643step0 = (fun i j => raw21643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21643step0 raw21643; decide +kernel
      have hl : raw21643step0Labels = raw21643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21643 raw21643Labels permutation346 hz
    mixedMoment B raw21643step0 raw21643step0Labels = mixedMoment B raw21643step1 raw21643step1Labels := by
      have hz : ∀ j, raw21643step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21643step1 = (fun i j => raw21643step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21643step1 raw21643step0; decide +kernel
      have hl : raw21643step1Labels = raw21643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21643step0 raw21643step0Labels permutation56 hz
    _ = mixedMoment B node4178 node4178Labels := by rfl

def raw21644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21644 raw21644Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw21644 raw21644Labels = mixedMoment B raw21644step0 raw21644step0Labels := by
      have hz : ∀ j, raw21644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21644step0 = (fun i j => raw21644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21644step0 raw21644; decide +kernel
      have hl : raw21644step0Labels = raw21644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21644 raw21644Labels permutation346 hz
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw21645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21645 raw21645Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw21645 raw21645Labels = mixedMoment B raw21645step0 raw21645step0Labels := by
      have hz : ∀ j, raw21645 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21645step0 = (fun i j => raw21645 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21645step0 raw21645; decide +kernel
      have hl : raw21645step0Labels = raw21645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21645 raw21645Labels permutation265 hz
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw21646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21646 raw21646Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw21646 raw21646Labels = mixedMoment B raw21646step0 raw21646step0Labels := by
      have hz : ∀ j, raw21646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21646step0 = (fun i j => raw21646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21646step0 raw21646; decide +kernel
      have hl : raw21646step0Labels = raw21646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21646 raw21646Labels permutation346 hz
    mixedMoment B raw21646step0 raw21646step0Labels = mixedMoment B raw21646step1 raw21646step1Labels := by
      have hz : ∀ j, raw21646step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21646step1 = (fun i j => raw21646step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21646step1 raw21646step0; decide +kernel
      have hl : raw21646step1Labels = raw21646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21646step0 raw21646step0Labels permutation56 hz
    mixedMoment B raw21646step1 raw21646step1Labels = mixedMoment B raw21646step2 raw21646step2Labels := by
      have ha : raw21646step2 = (fun i j => raw21646step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21646step2 raw21646step1; decide +kernel
      have hl : raw21646step2Labels = raw21646step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21646step1 raw21646step1Labels permutation10 permutation2
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw21647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21647step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw21647step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21647 raw21647Labels = mixedMoment B node4192 node4192Labels := by
  calc
    mixedMoment B raw21647 raw21647Labels = mixedMoment B raw21647step0 raw21647step0Labels := by
      have hz : ∀ j, raw21647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21647step0 = (fun i j => raw21647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21647step0 raw21647; decide +kernel
      have hl : raw21647step0Labels = raw21647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21647 raw21647Labels permutation434 hz
    mixedMoment B raw21647step0 raw21647step0Labels = mixedMoment B raw21647step1 raw21647step1Labels := by
      have hz : ∀ j, raw21647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21647step1 = (fun i j => raw21647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21647step1 raw21647step0; decide +kernel
      have hl : raw21647step1Labels = raw21647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21647step0 raw21647step0Labels permutation80 hz
    mixedMoment B raw21647step1 raw21647step1Labels = mixedMoment B raw21647step2 raw21647step2Labels := by
      have hz : ∀ j, raw21647step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21647step2 = (fun i j => raw21647step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21647step2 raw21647step1; decide +kernel
      have hl : raw21647step2Labels = raw21647step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21647step1 raw21647step1Labels permutation14 hz
    _ = mixedMoment B node4192 node4192Labels := by rfl

def raw21648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21648 raw21648Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw21648 raw21648Labels = mixedMoment B raw21648step0 raw21648step0Labels := by
      have hz : ∀ j, raw21648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21648step0 = (fun i j => raw21648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21648step0 raw21648; decide +kernel
      have hl : raw21648step0Labels = raw21648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21648 raw21648Labels permutation434 hz
    mixedMoment B raw21648step0 raw21648step0Labels = mixedMoment B raw21648step1 raw21648step1Labels := by
      have hz : ∀ j, raw21648step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21648step1 = (fun i j => raw21648step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21648step1 raw21648step0; decide +kernel
      have hl : raw21648step1Labels = raw21648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21648step0 raw21648step0Labels permutation80 hz
    _ = mixedMoment B node4361 node4361Labels := by rfl

def raw21649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21649 raw21649Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw21649 raw21649Labels = mixedMoment B raw21649step0 raw21649step0Labels := by
      have hz : ∀ j, raw21649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21649step0 = (fun i j => raw21649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21649step0 raw21649; decide +kernel
      have hl : raw21649step0Labels = raw21649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21649 raw21649Labels permutation434 hz
    mixedMoment B raw21649step0 raw21649step0Labels = mixedMoment B raw21649step1 raw21649step1Labels := by
      have hz : ∀ j, raw21649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21649step1 = (fun i j => raw21649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21649step1 raw21649step0; decide +kernel
      have hl : raw21649step1Labels = raw21649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21649step0 raw21649step0Labels permutation56 hz
    _ = mixedMoment B node4361 node4361Labels := by rfl

def raw21650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21650 raw21650Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw21650 raw21650Labels = mixedMoment B raw21650step0 raw21650step0Labels := by
      have hz : ∀ j, raw21650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21650step0 = (fun i j => raw21650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21650step0 raw21650; decide +kernel
      have hl : raw21650step0Labels = raw21650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21650 raw21650Labels permutation346 hz
    mixedMoment B raw21650step0 raw21650step0Labels = mixedMoment B raw21650step1 raw21650step1Labels := by
      have hz : ∀ j, raw21650step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21650step1 = (fun i j => raw21650step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21650step1 raw21650step0; decide +kernel
      have hl : raw21650step1Labels = raw21650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21650step0 raw21650step0Labels permutation56 hz
    _ = mixedMoment B node4361 node4361Labels := by rfl

def raw21651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21651step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw21651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21651 raw21651Labels = mixedMoment B node4189 node4189Labels := by
  calc
    mixedMoment B raw21651 raw21651Labels = mixedMoment B raw21651step0 raw21651step0Labels := by
      have hz : ∀ j, raw21651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21651step0 = (fun i j => raw21651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21651step0 raw21651; decide +kernel
      have hl : raw21651step0Labels = raw21651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21651 raw21651Labels permutation434 hz
    mixedMoment B raw21651step0 raw21651step0Labels = mixedMoment B raw21651step1 raw21651step1Labels := by
      have hz : ∀ j, raw21651step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21651step1 = (fun i j => raw21651step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21651step1 raw21651step0; decide +kernel
      have hl : raw21651step1Labels = raw21651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21651step0 raw21651step0Labels permutation80 hz
    mixedMoment B raw21651step1 raw21651step1Labels = mixedMoment B raw21651step2 raw21651step2Labels := by
      have hz : ∀ j, raw21651step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21651step2 = (fun i j => raw21651step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21651step2 raw21651step1; decide +kernel
      have hl : raw21651step2Labels = raw21651step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21651step1 raw21651step1Labels permutation14 hz
    _ = mixedMoment B node4189 node4189Labels := by rfl

def raw21652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21652 raw21652Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw21652 raw21652Labels = mixedMoment B raw21652step0 raw21652step0Labels := by
      have hz : ∀ j, raw21652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21652step0 = (fun i j => raw21652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21652step0 raw21652; decide +kernel
      have hl : raw21652step0Labels = raw21652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21652 raw21652Labels permutation434 hz
    mixedMoment B raw21652step0 raw21652step0Labels = mixedMoment B raw21652step1 raw21652step1Labels := by
      have hz : ∀ j, raw21652step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21652step1 = (fun i j => raw21652step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21652step1 raw21652step0; decide +kernel
      have hl : raw21652step1Labels = raw21652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21652step0 raw21652step0Labels permutation80 hz
    _ = mixedMoment B node4358 node4358Labels := by rfl

def raw21653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21653 raw21653Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw21653 raw21653Labels = mixedMoment B raw21653step0 raw21653step0Labels := by
      have hz : ∀ j, raw21653 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21653step0 = (fun i j => raw21653 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21653step0 raw21653; decide +kernel
      have hl : raw21653step0Labels = raw21653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21653 raw21653Labels permutation434 hz
    mixedMoment B raw21653step0 raw21653step0Labels = mixedMoment B raw21653step1 raw21653step1Labels := by
      have hz : ∀ j, raw21653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21653step1 = (fun i j => raw21653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21653step1 raw21653step0; decide +kernel
      have hl : raw21653step1Labels = raw21653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21653step0 raw21653step0Labels permutation56 hz
    _ = mixedMoment B node4358 node4358Labels := by rfl

def raw21654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21654 raw21654Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw21654 raw21654Labels = mixedMoment B raw21654step0 raw21654step0Labels := by
      have hz : ∀ j, raw21654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21654step0 = (fun i j => raw21654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21654step0 raw21654; decide +kernel
      have hl : raw21654step0Labels = raw21654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21654 raw21654Labels permutation346 hz
    mixedMoment B raw21654step0 raw21654step0Labels = mixedMoment B raw21654step1 raw21654step1Labels := by
      have hz : ∀ j, raw21654step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21654step1 = (fun i j => raw21654step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21654step1 raw21654step0; decide +kernel
      have hl : raw21654step1Labels = raw21654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21654step0 raw21654step0Labels permutation56 hz
    _ = mixedMoment B node4358 node4358Labels := by rfl

def raw21655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21655step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw21655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21655 raw21655Labels = mixedMoment B node4481 node4481Labels := by
  calc
    mixedMoment B raw21655 raw21655Labels = mixedMoment B raw21655step0 raw21655step0Labels := by
      have hz : ∀ j, raw21655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21655step0 = (fun i j => raw21655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21655step0 raw21655; decide +kernel
      have hl : raw21655step0Labels = raw21655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21655 raw21655Labels permutation434 hz
    mixedMoment B raw21655step0 raw21655step0Labels = mixedMoment B raw21655step1 raw21655step1Labels := by
      have hz : ∀ j, raw21655step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21655step1 = (fun i j => raw21655step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21655step1 raw21655step0; decide +kernel
      have hl : raw21655step1Labels = raw21655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21655step0 raw21655step0Labels permutation80 hz
    mixedMoment B raw21655step1 raw21655step1Labels = mixedMoment B raw21655step2 raw21655step2Labels := by
      have hz : ∀ j, raw21655step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21655step2 = (fun i j => raw21655step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21655step2 raw21655step1; decide +kernel
      have hl : raw21655step2Labels = raw21655step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21655step1 raw21655step1Labels permutation14 hz
    _ = mixedMoment B node4481 node4481Labels := by rfl

def raw21656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21656step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21656step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21656step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21656step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21656step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21656step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21656 raw21656Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw21656 raw21656Labels = mixedMoment B raw21656step0 raw21656step0Labels := by
      have hz : ∀ j, raw21656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21656step0 = (fun i j => raw21656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21656step0 raw21656; decide +kernel
      have hl : raw21656step0Labels = raw21656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21656 raw21656Labels permutation434 hz
    mixedMoment B raw21656step0 raw21656step0Labels = mixedMoment B raw21656step1 raw21656step1Labels := by
      have hz : ∀ j, raw21656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21656step1 = (fun i j => raw21656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21656step1 raw21656step0; decide +kernel
      have hl : raw21656step1Labels = raw21656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21656step0 raw21656step0Labels permutation80 hz
    mixedMoment B raw21656step1 raw21656step1Labels = mixedMoment B raw21656step2 raw21656step2Labels := by
      have ha : raw21656step2 = (fun i j => raw21656step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21656step2 raw21656step1; decide +kernel
      have hl : raw21656step2Labels = raw21656step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21656step1 raw21656step1Labels permutation9 permutation7
    mixedMoment B raw21656step2 raw21656step2Labels = mixedMoment B raw21656step3 raw21656step3Labels := by
      have ha : raw21656step3 = -raw21656step2 := by apply Matrix.ext; change ∀ i j, raw21656step3 i j = -(raw21656step2 i j); unfold raw21656step3 raw21656step2; decide +kernel
      have hl : raw21656step3Labels = raw21656step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21656step3 raw21656step3Labels = mixedMoment B raw21656step4 raw21656step4Labels := by
      have ha : raw21656step4 = raw21656step3 := by apply Matrix.ext; unfold raw21656step4 raw21656step3; decide +kernel
      have hl : raw21656step3Labels = labelEmbedding1 ∘ raw21656step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21656step3 raw21656step3Labels raw21656step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw21657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21657Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21657step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21657step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21657step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21657step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21657step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21657step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21657 raw21657Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw21657 raw21657Labels = mixedMoment B raw21657step0 raw21657step0Labels := by
      have hz : ∀ j, raw21657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21657step0 = (fun i j => raw21657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21657step0 raw21657; decide +kernel
      have hl : raw21657step0Labels = raw21657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21657 raw21657Labels permutation434 hz
    mixedMoment B raw21657step0 raw21657step0Labels = mixedMoment B raw21657step1 raw21657step1Labels := by
      have hz : ∀ j, raw21657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21657step1 = (fun i j => raw21657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21657step1 raw21657step0; decide +kernel
      have hl : raw21657step1Labels = raw21657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21657step0 raw21657step0Labels permutation56 hz
    mixedMoment B raw21657step1 raw21657step1Labels = mixedMoment B raw21657step2 raw21657step2Labels := by
      have ha : raw21657step2 = (fun i j => raw21657step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21657step2 raw21657step1; decide +kernel
      have hl : raw21657step2Labels = raw21657step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21657step1 raw21657step1Labels permutation9 permutation7
    mixedMoment B raw21657step2 raw21657step2Labels = mixedMoment B raw21657step3 raw21657step3Labels := by
      have ha : raw21657step3 = -raw21657step2 := by apply Matrix.ext; change ∀ i j, raw21657step3 i j = -(raw21657step2 i j); unfold raw21657step3 raw21657step2; decide +kernel
      have hl : raw21657step3Labels = raw21657step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21657step3 raw21657step3Labels = mixedMoment B raw21657step4 raw21657step4Labels := by
      have ha : raw21657step4 = raw21657step3 := by apply Matrix.ext; unfold raw21657step4 raw21657step3; decide +kernel
      have hl : raw21657step3Labels = labelEmbedding1 ∘ raw21657step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21657step3 raw21657step3Labels raw21657step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw21658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21658step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21658step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21658step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21658step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21658step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21658step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21658 raw21658Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw21658 raw21658Labels = mixedMoment B raw21658step0 raw21658step0Labels := by
      have hz : ∀ j, raw21658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21658step0 = (fun i j => raw21658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21658step0 raw21658; decide +kernel
      have hl : raw21658step0Labels = raw21658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21658 raw21658Labels permutation346 hz
    mixedMoment B raw21658step0 raw21658step0Labels = mixedMoment B raw21658step1 raw21658step1Labels := by
      have hz : ∀ j, raw21658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21658step1 = (fun i j => raw21658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21658step1 raw21658step0; decide +kernel
      have hl : raw21658step1Labels = raw21658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21658step0 raw21658step0Labels permutation56 hz
    mixedMoment B raw21658step1 raw21658step1Labels = mixedMoment B raw21658step2 raw21658step2Labels := by
      have ha : raw21658step2 = (fun i j => raw21658step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21658step2 raw21658step1; decide +kernel
      have hl : raw21658step2Labels = raw21658step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21658step1 raw21658step1Labels permutation9 permutation7
    mixedMoment B raw21658step2 raw21658step2Labels = mixedMoment B raw21658step3 raw21658step3Labels := by
      have ha : raw21658step3 = -raw21658step2 := by apply Matrix.ext; change ∀ i j, raw21658step3 i j = -(raw21658step2 i j); unfold raw21658step3 raw21658step2; decide +kernel
      have hl : raw21658step3Labels = raw21658step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21658step3 raw21658step3Labels = mixedMoment B raw21658step4 raw21658step4Labels := by
      have ha : raw21658step4 = raw21658step3 := by apply Matrix.ext; unfold raw21658step4 raw21658step3; decide +kernel
      have hl : raw21658step3Labels = labelEmbedding1 ∘ raw21658step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21658step3 raw21658step3Labels raw21658step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw21659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21659Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21659step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21659step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21659step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw21659step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21659step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw21659step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21659step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw21659step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21659step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw21659step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21659 raw21659Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw21659 raw21659Labels = mixedMoment B raw21659step0 raw21659step0Labels := by
      have hz : ∀ j, raw21659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21659step0 = (fun i j => raw21659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21659step0 raw21659; decide +kernel
      have hl : raw21659step0Labels = raw21659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21659 raw21659Labels permutation434 hz
    mixedMoment B raw21659step0 raw21659step0Labels = mixedMoment B raw21659step1 raw21659step1Labels := by
      have hz : ∀ j, raw21659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21659step1 = (fun i j => raw21659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21659step1 raw21659step0; decide +kernel
      have hl : raw21659step1Labels = raw21659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21659step0 raw21659step0Labels permutation80 hz
    mixedMoment B raw21659step1 raw21659step1Labels = mixedMoment B raw21659step2 raw21659step2Labels := by
      have hz : ∀ j, raw21659step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21659step2 = (fun i j => raw21659step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21659step2 raw21659step1; decide +kernel
      have hl : raw21659step2Labels = raw21659step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21659step1 raw21659step1Labels permutation14 hz
    mixedMoment B raw21659step2 raw21659step2Labels = mixedMoment B raw21659step3 raw21659step3Labels := by
      have ha : raw21659step3 = (fun i j => raw21659step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21659step3 raw21659step2; decide +kernel
      have hl : raw21659step3Labels = raw21659step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21659step2 raw21659step2Labels permutation3 permutation7
    mixedMoment B raw21659step3 raw21659step3Labels = mixedMoment B raw21659step4 raw21659step4Labels := by
      have ha : raw21659step4 = -raw21659step3 := by apply Matrix.ext; change ∀ i j, raw21659step4 i j = -(raw21659step3 i j); unfold raw21659step4 raw21659step3; decide +kernel
      have hl : raw21659step4Labels = raw21659step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21659step4 raw21659step4Labels = mixedMoment B raw21659step5 raw21659step5Labels := by
      have ha : raw21659step5 = raw21659step4 := by apply Matrix.ext; unfold raw21659step5 raw21659step4; decide +kernel
      have hl : raw21659step4Labels = labelEmbedding1 ∘ raw21659step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21659step4 raw21659step4Labels raw21659step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw21660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21660Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21660step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21660step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21660step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw21660step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21660step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw21660step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21660step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw21660step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21660step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw21660step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21660 raw21660Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw21660 raw21660Labels = mixedMoment B raw21660step0 raw21660step0Labels := by
      have hz : ∀ j, raw21660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21660step0 = (fun i j => raw21660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21660step0 raw21660; decide +kernel
      have hl : raw21660step0Labels = raw21660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660 raw21660Labels permutation434 hz
    mixedMoment B raw21660step0 raw21660step0Labels = mixedMoment B raw21660step1 raw21660step1Labels := by
      have hz : ∀ j, raw21660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21660step1 = (fun i j => raw21660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21660step1 raw21660step0; decide +kernel
      have hl : raw21660step1Labels = raw21660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660step0 raw21660step0Labels permutation80 hz
    mixedMoment B raw21660step1 raw21660step1Labels = mixedMoment B raw21660step2 raw21660step2Labels := by
      have hz : ∀ j, raw21660step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21660step2 = (fun i j => raw21660step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21660step2 raw21660step1; decide +kernel
      have hl : raw21660step2Labels = raw21660step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21660step1 raw21660step1Labels permutation14 hz
    mixedMoment B raw21660step2 raw21660step2Labels = mixedMoment B raw21660step3 raw21660step3Labels := by
      have ha : raw21660step3 = (fun i j => raw21660step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21660step3 raw21660step2; decide +kernel
      have hl : raw21660step3Labels = raw21660step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21660step2 raw21660step2Labels permutation3 permutation7
    mixedMoment B raw21660step3 raw21660step3Labels = mixedMoment B raw21660step4 raw21660step4Labels := by
      have ha : raw21660step4 = -raw21660step3 := by apply Matrix.ext; change ∀ i j, raw21660step4 i j = -(raw21660step3 i j); unfold raw21660step4 raw21660step3; decide +kernel
      have hl : raw21660step4Labels = raw21660step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21660step4 raw21660step4Labels = mixedMoment B raw21660step5 raw21660step5Labels := by
      have ha : raw21660step5 = raw21660step4 := by apply Matrix.ext; unfold raw21660step5 raw21660step4; decide +kernel
      have hl : raw21660step4Labels = labelEmbedding1 ∘ raw21660step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21660step4 raw21660step4Labels raw21660step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw21661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21661Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21661step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21661step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21661step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21661step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21661step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21661step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21661 raw21661Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw21661 raw21661Labels = mixedMoment B raw21661step0 raw21661step0Labels := by
      have hz : ∀ j, raw21661 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21661step0 = (fun i j => raw21661 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21661step0 raw21661; decide +kernel
      have hl : raw21661step0Labels = raw21661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21661 raw21661Labels permutation434 hz
    mixedMoment B raw21661step0 raw21661step0Labels = mixedMoment B raw21661step1 raw21661step1Labels := by
      have hz : ∀ j, raw21661step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21661step1 = (fun i j => raw21661step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21661step1 raw21661step0; decide +kernel
      have hl : raw21661step1Labels = raw21661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21661step0 raw21661step0Labels permutation80 hz
    mixedMoment B raw21661step1 raw21661step1Labels = mixedMoment B raw21661step2 raw21661step2Labels := by
      have ha : raw21661step2 = (fun i j => raw21661step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21661step2 raw21661step1; decide +kernel
      have hl : raw21661step2Labels = raw21661step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21661step1 raw21661step1Labels permutation9 permutation7
    mixedMoment B raw21661step2 raw21661step2Labels = mixedMoment B raw21661step3 raw21661step3Labels := by
      have ha : raw21661step3 = -raw21661step2 := by apply Matrix.ext; change ∀ i j, raw21661step3 i j = -(raw21661step2 i j); unfold raw21661step3 raw21661step2; decide +kernel
      have hl : raw21661step3Labels = raw21661step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21661step3 raw21661step3Labels = mixedMoment B raw21661step4 raw21661step4Labels := by
      have ha : raw21661step4 = raw21661step3 := by apply Matrix.ext; unfold raw21661step4 raw21661step3; decide +kernel
      have hl : raw21661step3Labels = labelEmbedding1 ∘ raw21661step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21661step3 raw21661step3Labels raw21661step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

def raw21662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21662Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21662step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21662step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21662step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21662step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21662step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21662 raw21662Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21662 raw21662Labels = mixedMoment B raw21662step0 raw21662step0Labels := by
      have hz : ∀ j, raw21662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21662step0 = (fun i j => raw21662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21662step0 raw21662; decide +kernel
      have hl : raw21662step0Labels = raw21662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21662 raw21662Labels permutation434 hz
    mixedMoment B raw21662step0 raw21662step0Labels = mixedMoment B raw21662step1 raw21662step1Labels := by
      have ha : raw21662step1 = (fun i j => raw21662step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21662step1 raw21662step0; decide +kernel
      have hl : raw21662step1Labels = raw21662step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21662step0 raw21662step0Labels permutation39 permutation7
    mixedMoment B raw21662step1 raw21662step1Labels = mixedMoment B raw21662step2 raw21662step2Labels := by
      have ha : raw21662step2 = -raw21662step1 := by apply Matrix.ext; change ∀ i j, raw21662step2 i j = -(raw21662step1 i j); unfold raw21662step2 raw21662step1; decide +kernel
      have hl : raw21662step2Labels = raw21662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21662step2 raw21662step2Labels = mixedMoment B raw21662step3 raw21662step3Labels := by
      have ha : raw21662step3 = raw21662step2 := by apply Matrix.ext; unfold raw21662step3 raw21662step2; decide +kernel
      have hl : raw21662step2Labels = labelEmbedding1 ∘ raw21662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21662step2 raw21662step2Labels raw21662step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw21663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21663Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21663step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21663step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21663step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21663step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21663step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21663 raw21663Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21663 raw21663Labels = mixedMoment B raw21663step0 raw21663step0Labels := by
      have hz : ∀ j, raw21663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21663step0 = (fun i j => raw21663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21663step0 raw21663; decide +kernel
      have hl : raw21663step0Labels = raw21663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21663 raw21663Labels permutation346 hz
    mixedMoment B raw21663step0 raw21663step0Labels = mixedMoment B raw21663step1 raw21663step1Labels := by
      have ha : raw21663step1 = (fun i j => raw21663step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21663step1 raw21663step0; decide +kernel
      have hl : raw21663step1Labels = raw21663step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21663step0 raw21663step0Labels permutation39 permutation7
    mixedMoment B raw21663step1 raw21663step1Labels = mixedMoment B raw21663step2 raw21663step2Labels := by
      have ha : raw21663step2 = -raw21663step1 := by apply Matrix.ext; change ∀ i j, raw21663step2 i j = -(raw21663step1 i j); unfold raw21663step2 raw21663step1; decide +kernel
      have hl : raw21663step2Labels = raw21663step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21663step2 raw21663step2Labels = mixedMoment B raw21663step3 raw21663step3Labels := by
      have ha : raw21663step3 = raw21663step2 := by apply Matrix.ext; unfold raw21663step3 raw21663step2; decide +kernel
      have hl : raw21663step2Labels = labelEmbedding1 ∘ raw21663step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21663step2 raw21663step2Labels raw21663step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw21664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21664Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21664step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21664step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw21664step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21664step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21664step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21664step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21664 raw21664Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw21664 raw21664Labels = mixedMoment B raw21664step0 raw21664step0Labels := by
      have hz : ∀ j, raw21664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21664step0 = (fun i j => raw21664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21664step0 raw21664; decide +kernel
      have hl : raw21664step0Labels = raw21664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21664 raw21664Labels permutation434 hz
    mixedMoment B raw21664step0 raw21664step0Labels = mixedMoment B raw21664step1 raw21664step1Labels := by
      have hz : ∀ j, raw21664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21664step1 = (fun i j => raw21664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21664step1 raw21664step0; decide +kernel
      have hl : raw21664step1Labels = raw21664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21664step0 raw21664step0Labels permutation80 hz
    mixedMoment B raw21664step1 raw21664step1Labels = mixedMoment B raw21664step2 raw21664step2Labels := by
      have ha : raw21664step2 = (fun i j => raw21664step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21664step2 raw21664step1; decide +kernel
      have hl : raw21664step2Labels = raw21664step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21664step1 raw21664step1Labels permutation9 permutation7
    mixedMoment B raw21664step2 raw21664step2Labels = mixedMoment B raw21664step3 raw21664step3Labels := by
      have ha : raw21664step3 = -raw21664step2 := by apply Matrix.ext; change ∀ i j, raw21664step3 i j = -(raw21664step2 i j); unfold raw21664step3 raw21664step2; decide +kernel
      have hl : raw21664step3Labels = raw21664step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21664step3 raw21664step3Labels = mixedMoment B raw21664step4 raw21664step4Labels := by
      have ha : raw21664step4 = raw21664step3 := by apply Matrix.ext; unfold raw21664step4 raw21664step3; decide +kernel
      have hl : raw21664step3Labels = labelEmbedding1 ∘ raw21664step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21664step3 raw21664step3Labels raw21664step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw21665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21665Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21665step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21665step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw21665step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21665step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21665step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21665step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21665 raw21665Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw21665 raw21665Labels = mixedMoment B raw21665step0 raw21665step0Labels := by
      have hz : ∀ j, raw21665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21665step0 = (fun i j => raw21665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21665step0 raw21665; decide +kernel
      have hl : raw21665step0Labels = raw21665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21665 raw21665Labels permutation434 hz
    mixedMoment B raw21665step0 raw21665step0Labels = mixedMoment B raw21665step1 raw21665step1Labels := by
      have hz : ∀ j, raw21665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21665step1 = (fun i j => raw21665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21665step1 raw21665step0; decide +kernel
      have hl : raw21665step1Labels = raw21665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21665step0 raw21665step0Labels permutation80 hz
    mixedMoment B raw21665step1 raw21665step1Labels = mixedMoment B raw21665step2 raw21665step2Labels := by
      have ha : raw21665step2 = (fun i j => raw21665step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21665step2 raw21665step1; decide +kernel
      have hl : raw21665step2Labels = raw21665step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21665step1 raw21665step1Labels permutation9 permutation7
    mixedMoment B raw21665step2 raw21665step2Labels = mixedMoment B raw21665step3 raw21665step3Labels := by
      have ha : raw21665step3 = -raw21665step2 := by apply Matrix.ext; change ∀ i j, raw21665step3 i j = -(raw21665step2 i j); unfold raw21665step3 raw21665step2; decide +kernel
      have hl : raw21665step3Labels = raw21665step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21665step3 raw21665step3Labels = mixedMoment B raw21665step4 raw21665step4Labels := by
      have ha : raw21665step4 = raw21665step3 := by apply Matrix.ext; unfold raw21665step4 raw21665step3; decide +kernel
      have hl : raw21665step3Labels = labelEmbedding1 ∘ raw21665step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21665step3 raw21665step3Labels raw21665step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw21666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21666Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21666step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21666step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21666step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21666step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21666step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21666step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21666 raw21666Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw21666 raw21666Labels = mixedMoment B raw21666step0 raw21666step0Labels := by
      have hz : ∀ j, raw21666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21666step0 = (fun i j => raw21666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21666step0 raw21666; decide +kernel
      have hl : raw21666step0Labels = raw21666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21666 raw21666Labels permutation434 hz
    mixedMoment B raw21666step0 raw21666step0Labels = mixedMoment B raw21666step1 raw21666step1Labels := by
      have hz : ∀ j, raw21666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21666step1 = (fun i j => raw21666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21666step1 raw21666step0; decide +kernel
      have hl : raw21666step1Labels = raw21666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21666step0 raw21666step0Labels permutation56 hz
    mixedMoment B raw21666step1 raw21666step1Labels = mixedMoment B raw21666step2 raw21666step2Labels := by
      have ha : raw21666step2 = (fun i j => raw21666step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21666step2 raw21666step1; decide +kernel
      have hl : raw21666step2Labels = raw21666step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21666step1 raw21666step1Labels permutation9 permutation7
    mixedMoment B raw21666step2 raw21666step2Labels = mixedMoment B raw21666step3 raw21666step3Labels := by
      have ha : raw21666step3 = -raw21666step2 := by apply Matrix.ext; change ∀ i j, raw21666step3 i j = -(raw21666step2 i j); unfold raw21666step3 raw21666step2; decide +kernel
      have hl : raw21666step3Labels = raw21666step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21666step3 raw21666step3Labels = mixedMoment B raw21666step4 raw21666step4Labels := by
      have ha : raw21666step4 = raw21666step3 := by apply Matrix.ext; unfold raw21666step4 raw21666step3; decide +kernel
      have hl : raw21666step3Labels = labelEmbedding1 ∘ raw21666step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21666step3 raw21666step3Labels raw21666step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

def raw21667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21667Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21667step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21667step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21667step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21667step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21667step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21667 raw21667Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21667 raw21667Labels = mixedMoment B raw21667step0 raw21667step0Labels := by
      have hz : ∀ j, raw21667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21667step0 = (fun i j => raw21667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21667step0 raw21667; decide +kernel
      have hl : raw21667step0Labels = raw21667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21667 raw21667Labels permutation434 hz
    mixedMoment B raw21667step0 raw21667step0Labels = mixedMoment B raw21667step1 raw21667step1Labels := by
      have ha : raw21667step1 = (fun i j => raw21667step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21667step1 raw21667step0; decide +kernel
      have hl : raw21667step1Labels = raw21667step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21667step0 raw21667step0Labels permutation33 permutation7
    mixedMoment B raw21667step1 raw21667step1Labels = mixedMoment B raw21667step2 raw21667step2Labels := by
      have ha : raw21667step2 = -raw21667step1 := by apply Matrix.ext; change ∀ i j, raw21667step2 i j = -(raw21667step1 i j); unfold raw21667step2 raw21667step1; decide +kernel
      have hl : raw21667step2Labels = raw21667step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21667step2 raw21667step2Labels = mixedMoment B raw21667step3 raw21667step3Labels := by
      have ha : raw21667step3 = raw21667step2 := by apply Matrix.ext; unfold raw21667step3 raw21667step2; decide +kernel
      have hl : raw21667step2Labels = labelEmbedding1 ∘ raw21667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21667step2 raw21667step2Labels raw21667step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw21668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21668Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21668step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21668step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21668step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21668step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21668 raw21668Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21668 raw21668Labels = mixedMoment B raw21668step0 raw21668step0Labels := by
      have hz : ∀ j, raw21668 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21668step0 = (fun i j => raw21668 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21668step0 raw21668; decide +kernel
      have hl : raw21668step0Labels = raw21668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21668 raw21668Labels permutation265 hz
    mixedMoment B raw21668step0 raw21668step0Labels = mixedMoment B raw21668step1 raw21668step1Labels := by
      have ha : raw21668step1 = (fun i j => raw21668step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21668step1 raw21668step0; decide +kernel
      have hl : raw21668step1Labels = raw21668step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21668step0 raw21668step0Labels permutation39 permutation7
    mixedMoment B raw21668step1 raw21668step1Labels = mixedMoment B raw21668step2 raw21668step2Labels := by
      have ha : raw21668step2 = -raw21668step1 := by apply Matrix.ext; change ∀ i j, raw21668step2 i j = -(raw21668step1 i j); unfold raw21668step2 raw21668step1; decide +kernel
      have hl : raw21668step2Labels = raw21668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21668step2 raw21668step2Labels = mixedMoment B raw21668step3 raw21668step3Labels := by
      have ha : raw21668step3 = raw21668step2 := by apply Matrix.ext; unfold raw21668step3 raw21668step2; decide +kernel
      have hl : raw21668step2Labels = labelEmbedding1 ∘ raw21668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21668step2 raw21668step2Labels raw21668step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw21669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21669Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21669step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21669step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw21669step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21669step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21669step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21669step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21669step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21669 raw21669Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw21669 raw21669Labels = mixedMoment B raw21669step0 raw21669step0Labels := by
      have hz : ∀ j, raw21669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21669step0 = (fun i j => raw21669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21669step0 raw21669; decide +kernel
      have hl : raw21669step0Labels = raw21669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21669 raw21669Labels permutation434 hz
    mixedMoment B raw21669step0 raw21669step0Labels = mixedMoment B raw21669step1 raw21669step1Labels := by
      have hz : ∀ j, raw21669step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21669step1 = (fun i j => raw21669step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21669step1 raw21669step0; decide +kernel
      have hl : raw21669step1Labels = raw21669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21669step0 raw21669step0Labels permutation56 hz
    mixedMoment B raw21669step1 raw21669step1Labels = mixedMoment B raw21669step2 raw21669step2Labels := by
      have ha : raw21669step2 = (fun i j => raw21669step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21669step2 raw21669step1; decide +kernel
      have hl : raw21669step2Labels = raw21669step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21669step1 raw21669step1Labels permutation9 permutation7
    mixedMoment B raw21669step2 raw21669step2Labels = mixedMoment B raw21669step3 raw21669step3Labels := by
      have ha : raw21669step3 = -raw21669step2 := by apply Matrix.ext; change ∀ i j, raw21669step3 i j = -(raw21669step2 i j); unfold raw21669step3 raw21669step2; decide +kernel
      have hl : raw21669step3Labels = raw21669step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21669step3 raw21669step3Labels = mixedMoment B raw21669step4 raw21669step4Labels := by
      have ha : raw21669step4 = raw21669step3 := by apply Matrix.ext; unfold raw21669step4 raw21669step3; decide +kernel
      have hl : raw21669step3Labels = labelEmbedding1 ∘ raw21669step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21669step3 raw21669step3Labels raw21669step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw21670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21670Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21670step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21670step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw21670step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21670step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21670step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21670step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21670step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21670 raw21670Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw21670 raw21670Labels = mixedMoment B raw21670step0 raw21670step0Labels := by
      have hz : ∀ j, raw21670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21670step0 = (fun i j => raw21670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21670step0 raw21670; decide +kernel
      have hl : raw21670step0Labels = raw21670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21670 raw21670Labels permutation434 hz
    mixedMoment B raw21670step0 raw21670step0Labels = mixedMoment B raw21670step1 raw21670step1Labels := by
      have hz : ∀ j, raw21670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21670step1 = (fun i j => raw21670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21670step1 raw21670step0; decide +kernel
      have hl : raw21670step1Labels = raw21670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21670step0 raw21670step0Labels permutation56 hz
    mixedMoment B raw21670step1 raw21670step1Labels = mixedMoment B raw21670step2 raw21670step2Labels := by
      have ha : raw21670step2 = (fun i j => raw21670step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21670step2 raw21670step1; decide +kernel
      have hl : raw21670step2Labels = raw21670step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21670step1 raw21670step1Labels permutation9 permutation7
    mixedMoment B raw21670step2 raw21670step2Labels = mixedMoment B raw21670step3 raw21670step3Labels := by
      have ha : raw21670step3 = -raw21670step2 := by apply Matrix.ext; change ∀ i j, raw21670step3 i j = -(raw21670step2 i j); unfold raw21670step3 raw21670step2; decide +kernel
      have hl : raw21670step3Labels = raw21670step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21670step3 raw21670step3Labels = mixedMoment B raw21670step4 raw21670step4Labels := by
      have ha : raw21670step4 = raw21670step3 := by apply Matrix.ext; unfold raw21670step4 raw21670step3; decide +kernel
      have hl : raw21670step3Labels = labelEmbedding1 ∘ raw21670step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21670step3 raw21670step3Labels raw21670step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw21671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21671Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21671step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21671step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21671step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21671step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21671step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21671step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21671 raw21671Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw21671 raw21671Labels = mixedMoment B raw21671step0 raw21671step0Labels := by
      have hz : ∀ j, raw21671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21671step0 = (fun i j => raw21671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21671step0 raw21671; decide +kernel
      have hl : raw21671step0Labels = raw21671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21671 raw21671Labels permutation346 hz
    mixedMoment B raw21671step0 raw21671step0Labels = mixedMoment B raw21671step1 raw21671step1Labels := by
      have hz : ∀ j, raw21671step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21671step1 = (fun i j => raw21671step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21671step1 raw21671step0; decide +kernel
      have hl : raw21671step1Labels = raw21671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21671step0 raw21671step0Labels permutation56 hz
    mixedMoment B raw21671step1 raw21671step1Labels = mixedMoment B raw21671step2 raw21671step2Labels := by
      have ha : raw21671step2 = (fun i j => raw21671step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21671step2 raw21671step1; decide +kernel
      have hl : raw21671step2Labels = raw21671step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21671step1 raw21671step1Labels permutation9 permutation7
    mixedMoment B raw21671step2 raw21671step2Labels = mixedMoment B raw21671step3 raw21671step3Labels := by
      have ha : raw21671step3 = -raw21671step2 := by apply Matrix.ext; change ∀ i j, raw21671step3 i j = -(raw21671step2 i j); unfold raw21671step3 raw21671step2; decide +kernel
      have hl : raw21671step3Labels = raw21671step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21671step3 raw21671step3Labels = mixedMoment B raw21671step4 raw21671step4Labels := by
      have ha : raw21671step4 = raw21671step3 := by apply Matrix.ext; unfold raw21671step4 raw21671step3; decide +kernel
      have hl : raw21671step3Labels = labelEmbedding1 ∘ raw21671step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21671step3 raw21671step3Labels raw21671step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

def raw21672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21672Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21672step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21672step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21672step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21672step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21672step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21672step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21672 raw21672Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21672 raw21672Labels = mixedMoment B raw21672step0 raw21672step0Labels := by
      have hz : ∀ j, raw21672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21672step0 = (fun i j => raw21672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21672step0 raw21672; decide +kernel
      have hl : raw21672step0Labels = raw21672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21672 raw21672Labels permutation346 hz
    mixedMoment B raw21672step0 raw21672step0Labels = mixedMoment B raw21672step1 raw21672step1Labels := by
      have ha : raw21672step1 = (fun i j => raw21672step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21672step1 raw21672step0; decide +kernel
      have hl : raw21672step1Labels = raw21672step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21672step0 raw21672step0Labels permutation33 permutation7
    mixedMoment B raw21672step1 raw21672step1Labels = mixedMoment B raw21672step2 raw21672step2Labels := by
      have ha : raw21672step2 = -raw21672step1 := by apply Matrix.ext; change ∀ i j, raw21672step2 i j = -(raw21672step1 i j); unfold raw21672step2 raw21672step1; decide +kernel
      have hl : raw21672step2Labels = raw21672step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21672step2 raw21672step2Labels = mixedMoment B raw21672step3 raw21672step3Labels := by
      have ha : raw21672step3 = raw21672step2 := by apply Matrix.ext; unfold raw21672step3 raw21672step2; decide +kernel
      have hl : raw21672step2Labels = labelEmbedding1 ∘ raw21672step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21672step2 raw21672step2Labels raw21672step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw21673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21673Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21673step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw21673step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21673step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw21673step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21673 raw21673Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw21673 raw21673Labels = mixedMoment B raw21673step0 raw21673step0Labels := by
      have hz : ∀ j, raw21673 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21673step0 = (fun i j => raw21673 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21673step0 raw21673; decide +kernel
      have hl : raw21673step0Labels = raw21673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21673 raw21673Labels permutation265 hz
    mixedMoment B raw21673step0 raw21673step0Labels = mixedMoment B raw21673step1 raw21673step1Labels := by
      have ha : raw21673step1 = (fun i j => raw21673step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21673step1 raw21673step0; decide +kernel
      have hl : raw21673step1Labels = raw21673step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21673step0 raw21673step0Labels permutation33 permutation7
    mixedMoment B raw21673step1 raw21673step1Labels = mixedMoment B raw21673step2 raw21673step2Labels := by
      have ha : raw21673step2 = -raw21673step1 := by apply Matrix.ext; change ∀ i j, raw21673step2 i j = -(raw21673step1 i j); unfold raw21673step2 raw21673step1; decide +kernel
      have hl : raw21673step2Labels = raw21673step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21673step2 raw21673step2Labels = mixedMoment B raw21673step3 raw21673step3Labels := by
      have ha : raw21673step3 = raw21673step2 := by apply Matrix.ext; unfold raw21673step3 raw21673step2; decide +kernel
      have hl : raw21673step2Labels = labelEmbedding1 ∘ raw21673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21673step2 raw21673step2Labels raw21673step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw21674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21674Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21674step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw21674step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw21674step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21674step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21674step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21674step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21674step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21674 raw21674Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw21674 raw21674Labels = mixedMoment B raw21674step0 raw21674step0Labels := by
      have hz : ∀ j, raw21674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21674step0 = (fun i j => raw21674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21674step0 raw21674; decide +kernel
      have hl : raw21674step0Labels = raw21674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21674 raw21674Labels permutation346 hz
    mixedMoment B raw21674step0 raw21674step0Labels = mixedMoment B raw21674step1 raw21674step1Labels := by
      have hz : ∀ j, raw21674step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21674step1 = (fun i j => raw21674step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21674step1 raw21674step0; decide +kernel
      have hl : raw21674step1Labels = raw21674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21674step0 raw21674step0Labels permutation56 hz
    mixedMoment B raw21674step1 raw21674step1Labels = mixedMoment B raw21674step2 raw21674step2Labels := by
      have ha : raw21674step2 = (fun i j => raw21674step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21674step2 raw21674step1; decide +kernel
      have hl : raw21674step2Labels = raw21674step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21674step1 raw21674step1Labels permutation9 permutation7
    mixedMoment B raw21674step2 raw21674step2Labels = mixedMoment B raw21674step3 raw21674step3Labels := by
      have ha : raw21674step3 = -raw21674step2 := by apply Matrix.ext; change ∀ i j, raw21674step3 i j = -(raw21674step2 i j); unfold raw21674step3 raw21674step2; decide +kernel
      have hl : raw21674step3Labels = raw21674step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21674step3 raw21674step3Labels = mixedMoment B raw21674step4 raw21674step4Labels := by
      have ha : raw21674step4 = raw21674step3 := by apply Matrix.ext; unfold raw21674step4 raw21674step3; decide +kernel
      have hl : raw21674step3Labels = labelEmbedding1 ∘ raw21674step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21674step3 raw21674step3Labels raw21674step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw21675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21675Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21675step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21675step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw21675step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21675step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21675step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21675step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21675 raw21675Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw21675 raw21675Labels = mixedMoment B raw21675step0 raw21675step0Labels := by
      have hz : ∀ j, raw21675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21675step0 = (fun i j => raw21675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21675step0 raw21675; decide +kernel
      have hl : raw21675step0Labels = raw21675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21675 raw21675Labels permutation346 hz
    mixedMoment B raw21675step0 raw21675step0Labels = mixedMoment B raw21675step1 raw21675step1Labels := by
      have hz : ∀ j, raw21675step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21675step1 = (fun i j => raw21675step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21675step1 raw21675step0; decide +kernel
      have hl : raw21675step1Labels = raw21675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21675step0 raw21675step0Labels permutation56 hz
    mixedMoment B raw21675step1 raw21675step1Labels = mixedMoment B raw21675step2 raw21675step2Labels := by
      have ha : raw21675step2 = (fun i j => raw21675step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21675step2 raw21675step1; decide +kernel
      have hl : raw21675step2Labels = raw21675step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21675step1 raw21675step1Labels permutation9 permutation7
    mixedMoment B raw21675step2 raw21675step2Labels = mixedMoment B raw21675step3 raw21675step3Labels := by
      have ha : raw21675step3 = -raw21675step2 := by apply Matrix.ext; change ∀ i j, raw21675step3 i j = -(raw21675step2 i j); unfold raw21675step3 raw21675step2; decide +kernel
      have hl : raw21675step3Labels = raw21675step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21675step3 raw21675step3Labels = mixedMoment B raw21675step4 raw21675step4Labels := by
      have ha : raw21675step4 = raw21675step3 := by apply Matrix.ext; unfold raw21675step4 raw21675step3; decide +kernel
      have hl : raw21675step3Labels = labelEmbedding1 ∘ raw21675step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21675step3 raw21675step3Labels raw21675step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw21676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21676Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21676step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21676step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21676step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw21676step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21676step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -2, 3], ![-2, 0, 2]]
def raw21676step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21676step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw21676step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21676step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw21676step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21676 raw21676Labels = mixedMoment B node1539 node1539Labels := by
  calc
    mixedMoment B raw21676 raw21676Labels = mixedMoment B raw21676step0 raw21676step0Labels := by
      have hz : ∀ j, raw21676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21676step0 = (fun i j => raw21676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21676step0 raw21676; decide +kernel
      have hl : raw21676step0Labels = raw21676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21676 raw21676Labels permutation434 hz
    mixedMoment B raw21676step0 raw21676step0Labels = mixedMoment B raw21676step1 raw21676step1Labels := by
      have hz : ∀ j, raw21676step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21676step1 = (fun i j => raw21676step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21676step1 raw21676step0; decide +kernel
      have hl : raw21676step1Labels = raw21676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21676step0 raw21676step0Labels permutation80 hz
    mixedMoment B raw21676step1 raw21676step1Labels = mixedMoment B raw21676step2 raw21676step2Labels := by
      have hz : ∀ j, raw21676step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21676step2 = (fun i j => raw21676step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21676step2 raw21676step1; decide +kernel
      have hl : raw21676step2Labels = raw21676step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21676step1 raw21676step1Labels permutation14 hz
    mixedMoment B raw21676step2 raw21676step2Labels = mixedMoment B raw21676step3 raw21676step3Labels := by
      have ha : raw21676step3 = (fun i j => raw21676step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21676step3 raw21676step2; decide +kernel
      have hl : raw21676step3Labels = raw21676step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21676step2 raw21676step2Labels permutation3 permutation7
    mixedMoment B raw21676step3 raw21676step3Labels = mixedMoment B raw21676step4 raw21676step4Labels := by
      have ha : raw21676step4 = -raw21676step3 := by apply Matrix.ext; change ∀ i j, raw21676step4 i j = -(raw21676step3 i j); unfold raw21676step4 raw21676step3; decide +kernel
      have hl : raw21676step4Labels = raw21676step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21676step4 raw21676step4Labels = mixedMoment B raw21676step5 raw21676step5Labels := by
      have ha : raw21676step5 = raw21676step4 := by apply Matrix.ext; unfold raw21676step5 raw21676step4; decide +kernel
      have hl : raw21676step4Labels = labelEmbedding1 ∘ raw21676step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21676step4 raw21676step4Labels raw21676step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1539 node1539Labels := by rfl

def raw21677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21677Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21677step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21677step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw21677step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21677step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21677step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21677step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21677 raw21677Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw21677 raw21677Labels = mixedMoment B raw21677step0 raw21677step0Labels := by
      have hz : ∀ j, raw21677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21677step0 = (fun i j => raw21677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21677step0 raw21677; decide +kernel
      have hl : raw21677step0Labels = raw21677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21677 raw21677Labels permutation434 hz
    mixedMoment B raw21677step0 raw21677step0Labels = mixedMoment B raw21677step1 raw21677step1Labels := by
      have hz : ∀ j, raw21677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21677step1 = (fun i j => raw21677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21677step1 raw21677step0; decide +kernel
      have hl : raw21677step1Labels = raw21677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21677step0 raw21677step0Labels permutation80 hz
    mixedMoment B raw21677step1 raw21677step1Labels = mixedMoment B raw21677step2 raw21677step2Labels := by
      have ha : raw21677step2 = (fun i j => raw21677step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21677step2 raw21677step1; decide +kernel
      have hl : raw21677step2Labels = raw21677step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21677step1 raw21677step1Labels permutation9 permutation7
    mixedMoment B raw21677step2 raw21677step2Labels = mixedMoment B raw21677step3 raw21677step3Labels := by
      have ha : raw21677step3 = -raw21677step2 := by apply Matrix.ext; change ∀ i j, raw21677step3 i j = -(raw21677step2 i j); unfold raw21677step3 raw21677step2; decide +kernel
      have hl : raw21677step3Labels = raw21677step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21677step3 raw21677step3Labels = mixedMoment B raw21677step4 raw21677step4Labels := by
      have ha : raw21677step4 = raw21677step3 := by apply Matrix.ext; unfold raw21677step4 raw21677step3; decide +kernel
      have hl : raw21677step3Labels = labelEmbedding1 ∘ raw21677step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21677step3 raw21677step3Labels raw21677step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

def raw21678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21678Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21678step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21678step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw21678step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21678step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21678step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21678step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21678step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21678 raw21678Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw21678 raw21678Labels = mixedMoment B raw21678step0 raw21678step0Labels := by
      have hz : ∀ j, raw21678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21678step0 = (fun i j => raw21678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21678step0 raw21678; decide +kernel
      have hl : raw21678step0Labels = raw21678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21678 raw21678Labels permutation434 hz
    mixedMoment B raw21678step0 raw21678step0Labels = mixedMoment B raw21678step1 raw21678step1Labels := by
      have hz : ∀ j, raw21678step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21678step1 = (fun i j => raw21678step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21678step1 raw21678step0; decide +kernel
      have hl : raw21678step1Labels = raw21678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21678step0 raw21678step0Labels permutation56 hz
    mixedMoment B raw21678step1 raw21678step1Labels = mixedMoment B raw21678step2 raw21678step2Labels := by
      have ha : raw21678step2 = (fun i j => raw21678step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21678step2 raw21678step1; decide +kernel
      have hl : raw21678step2Labels = raw21678step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21678step1 raw21678step1Labels permutation9 permutation7
    mixedMoment B raw21678step2 raw21678step2Labels = mixedMoment B raw21678step3 raw21678step3Labels := by
      have ha : raw21678step3 = -raw21678step2 := by apply Matrix.ext; change ∀ i j, raw21678step3 i j = -(raw21678step2 i j); unfold raw21678step3 raw21678step2; decide +kernel
      have hl : raw21678step3Labels = raw21678step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21678step3 raw21678step3Labels = mixedMoment B raw21678step4 raw21678step4Labels := by
      have ha : raw21678step4 = raw21678step3 := by apply Matrix.ext; unfold raw21678step4 raw21678step3; decide +kernel
      have hl : raw21678step3Labels = labelEmbedding1 ∘ raw21678step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21678step3 raw21678step3Labels raw21678step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

def raw21679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21679Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21679step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21679step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw21679step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21679step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21679step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw21679step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21679 raw21679Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw21679 raw21679Labels = mixedMoment B raw21679step0 raw21679step0Labels := by
      have hz : ∀ j, raw21679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21679step0 = (fun i j => raw21679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21679step0 raw21679; decide +kernel
      have hl : raw21679step0Labels = raw21679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21679 raw21679Labels permutation346 hz
    mixedMoment B raw21679step0 raw21679step0Labels = mixedMoment B raw21679step1 raw21679step1Labels := by
      have hz : ∀ j, raw21679step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21679step1 = (fun i j => raw21679step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21679step1 raw21679step0; decide +kernel
      have hl : raw21679step1Labels = raw21679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21679step0 raw21679step0Labels permutation56 hz
    mixedMoment B raw21679step1 raw21679step1Labels = mixedMoment B raw21679step2 raw21679step2Labels := by
      have ha : raw21679step2 = (fun i j => raw21679step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21679step2 raw21679step1; decide +kernel
      have hl : raw21679step2Labels = raw21679step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21679step1 raw21679step1Labels permutation9 permutation7
    mixedMoment B raw21679step2 raw21679step2Labels = mixedMoment B raw21679step3 raw21679step3Labels := by
      have ha : raw21679step3 = -raw21679step2 := by apply Matrix.ext; change ∀ i j, raw21679step3 i j = -(raw21679step2 i j); unfold raw21679step3 raw21679step2; decide +kernel
      have hl : raw21679step3Labels = raw21679step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21679step3 raw21679step3Labels = mixedMoment B raw21679step4 raw21679step4Labels := by
      have ha : raw21679step4 = raw21679step3 := by apply Matrix.ext; unfold raw21679step4 raw21679step3; decide +kernel
      have hl : raw21679step3Labels = labelEmbedding1 ∘ raw21679step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21679step3 raw21679step3Labels raw21679step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

def raw21680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw21680Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw21680step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw21680step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21680step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw21680step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21680step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw21680step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21680step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw21680step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21680step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw21680step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21680 raw21680Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw21680 raw21680Labels = mixedMoment B raw21680step0 raw21680step0Labels := by
      have hz : ∀ j, raw21680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21680step0 = (fun i j => raw21680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21680step0 raw21680; decide +kernel
      have hl : raw21680step0Labels = raw21680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21680 raw21680Labels permutation434 hz
    mixedMoment B raw21680step0 raw21680step0Labels = mixedMoment B raw21680step1 raw21680step1Labels := by
      have hz : ∀ j, raw21680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21680step1 = (fun i j => raw21680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21680step1 raw21680step0; decide +kernel
      have hl : raw21680step1Labels = raw21680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21680step0 raw21680step0Labels permutation80 hz
    mixedMoment B raw21680step1 raw21680step1Labels = mixedMoment B raw21680step2 raw21680step2Labels := by
      have hz : ∀ j, raw21680step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21680step2 = (fun i j => raw21680step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21680step2 raw21680step1; decide +kernel
      have hl : raw21680step2Labels = raw21680step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21680step1 raw21680step1Labels permutation14 hz
    mixedMoment B raw21680step2 raw21680step2Labels = mixedMoment B raw21680step3 raw21680step3Labels := by
      have ha : raw21680step3 = (fun i j => raw21680step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21680step3 raw21680step2; decide +kernel
      have hl : raw21680step3Labels = raw21680step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21680step2 raw21680step2Labels permutation3 permutation7
    mixedMoment B raw21680step3 raw21680step3Labels = mixedMoment B raw21680step4 raw21680step4Labels := by
      have ha : raw21680step4 = -raw21680step3 := by apply Matrix.ext; change ∀ i j, raw21680step4 i j = -(raw21680step3 i j); unfold raw21680step4 raw21680step3; decide +kernel
      have hl : raw21680step4Labels = raw21680step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21680step4 raw21680step4Labels = mixedMoment B raw21680step5 raw21680step5Labels := by
      have ha : raw21680step5 = raw21680step4 := by apply Matrix.ext; unfold raw21680step5 raw21680step4; decide +kernel
      have hl : raw21680step4Labels = labelEmbedding1 ∘ raw21680step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21680step4 raw21680step4Labels raw21680step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1755 node1755Labels := by rfl

def raw21681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21681Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21681step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21681step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21681step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw21681step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21681step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -3, 4], ![-2, 1, 1]]
def raw21681step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21681step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw21681step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21681step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw21681step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21681 raw21681Labels = mixedMoment B node1540 node1540Labels := by
  calc
    mixedMoment B raw21681 raw21681Labels = mixedMoment B raw21681step0 raw21681step0Labels := by
      have hz : ∀ j, raw21681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21681step0 = (fun i j => raw21681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21681step0 raw21681; decide +kernel
      have hl : raw21681step0Labels = raw21681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21681 raw21681Labels permutation434 hz
    mixedMoment B raw21681step0 raw21681step0Labels = mixedMoment B raw21681step1 raw21681step1Labels := by
      have hz : ∀ j, raw21681step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21681step1 = (fun i j => raw21681step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21681step1 raw21681step0; decide +kernel
      have hl : raw21681step1Labels = raw21681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21681step0 raw21681step0Labels permutation80 hz
    mixedMoment B raw21681step1 raw21681step1Labels = mixedMoment B raw21681step2 raw21681step2Labels := by
      have hz : ∀ j, raw21681step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21681step2 = (fun i j => raw21681step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21681step2 raw21681step1; decide +kernel
      have hl : raw21681step2Labels = raw21681step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21681step1 raw21681step1Labels permutation14 hz
    mixedMoment B raw21681step2 raw21681step2Labels = mixedMoment B raw21681step3 raw21681step3Labels := by
      have ha : raw21681step3 = (fun i j => raw21681step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21681step3 raw21681step2; decide +kernel
      have hl : raw21681step3Labels = raw21681step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21681step2 raw21681step2Labels permutation3 permutation7
    mixedMoment B raw21681step3 raw21681step3Labels = mixedMoment B raw21681step4 raw21681step4Labels := by
      have ha : raw21681step4 = -raw21681step3 := by apply Matrix.ext; change ∀ i j, raw21681step4 i j = -(raw21681step3 i j); unfold raw21681step4 raw21681step3; decide +kernel
      have hl : raw21681step4Labels = raw21681step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21681step4 raw21681step4Labels = mixedMoment B raw21681step5 raw21681step5Labels := by
      have ha : raw21681step5 = raw21681step4 := by apply Matrix.ext; unfold raw21681step5 raw21681step4; decide +kernel
      have hl : raw21681step4Labels = labelEmbedding1 ∘ raw21681step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21681step4 raw21681step4Labels raw21681step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1540 node1540Labels := by rfl

def raw21682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21682Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21682step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21682step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw21682step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21682step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21682step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21682step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21682 raw21682Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw21682 raw21682Labels = mixedMoment B raw21682step0 raw21682step0Labels := by
      have hz : ∀ j, raw21682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21682step0 = (fun i j => raw21682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21682step0 raw21682; decide +kernel
      have hl : raw21682step0Labels = raw21682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21682 raw21682Labels permutation434 hz
    mixedMoment B raw21682step0 raw21682step0Labels = mixedMoment B raw21682step1 raw21682step1Labels := by
      have hz : ∀ j, raw21682step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21682step1 = (fun i j => raw21682step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21682step1 raw21682step0; decide +kernel
      have hl : raw21682step1Labels = raw21682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21682step0 raw21682step0Labels permutation80 hz
    mixedMoment B raw21682step1 raw21682step1Labels = mixedMoment B raw21682step2 raw21682step2Labels := by
      have ha : raw21682step2 = (fun i j => raw21682step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21682step2 raw21682step1; decide +kernel
      have hl : raw21682step2Labels = raw21682step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21682step1 raw21682step1Labels permutation9 permutation7
    mixedMoment B raw21682step2 raw21682step2Labels = mixedMoment B raw21682step3 raw21682step3Labels := by
      have ha : raw21682step3 = -raw21682step2 := by apply Matrix.ext; change ∀ i j, raw21682step3 i j = -(raw21682step2 i j); unfold raw21682step3 raw21682step2; decide +kernel
      have hl : raw21682step3Labels = raw21682step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21682step3 raw21682step3Labels = mixedMoment B raw21682step4 raw21682step4Labels := by
      have ha : raw21682step4 = raw21682step3 := by apply Matrix.ext; unfold raw21682step4 raw21682step3; decide +kernel
      have hl : raw21682step3Labels = labelEmbedding1 ∘ raw21682step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21682step3 raw21682step3Labels raw21682step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

def raw21683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21683Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21683step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21683step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw21683step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21683step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21683step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21683step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21683 raw21683Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw21683 raw21683Labels = mixedMoment B raw21683step0 raw21683step0Labels := by
      have hz : ∀ j, raw21683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21683step0 = (fun i j => raw21683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21683step0 raw21683; decide +kernel
      have hl : raw21683step0Labels = raw21683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21683 raw21683Labels permutation434 hz
    mixedMoment B raw21683step0 raw21683step0Labels = mixedMoment B raw21683step1 raw21683step1Labels := by
      have hz : ∀ j, raw21683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21683step1 = (fun i j => raw21683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21683step1 raw21683step0; decide +kernel
      have hl : raw21683step1Labels = raw21683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21683step0 raw21683step0Labels permutation56 hz
    mixedMoment B raw21683step1 raw21683step1Labels = mixedMoment B raw21683step2 raw21683step2Labels := by
      have ha : raw21683step2 = (fun i j => raw21683step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21683step2 raw21683step1; decide +kernel
      have hl : raw21683step2Labels = raw21683step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21683step1 raw21683step1Labels permutation9 permutation7
    mixedMoment B raw21683step2 raw21683step2Labels = mixedMoment B raw21683step3 raw21683step3Labels := by
      have ha : raw21683step3 = -raw21683step2 := by apply Matrix.ext; change ∀ i j, raw21683step3 i j = -(raw21683step2 i j); unfold raw21683step3 raw21683step2; decide +kernel
      have hl : raw21683step3Labels = raw21683step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21683step3 raw21683step3Labels = mixedMoment B raw21683step4 raw21683step4Labels := by
      have ha : raw21683step4 = raw21683step3 := by apply Matrix.ext; unfold raw21683step4 raw21683step3; decide +kernel
      have hl : raw21683step3Labels = labelEmbedding1 ∘ raw21683step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21683step3 raw21683step3Labels raw21683step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

def raw21684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21684Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21684step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw21684step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw21684step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21684step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21684step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw21684step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21684 raw21684Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw21684 raw21684Labels = mixedMoment B raw21684step0 raw21684step0Labels := by
      have hz : ∀ j, raw21684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21684step0 = (fun i j => raw21684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21684step0 raw21684; decide +kernel
      have hl : raw21684step0Labels = raw21684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21684 raw21684Labels permutation346 hz
    mixedMoment B raw21684step0 raw21684step0Labels = mixedMoment B raw21684step1 raw21684step1Labels := by
      have hz : ∀ j, raw21684step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21684step1 = (fun i j => raw21684step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21684step1 raw21684step0; decide +kernel
      have hl : raw21684step1Labels = raw21684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21684step0 raw21684step0Labels permutation56 hz
    mixedMoment B raw21684step1 raw21684step1Labels = mixedMoment B raw21684step2 raw21684step2Labels := by
      have ha : raw21684step2 = (fun i j => raw21684step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21684step2 raw21684step1; decide +kernel
      have hl : raw21684step2Labels = raw21684step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21684step1 raw21684step1Labels permutation9 permutation7
    mixedMoment B raw21684step2 raw21684step2Labels = mixedMoment B raw21684step3 raw21684step3Labels := by
      have ha : raw21684step3 = -raw21684step2 := by apply Matrix.ext; change ∀ i j, raw21684step3 i j = -(raw21684step2 i j); unfold raw21684step3 raw21684step2; decide +kernel
      have hl : raw21684step3Labels = raw21684step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21684step3 raw21684step3Labels = mixedMoment B raw21684step4 raw21684step4Labels := by
      have ha : raw21684step4 = raw21684step3 := by apply Matrix.ext; unfold raw21684step4 raw21684step3; decide +kernel
      have hl : raw21684step3Labels = labelEmbedding1 ∘ raw21684step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21684step3 raw21684step3Labels raw21684step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

def raw21685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21685Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21685step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw21685step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21685step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw21685step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21685step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw21685step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21685step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw21685step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21685 raw21685Labels = mixedMoment B node1757 node1757Labels := by
  calc
    mixedMoment B raw21685 raw21685Labels = mixedMoment B raw21685step0 raw21685step0Labels := by
      have hz : ∀ j, raw21685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21685step0 = (fun i j => raw21685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21685step0 raw21685; decide +kernel
      have hl : raw21685step0Labels = raw21685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21685 raw21685Labels permutation434 hz
    mixedMoment B raw21685step0 raw21685step0Labels = mixedMoment B raw21685step1 raw21685step1Labels := by
      have hz : ∀ j, raw21685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21685step1 = (fun i j => raw21685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21685step1 raw21685step0; decide +kernel
      have hl : raw21685step1Labels = raw21685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21685step0 raw21685step0Labels permutation80 hz
    mixedMoment B raw21685step1 raw21685step1Labels = mixedMoment B raw21685step2 raw21685step2Labels := by
      have hz : ∀ j, raw21685step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21685step2 = (fun i j => raw21685step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21685step2 raw21685step1; decide +kernel
      have hl : raw21685step2Labels = raw21685step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21685step1 raw21685step1Labels permutation14 hz
    mixedMoment B raw21685step2 raw21685step2Labels = mixedMoment B raw21685step3 raw21685step3Labels := by
      have ha : raw21685step3 = (fun i j => raw21685step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21685step3 raw21685step2; decide +kernel
      have hl : raw21685step3Labels = raw21685step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21685step2 raw21685step2Labels permutation6 permutation5
    mixedMoment B raw21685step3 raw21685step3Labels = mixedMoment B raw21685step4 raw21685step4Labels := by
      have ha : raw21685step4 = raw21685step3 := by apply Matrix.ext; unfold raw21685step4 raw21685step3; decide +kernel
      have hl : raw21685step3Labels = labelEmbedding1 ∘ raw21685step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21685step3 raw21685step3Labels raw21685step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1757 node1757Labels := by rfl

def raw21686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21686 raw21686Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw21686 raw21686Labels = mixedMoment B raw21686step0 raw21686step0Labels := by
      have hz : ∀ j, raw21686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21686step0 = (fun i j => raw21686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21686step0 raw21686; decide +kernel
      have hl : raw21686step0Labels = raw21686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21686 raw21686Labels permutation434 hz
    mixedMoment B raw21686step0 raw21686step0Labels = mixedMoment B raw21686step1 raw21686step1Labels := by
      have hz : ∀ j, raw21686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21686step1 = (fun i j => raw21686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21686step1 raw21686step0; decide +kernel
      have hl : raw21686step1Labels = raw21686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21686step0 raw21686step0Labels permutation80 hz
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw21687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21687 raw21687Labels = mixedMoment B node925 node925Labels := by
  calc
    mixedMoment B raw21687 raw21687Labels = mixedMoment B raw21687step0 raw21687step0Labels := by
      have hz : ∀ j, raw21687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21687step0 = (fun i j => raw21687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21687step0 raw21687; decide +kernel
      have hl : raw21687step0Labels = raw21687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21687 raw21687Labels permutation434 hz
    _ = mixedMoment B node925 node925Labels := by rfl

def raw21688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw21688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21688 raw21688Labels = mixedMoment B node925 node925Labels := by
  calc
    mixedMoment B raw21688 raw21688Labels = mixedMoment B raw21688step0 raw21688step0Labels := by
      have hz : ∀ j, raw21688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21688step0 = (fun i j => raw21688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21688step0 raw21688; decide +kernel
      have hl : raw21688step0Labels = raw21688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21688 raw21688Labels permutation346 hz
    _ = mixedMoment B node925 node925Labels := by rfl

def raw21689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21689 raw21689Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw21689 raw21689Labels = mixedMoment B raw21689step0 raw21689step0Labels := by
      have hz : ∀ j, raw21689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21689step0 = (fun i j => raw21689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21689step0 raw21689; decide +kernel
      have hl : raw21689step0Labels = raw21689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21689 raw21689Labels permutation434 hz
    mixedMoment B raw21689step0 raw21689step0Labels = mixedMoment B raw21689step1 raw21689step1Labels := by
      have hz : ∀ j, raw21689step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21689step1 = (fun i j => raw21689step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21689step1 raw21689step0; decide +kernel
      have hl : raw21689step1Labels = raw21689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21689step0 raw21689step0Labels permutation80 hz
    _ = mixedMoment B node939 node939Labels := by rfl

def raw21690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21690step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21690 raw21690Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw21690 raw21690Labels = mixedMoment B raw21690step0 raw21690step0Labels := by
      have hz : ∀ j, raw21690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21690step0 = (fun i j => raw21690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21690step0 raw21690; decide +kernel
      have hl : raw21690step0Labels = raw21690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21690 raw21690Labels permutation434 hz
    mixedMoment B raw21690step0 raw21690step0Labels = mixedMoment B raw21690step1 raw21690step1Labels := by
      have hz : ∀ j, raw21690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21690step1 = (fun i j => raw21690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21690step1 raw21690step0; decide +kernel
      have hl : raw21690step1Labels = raw21690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21690step0 raw21690step0Labels permutation80 hz
    mixedMoment B raw21690step1 raw21690step1Labels = mixedMoment B raw21690step2 raw21690step2Labels := by
      have ha : raw21690step2 = (fun i j => raw21690step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21690step2 raw21690step1; decide +kernel
      have hl : raw21690step2Labels = raw21690step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21690step1 raw21690step1Labels permutation8 permutation3
    mixedMoment B raw21690step2 raw21690step2Labels = mixedMoment B raw21690step3 raw21690step3Labels := by
      have ha : raw21690step3 = raw21690step2 := by apply Matrix.ext; unfold raw21690step3 raw21690step2; decide +kernel
      have hl : raw21690step2Labels = labelEmbedding6 ∘ raw21690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21690step2 raw21690step2Labels raw21690step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4128 node4128Labels := by rfl

def raw21691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21691step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21691 raw21691Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21691 raw21691Labels = mixedMoment B raw21691step0 raw21691step0Labels := by
      have hz : ∀ j, raw21691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21691step0 = (fun i j => raw21691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21691step0 raw21691; decide +kernel
      have hl : raw21691step0Labels = raw21691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21691 raw21691Labels permutation434 hz
    mixedMoment B raw21691step0 raw21691step0Labels = mixedMoment B raw21691step1 raw21691step1Labels := by
      have ha : raw21691step1 = (fun i j => raw21691step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21691step1 raw21691step0; decide +kernel
      have hl : raw21691step1Labels = raw21691step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21691step0 raw21691step0Labels permutation38 permutation3
    mixedMoment B raw21691step1 raw21691step1Labels = mixedMoment B raw21691step2 raw21691step2Labels := by
      have ha : raw21691step2 = raw21691step1 := by apply Matrix.ext; unfold raw21691step2 raw21691step1; decide +kernel
      have hl : raw21691step1Labels = labelEmbedding6 ∘ raw21691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21691step1 raw21691step1Labels raw21691step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw21692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21692step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21692step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21692 raw21692Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21692 raw21692Labels = mixedMoment B raw21692step0 raw21692step0Labels := by
      have hz : ∀ j, raw21692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21692step0 = (fun i j => raw21692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21692step0 raw21692; decide +kernel
      have hl : raw21692step0Labels = raw21692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21692 raw21692Labels permutation346 hz
    mixedMoment B raw21692step0 raw21692step0Labels = mixedMoment B raw21692step1 raw21692step1Labels := by
      have ha : raw21692step1 = (fun i j => raw21692step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21692step1 raw21692step0; decide +kernel
      have hl : raw21692step1Labels = raw21692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21692step0 raw21692step0Labels permutation38 permutation3
    mixedMoment B raw21692step1 raw21692step1Labels = mixedMoment B raw21692step2 raw21692step2Labels := by
      have ha : raw21692step2 = raw21692step1 := by apply Matrix.ext; unfold raw21692step2 raw21692step1; decide +kernel
      have hl : raw21692step1Labels = labelEmbedding6 ∘ raw21692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21692step1 raw21692step1Labels raw21692step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw21693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21693step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21693step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21693 raw21693Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21693 raw21693Labels = mixedMoment B raw21693step0 raw21693step0Labels := by
      have hz : ∀ j, raw21693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21693step0 = (fun i j => raw21693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21693step0 raw21693; decide +kernel
      have hl : raw21693step0Labels = raw21693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21693 raw21693Labels permutation434 hz
    mixedMoment B raw21693step0 raw21693step0Labels = mixedMoment B raw21693step1 raw21693step1Labels := by
      have hz : ∀ j, raw21693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21693step1 = (fun i j => raw21693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21693step1 raw21693step0; decide +kernel
      have hl : raw21693step1Labels = raw21693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21693step0 raw21693step0Labels permutation80 hz
    mixedMoment B raw21693step1 raw21693step1Labels = mixedMoment B raw21693step2 raw21693step2Labels := by
      have ha : raw21693step2 = (fun i j => raw21693step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21693step2 raw21693step1; decide +kernel
      have hl : raw21693step2Labels = raw21693step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21693step1 raw21693step1Labels permutation10 permutation3
    mixedMoment B raw21693step2 raw21693step2Labels = mixedMoment B raw21693step3 raw21693step3Labels := by
      have ha : raw21693step3 = raw21693step2 := by apply Matrix.ext; unfold raw21693step3 raw21693step2; decide +kernel
      have hl : raw21693step2Labels = labelEmbedding6 ∘ raw21693step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21693step2 raw21693step2Labels raw21693step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw21694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21694step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21694step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21694 raw21694Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw21694 raw21694Labels = mixedMoment B raw21694step0 raw21694step0Labels := by
      have hz : ∀ j, raw21694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21694step0 = (fun i j => raw21694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21694step0 raw21694; decide +kernel
      have hl : raw21694step0Labels = raw21694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21694 raw21694Labels permutation434 hz
    mixedMoment B raw21694step0 raw21694step0Labels = mixedMoment B raw21694step1 raw21694step1Labels := by
      have hz : ∀ j, raw21694step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21694step1 = (fun i j => raw21694step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21694step1 raw21694step0; decide +kernel
      have hl : raw21694step1Labels = raw21694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21694step0 raw21694step0Labels permutation56 hz
    mixedMoment B raw21694step1 raw21694step1Labels = mixedMoment B raw21694step2 raw21694step2Labels := by
      have ha : raw21694step2 = (fun i j => raw21694step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21694step2 raw21694step1; decide +kernel
      have hl : raw21694step2Labels = raw21694step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21694step1 raw21694step1Labels permutation8 permutation3
    mixedMoment B raw21694step2 raw21694step2Labels = mixedMoment B raw21694step3 raw21694step3Labels := by
      have ha : raw21694step3 = raw21694step2 := by apply Matrix.ext; unfold raw21694step3 raw21694step2; decide +kernel
      have hl : raw21694step2Labels = labelEmbedding6 ∘ raw21694step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21694step2 raw21694step2Labels raw21694step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4128 node4128Labels := by rfl

def raw21695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21695step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21695 raw21695Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21695 raw21695Labels = mixedMoment B raw21695step0 raw21695step0Labels := by
      have hz : ∀ j, raw21695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21695step0 = (fun i j => raw21695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21695step0 raw21695; decide +kernel
      have hl : raw21695step0Labels = raw21695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21695 raw21695Labels permutation434 hz
    mixedMoment B raw21695step0 raw21695step0Labels = mixedMoment B raw21695step1 raw21695step1Labels := by
      have ha : raw21695step1 = (fun i j => raw21695step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21695step1 raw21695step0; decide +kernel
      have hl : raw21695step1Labels = raw21695step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21695step0 raw21695step0Labels permutation32 permutation3
    mixedMoment B raw21695step1 raw21695step1Labels = mixedMoment B raw21695step2 raw21695step2Labels := by
      have ha : raw21695step2 = raw21695step1 := by apply Matrix.ext; unfold raw21695step2 raw21695step1; decide +kernel
      have hl : raw21695step1Labels = labelEmbedding6 ∘ raw21695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21695step1 raw21695step1Labels raw21695step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw21696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21696step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21696 raw21696Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21696 raw21696Labels = mixedMoment B raw21696step0 raw21696step0Labels := by
      have hz : ∀ j, raw21696 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21696step0 = (fun i j => raw21696 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21696step0 raw21696; decide +kernel
      have hl : raw21696step0Labels = raw21696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21696 raw21696Labels permutation265 hz
    mixedMoment B raw21696step0 raw21696step0Labels = mixedMoment B raw21696step1 raw21696step1Labels := by
      have ha : raw21696step1 = (fun i j => raw21696step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21696step1 raw21696step0; decide +kernel
      have hl : raw21696step1Labels = raw21696step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21696step0 raw21696step0Labels permutation38 permutation3
    mixedMoment B raw21696step1 raw21696step1Labels = mixedMoment B raw21696step2 raw21696step2Labels := by
      have ha : raw21696step2 = raw21696step1 := by apply Matrix.ext; unfold raw21696step2 raw21696step1; decide +kernel
      have hl : raw21696step1Labels = labelEmbedding6 ∘ raw21696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21696step1 raw21696step1Labels raw21696step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw21697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21697step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21697step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21697 raw21697Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21697 raw21697Labels = mixedMoment B raw21697step0 raw21697step0Labels := by
      have hz : ∀ j, raw21697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21697step0 = (fun i j => raw21697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21697step0 raw21697; decide +kernel
      have hl : raw21697step0Labels = raw21697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21697 raw21697Labels permutation434 hz
    mixedMoment B raw21697step0 raw21697step0Labels = mixedMoment B raw21697step1 raw21697step1Labels := by
      have hz : ∀ j, raw21697step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21697step1 = (fun i j => raw21697step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21697step1 raw21697step0; decide +kernel
      have hl : raw21697step1Labels = raw21697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21697step0 raw21697step0Labels permutation56 hz
    mixedMoment B raw21697step1 raw21697step1Labels = mixedMoment B raw21697step2 raw21697step2Labels := by
      have ha : raw21697step2 = (fun i j => raw21697step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21697step2 raw21697step1; decide +kernel
      have hl : raw21697step2Labels = raw21697step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21697step1 raw21697step1Labels permutation10 permutation3
    mixedMoment B raw21697step2 raw21697step2Labels = mixedMoment B raw21697step3 raw21697step3Labels := by
      have ha : raw21697step3 = raw21697step2 := by apply Matrix.ext; unfold raw21697step3 raw21697step2; decide +kernel
      have hl : raw21697step2Labels = labelEmbedding6 ∘ raw21697step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21697step2 raw21697step2Labels raw21697step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw21698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21698step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21698 raw21698Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw21698 raw21698Labels = mixedMoment B raw21698step0 raw21698step0Labels := by
      have hz : ∀ j, raw21698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21698step0 = (fun i j => raw21698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21698step0 raw21698; decide +kernel
      have hl : raw21698step0Labels = raw21698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21698 raw21698Labels permutation346 hz
    mixedMoment B raw21698step0 raw21698step0Labels = mixedMoment B raw21698step1 raw21698step1Labels := by
      have hz : ∀ j, raw21698step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21698step1 = (fun i j => raw21698step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21698step1 raw21698step0; decide +kernel
      have hl : raw21698step1Labels = raw21698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21698step0 raw21698step0Labels permutation56 hz
    mixedMoment B raw21698step1 raw21698step1Labels = mixedMoment B raw21698step2 raw21698step2Labels := by
      have ha : raw21698step2 = (fun i j => raw21698step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21698step2 raw21698step1; decide +kernel
      have hl : raw21698step2Labels = raw21698step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21698step1 raw21698step1Labels permutation8 permutation3
    mixedMoment B raw21698step2 raw21698step2Labels = mixedMoment B raw21698step3 raw21698step3Labels := by
      have ha : raw21698step3 = raw21698step2 := by apply Matrix.ext; unfold raw21698step3 raw21698step2; decide +kernel
      have hl : raw21698step2Labels = labelEmbedding6 ∘ raw21698step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21698step2 raw21698step2Labels raw21698step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4128 node4128Labels := by rfl

def raw21699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21699step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21699 raw21699Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21699 raw21699Labels = mixedMoment B raw21699step0 raw21699step0Labels := by
      have hz : ∀ j, raw21699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21699step0 = (fun i j => raw21699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21699step0 raw21699; decide +kernel
      have hl : raw21699step0Labels = raw21699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21699 raw21699Labels permutation346 hz
    mixedMoment B raw21699step0 raw21699step0Labels = mixedMoment B raw21699step1 raw21699step1Labels := by
      have ha : raw21699step1 = (fun i j => raw21699step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21699step1 raw21699step0; decide +kernel
      have hl : raw21699step1Labels = raw21699step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21699step0 raw21699step0Labels permutation32 permutation3
    mixedMoment B raw21699step1 raw21699step1Labels = mixedMoment B raw21699step2 raw21699step2Labels := by
      have ha : raw21699step2 = raw21699step1 := by apply Matrix.ext; unfold raw21699step2 raw21699step1; decide +kernel
      have hl : raw21699step1Labels = labelEmbedding6 ∘ raw21699step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21699step1 raw21699step1Labels raw21699step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw21700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21700step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21700 raw21700Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21700 raw21700Labels = mixedMoment B raw21700step0 raw21700step0Labels := by
      have hz : ∀ j, raw21700 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21700step0 = (fun i j => raw21700 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21700step0 raw21700; decide +kernel
      have hl : raw21700step0Labels = raw21700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21700 raw21700Labels permutation265 hz
    mixedMoment B raw21700step0 raw21700step0Labels = mixedMoment B raw21700step1 raw21700step1Labels := by
      have ha : raw21700step1 = (fun i j => raw21700step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21700step1 raw21700step0; decide +kernel
      have hl : raw21700step1Labels = raw21700step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21700step0 raw21700step0Labels permutation32 permutation3
    mixedMoment B raw21700step1 raw21700step1Labels = mixedMoment B raw21700step2 raw21700step2Labels := by
      have ha : raw21700step2 = raw21700step1 := by apply Matrix.ext; unfold raw21700step2 raw21700step1; decide +kernel
      have hl : raw21700step1Labels = labelEmbedding6 ∘ raw21700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21700step1 raw21700step1Labels raw21700step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw21701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21701step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21701step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21701step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21701 raw21701Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21701 raw21701Labels = mixedMoment B raw21701step0 raw21701step0Labels := by
      have hz : ∀ j, raw21701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21701step0 = (fun i j => raw21701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21701step0 raw21701; decide +kernel
      have hl : raw21701step0Labels = raw21701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21701 raw21701Labels permutation346 hz
    mixedMoment B raw21701step0 raw21701step0Labels = mixedMoment B raw21701step1 raw21701step1Labels := by
      have hz : ∀ j, raw21701step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21701step1 = (fun i j => raw21701step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21701step1 raw21701step0; decide +kernel
      have hl : raw21701step1Labels = raw21701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21701step0 raw21701step0Labels permutation56 hz
    mixedMoment B raw21701step1 raw21701step1Labels = mixedMoment B raw21701step2 raw21701step2Labels := by
      have ha : raw21701step2 = (fun i j => raw21701step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21701step2 raw21701step1; decide +kernel
      have hl : raw21701step2Labels = raw21701step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21701step1 raw21701step1Labels permutation10 permutation3
    mixedMoment B raw21701step2 raw21701step2Labels = mixedMoment B raw21701step3 raw21701step3Labels := by
      have ha : raw21701step3 = raw21701step2 := by apply Matrix.ext; unfold raw21701step3 raw21701step2; decide +kernel
      have hl : raw21701step2Labels = labelEmbedding6 ∘ raw21701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21701step2 raw21701step2Labels raw21701step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw21702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21702step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -3, 1], ![3, -1, -2]]
def raw21702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21702step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw21702step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21702step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw21702step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21702 raw21702Labels = mixedMoment B node4138 node4138Labels := by
  calc
    mixedMoment B raw21702 raw21702Labels = mixedMoment B raw21702step0 raw21702step0Labels := by
      have hz : ∀ j, raw21702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21702step0 = (fun i j => raw21702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21702step0 raw21702; decide +kernel
      have hl : raw21702step0Labels = raw21702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21702 raw21702Labels permutation434 hz
    mixedMoment B raw21702step0 raw21702step0Labels = mixedMoment B raw21702step1 raw21702step1Labels := by
      have hz : ∀ j, raw21702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21702step1 = (fun i j => raw21702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21702step1 raw21702step0; decide +kernel
      have hl : raw21702step1Labels = raw21702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21702step0 raw21702step0Labels permutation80 hz
    mixedMoment B raw21702step1 raw21702step1Labels = mixedMoment B raw21702step2 raw21702step2Labels := by
      have hz : ∀ j, raw21702step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21702step2 = (fun i j => raw21702step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21702step2 raw21702step1; decide +kernel
      have hl : raw21702step2Labels = raw21702step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21702step1 raw21702step1Labels permutation14 hz
    mixedMoment B raw21702step2 raw21702step2Labels = mixedMoment B raw21702step3 raw21702step3Labels := by
      have ha : raw21702step3 = (fun i j => raw21702step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21702step3 raw21702step2; decide +kernel
      have hl : raw21702step3Labels = raw21702step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21702step2 raw21702step2Labels permutation2 permutation3
    mixedMoment B raw21702step3 raw21702step3Labels = mixedMoment B raw21702step4 raw21702step4Labels := by
      have ha : raw21702step4 = raw21702step3 := by apply Matrix.ext; unfold raw21702step4 raw21702step3; decide +kernel
      have hl : raw21702step3Labels = labelEmbedding6 ∘ raw21702step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21702step3 raw21702step3Labels raw21702step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4138 node4138Labels := by rfl

def raw21703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21703step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21703step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21703step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21703 raw21703Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw21703 raw21703Labels = mixedMoment B raw21703step0 raw21703step0Labels := by
      have hz : ∀ j, raw21703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21703step0 = (fun i j => raw21703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21703step0 raw21703; decide +kernel
      have hl : raw21703step0Labels = raw21703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21703 raw21703Labels permutation434 hz
    mixedMoment B raw21703step0 raw21703step0Labels = mixedMoment B raw21703step1 raw21703step1Labels := by
      have hz : ∀ j, raw21703step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21703step1 = (fun i j => raw21703step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21703step1 raw21703step0; decide +kernel
      have hl : raw21703step1Labels = raw21703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21703step0 raw21703step0Labels permutation80 hz
    mixedMoment B raw21703step1 raw21703step1Labels = mixedMoment B raw21703step2 raw21703step2Labels := by
      have ha : raw21703step2 = (fun i j => raw21703step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21703step2 raw21703step1; decide +kernel
      have hl : raw21703step2Labels = raw21703step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21703step1 raw21703step1Labels permutation8 permutation3
    mixedMoment B raw21703step2 raw21703step2Labels = mixedMoment B raw21703step3 raw21703step3Labels := by
      have ha : raw21703step3 = raw21703step2 := by apply Matrix.ext; unfold raw21703step3 raw21703step2; decide +kernel
      have hl : raw21703step2Labels = labelEmbedding6 ∘ raw21703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21703step2 raw21703step2Labels raw21703step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

def raw21704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21704step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21704step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21704 raw21704Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw21704 raw21704Labels = mixedMoment B raw21704step0 raw21704step0Labels := by
      have hz : ∀ j, raw21704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21704step0 = (fun i j => raw21704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21704step0 raw21704; decide +kernel
      have hl : raw21704step0Labels = raw21704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21704 raw21704Labels permutation434 hz
    mixedMoment B raw21704step0 raw21704step0Labels = mixedMoment B raw21704step1 raw21704step1Labels := by
      have hz : ∀ j, raw21704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21704step1 = (fun i j => raw21704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21704step1 raw21704step0; decide +kernel
      have hl : raw21704step1Labels = raw21704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21704step0 raw21704step0Labels permutation56 hz
    mixedMoment B raw21704step1 raw21704step1Labels = mixedMoment B raw21704step2 raw21704step2Labels := by
      have ha : raw21704step2 = (fun i j => raw21704step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21704step2 raw21704step1; decide +kernel
      have hl : raw21704step2Labels = raw21704step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21704step1 raw21704step1Labels permutation8 permutation3
    mixedMoment B raw21704step2 raw21704step2Labels = mixedMoment B raw21704step3 raw21704step3Labels := by
      have ha : raw21704step3 = raw21704step2 := by apply Matrix.ext; unfold raw21704step3 raw21704step2; decide +kernel
      have hl : raw21704step2Labels = labelEmbedding6 ∘ raw21704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21704step2 raw21704step2Labels raw21704step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

def raw21705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21705step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21705step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21705 raw21705Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw21705 raw21705Labels = mixedMoment B raw21705step0 raw21705step0Labels := by
      have hz : ∀ j, raw21705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21705step0 = (fun i j => raw21705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21705step0 raw21705; decide +kernel
      have hl : raw21705step0Labels = raw21705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21705 raw21705Labels permutation346 hz
    mixedMoment B raw21705step0 raw21705step0Labels = mixedMoment B raw21705step1 raw21705step1Labels := by
      have hz : ∀ j, raw21705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21705step1 = (fun i j => raw21705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21705step1 raw21705step0; decide +kernel
      have hl : raw21705step1Labels = raw21705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21705step0 raw21705step0Labels permutation56 hz
    mixedMoment B raw21705step1 raw21705step1Labels = mixedMoment B raw21705step2 raw21705step2Labels := by
      have ha : raw21705step2 = (fun i j => raw21705step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21705step2 raw21705step1; decide +kernel
      have hl : raw21705step2Labels = raw21705step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21705step1 raw21705step1Labels permutation8 permutation3
    mixedMoment B raw21705step2 raw21705step2Labels = mixedMoment B raw21705step3 raw21705step3Labels := by
      have ha : raw21705step3 = raw21705step2 := by apply Matrix.ext; unfold raw21705step3 raw21705step2; decide +kernel
      have hl : raw21705step2Labels = labelEmbedding6 ∘ raw21705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21705step2 raw21705step2Labels raw21705step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

def raw21706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21706step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![4, -2, -2]]
def raw21706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21706step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw21706step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21706step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw21706step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21706 raw21706Labels = mixedMoment B node4134 node4134Labels := by
  calc
    mixedMoment B raw21706 raw21706Labels = mixedMoment B raw21706step0 raw21706step0Labels := by
      have hz : ∀ j, raw21706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21706step0 = (fun i j => raw21706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21706step0 raw21706; decide +kernel
      have hl : raw21706step0Labels = raw21706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21706 raw21706Labels permutation434 hz
    mixedMoment B raw21706step0 raw21706step0Labels = mixedMoment B raw21706step1 raw21706step1Labels := by
      have hz : ∀ j, raw21706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21706step1 = (fun i j => raw21706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21706step1 raw21706step0; decide +kernel
      have hl : raw21706step1Labels = raw21706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21706step0 raw21706step0Labels permutation80 hz
    mixedMoment B raw21706step1 raw21706step1Labels = mixedMoment B raw21706step2 raw21706step2Labels := by
      have hz : ∀ j, raw21706step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21706step2 = (fun i j => raw21706step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21706step2 raw21706step1; decide +kernel
      have hl : raw21706step2Labels = raw21706step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21706step1 raw21706step1Labels permutation14 hz
    mixedMoment B raw21706step2 raw21706step2Labels = mixedMoment B raw21706step3 raw21706step3Labels := by
      have ha : raw21706step3 = (fun i j => raw21706step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21706step3 raw21706step2; decide +kernel
      have hl : raw21706step3Labels = raw21706step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21706step2 raw21706step2Labels permutation2 permutation3
    mixedMoment B raw21706step3 raw21706step3Labels = mixedMoment B raw21706step4 raw21706step4Labels := by
      have ha : raw21706step4 = raw21706step3 := by apply Matrix.ext; unfold raw21706step4 raw21706step3; decide +kernel
      have hl : raw21706step3Labels = labelEmbedding6 ∘ raw21706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21706step3 raw21706step3Labels raw21706step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4134 node4134Labels := by rfl

def raw21707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21707step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21707step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21707 raw21707Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw21707 raw21707Labels = mixedMoment B raw21707step0 raw21707step0Labels := by
      have hz : ∀ j, raw21707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21707step0 = (fun i j => raw21707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21707step0 raw21707; decide +kernel
      have hl : raw21707step0Labels = raw21707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21707 raw21707Labels permutation434 hz
    mixedMoment B raw21707step0 raw21707step0Labels = mixedMoment B raw21707step1 raw21707step1Labels := by
      have hz : ∀ j, raw21707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21707step1 = (fun i j => raw21707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21707step1 raw21707step0; decide +kernel
      have hl : raw21707step1Labels = raw21707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21707step0 raw21707step0Labels permutation80 hz
    mixedMoment B raw21707step1 raw21707step1Labels = mixedMoment B raw21707step2 raw21707step2Labels := by
      have ha : raw21707step2 = (fun i j => raw21707step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21707step2 raw21707step1; decide +kernel
      have hl : raw21707step2Labels = raw21707step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21707step1 raw21707step1Labels permutation8 permutation3
    mixedMoment B raw21707step2 raw21707step2Labels = mixedMoment B raw21707step3 raw21707step3Labels := by
      have ha : raw21707step3 = raw21707step2 := by apply Matrix.ext; unfold raw21707step3 raw21707step2; decide +kernel
      have hl : raw21707step2Labels = labelEmbedding6 ∘ raw21707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21707step2 raw21707step2Labels raw21707step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

def raw21708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21708step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21708 raw21708Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw21708 raw21708Labels = mixedMoment B raw21708step0 raw21708step0Labels := by
      have hz : ∀ j, raw21708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21708step0 = (fun i j => raw21708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21708step0 raw21708; decide +kernel
      have hl : raw21708step0Labels = raw21708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21708 raw21708Labels permutation434 hz
    mixedMoment B raw21708step0 raw21708step0Labels = mixedMoment B raw21708step1 raw21708step1Labels := by
      have hz : ∀ j, raw21708step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21708step1 = (fun i j => raw21708step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21708step1 raw21708step0; decide +kernel
      have hl : raw21708step1Labels = raw21708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21708step0 raw21708step0Labels permutation56 hz
    mixedMoment B raw21708step1 raw21708step1Labels = mixedMoment B raw21708step2 raw21708step2Labels := by
      have ha : raw21708step2 = (fun i j => raw21708step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21708step2 raw21708step1; decide +kernel
      have hl : raw21708step2Labels = raw21708step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21708step1 raw21708step1Labels permutation8 permutation3
    mixedMoment B raw21708step2 raw21708step2Labels = mixedMoment B raw21708step3 raw21708step3Labels := by
      have ha : raw21708step3 = raw21708step2 := by apply Matrix.ext; unfold raw21708step3 raw21708step2; decide +kernel
      have hl : raw21708step2Labels = labelEmbedding6 ∘ raw21708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21708step2 raw21708step2Labels raw21708step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

def raw21709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21709step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21709step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21709 raw21709Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw21709 raw21709Labels = mixedMoment B raw21709step0 raw21709step0Labels := by
      have hz : ∀ j, raw21709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21709step0 = (fun i j => raw21709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21709step0 raw21709; decide +kernel
      have hl : raw21709step0Labels = raw21709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21709 raw21709Labels permutation346 hz
    mixedMoment B raw21709step0 raw21709step0Labels = mixedMoment B raw21709step1 raw21709step1Labels := by
      have hz : ∀ j, raw21709step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21709step1 = (fun i j => raw21709step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21709step1 raw21709step0; decide +kernel
      have hl : raw21709step1Labels = raw21709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21709step0 raw21709step0Labels permutation56 hz
    mixedMoment B raw21709step1 raw21709step1Labels = mixedMoment B raw21709step2 raw21709step2Labels := by
      have ha : raw21709step2 = (fun i j => raw21709step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21709step2 raw21709step1; decide +kernel
      have hl : raw21709step2Labels = raw21709step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21709step1 raw21709step1Labels permutation8 permutation3
    mixedMoment B raw21709step2 raw21709step2Labels = mixedMoment B raw21709step3 raw21709step3Labels := by
      have ha : raw21709step3 = raw21709step2 := by apply Matrix.ext; unfold raw21709step3 raw21709step2; decide +kernel
      have hl : raw21709step2Labels = labelEmbedding6 ∘ raw21709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21709step2 raw21709step2Labels raw21709step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

def raw21710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw21710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw21710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw21710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21710step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![4, -2, -2]]
def raw21710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21710step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21710step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21710step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21710step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21710 raw21710Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw21710 raw21710Labels = mixedMoment B raw21710step0 raw21710step0Labels := by
      have hz : ∀ j, raw21710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21710step0 = (fun i j => raw21710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21710step0 raw21710; decide +kernel
      have hl : raw21710step0Labels = raw21710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21710 raw21710Labels permutation434 hz
    mixedMoment B raw21710step0 raw21710step0Labels = mixedMoment B raw21710step1 raw21710step1Labels := by
      have hz : ∀ j, raw21710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21710step1 = (fun i j => raw21710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21710step1 raw21710step0; decide +kernel
      have hl : raw21710step1Labels = raw21710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21710step0 raw21710step0Labels permutation80 hz
    mixedMoment B raw21710step1 raw21710step1Labels = mixedMoment B raw21710step2 raw21710step2Labels := by
      have hz : ∀ j, raw21710step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21710step2 = (fun i j => raw21710step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21710step2 raw21710step1; decide +kernel
      have hl : raw21710step2Labels = raw21710step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21710step1 raw21710step1Labels permutation14 hz
    mixedMoment B raw21710step2 raw21710step2Labels = mixedMoment B raw21710step3 raw21710step3Labels := by
      have ha : raw21710step3 = (fun i j => raw21710step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21710step3 raw21710step2; decide +kernel
      have hl : raw21710step3Labels = raw21710step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21710step2 raw21710step2Labels permutation2 permutation3
    mixedMoment B raw21710step3 raw21710step3Labels = mixedMoment B raw21710step4 raw21710step4Labels := by
      have ha : raw21710step4 = raw21710step3 := by apply Matrix.ext; unfold raw21710step4 raw21710step3; decide +kernel
      have hl : raw21710step3Labels = labelEmbedding6 ∘ raw21710step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21710step3 raw21710step3Labels raw21710step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw21711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21711step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21711step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw21711step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21711step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw21711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21711 raw21711Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw21711 raw21711Labels = mixedMoment B raw21711step0 raw21711step0Labels := by
      have hz : ∀ j, raw21711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21711step0 = (fun i j => raw21711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21711step0 raw21711; decide +kernel
      have hl : raw21711step0Labels = raw21711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21711 raw21711Labels permutation434 hz
    mixedMoment B raw21711step0 raw21711step0Labels = mixedMoment B raw21711step1 raw21711step1Labels := by
      have hz : ∀ j, raw21711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21711step1 = (fun i j => raw21711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21711step1 raw21711step0; decide +kernel
      have hl : raw21711step1Labels = raw21711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21711step0 raw21711step0Labels permutation80 hz
    mixedMoment B raw21711step1 raw21711step1Labels = mixedMoment B raw21711step2 raw21711step2Labels := by
      have hz : ∀ j, raw21711step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21711step2 = (fun i j => raw21711step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21711step2 raw21711step1; decide +kernel
      have hl : raw21711step2Labels = raw21711step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21711step1 raw21711step1Labels permutation14 hz
    mixedMoment B raw21711step2 raw21711step2Labels = mixedMoment B raw21711step3 raw21711step3Labels := by
      have ha : raw21711step3 = (fun i j => raw21711step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21711step3 raw21711step2; decide +kernel
      have hl : raw21711step3Labels = raw21711step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21711step2 raw21711step2Labels permutation2 permutation3
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw21712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21712step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21712 raw21712Labels = mixedMoment B node559 node559Labels := by
  calc
    mixedMoment B raw21712 raw21712Labels = mixedMoment B raw21712step0 raw21712step0Labels := by
      have hz : ∀ j, raw21712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21712step0 = (fun i j => raw21712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21712step0 raw21712; decide +kernel
      have hl : raw21712step0Labels = raw21712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21712 raw21712Labels permutation434 hz
    mixedMoment B raw21712step0 raw21712step0Labels = mixedMoment B raw21712step1 raw21712step1Labels := by
      have hz : ∀ j, raw21712step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21712step1 = (fun i j => raw21712step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21712step1 raw21712step0; decide +kernel
      have hl : raw21712step1Labels = raw21712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21712step0 raw21712step0Labels permutation80 hz
    mixedMoment B raw21712step1 raw21712step1Labels = mixedMoment B raw21712step2 raw21712step2Labels := by
      have ha : raw21712step2 = (fun i j => raw21712step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21712step2 raw21712step1; decide +kernel
      have hl : raw21712step2Labels = raw21712step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21712step1 raw21712step1Labels permutation8 permutation3
    _ = mixedMoment B node559 node559Labels := by rfl

def raw21713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21713 raw21713Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw21713 raw21713Labels = mixedMoment B raw21713step0 raw21713step0Labels := by
      have hz : ∀ j, raw21713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21713step0 = (fun i j => raw21713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21713step0 raw21713; decide +kernel
      have hl : raw21713step0Labels = raw21713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21713 raw21713Labels permutation434 hz
    mixedMoment B raw21713step0 raw21713step0Labels = mixedMoment B raw21713step1 raw21713step1Labels := by
      have ha : raw21713step1 = (fun i j => raw21713step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21713step1 raw21713step0; decide +kernel
      have hl : raw21713step1Labels = raw21713step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21713step0 raw21713step0Labels permutation38 permutation3
    _ = mixedMoment B node887 node887Labels := by rfl

def raw21714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21714 raw21714Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw21714 raw21714Labels = mixedMoment B raw21714step0 raw21714step0Labels := by
      have hz : ∀ j, raw21714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21714step0 = (fun i j => raw21714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21714step0 raw21714; decide +kernel
      have hl : raw21714step0Labels = raw21714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21714 raw21714Labels permutation346 hz
    mixedMoment B raw21714step0 raw21714step0Labels = mixedMoment B raw21714step1 raw21714step1Labels := by
      have ha : raw21714step1 = (fun i j => raw21714step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21714step1 raw21714step0; decide +kernel
      have hl : raw21714step1Labels = raw21714step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21714step0 raw21714step0Labels permutation38 permutation3
    _ = mixedMoment B node887 node887Labels := by rfl

def raw21715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21715step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21715step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21715 raw21715Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21715 raw21715Labels = mixedMoment B raw21715step0 raw21715step0Labels := by
      have hz : ∀ j, raw21715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21715step0 = (fun i j => raw21715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21715step0 raw21715; decide +kernel
      have hl : raw21715step0Labels = raw21715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21715 raw21715Labels permutation434 hz
    mixedMoment B raw21715step0 raw21715step0Labels = mixedMoment B raw21715step1 raw21715step1Labels := by
      have hz : ∀ j, raw21715step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21715step1 = (fun i j => raw21715step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21715step1 raw21715step0; decide +kernel
      have hl : raw21715step1Labels = raw21715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21715step0 raw21715step0Labels permutation80 hz
    mixedMoment B raw21715step1 raw21715step1Labels = mixedMoment B raw21715step2 raw21715step2Labels := by
      have ha : raw21715step2 = (fun i j => raw21715step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21715step2 raw21715step1; decide +kernel
      have hl : raw21715step2Labels = raw21715step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21715step1 raw21715step1Labels permutation10 permutation3
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw21716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21716step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21716step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21716 raw21716Labels = mixedMoment B node559 node559Labels := by
  calc
    mixedMoment B raw21716 raw21716Labels = mixedMoment B raw21716step0 raw21716step0Labels := by
      have hz : ∀ j, raw21716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21716step0 = (fun i j => raw21716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21716step0 raw21716; decide +kernel
      have hl : raw21716step0Labels = raw21716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21716 raw21716Labels permutation434 hz
    mixedMoment B raw21716step0 raw21716step0Labels = mixedMoment B raw21716step1 raw21716step1Labels := by
      have hz : ∀ j, raw21716step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21716step1 = (fun i j => raw21716step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21716step1 raw21716step0; decide +kernel
      have hl : raw21716step1Labels = raw21716step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21716step0 raw21716step0Labels permutation56 hz
    mixedMoment B raw21716step1 raw21716step1Labels = mixedMoment B raw21716step2 raw21716step2Labels := by
      have ha : raw21716step2 = (fun i j => raw21716step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21716step2 raw21716step1; decide +kernel
      have hl : raw21716step2Labels = raw21716step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21716step1 raw21716step1Labels permutation8 permutation3
    _ = mixedMoment B node559 node559Labels := by rfl

def raw21717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21717 raw21717Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw21717 raw21717Labels = mixedMoment B raw21717step0 raw21717step0Labels := by
      have hz : ∀ j, raw21717 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21717step0 = (fun i j => raw21717 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21717step0 raw21717; decide +kernel
      have hl : raw21717step0Labels = raw21717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21717 raw21717Labels permutation434 hz
    mixedMoment B raw21717step0 raw21717step0Labels = mixedMoment B raw21717step1 raw21717step1Labels := by
      have ha : raw21717step1 = (fun i j => raw21717step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21717step1 raw21717step0; decide +kernel
      have hl : raw21717step1Labels = raw21717step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21717step0 raw21717step0Labels permutation32 permutation3
    _ = mixedMoment B node887 node887Labels := by rfl

def raw21718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21718step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21718 raw21718Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw21718 raw21718Labels = mixedMoment B raw21718step0 raw21718step0Labels := by
      have hz : ∀ j, raw21718 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21718step0 = (fun i j => raw21718 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21718step0 raw21718; decide +kernel
      have hl : raw21718step0Labels = raw21718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21718 raw21718Labels permutation265 hz
    mixedMoment B raw21718step0 raw21718step0Labels = mixedMoment B raw21718step1 raw21718step1Labels := by
      have ha : raw21718step1 = (fun i j => raw21718step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21718step1 raw21718step0; decide +kernel
      have hl : raw21718step1Labels = raw21718step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21718step0 raw21718step0Labels permutation38 permutation3
    _ = mixedMoment B node887 node887Labels := by rfl

def raw21719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21719step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21719step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21719step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21719 raw21719Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21719 raw21719Labels = mixedMoment B raw21719step0 raw21719step0Labels := by
      have hz : ∀ j, raw21719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21719step0 = (fun i j => raw21719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21719step0 raw21719; decide +kernel
      have hl : raw21719step0Labels = raw21719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21719 raw21719Labels permutation434 hz
    mixedMoment B raw21719step0 raw21719step0Labels = mixedMoment B raw21719step1 raw21719step1Labels := by
      have hz : ∀ j, raw21719step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21719step1 = (fun i j => raw21719step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21719step1 raw21719step0; decide +kernel
      have hl : raw21719step1Labels = raw21719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21719step0 raw21719step0Labels permutation56 hz
    mixedMoment B raw21719step1 raw21719step1Labels = mixedMoment B raw21719step2 raw21719step2Labels := by
      have ha : raw21719step2 = (fun i j => raw21719step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21719step2 raw21719step1; decide +kernel
      have hl : raw21719step2Labels = raw21719step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21719step1 raw21719step1Labels permutation10 permutation3
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw21720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21720step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21720step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21720 raw21720Labels = mixedMoment B node559 node559Labels := by
  calc
    mixedMoment B raw21720 raw21720Labels = mixedMoment B raw21720step0 raw21720step0Labels := by
      have hz : ∀ j, raw21720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21720step0 = (fun i j => raw21720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21720step0 raw21720; decide +kernel
      have hl : raw21720step0Labels = raw21720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21720 raw21720Labels permutation346 hz
    mixedMoment B raw21720step0 raw21720step0Labels = mixedMoment B raw21720step1 raw21720step1Labels := by
      have hz : ∀ j, raw21720step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21720step1 = (fun i j => raw21720step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21720step1 raw21720step0; decide +kernel
      have hl : raw21720step1Labels = raw21720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21720step0 raw21720step0Labels permutation56 hz
    mixedMoment B raw21720step1 raw21720step1Labels = mixedMoment B raw21720step2 raw21720step2Labels := by
      have ha : raw21720step2 = (fun i j => raw21720step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21720step2 raw21720step1; decide +kernel
      have hl : raw21720step2Labels = raw21720step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21720step1 raw21720step1Labels permutation8 permutation3
    _ = mixedMoment B node559 node559Labels := by rfl

def raw21721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21721step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21721 raw21721Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw21721 raw21721Labels = mixedMoment B raw21721step0 raw21721step0Labels := by
      have hz : ∀ j, raw21721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21721step0 = (fun i j => raw21721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21721step0 raw21721; decide +kernel
      have hl : raw21721step0Labels = raw21721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21721 raw21721Labels permutation346 hz
    mixedMoment B raw21721step0 raw21721step0Labels = mixedMoment B raw21721step1 raw21721step1Labels := by
      have ha : raw21721step1 = (fun i j => raw21721step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21721step1 raw21721step0; decide +kernel
      have hl : raw21721step1Labels = raw21721step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21721step0 raw21721step0Labels permutation32 permutation3
    _ = mixedMoment B node887 node887Labels := by rfl

def raw21722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21722step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21722 raw21722Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw21722 raw21722Labels = mixedMoment B raw21722step0 raw21722step0Labels := by
      have hz : ∀ j, raw21722 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21722step0 = (fun i j => raw21722 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21722step0 raw21722; decide +kernel
      have hl : raw21722step0Labels = raw21722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21722 raw21722Labels permutation265 hz
    mixedMoment B raw21722step0 raw21722step0Labels = mixedMoment B raw21722step1 raw21722step1Labels := by
      have ha : raw21722step1 = (fun i j => raw21722step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21722step1 raw21722step0; decide +kernel
      have hl : raw21722step1Labels = raw21722step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21722step0 raw21722step0Labels permutation32 permutation3
    _ = mixedMoment B node887 node887Labels := by rfl

def raw21723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21723step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21723step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21723 raw21723Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21723 raw21723Labels = mixedMoment B raw21723step0 raw21723step0Labels := by
      have hz : ∀ j, raw21723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21723step0 = (fun i j => raw21723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21723step0 raw21723; decide +kernel
      have hl : raw21723step0Labels = raw21723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21723 raw21723Labels permutation346 hz
    mixedMoment B raw21723step0 raw21723step0Labels = mixedMoment B raw21723step1 raw21723step1Labels := by
      have hz : ∀ j, raw21723step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21723step1 = (fun i j => raw21723step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21723step1 raw21723step0; decide +kernel
      have hl : raw21723step1Labels = raw21723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21723step0 raw21723step0Labels permutation56 hz
    mixedMoment B raw21723step1 raw21723step1Labels = mixedMoment B raw21723step2 raw21723step2Labels := by
      have ha : raw21723step2 = (fun i j => raw21723step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21723step2 raw21723step1; decide +kernel
      have hl : raw21723step2Labels = raw21723step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21723step1 raw21723step1Labels permutation10 permutation3
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw21724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21724step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21724step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21724step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -3, 1], ![3, -1, -2]]
def raw21724step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21724step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw21724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21724 raw21724Labels = mixedMoment B node566 node566Labels := by
  calc
    mixedMoment B raw21724 raw21724Labels = mixedMoment B raw21724step0 raw21724step0Labels := by
      have hz : ∀ j, raw21724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21724step0 = (fun i j => raw21724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21724step0 raw21724; decide +kernel
      have hl : raw21724step0Labels = raw21724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21724 raw21724Labels permutation434 hz
    mixedMoment B raw21724step0 raw21724step0Labels = mixedMoment B raw21724step1 raw21724step1Labels := by
      have hz : ∀ j, raw21724step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21724step1 = (fun i j => raw21724step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21724step1 raw21724step0; decide +kernel
      have hl : raw21724step1Labels = raw21724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21724step0 raw21724step0Labels permutation80 hz
    mixedMoment B raw21724step1 raw21724step1Labels = mixedMoment B raw21724step2 raw21724step2Labels := by
      have hz : ∀ j, raw21724step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21724step2 = (fun i j => raw21724step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21724step2 raw21724step1; decide +kernel
      have hl : raw21724step2Labels = raw21724step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21724step1 raw21724step1Labels permutation14 hz
    mixedMoment B raw21724step2 raw21724step2Labels = mixedMoment B raw21724step3 raw21724step3Labels := by
      have ha : raw21724step3 = (fun i j => raw21724step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21724step3 raw21724step2; decide +kernel
      have hl : raw21724step3Labels = raw21724step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21724step2 raw21724step2Labels permutation2 permutation3
    _ = mixedMoment B node566 node566Labels := by rfl

def raw21725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21725step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21725step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21725 raw21725Labels = mixedMoment B node897 node897Labels := by
  calc
    mixedMoment B raw21725 raw21725Labels = mixedMoment B raw21725step0 raw21725step0Labels := by
      have hz : ∀ j, raw21725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21725step0 = (fun i j => raw21725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21725step0 raw21725; decide +kernel
      have hl : raw21725step0Labels = raw21725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21725 raw21725Labels permutation434 hz
    mixedMoment B raw21725step0 raw21725step0Labels = mixedMoment B raw21725step1 raw21725step1Labels := by
      have hz : ∀ j, raw21725step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21725step1 = (fun i j => raw21725step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21725step1 raw21725step0; decide +kernel
      have hl : raw21725step1Labels = raw21725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21725step0 raw21725step0Labels permutation80 hz
    mixedMoment B raw21725step1 raw21725step1Labels = mixedMoment B raw21725step2 raw21725step2Labels := by
      have ha : raw21725step2 = (fun i j => raw21725step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21725step2 raw21725step1; decide +kernel
      have hl : raw21725step2Labels = raw21725step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21725step1 raw21725step1Labels permutation8 permutation3
    _ = mixedMoment B node897 node897Labels := by rfl

def raw21726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21726step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21726step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21726 raw21726Labels = mixedMoment B node897 node897Labels := by
  calc
    mixedMoment B raw21726 raw21726Labels = mixedMoment B raw21726step0 raw21726step0Labels := by
      have hz : ∀ j, raw21726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21726step0 = (fun i j => raw21726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21726step0 raw21726; decide +kernel
      have hl : raw21726step0Labels = raw21726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21726 raw21726Labels permutation434 hz
    mixedMoment B raw21726step0 raw21726step0Labels = mixedMoment B raw21726step1 raw21726step1Labels := by
      have hz : ∀ j, raw21726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21726step1 = (fun i j => raw21726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21726step1 raw21726step0; decide +kernel
      have hl : raw21726step1Labels = raw21726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21726step0 raw21726step0Labels permutation56 hz
    mixedMoment B raw21726step1 raw21726step1Labels = mixedMoment B raw21726step2 raw21726step2Labels := by
      have ha : raw21726step2 = (fun i j => raw21726step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21726step2 raw21726step1; decide +kernel
      have hl : raw21726step2Labels = raw21726step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21726step1 raw21726step1Labels permutation8 permutation3
    _ = mixedMoment B node897 node897Labels := by rfl

def raw21727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw21727step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw21727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21727 raw21727Labels = mixedMoment B node897 node897Labels := by
  calc
    mixedMoment B raw21727 raw21727Labels = mixedMoment B raw21727step0 raw21727step0Labels := by
      have hz : ∀ j, raw21727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21727step0 = (fun i j => raw21727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21727step0 raw21727; decide +kernel
      have hl : raw21727step0Labels = raw21727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21727 raw21727Labels permutation346 hz
    mixedMoment B raw21727step0 raw21727step0Labels = mixedMoment B raw21727step1 raw21727step1Labels := by
      have hz : ∀ j, raw21727step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21727step1 = (fun i j => raw21727step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21727step1 raw21727step0; decide +kernel
      have hl : raw21727step1Labels = raw21727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21727step0 raw21727step0Labels permutation56 hz
    mixedMoment B raw21727step1 raw21727step1Labels = mixedMoment B raw21727step2 raw21727step2Labels := by
      have ha : raw21727step2 = (fun i j => raw21727step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21727step2 raw21727step1; decide +kernel
      have hl : raw21727step2Labels = raw21727step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21727step1 raw21727step1Labels permutation8 permutation3
    _ = mixedMoment B node897 node897Labels := by rfl

def raw21728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21728step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21728step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![4, -2, -2]]
def raw21728step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21728step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw21728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21728 raw21728Labels = mixedMoment B node564 node564Labels := by
  calc
    mixedMoment B raw21728 raw21728Labels = mixedMoment B raw21728step0 raw21728step0Labels := by
      have hz : ∀ j, raw21728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21728step0 = (fun i j => raw21728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21728step0 raw21728; decide +kernel
      have hl : raw21728step0Labels = raw21728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21728 raw21728Labels permutation434 hz
    mixedMoment B raw21728step0 raw21728step0Labels = mixedMoment B raw21728step1 raw21728step1Labels := by
      have hz : ∀ j, raw21728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21728step1 = (fun i j => raw21728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21728step1 raw21728step0; decide +kernel
      have hl : raw21728step1Labels = raw21728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21728step0 raw21728step0Labels permutation80 hz
    mixedMoment B raw21728step1 raw21728step1Labels = mixedMoment B raw21728step2 raw21728step2Labels := by
      have hz : ∀ j, raw21728step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21728step2 = (fun i j => raw21728step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21728step2 raw21728step1; decide +kernel
      have hl : raw21728step2Labels = raw21728step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21728step1 raw21728step1Labels permutation14 hz
    mixedMoment B raw21728step2 raw21728step2Labels = mixedMoment B raw21728step3 raw21728step3Labels := by
      have ha : raw21728step3 = (fun i j => raw21728step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21728step3 raw21728step2; decide +kernel
      have hl : raw21728step3Labels = raw21728step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21728step2 raw21728step2Labels permutation2 permutation3
    _ = mixedMoment B node564 node564Labels := by rfl

def raw21729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21729step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21729 raw21729Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw21729 raw21729Labels = mixedMoment B raw21729step0 raw21729step0Labels := by
      have hz : ∀ j, raw21729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21729step0 = (fun i j => raw21729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21729step0 raw21729; decide +kernel
      have hl : raw21729step0Labels = raw21729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21729 raw21729Labels permutation434 hz
    mixedMoment B raw21729step0 raw21729step0Labels = mixedMoment B raw21729step1 raw21729step1Labels := by
      have hz : ∀ j, raw21729step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21729step1 = (fun i j => raw21729step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21729step1 raw21729step0; decide +kernel
      have hl : raw21729step1Labels = raw21729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21729step0 raw21729step0Labels permutation80 hz
    mixedMoment B raw21729step1 raw21729step1Labels = mixedMoment B raw21729step2 raw21729step2Labels := by
      have ha : raw21729step2 = (fun i j => raw21729step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21729step2 raw21729step1; decide +kernel
      have hl : raw21729step2Labels = raw21729step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21729step1 raw21729step1Labels permutation8 permutation3
    _ = mixedMoment B node893 node893Labels := by rfl

def raw21730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21730step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21730 raw21730Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw21730 raw21730Labels = mixedMoment B raw21730step0 raw21730step0Labels := by
      have hz : ∀ j, raw21730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21730step0 = (fun i j => raw21730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21730step0 raw21730; decide +kernel
      have hl : raw21730step0Labels = raw21730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21730 raw21730Labels permutation434 hz
    mixedMoment B raw21730step0 raw21730step0Labels = mixedMoment B raw21730step1 raw21730step1Labels := by
      have hz : ∀ j, raw21730step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21730step1 = (fun i j => raw21730step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21730step1 raw21730step0; decide +kernel
      have hl : raw21730step1Labels = raw21730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21730step0 raw21730step0Labels permutation56 hz
    mixedMoment B raw21730step1 raw21730step1Labels = mixedMoment B raw21730step2 raw21730step2Labels := by
      have ha : raw21730step2 = (fun i j => raw21730step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21730step2 raw21730step1; decide +kernel
      have hl : raw21730step2Labels = raw21730step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21730step1 raw21730step1Labels permutation8 permutation3
    _ = mixedMoment B node893 node893Labels := by rfl

def raw21731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -2, -2]]
def raw21731step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21731 raw21731Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw21731 raw21731Labels = mixedMoment B raw21731step0 raw21731step0Labels := by
      have hz : ∀ j, raw21731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21731step0 = (fun i j => raw21731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21731step0 raw21731; decide +kernel
      have hl : raw21731step0Labels = raw21731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21731 raw21731Labels permutation346 hz
    mixedMoment B raw21731step0 raw21731step0Labels = mixedMoment B raw21731step1 raw21731step1Labels := by
      have hz : ∀ j, raw21731step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21731step1 = (fun i j => raw21731step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21731step1 raw21731step0; decide +kernel
      have hl : raw21731step1Labels = raw21731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21731step0 raw21731step0Labels permutation56 hz
    mixedMoment B raw21731step1 raw21731step1Labels = mixedMoment B raw21731step2 raw21731step2Labels := by
      have ha : raw21731step2 = (fun i j => raw21731step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21731step2 raw21731step1; decide +kernel
      have hl : raw21731step2Labels = raw21731step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21731step1 raw21731step1Labels permutation8 permutation3
    _ = mixedMoment B node893 node893Labels := by rfl

def raw21732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw21732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw21732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw21732step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21732step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![4, -2, -2]]
def raw21732step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21732step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21732 raw21732Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw21732 raw21732Labels = mixedMoment B raw21732step0 raw21732step0Labels := by
      have hz : ∀ j, raw21732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21732step0 = (fun i j => raw21732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21732step0 raw21732; decide +kernel
      have hl : raw21732step0Labels = raw21732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21732 raw21732Labels permutation434 hz
    mixedMoment B raw21732step0 raw21732step0Labels = mixedMoment B raw21732step1 raw21732step1Labels := by
      have hz : ∀ j, raw21732step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21732step1 = (fun i j => raw21732step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21732step1 raw21732step0; decide +kernel
      have hl : raw21732step1Labels = raw21732step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21732step0 raw21732step0Labels permutation80 hz
    mixedMoment B raw21732step1 raw21732step1Labels = mixedMoment B raw21732step2 raw21732step2Labels := by
      have hz : ∀ j, raw21732step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21732step2 = (fun i j => raw21732step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21732step2 raw21732step1; decide +kernel
      have hl : raw21732step2Labels = raw21732step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21732step1 raw21732step1Labels permutation14 hz
    mixedMoment B raw21732step2 raw21732step2Labels = mixedMoment B raw21732step3 raw21732step3Labels := by
      have ha : raw21732step3 = (fun i j => raw21732step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21732step3 raw21732step2; decide +kernel
      have hl : raw21732step3Labels = raw21732step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21732step2 raw21732step2Labels permutation2 permutation3
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw21733 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21733step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21733step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21733step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21733 raw21733Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw21733 raw21733Labels = mixedMoment B raw21733step0 raw21733step0Labels := by
      have hz : ∀ j, raw21733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21733step0 = (fun i j => raw21733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21733step0 raw21733; decide +kernel
      have hl : raw21733step0Labels = raw21733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21733 raw21733Labels permutation434 hz
    mixedMoment B raw21733step0 raw21733step0Labels = mixedMoment B raw21733step1 raw21733step1Labels := by
      have hz : ∀ j, raw21733step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21733step1 = (fun i j => raw21733step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21733step1 raw21733step0; decide +kernel
      have hl : raw21733step1Labels = raw21733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21733step0 raw21733step0Labels permutation80 hz
    mixedMoment B raw21733step1 raw21733step1Labels = mixedMoment B raw21733step2 raw21733step2Labels := by
      have ha : raw21733step2 = (fun i j => raw21733step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21733step2 raw21733step1; decide +kernel
      have hl : raw21733step2Labels = raw21733step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21733step1 raw21733step1Labels permutation8 permutation6
    mixedMoment B raw21733step2 raw21733step2Labels = mixedMoment B raw21733step3 raw21733step3Labels := by
      have ha : raw21733step3 = raw21733step2 := by apply Matrix.ext; unfold raw21733step3 raw21733step2; decide +kernel
      have hl : raw21733step2Labels = labelEmbedding9 ∘ raw21733step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21733step2 raw21733step2Labels raw21733step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw21734 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21734step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21734step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21734step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21734step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21734 raw21734Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw21734 raw21734Labels = mixedMoment B raw21734step0 raw21734step0Labels := by
      have hz : ∀ j, raw21734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21734step0 = (fun i j => raw21734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21734step0 raw21734; decide +kernel
      have hl : raw21734step0Labels = raw21734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21734 raw21734Labels permutation434 hz
    mixedMoment B raw21734step0 raw21734step0Labels = mixedMoment B raw21734step1 raw21734step1Labels := by
      have hz : ∀ j, raw21734step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21734step1 = (fun i j => raw21734step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21734step1 raw21734step0; decide +kernel
      have hl : raw21734step1Labels = raw21734step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21734step0 raw21734step0Labels permutation56 hz
    mixedMoment B raw21734step1 raw21734step1Labels = mixedMoment B raw21734step2 raw21734step2Labels := by
      have ha : raw21734step2 = (fun i j => raw21734step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21734step2 raw21734step1; decide +kernel
      have hl : raw21734step2Labels = raw21734step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21734step1 raw21734step1Labels permutation8 permutation6
    mixedMoment B raw21734step2 raw21734step2Labels = mixedMoment B raw21734step3 raw21734step3Labels := by
      have ha : raw21734step3 = raw21734step2 := by apply Matrix.ext; unfold raw21734step3 raw21734step2; decide +kernel
      have hl : raw21734step2Labels = labelEmbedding9 ∘ raw21734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21734step2 raw21734step2Labels raw21734step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw21735 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21735step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-3, 0, 3]]
def raw21735step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21735step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw21735step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21735step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw21735step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21735 raw21735Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw21735 raw21735Labels = mixedMoment B raw21735step0 raw21735step0Labels := by
      have hz : ∀ j, raw21735 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21735step0 = (fun i j => raw21735 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21735step0 raw21735; decide +kernel
      have hl : raw21735step0Labels = raw21735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21735 raw21735Labels permutation434 hz
    mixedMoment B raw21735step0 raw21735step0Labels = mixedMoment B raw21735step1 raw21735step1Labels := by
      have hz : ∀ j, raw21735step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21735step1 = (fun i j => raw21735step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21735step1 raw21735step0; decide +kernel
      have hl : raw21735step1Labels = raw21735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21735step0 raw21735step0Labels permutation80 hz
    mixedMoment B raw21735step1 raw21735step1Labels = mixedMoment B raw21735step2 raw21735step2Labels := by
      have hz : ∀ j, raw21735step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21735step2 = (fun i j => raw21735step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21735step2 raw21735step1; decide +kernel
      have hl : raw21735step2Labels = raw21735step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21735step1 raw21735step1Labels permutation14 hz
    mixedMoment B raw21735step2 raw21735step2Labels = mixedMoment B raw21735step3 raw21735step3Labels := by
      have ha : raw21735step3 = (fun i j => raw21735step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21735step3 raw21735step2; decide +kernel
      have hl : raw21735step3Labels = raw21735step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21735step2 raw21735step2Labels permutation2 permutation7
    mixedMoment B raw21735step3 raw21735step3Labels = mixedMoment B raw21735step4 raw21735step4Labels := by
      have ha : raw21735step4 = raw21735step3 := by apply Matrix.ext; unfold raw21735step4 raw21735step3; decide +kernel
      have hl : raw21735step3Labels = labelEmbedding10 ∘ raw21735step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21735step3 raw21735step3Labels raw21735step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

def raw21736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21736step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21736step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21736step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21736 raw21736Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw21736 raw21736Labels = mixedMoment B raw21736step0 raw21736step0Labels := by
      have hz : ∀ j, raw21736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21736step0 = (fun i j => raw21736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21736step0 raw21736; decide +kernel
      have hl : raw21736step0Labels = raw21736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21736 raw21736Labels permutation434 hz
    mixedMoment B raw21736step0 raw21736step0Labels = mixedMoment B raw21736step1 raw21736step1Labels := by
      have hz : ∀ j, raw21736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21736step1 = (fun i j => raw21736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21736step1 raw21736step0; decide +kernel
      have hl : raw21736step1Labels = raw21736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21736step0 raw21736step0Labels permutation56 hz
    mixedMoment B raw21736step1 raw21736step1Labels = mixedMoment B raw21736step2 raw21736step2Labels := by
      have ha : raw21736step2 = (fun i j => raw21736step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21736step2 raw21736step1; decide +kernel
      have hl : raw21736step2Labels = raw21736step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21736step1 raw21736step1Labels permutation8 permutation6
    mixedMoment B raw21736step2 raw21736step2Labels = mixedMoment B raw21736step3 raw21736step3Labels := by
      have ha : raw21736step3 = raw21736step2 := by apply Matrix.ext; unfold raw21736step3 raw21736step2; decide +kernel
      have hl : raw21736step2Labels = labelEmbedding9 ∘ raw21736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21736step2 raw21736step2Labels raw21736step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw21737 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21737step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21737step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21737 raw21737Labels = mixedMoment B node4402 node4402Labels := by
  calc
    mixedMoment B raw21737 raw21737Labels = mixedMoment B raw21737step0 raw21737step0Labels := by
      have hz : ∀ j, raw21737 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21737step0 = (fun i j => raw21737 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21737step0 raw21737; decide +kernel
      have hl : raw21737step0Labels = raw21737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21737 raw21737Labels permutation434 hz
    mixedMoment B raw21737step0 raw21737step0Labels = mixedMoment B raw21737step1 raw21737step1Labels := by
      have ha : raw21737step1 = (fun i j => raw21737step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21737step1 raw21737step0; decide +kernel
      have hl : raw21737step1Labels = raw21737step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21737step0 raw21737step0Labels permutation32 permutation6
    mixedMoment B raw21737step1 raw21737step1Labels = mixedMoment B raw21737step2 raw21737step2Labels := by
      have ha : raw21737step2 = raw21737step1 := by apply Matrix.ext; unfold raw21737step2 raw21737step1; decide +kernel
      have hl : raw21737step1Labels = labelEmbedding9 ∘ raw21737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21737step1 raw21737step1Labels raw21737step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4402 node4402Labels := by rfl

def raw21738 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21738step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21738step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21738 raw21738Labels = mixedMoment B node4402 node4402Labels := by
  calc
    mixedMoment B raw21738 raw21738Labels = mixedMoment B raw21738step0 raw21738step0Labels := by
      have hz : ∀ j, raw21738 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21738step0 = (fun i j => raw21738 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21738step0 raw21738; decide +kernel
      have hl : raw21738step0Labels = raw21738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21738 raw21738Labels permutation265 hz
    mixedMoment B raw21738step0 raw21738step0Labels = mixedMoment B raw21738step1 raw21738step1Labels := by
      have ha : raw21738step1 = (fun i j => raw21738step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21738step1 raw21738step0; decide +kernel
      have hl : raw21738step1Labels = raw21738step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21738step0 raw21738step0Labels permutation38 permutation6
    mixedMoment B raw21738step1 raw21738step1Labels = mixedMoment B raw21738step2 raw21738step2Labels := by
      have ha : raw21738step2 = raw21738step1 := by apply Matrix.ext; unfold raw21738step2 raw21738step1; decide +kernel
      have hl : raw21738step1Labels = labelEmbedding9 ∘ raw21738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21738step1 raw21738step1Labels raw21738step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4402 node4402Labels := by rfl

def raw21739 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21739step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21739step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21739step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21739step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21739 raw21739Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw21739 raw21739Labels = mixedMoment B raw21739step0 raw21739step0Labels := by
      have hz : ∀ j, raw21739 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21739step0 = (fun i j => raw21739 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21739step0 raw21739; decide +kernel
      have hl : raw21739step0Labels = raw21739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21739 raw21739Labels permutation434 hz
    mixedMoment B raw21739step0 raw21739step0Labels = mixedMoment B raw21739step1 raw21739step1Labels := by
      have hz : ∀ j, raw21739step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21739step1 = (fun i j => raw21739step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21739step1 raw21739step0; decide +kernel
      have hl : raw21739step1Labels = raw21739step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21739step0 raw21739step0Labels permutation56 hz
    mixedMoment B raw21739step1 raw21739step1Labels = mixedMoment B raw21739step2 raw21739step2Labels := by
      have ha : raw21739step2 = (fun i j => raw21739step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21739step2 raw21739step1; decide +kernel
      have hl : raw21739step2Labels = raw21739step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21739step1 raw21739step1Labels permutation8 permutation6
    mixedMoment B raw21739step2 raw21739step2Labels = mixedMoment B raw21739step3 raw21739step3Labels := by
      have ha : raw21739step3 = raw21739step2 := by apply Matrix.ext; unfold raw21739step3 raw21739step2; decide +kernel
      have hl : raw21739step2Labels = labelEmbedding9 ∘ raw21739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21739step2 raw21739step2Labels raw21739step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw21740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21740step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21740step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21740step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21740step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21740 raw21740Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw21740 raw21740Labels = mixedMoment B raw21740step0 raw21740step0Labels := by
      have hz : ∀ j, raw21740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21740step0 = (fun i j => raw21740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21740step0 raw21740; decide +kernel
      have hl : raw21740step0Labels = raw21740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21740 raw21740Labels permutation346 hz
    mixedMoment B raw21740step0 raw21740step0Labels = mixedMoment B raw21740step1 raw21740step1Labels := by
      have hz : ∀ j, raw21740step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21740step1 = (fun i j => raw21740step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21740step1 raw21740step0; decide +kernel
      have hl : raw21740step1Labels = raw21740step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21740step0 raw21740step0Labels permutation56 hz
    mixedMoment B raw21740step1 raw21740step1Labels = mixedMoment B raw21740step2 raw21740step2Labels := by
      have ha : raw21740step2 = (fun i j => raw21740step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21740step2 raw21740step1; decide +kernel
      have hl : raw21740step2Labels = raw21740step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21740step1 raw21740step1Labels permutation8 permutation6
    mixedMoment B raw21740step2 raw21740step2Labels = mixedMoment B raw21740step3 raw21740step3Labels := by
      have ha : raw21740step3 = raw21740step2 := by apply Matrix.ext; unfold raw21740step3 raw21740step2; decide +kernel
      have hl : raw21740step2Labels = labelEmbedding9 ∘ raw21740step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21740step2 raw21740step2Labels raw21740step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw21741 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21741step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21741step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21741 raw21741Labels = mixedMoment B node4402 node4402Labels := by
  calc
    mixedMoment B raw21741 raw21741Labels = mixedMoment B raw21741step0 raw21741step0Labels := by
      have hz : ∀ j, raw21741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21741step0 = (fun i j => raw21741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21741step0 raw21741; decide +kernel
      have hl : raw21741step0Labels = raw21741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21741 raw21741Labels permutation346 hz
    mixedMoment B raw21741step0 raw21741step0Labels = mixedMoment B raw21741step1 raw21741step1Labels := by
      have ha : raw21741step1 = (fun i j => raw21741step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21741step1 raw21741step0; decide +kernel
      have hl : raw21741step1Labels = raw21741step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21741step0 raw21741step0Labels permutation32 permutation6
    mixedMoment B raw21741step1 raw21741step1Labels = mixedMoment B raw21741step2 raw21741step2Labels := by
      have ha : raw21741step2 = raw21741step1 := by apply Matrix.ext; unfold raw21741step2 raw21741step1; decide +kernel
      have hl : raw21741step1Labels = labelEmbedding9 ∘ raw21741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21741step1 raw21741step1Labels raw21741step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4402 node4402Labels := by rfl

def raw21742 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21742step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21742step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21742 raw21742Labels = mixedMoment B node4402 node4402Labels := by
  calc
    mixedMoment B raw21742 raw21742Labels = mixedMoment B raw21742step0 raw21742step0Labels := by
      have hz : ∀ j, raw21742 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21742step0 = (fun i j => raw21742 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21742step0 raw21742; decide +kernel
      have hl : raw21742step0Labels = raw21742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21742 raw21742Labels permutation265 hz
    mixedMoment B raw21742step0 raw21742step0Labels = mixedMoment B raw21742step1 raw21742step1Labels := by
      have ha : raw21742step1 = (fun i j => raw21742step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21742step1 raw21742step0; decide +kernel
      have hl : raw21742step1Labels = raw21742step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21742step0 raw21742step0Labels permutation32 permutation6
    mixedMoment B raw21742step1 raw21742step1Labels = mixedMoment B raw21742step2 raw21742step2Labels := by
      have ha : raw21742step2 = raw21742step1 := by apply Matrix.ext; unfold raw21742step2 raw21742step1; decide +kernel
      have hl : raw21742step1Labels = labelEmbedding9 ∘ raw21742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21742step1 raw21742step1Labels raw21742step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4402 node4402Labels := by rfl

def raw21743 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21743step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21743step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21743step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21743 raw21743Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw21743 raw21743Labels = mixedMoment B raw21743step0 raw21743step0Labels := by
      have hz : ∀ j, raw21743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21743step0 = (fun i j => raw21743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21743step0 raw21743; decide +kernel
      have hl : raw21743step0Labels = raw21743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21743 raw21743Labels permutation346 hz
    mixedMoment B raw21743step0 raw21743step0Labels = mixedMoment B raw21743step1 raw21743step1Labels := by
      have hz : ∀ j, raw21743step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21743step1 = (fun i j => raw21743step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21743step1 raw21743step0; decide +kernel
      have hl : raw21743step1Labels = raw21743step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21743step0 raw21743step0Labels permutation56 hz
    mixedMoment B raw21743step1 raw21743step1Labels = mixedMoment B raw21743step2 raw21743step2Labels := by
      have ha : raw21743step2 = (fun i j => raw21743step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21743step2 raw21743step1; decide +kernel
      have hl : raw21743step2Labels = raw21743step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21743step1 raw21743step1Labels permutation8 permutation6
    mixedMoment B raw21743step2 raw21743step2Labels = mixedMoment B raw21743step3 raw21743step3Labels := by
      have ha : raw21743step3 = raw21743step2 := by apply Matrix.ext; unfold raw21743step3 raw21743step2; decide +kernel
      have hl : raw21743step2Labels = labelEmbedding9 ∘ raw21743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21743step2 raw21743step2Labels raw21743step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw21744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21744step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21744step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![-2, -1, 3]]
def raw21744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21744step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw21744step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21744step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw21744step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21744step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw21744step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21744 raw21744Labels = mixedMoment B node4285 node4285Labels := by
  calc
    mixedMoment B raw21744 raw21744Labels = mixedMoment B raw21744step0 raw21744step0Labels := by
      have hz : ∀ j, raw21744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21744step0 = (fun i j => raw21744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21744step0 raw21744; decide +kernel
      have hl : raw21744step0Labels = raw21744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21744 raw21744Labels permutation434 hz
    mixedMoment B raw21744step0 raw21744step0Labels = mixedMoment B raw21744step1 raw21744step1Labels := by
      have hz : ∀ j, raw21744step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21744step1 = (fun i j => raw21744step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21744step1 raw21744step0; decide +kernel
      have hl : raw21744step1Labels = raw21744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21744step0 raw21744step0Labels permutation80 hz
    mixedMoment B raw21744step1 raw21744step1Labels = mixedMoment B raw21744step2 raw21744step2Labels := by
      have hz : ∀ j, raw21744step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21744step2 = (fun i j => raw21744step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21744step2 raw21744step1; decide +kernel
      have hl : raw21744step2Labels = raw21744step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21744step1 raw21744step1Labels permutation14 hz
    mixedMoment B raw21744step2 raw21744step2Labels = mixedMoment B raw21744step3 raw21744step3Labels := by
      have ha : raw21744step3 = (fun i j => raw21744step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21744step3 raw21744step2; decide +kernel
      have hl : raw21744step3Labels = raw21744step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21744step2 raw21744step2Labels permutation3 permutation4
    mixedMoment B raw21744step3 raw21744step3Labels = mixedMoment B raw21744step4 raw21744step4Labels := by
      have ha : raw21744step4 = -raw21744step3 := by apply Matrix.ext; change ∀ i j, raw21744step4 i j = -(raw21744step3 i j); unfold raw21744step4 raw21744step3; decide +kernel
      have hl : raw21744step4Labels = raw21744step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21744step4 raw21744step4Labels = mixedMoment B raw21744step5 raw21744step5Labels := by
      have ha : raw21744step5 = raw21744step4 := by apply Matrix.ext; unfold raw21744step5 raw21744step4; decide +kernel
      have hl : raw21744step4Labels = labelEmbedding7 ∘ raw21744step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21744step4 raw21744step4Labels raw21744step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4285 node4285Labels := by rfl

def raw21745 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21745step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21745step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21745step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21745 raw21745Labels = mixedMoment B node4429 node4429Labels := by
  calc
    mixedMoment B raw21745 raw21745Labels = mixedMoment B raw21745step0 raw21745step0Labels := by
      have hz : ∀ j, raw21745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21745step0 = (fun i j => raw21745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21745step0 raw21745; decide +kernel
      have hl : raw21745step0Labels = raw21745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21745 raw21745Labels permutation434 hz
    mixedMoment B raw21745step0 raw21745step0Labels = mixedMoment B raw21745step1 raw21745step1Labels := by
      have hz : ∀ j, raw21745step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21745step1 = (fun i j => raw21745step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21745step1 raw21745step0; decide +kernel
      have hl : raw21745step1Labels = raw21745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21745step0 raw21745step0Labels permutation80 hz
    mixedMoment B raw21745step1 raw21745step1Labels = mixedMoment B raw21745step2 raw21745step2Labels := by
      have ha : raw21745step2 = (fun i j => raw21745step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21745step2 raw21745step1; decide +kernel
      have hl : raw21745step2Labels = raw21745step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21745step1 raw21745step1Labels permutation8 permutation6
    mixedMoment B raw21745step2 raw21745step2Labels = mixedMoment B raw21745step3 raw21745step3Labels := by
      have ha : raw21745step3 = raw21745step2 := by apply Matrix.ext; unfold raw21745step3 raw21745step2; decide +kernel
      have hl : raw21745step2Labels = labelEmbedding9 ∘ raw21745step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21745step2 raw21745step2Labels raw21745step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4429 node4429Labels := by rfl

def raw21746 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21746step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21746step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21746step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21746 raw21746Labels = mixedMoment B node4429 node4429Labels := by
  calc
    mixedMoment B raw21746 raw21746Labels = mixedMoment B raw21746step0 raw21746step0Labels := by
      have hz : ∀ j, raw21746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21746step0 = (fun i j => raw21746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21746step0 raw21746; decide +kernel
      have hl : raw21746step0Labels = raw21746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21746 raw21746Labels permutation434 hz
    mixedMoment B raw21746step0 raw21746step0Labels = mixedMoment B raw21746step1 raw21746step1Labels := by
      have hz : ∀ j, raw21746step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21746step1 = (fun i j => raw21746step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21746step1 raw21746step0; decide +kernel
      have hl : raw21746step1Labels = raw21746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21746step0 raw21746step0Labels permutation56 hz
    mixedMoment B raw21746step1 raw21746step1Labels = mixedMoment B raw21746step2 raw21746step2Labels := by
      have ha : raw21746step2 = (fun i j => raw21746step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21746step2 raw21746step1; decide +kernel
      have hl : raw21746step2Labels = raw21746step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21746step1 raw21746step1Labels permutation8 permutation6
    mixedMoment B raw21746step2 raw21746step2Labels = mixedMoment B raw21746step3 raw21746step3Labels := by
      have ha : raw21746step3 = raw21746step2 := by apply Matrix.ext; unfold raw21746step3 raw21746step2; decide +kernel
      have hl : raw21746step2Labels = labelEmbedding9 ∘ raw21746step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21746step2 raw21746step2Labels raw21746step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4429 node4429Labels := by rfl

def raw21747 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21747step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21747step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21747step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21747step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21747step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21747 raw21747Labels = mixedMoment B node4429 node4429Labels := by
  calc
    mixedMoment B raw21747 raw21747Labels = mixedMoment B raw21747step0 raw21747step0Labels := by
      have hz : ∀ j, raw21747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21747step0 = (fun i j => raw21747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21747step0 raw21747; decide +kernel
      have hl : raw21747step0Labels = raw21747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21747 raw21747Labels permutation346 hz
    mixedMoment B raw21747step0 raw21747step0Labels = mixedMoment B raw21747step1 raw21747step1Labels := by
      have hz : ∀ j, raw21747step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21747step1 = (fun i j => raw21747step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21747step1 raw21747step0; decide +kernel
      have hl : raw21747step1Labels = raw21747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21747step0 raw21747step0Labels permutation56 hz
    mixedMoment B raw21747step1 raw21747step1Labels = mixedMoment B raw21747step2 raw21747step2Labels := by
      have ha : raw21747step2 = (fun i j => raw21747step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21747step2 raw21747step1; decide +kernel
      have hl : raw21747step2Labels = raw21747step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21747step1 raw21747step1Labels permutation8 permutation6
    mixedMoment B raw21747step2 raw21747step2Labels = mixedMoment B raw21747step3 raw21747step3Labels := by
      have ha : raw21747step3 = raw21747step2 := by apply Matrix.ext; unfold raw21747step3 raw21747step2; decide +kernel
      have hl : raw21747step2Labels = labelEmbedding9 ∘ raw21747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21747step2 raw21747step2Labels raw21747step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4429 node4429Labels := by rfl

def raw21748 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw21748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw21748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw21748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21748step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-3, 0, 3]]
def raw21748step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21748step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw21748step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21748step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw21748step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21748 raw21748Labels = mixedMoment B node4508 node4508Labels := by
  calc
    mixedMoment B raw21748 raw21748Labels = mixedMoment B raw21748step0 raw21748step0Labels := by
      have hz : ∀ j, raw21748 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21748step0 = (fun i j => raw21748 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21748step0 raw21748; decide +kernel
      have hl : raw21748step0Labels = raw21748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21748 raw21748Labels permutation434 hz
    mixedMoment B raw21748step0 raw21748step0Labels = mixedMoment B raw21748step1 raw21748step1Labels := by
      have hz : ∀ j, raw21748step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21748step1 = (fun i j => raw21748step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21748step1 raw21748step0; decide +kernel
      have hl : raw21748step1Labels = raw21748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21748step0 raw21748step0Labels permutation80 hz
    mixedMoment B raw21748step1 raw21748step1Labels = mixedMoment B raw21748step2 raw21748step2Labels := by
      have hz : ∀ j, raw21748step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21748step2 = (fun i j => raw21748step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21748step2 raw21748step1; decide +kernel
      have hl : raw21748step2Labels = raw21748step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21748step1 raw21748step1Labels permutation14 hz
    mixedMoment B raw21748step2 raw21748step2Labels = mixedMoment B raw21748step3 raw21748step3Labels := by
      have ha : raw21748step3 = (fun i j => raw21748step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21748step3 raw21748step2; decide +kernel
      have hl : raw21748step3Labels = raw21748step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21748step2 raw21748step2Labels permutation2 permutation6
    mixedMoment B raw21748step3 raw21748step3Labels = mixedMoment B raw21748step4 raw21748step4Labels := by
      have ha : raw21748step4 = raw21748step3 := by apply Matrix.ext; unfold raw21748step4 raw21748step3; decide +kernel
      have hl : raw21748step3Labels = labelEmbedding9 ∘ raw21748step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21748step3 raw21748step3Labels raw21748step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4508 node4508Labels := by rfl

def raw21749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21749step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-1, -2, 3]]
def raw21749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21749step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw21749step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21749step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw21749step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21749 raw21749Labels = mixedMoment B node4284 node4284Labels := by
  calc
    mixedMoment B raw21749 raw21749Labels = mixedMoment B raw21749step0 raw21749step0Labels := by
      have hz : ∀ j, raw21749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21749step0 = (fun i j => raw21749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21749step0 raw21749; decide +kernel
      have hl : raw21749step0Labels = raw21749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21749 raw21749Labels permutation434 hz
    mixedMoment B raw21749step0 raw21749step0Labels = mixedMoment B raw21749step1 raw21749step1Labels := by
      have hz : ∀ j, raw21749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21749step1 = (fun i j => raw21749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21749step1 raw21749step0; decide +kernel
      have hl : raw21749step1Labels = raw21749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21749step0 raw21749step0Labels permutation80 hz
    mixedMoment B raw21749step1 raw21749step1Labels = mixedMoment B raw21749step2 raw21749step2Labels := by
      have hz : ∀ j, raw21749step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21749step2 = (fun i j => raw21749step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21749step2 raw21749step1; decide +kernel
      have hl : raw21749step2Labels = raw21749step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21749step1 raw21749step1Labels permutation14 hz
    mixedMoment B raw21749step2 raw21749step2Labels = mixedMoment B raw21749step3 raw21749step3Labels := by
      have ha : raw21749step3 = (fun i j => raw21749step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21749step3 raw21749step2; decide +kernel
      have hl : raw21749step3Labels = raw21749step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21749step2 raw21749step2Labels permutation2 permutation6
    mixedMoment B raw21749step3 raw21749step3Labels = mixedMoment B raw21749step4 raw21749step4Labels := by
      have ha : raw21749step4 = raw21749step3 := by apply Matrix.ext; unfold raw21749step4 raw21749step3; decide +kernel
      have hl : raw21749step3Labels = labelEmbedding9 ∘ raw21749step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21749step3 raw21749step3Labels raw21749step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4284 node4284Labels := by rfl

def raw21750 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21750step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21750step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21750step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21750 raw21750Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw21750 raw21750Labels = mixedMoment B raw21750step0 raw21750step0Labels := by
      have hz : ∀ j, raw21750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21750step0 = (fun i j => raw21750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21750step0 raw21750; decide +kernel
      have hl : raw21750step0Labels = raw21750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21750 raw21750Labels permutation434 hz
    mixedMoment B raw21750step0 raw21750step0Labels = mixedMoment B raw21750step1 raw21750step1Labels := by
      have hz : ∀ j, raw21750step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21750step1 = (fun i j => raw21750step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21750step1 raw21750step0; decide +kernel
      have hl : raw21750step1Labels = raw21750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21750step0 raw21750step0Labels permutation80 hz
    mixedMoment B raw21750step1 raw21750step1Labels = mixedMoment B raw21750step2 raw21750step2Labels := by
      have ha : raw21750step2 = (fun i j => raw21750step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21750step2 raw21750step1; decide +kernel
      have hl : raw21750step2Labels = raw21750step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21750step1 raw21750step1Labels permutation8 permutation6
    mixedMoment B raw21750step2 raw21750step2Labels = mixedMoment B raw21750step3 raw21750step3Labels := by
      have ha : raw21750step3 = raw21750step2 := by apply Matrix.ext; unfold raw21750step3 raw21750step2; decide +kernel
      have hl : raw21750step2Labels = labelEmbedding9 ∘ raw21750step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21750step2 raw21750step2Labels raw21750step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw21751 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21751step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21751step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21751step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21751 raw21751Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw21751 raw21751Labels = mixedMoment B raw21751step0 raw21751step0Labels := by
      have hz : ∀ j, raw21751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21751step0 = (fun i j => raw21751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21751step0 raw21751; decide +kernel
      have hl : raw21751step0Labels = raw21751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21751 raw21751Labels permutation434 hz
    mixedMoment B raw21751step0 raw21751step0Labels = mixedMoment B raw21751step1 raw21751step1Labels := by
      have hz : ∀ j, raw21751step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21751step1 = (fun i j => raw21751step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21751step1 raw21751step0; decide +kernel
      have hl : raw21751step1Labels = raw21751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21751step0 raw21751step0Labels permutation56 hz
    mixedMoment B raw21751step1 raw21751step1Labels = mixedMoment B raw21751step2 raw21751step2Labels := by
      have ha : raw21751step2 = (fun i j => raw21751step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21751step2 raw21751step1; decide +kernel
      have hl : raw21751step2Labels = raw21751step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21751step1 raw21751step1Labels permutation8 permutation6
    mixedMoment B raw21751step2 raw21751step2Labels = mixedMoment B raw21751step3 raw21751step3Labels := by
      have ha : raw21751step3 = raw21751step2 := by apply Matrix.ext; unfold raw21751step3 raw21751step2; decide +kernel
      have hl : raw21751step2Labels = labelEmbedding9 ∘ raw21751step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21751step2 raw21751step2Labels raw21751step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw21752 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21752step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21752step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21752 raw21752Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw21752 raw21752Labels = mixedMoment B raw21752step0 raw21752step0Labels := by
      have hz : ∀ j, raw21752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21752step0 = (fun i j => raw21752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21752step0 raw21752; decide +kernel
      have hl : raw21752step0Labels = raw21752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21752 raw21752Labels permutation434 hz
    mixedMoment B raw21752step0 raw21752step0Labels = mixedMoment B raw21752step1 raw21752step1Labels := by
      have hz : ∀ j, raw21752step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21752step1 = (fun i j => raw21752step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21752step1 raw21752step0; decide +kernel
      have hl : raw21752step1Labels = raw21752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21752step0 raw21752step0Labels permutation80 hz
    mixedMoment B raw21752step1 raw21752step1Labels = mixedMoment B raw21752step2 raw21752step2Labels := by
      have ha : raw21752step2 = (fun i j => raw21752step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21752step2 raw21752step1; decide +kernel
      have hl : raw21752step2Labels = raw21752step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21752step1 raw21752step1Labels permutation8 permutation6
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw21753 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21753step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21753step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21753 raw21753Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw21753 raw21753Labels = mixedMoment B raw21753step0 raw21753step0Labels := by
      have hz : ∀ j, raw21753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21753step0 = (fun i j => raw21753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21753step0 raw21753; decide +kernel
      have hl : raw21753step0Labels = raw21753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21753 raw21753Labels permutation434 hz
    mixedMoment B raw21753step0 raw21753step0Labels = mixedMoment B raw21753step1 raw21753step1Labels := by
      have hz : ∀ j, raw21753step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21753step1 = (fun i j => raw21753step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21753step1 raw21753step0; decide +kernel
      have hl : raw21753step1Labels = raw21753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21753step0 raw21753step0Labels permutation56 hz
    mixedMoment B raw21753step1 raw21753step1Labels = mixedMoment B raw21753step2 raw21753step2Labels := by
      have ha : raw21753step2 = (fun i j => raw21753step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21753step2 raw21753step1; decide +kernel
      have hl : raw21753step2Labels = raw21753step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21753step1 raw21753step1Labels permutation8 permutation6
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw21754 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21754step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21754step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-3, 0, 3]]
def raw21754step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21754step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw21754step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21754 raw21754Labels = mixedMoment B node1308 node1308Labels := by
  calc
    mixedMoment B raw21754 raw21754Labels = mixedMoment B raw21754step0 raw21754step0Labels := by
      have hz : ∀ j, raw21754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21754step0 = (fun i j => raw21754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21754step0 raw21754; decide +kernel
      have hl : raw21754step0Labels = raw21754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21754 raw21754Labels permutation434 hz
    mixedMoment B raw21754step0 raw21754step0Labels = mixedMoment B raw21754step1 raw21754step1Labels := by
      have hz : ∀ j, raw21754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21754step1 = (fun i j => raw21754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21754step1 raw21754step0; decide +kernel
      have hl : raw21754step1Labels = raw21754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21754step0 raw21754step0Labels permutation80 hz
    mixedMoment B raw21754step1 raw21754step1Labels = mixedMoment B raw21754step2 raw21754step2Labels := by
      have hz : ∀ j, raw21754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21754step2 = (fun i j => raw21754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21754step2 raw21754step1; decide +kernel
      have hl : raw21754step2Labels = raw21754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21754step1 raw21754step1Labels permutation14 hz
    mixedMoment B raw21754step2 raw21754step2Labels = mixedMoment B raw21754step3 raw21754step3Labels := by
      have ha : raw21754step3 = (fun i j => raw21754step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21754step3 raw21754step2; decide +kernel
      have hl : raw21754step3Labels = raw21754step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21754step2 raw21754step2Labels permutation2 permutation6
    _ = mixedMoment B node1308 node1308Labels := by rfl

def raw21755 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21755step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21755step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21755step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21755step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21755 raw21755Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw21755 raw21755Labels = mixedMoment B raw21755step0 raw21755step0Labels := by
      have hz : ∀ j, raw21755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21755step0 = (fun i j => raw21755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21755step0 raw21755; decide +kernel
      have hl : raw21755step0Labels = raw21755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21755 raw21755Labels permutation434 hz
    mixedMoment B raw21755step0 raw21755step0Labels = mixedMoment B raw21755step1 raw21755step1Labels := by
      have hz : ∀ j, raw21755step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21755step1 = (fun i j => raw21755step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21755step1 raw21755step0; decide +kernel
      have hl : raw21755step1Labels = raw21755step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21755step0 raw21755step0Labels permutation56 hz
    mixedMoment B raw21755step1 raw21755step1Labels = mixedMoment B raw21755step2 raw21755step2Labels := by
      have ha : raw21755step2 = (fun i j => raw21755step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21755step2 raw21755step1; decide +kernel
      have hl : raw21755step2Labels = raw21755step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21755step1 raw21755step1Labels permutation8 permutation6
    _ = mixedMoment B node813 node813Labels := by rfl

def raw21756 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21756 raw21756Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw21756 raw21756Labels = mixedMoment B raw21756step0 raw21756step0Labels := by
      have hz : ∀ j, raw21756 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21756step0 = (fun i j => raw21756 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21756step0 raw21756; decide +kernel
      have hl : raw21756step0Labels = raw21756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21756 raw21756Labels permutation434 hz
    mixedMoment B raw21756step0 raw21756step0Labels = mixedMoment B raw21756step1 raw21756step1Labels := by
      have ha : raw21756step1 = (fun i j => raw21756step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21756step1 raw21756step0; decide +kernel
      have hl : raw21756step1Labels = raw21756step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21756step0 raw21756step0Labels permutation32 permutation6
    _ = mixedMoment B node983 node983Labels := by rfl

def raw21757 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21757 raw21757Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw21757 raw21757Labels = mixedMoment B raw21757step0 raw21757step0Labels := by
      have hz : ∀ j, raw21757 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21757step0 = (fun i j => raw21757 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21757step0 raw21757; decide +kernel
      have hl : raw21757step0Labels = raw21757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21757 raw21757Labels permutation265 hz
    mixedMoment B raw21757step0 raw21757step0Labels = mixedMoment B raw21757step1 raw21757step1Labels := by
      have ha : raw21757step1 = (fun i j => raw21757step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21757step1 raw21757step0; decide +kernel
      have hl : raw21757step1Labels = raw21757step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21757step0 raw21757step0Labels permutation38 permutation6
    _ = mixedMoment B node983 node983Labels := by rfl

def raw21758 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21758step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21758step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21758 raw21758Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw21758 raw21758Labels = mixedMoment B raw21758step0 raw21758step0Labels := by
      have hz : ∀ j, raw21758 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21758step0 = (fun i j => raw21758 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21758step0 raw21758; decide +kernel
      have hl : raw21758step0Labels = raw21758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21758 raw21758Labels permutation434 hz
    mixedMoment B raw21758step0 raw21758step0Labels = mixedMoment B raw21758step1 raw21758step1Labels := by
      have hz : ∀ j, raw21758step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21758step1 = (fun i j => raw21758step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21758step1 raw21758step0; decide +kernel
      have hl : raw21758step1Labels = raw21758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21758step0 raw21758step0Labels permutation56 hz
    mixedMoment B raw21758step1 raw21758step1Labels = mixedMoment B raw21758step2 raw21758step2Labels := by
      have ha : raw21758step2 = (fun i j => raw21758step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21758step2 raw21758step1; decide +kernel
      have hl : raw21758step2Labels = raw21758step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21758step1 raw21758step1Labels permutation8 permutation6
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw21759 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21759step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21759step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21759 raw21759Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw21759 raw21759Labels = mixedMoment B raw21759step0 raw21759step0Labels := by
      have hz : ∀ j, raw21759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21759step0 = (fun i j => raw21759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21759step0 raw21759; decide +kernel
      have hl : raw21759step0Labels = raw21759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21759 raw21759Labels permutation346 hz
    mixedMoment B raw21759step0 raw21759step0Labels = mixedMoment B raw21759step1 raw21759step1Labels := by
      have hz : ∀ j, raw21759step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21759step1 = (fun i j => raw21759step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21759step1 raw21759step0; decide +kernel
      have hl : raw21759step1Labels = raw21759step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21759step0 raw21759step0Labels permutation56 hz
    mixedMoment B raw21759step1 raw21759step1Labels = mixedMoment B raw21759step2 raw21759step2Labels := by
      have ha : raw21759step2 = (fun i j => raw21759step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21759step2 raw21759step1; decide +kernel
      have hl : raw21759step2Labels = raw21759step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21759step1 raw21759step1Labels permutation8 permutation6
    _ = mixedMoment B node813 node813Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
