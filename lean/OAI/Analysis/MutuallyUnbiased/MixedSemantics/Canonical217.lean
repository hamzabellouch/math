import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27776 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -3, 1], ![-3, 0, 3]]
def raw27776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw27776step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27776step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27776step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27776step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27776 raw27776Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw27776 raw27776Labels = mixedMoment B raw27776step0 raw27776step0Labels := by
      have hz : ∀ j, raw27776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27776step0 = (fun i j => raw27776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27776step0 raw27776; decide +kernel
      have hl : raw27776step0Labels = raw27776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27776 raw27776Labels permutation434 hz
    mixedMoment B raw27776step0 raw27776step0Labels = mixedMoment B raw27776step1 raw27776step1Labels := by
      have hz : ∀ j, raw27776step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27776step1 = (fun i j => raw27776step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27776step1 raw27776step0; decide +kernel
      have hl : raw27776step1Labels = raw27776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27776step0 raw27776step0Labels permutation80 hz
    mixedMoment B raw27776step1 raw27776step1Labels = mixedMoment B raw27776step2 raw27776step2Labels := by
      have ha : raw27776step2 = (fun i j => raw27776step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27776step2 raw27776step1; decide +kernel
      have hl : raw27776step2Labels = raw27776step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27776step1 raw27776step1Labels permutation31 permutation7
    mixedMoment B raw27776step2 raw27776step2Labels = mixedMoment B raw27776step3 raw27776step3Labels := by
      have ha : raw27776step3 = -raw27776step2 := by apply Matrix.ext; change ∀ i j, raw27776step3 i j = -(raw27776step2 i j); unfold raw27776step3 raw27776step2; decide +kernel
      have hl : raw27776step3Labels = raw27776step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27776step3 raw27776step3Labels = mixedMoment B raw27776step4 raw27776step4Labels := by
      have ha : raw27776step4 = raw27776step3 := by apply Matrix.ext; unfold raw27776step4 raw27776step3; decide +kernel
      have hl : raw27776step3Labels = labelEmbedding10 ∘ raw27776step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27776step3 raw27776step3Labels raw27776step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw27777 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw27777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27777 raw27777Labels = mixedMoment B node4840 node4840Labels := by
  calc
    mixedMoment B raw27777 raw27777Labels = mixedMoment B raw27777step0 raw27777step0Labels := by
      have hz : ∀ j, raw27777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27777step0 = (fun i j => raw27777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27777step0 raw27777; decide +kernel
      have hl : raw27777step0Labels = raw27777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27777 raw27777Labels permutation434 hz
    mixedMoment B raw27777step0 raw27777step0Labels = mixedMoment B raw27777step1 raw27777step1Labels := by
      have ha : raw27777step1 = (fun i j => raw27777step0 (permutation142 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27777step1 raw27777step0; decide +kernel
      have hl : raw27777step1Labels = raw27777step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27777step0 raw27777step0Labels permutation142 permutation2
    _ = mixedMoment B node4840 node4840Labels := by rfl

def raw27778 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw27778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27778 raw27778Labels = mixedMoment B node4840 node4840Labels := by
  calc
    mixedMoment B raw27778 raw27778Labels = mixedMoment B raw27778step0 raw27778step0Labels := by
      have hz : ∀ j, raw27778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27778step0 = (fun i j => raw27778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27778step0 raw27778; decide +kernel
      have hl : raw27778step0Labels = raw27778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27778 raw27778Labels permutation346 hz
    mixedMoment B raw27778step0 raw27778step0Labels = mixedMoment B raw27778step1 raw27778step1Labels := by
      have ha : raw27778step1 = (fun i j => raw27778step0 (permutation142 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27778step1 raw27778step0; decide +kernel
      have hl : raw27778step1Labels = raw27778step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27778step0 raw27778step0Labels permutation142 permutation2
    _ = mixedMoment B node4840 node4840Labels := by rfl

def raw27779 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw27779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw27779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -3, 1], ![-4, 1, 3]]
def raw27779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw27779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27779 raw27779Labels = mixedMoment B node4504 node4504Labels := by
  calc
    mixedMoment B raw27779 raw27779Labels = mixedMoment B raw27779step0 raw27779step0Labels := by
      have hz : ∀ j, raw27779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27779step0 = (fun i j => raw27779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27779step0 raw27779; decide +kernel
      have hl : raw27779step0Labels = raw27779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27779 raw27779Labels permutation434 hz
    mixedMoment B raw27779step0 raw27779step0Labels = mixedMoment B raw27779step1 raw27779step1Labels := by
      have hz : ∀ j, raw27779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27779step1 = (fun i j => raw27779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27779step1 raw27779step0; decide +kernel
      have hl : raw27779step1Labels = raw27779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27779step0 raw27779step0Labels permutation80 hz
    mixedMoment B raw27779step1 raw27779step1Labels = mixedMoment B raw27779step2 raw27779step2Labels := by
      have ha : raw27779step2 = (fun i j => raw27779step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27779step2 raw27779step1; decide +kernel
      have hl : raw27779step2Labels = raw27779step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27779step1 raw27779step1Labels permutation28 permutation2
    _ = mixedMoment B node4504 node4504Labels := by rfl

def raw27780 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27780step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27780step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27780 raw27780Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw27780 raw27780Labels = mixedMoment B raw27780step0 raw27780step0Labels := by
      have hz : ∀ j, raw27780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27780step0 = (fun i j => raw27780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27780step0 raw27780; decide +kernel
      have hl : raw27780step0Labels = raw27780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27780 raw27780Labels permutation434 hz
    mixedMoment B raw27780step0 raw27780step0Labels = mixedMoment B raw27780step1 raw27780step1Labels := by
      have hz : ∀ j, raw27780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27780step1 = (fun i j => raw27780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27780step1 raw27780step0; decide +kernel
      have hl : raw27780step1Labels = raw27780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27780step0 raw27780step0Labels permutation80 hz
    mixedMoment B raw27780step1 raw27780step1Labels = mixedMoment B raw27780step2 raw27780step2Labels := by
      have ha : raw27780step2 = (fun i j => raw27780step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27780step2 raw27780step1; decide +kernel
      have hl : raw27780step2Labels = raw27780step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27780step1 raw27780step1Labels permutation8 permutation6
    mixedMoment B raw27780step2 raw27780step2Labels = mixedMoment B raw27780step3 raw27780step3Labels := by
      have ha : raw27780step3 = raw27780step2 := by apply Matrix.ext; unfold raw27780step3 raw27780step2; decide +kernel
      have hl : raw27780step2Labels = labelEmbedding9 ∘ raw27780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27780step2 raw27780step2Labels raw27780step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw27781 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27781step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27781step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27781step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27781step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27781step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27781step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27781step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27781step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27781 raw27781Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw27781 raw27781Labels = mixedMoment B raw27781step0 raw27781step0Labels := by
      have hz : ∀ j, raw27781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27781step0 = (fun i j => raw27781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27781step0 raw27781; decide +kernel
      have hl : raw27781step0Labels = raw27781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27781 raw27781Labels permutation434 hz
    mixedMoment B raw27781step0 raw27781step0Labels = mixedMoment B raw27781step1 raw27781step1Labels := by
      have hz : ∀ j, raw27781step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27781step1 = (fun i j => raw27781step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27781step1 raw27781step0; decide +kernel
      have hl : raw27781step1Labels = raw27781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27781step0 raw27781step0Labels permutation80 hz
    mixedMoment B raw27781step1 raw27781step1Labels = mixedMoment B raw27781step2 raw27781step2Labels := by
      have ha : raw27781step2 = (fun i j => raw27781step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27781step2 raw27781step1; decide +kernel
      have hl : raw27781step2Labels = raw27781step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27781step1 raw27781step1Labels permutation31 permutation7
    mixedMoment B raw27781step2 raw27781step2Labels = mixedMoment B raw27781step3 raw27781step3Labels := by
      have ha : raw27781step3 = -raw27781step2 := by apply Matrix.ext; change ∀ i j, raw27781step3 i j = -(raw27781step2 i j); unfold raw27781step3 raw27781step2; decide +kernel
      have hl : raw27781step3Labels = raw27781step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27781step3 raw27781step3Labels = mixedMoment B raw27781step4 raw27781step4Labels := by
      have ha : raw27781step4 = raw27781step3 := by apply Matrix.ext; unfold raw27781step4 raw27781step3; decide +kernel
      have hl : raw27781step3Labels = labelEmbedding1 ∘ raw27781step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27781step3 raw27781step3Labels raw27781step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw27782 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27782step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27782step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27782step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27782 raw27782Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw27782 raw27782Labels = mixedMoment B raw27782step0 raw27782step0Labels := by
      have hz : ∀ j, raw27782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27782step0 = (fun i j => raw27782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27782step0 raw27782; decide +kernel
      have hl : raw27782step0Labels = raw27782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27782 raw27782Labels permutation434 hz
    mixedMoment B raw27782step0 raw27782step0Labels = mixedMoment B raw27782step1 raw27782step1Labels := by
      have ha : raw27782step1 = (fun i j => raw27782step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27782step1 raw27782step0; decide +kernel
      have hl : raw27782step1Labels = raw27782step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27782step0 raw27782step0Labels permutation151 permutation7
    mixedMoment B raw27782step1 raw27782step1Labels = mixedMoment B raw27782step2 raw27782step2Labels := by
      have ha : raw27782step2 = -raw27782step1 := by apply Matrix.ext; change ∀ i j, raw27782step2 i j = -(raw27782step1 i j); unfold raw27782step2 raw27782step1; decide +kernel
      have hl : raw27782step2Labels = raw27782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27782step2 raw27782step2Labels = mixedMoment B raw27782step3 raw27782step3Labels := by
      have ha : raw27782step3 = raw27782step2 := by apply Matrix.ext; unfold raw27782step3 raw27782step2; decide +kernel
      have hl : raw27782step2Labels = labelEmbedding1 ∘ raw27782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27782step2 raw27782step2Labels raw27782step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw27783 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27783step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27783step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27783step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27783step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27783 raw27783Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw27783 raw27783Labels = mixedMoment B raw27783step0 raw27783step0Labels := by
      have hz : ∀ j, raw27783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27783step0 = (fun i j => raw27783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27783step0 raw27783; decide +kernel
      have hl : raw27783step0Labels = raw27783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27783 raw27783Labels permutation346 hz
    mixedMoment B raw27783step0 raw27783step0Labels = mixedMoment B raw27783step1 raw27783step1Labels := by
      have ha : raw27783step1 = (fun i j => raw27783step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27783step1 raw27783step0; decide +kernel
      have hl : raw27783step1Labels = raw27783step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27783step0 raw27783step0Labels permutation151 permutation7
    mixedMoment B raw27783step1 raw27783step1Labels = mixedMoment B raw27783step2 raw27783step2Labels := by
      have ha : raw27783step2 = -raw27783step1 := by apply Matrix.ext; change ∀ i j, raw27783step2 i j = -(raw27783step1 i j); unfold raw27783step2 raw27783step1; decide +kernel
      have hl : raw27783step2Labels = raw27783step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27783step2 raw27783step2Labels = mixedMoment B raw27783step3 raw27783step3Labels := by
      have ha : raw27783step3 = raw27783step2 := by apply Matrix.ext; unfold raw27783step3 raw27783step2; decide +kernel
      have hl : raw27783step2Labels = labelEmbedding1 ∘ raw27783step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27783step2 raw27783step2Labels raw27783step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw27784 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw27784step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27784step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27784step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27784step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27784step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27784 raw27784Labels = mixedMoment B node2060 node2060Labels := by
  calc
    mixedMoment B raw27784 raw27784Labels = mixedMoment B raw27784step0 raw27784step0Labels := by
      have hz : ∀ j, raw27784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27784step0 = (fun i j => raw27784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27784step0 raw27784; decide +kernel
      have hl : raw27784step0Labels = raw27784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27784 raw27784Labels permutation434 hz
    mixedMoment B raw27784step0 raw27784step0Labels = mixedMoment B raw27784step1 raw27784step1Labels := by
      have hz : ∀ j, raw27784step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27784step1 = (fun i j => raw27784step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27784step1 raw27784step0; decide +kernel
      have hl : raw27784step1Labels = raw27784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27784step0 raw27784step0Labels permutation80 hz
    mixedMoment B raw27784step1 raw27784step1Labels = mixedMoment B raw27784step2 raw27784step2Labels := by
      have ha : raw27784step2 = (fun i j => raw27784step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27784step2 raw27784step1; decide +kernel
      have hl : raw27784step2Labels = raw27784step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27784step1 raw27784step1Labels permutation31 permutation7
    mixedMoment B raw27784step2 raw27784step2Labels = mixedMoment B raw27784step3 raw27784step3Labels := by
      have ha : raw27784step3 = -raw27784step2 := by apply Matrix.ext; change ∀ i j, raw27784step3 i j = -(raw27784step2 i j); unfold raw27784step3 raw27784step2; decide +kernel
      have hl : raw27784step3Labels = raw27784step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27784step3 raw27784step3Labels = mixedMoment B raw27784step4 raw27784step4Labels := by
      have ha : raw27784step4 = raw27784step3 := by apply Matrix.ext; unfold raw27784step4 raw27784step3; decide +kernel
      have hl : raw27784step3Labels = labelEmbedding1 ∘ raw27784step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27784step3 raw27784step3Labels raw27784step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2060 node2060Labels := by rfl

def raw27785 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27785step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-4, 1, 3]]
def raw27785step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27785step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27785step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27785step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27785step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27785step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27785 raw27785Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw27785 raw27785Labels = mixedMoment B raw27785step0 raw27785step0Labels := by
      have hz : ∀ j, raw27785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27785step0 = (fun i j => raw27785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27785step0 raw27785; decide +kernel
      have hl : raw27785step0Labels = raw27785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27785 raw27785Labels permutation434 hz
    mixedMoment B raw27785step0 raw27785step0Labels = mixedMoment B raw27785step1 raw27785step1Labels := by
      have hz : ∀ j, raw27785step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27785step1 = (fun i j => raw27785step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27785step1 raw27785step0; decide +kernel
      have hl : raw27785step1Labels = raw27785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27785step0 raw27785step0Labels permutation80 hz
    mixedMoment B raw27785step1 raw27785step1Labels = mixedMoment B raw27785step2 raw27785step2Labels := by
      have ha : raw27785step2 = (fun i j => raw27785step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27785step2 raw27785step1; decide +kernel
      have hl : raw27785step2Labels = raw27785step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27785step1 raw27785step1Labels permutation31 permutation7
    mixedMoment B raw27785step2 raw27785step2Labels = mixedMoment B raw27785step3 raw27785step3Labels := by
      have ha : raw27785step3 = -raw27785step2 := by apply Matrix.ext; change ∀ i j, raw27785step3 i j = -(raw27785step2 i j); unfold raw27785step3 raw27785step2; decide +kernel
      have hl : raw27785step3Labels = raw27785step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27785step3 raw27785step3Labels = mixedMoment B raw27785step4 raw27785step4Labels := by
      have ha : raw27785step4 = raw27785step3 := by apply Matrix.ext; unfold raw27785step4 raw27785step3; decide +kernel
      have hl : raw27785step3Labels = labelEmbedding1 ∘ raw27785step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27785step3 raw27785step3Labels raw27785step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1650 node1650Labels := by rfl

def raw27786 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27786step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27786step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27786step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27786step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27786step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27786step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27786 raw27786Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw27786 raw27786Labels = mixedMoment B raw27786step0 raw27786step0Labels := by
      have hz : ∀ j, raw27786 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27786step0 = (fun i j => raw27786 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27786step0 raw27786; decide +kernel
      have hl : raw27786step0Labels = raw27786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27786 raw27786Labels permutation434 hz
    mixedMoment B raw27786step0 raw27786step0Labels = mixedMoment B raw27786step1 raw27786step1Labels := by
      have hz : ∀ j, raw27786step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27786step1 = (fun i j => raw27786step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27786step1 raw27786step0; decide +kernel
      have hl : raw27786step1Labels = raw27786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27786step0 raw27786step0Labels permutation80 hz
    mixedMoment B raw27786step1 raw27786step1Labels = mixedMoment B raw27786step2 raw27786step2Labels := by
      have ha : raw27786step2 = (fun i j => raw27786step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27786step2 raw27786step1; decide +kernel
      have hl : raw27786step2Labels = raw27786step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27786step1 raw27786step1Labels permutation31 permutation7
    mixedMoment B raw27786step2 raw27786step2Labels = mixedMoment B raw27786step3 raw27786step3Labels := by
      have ha : raw27786step3 = -raw27786step2 := by apply Matrix.ext; change ∀ i j, raw27786step3 i j = -(raw27786step2 i j); unfold raw27786step3 raw27786step2; decide +kernel
      have hl : raw27786step3Labels = raw27786step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27786step3 raw27786step3Labels = mixedMoment B raw27786step4 raw27786step4Labels := by
      have ha : raw27786step4 = raw27786step3 := by apply Matrix.ext; unfold raw27786step4 raw27786step3; decide +kernel
      have hl : raw27786step3Labels = labelEmbedding1 ∘ raw27786step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27786step3 raw27786step3Labels raw27786step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2113 node2113Labels := by rfl

def raw27787 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27787step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27787step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27787step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27787step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27787 raw27787Labels = mixedMoment B node2080 node2080Labels := by
  calc
    mixedMoment B raw27787 raw27787Labels = mixedMoment B raw27787step0 raw27787step0Labels := by
      have hz : ∀ j, raw27787 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27787step0 = (fun i j => raw27787 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27787step0 raw27787; decide +kernel
      have hl : raw27787step0Labels = raw27787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27787 raw27787Labels permutation434 hz
    mixedMoment B raw27787step0 raw27787step0Labels = mixedMoment B raw27787step1 raw27787step1Labels := by
      have ha : raw27787step1 = (fun i j => raw27787step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27787step1 raw27787step0; decide +kernel
      have hl : raw27787step1Labels = raw27787step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27787step0 raw27787step0Labels permutation151 permutation7
    mixedMoment B raw27787step1 raw27787step1Labels = mixedMoment B raw27787step2 raw27787step2Labels := by
      have ha : raw27787step2 = -raw27787step1 := by apply Matrix.ext; change ∀ i j, raw27787step2 i j = -(raw27787step1 i j); unfold raw27787step2 raw27787step1; decide +kernel
      have hl : raw27787step2Labels = raw27787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27787step2 raw27787step2Labels = mixedMoment B raw27787step3 raw27787step3Labels := by
      have ha : raw27787step3 = raw27787step2 := by apply Matrix.ext; unfold raw27787step3 raw27787step2; decide +kernel
      have hl : raw27787step2Labels = labelEmbedding1 ∘ raw27787step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27787step2 raw27787step2Labels raw27787step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2080 node2080Labels := by rfl

def raw27788 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27788step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27788step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27788 raw27788Labels = mixedMoment B node2080 node2080Labels := by
  calc
    mixedMoment B raw27788 raw27788Labels = mixedMoment B raw27788step0 raw27788step0Labels := by
      have hz : ∀ j, raw27788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27788step0 = (fun i j => raw27788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27788step0 raw27788; decide +kernel
      have hl : raw27788step0Labels = raw27788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27788 raw27788Labels permutation346 hz
    mixedMoment B raw27788step0 raw27788step0Labels = mixedMoment B raw27788step1 raw27788step1Labels := by
      have ha : raw27788step1 = (fun i j => raw27788step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27788step1 raw27788step0; decide +kernel
      have hl : raw27788step1Labels = raw27788step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27788step0 raw27788step0Labels permutation151 permutation7
    mixedMoment B raw27788step1 raw27788step1Labels = mixedMoment B raw27788step2 raw27788step2Labels := by
      have ha : raw27788step2 = -raw27788step1 := by apply Matrix.ext; change ∀ i j, raw27788step2 i j = -(raw27788step1 i j); unfold raw27788step2 raw27788step1; decide +kernel
      have hl : raw27788step2Labels = raw27788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27788step2 raw27788step2Labels = mixedMoment B raw27788step3 raw27788step3Labels := by
      have ha : raw27788step3 = raw27788step2 := by apply Matrix.ext; unfold raw27788step3 raw27788step2; decide +kernel
      have hl : raw27788step2Labels = labelEmbedding1 ∘ raw27788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27788step2 raw27788step2Labels raw27788step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2080 node2080Labels := by rfl

def raw27789 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27789step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw27789step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw27789step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27789step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27789step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27789step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27789 raw27789Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw27789 raw27789Labels = mixedMoment B raw27789step0 raw27789step0Labels := by
      have hz : ∀ j, raw27789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27789step0 = (fun i j => raw27789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27789step0 raw27789; decide +kernel
      have hl : raw27789step0Labels = raw27789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27789 raw27789Labels permutation434 hz
    mixedMoment B raw27789step0 raw27789step0Labels = mixedMoment B raw27789step1 raw27789step1Labels := by
      have hz : ∀ j, raw27789step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27789step1 = (fun i j => raw27789step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27789step1 raw27789step0; decide +kernel
      have hl : raw27789step1Labels = raw27789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27789step0 raw27789step0Labels permutation80 hz
    mixedMoment B raw27789step1 raw27789step1Labels = mixedMoment B raw27789step2 raw27789step2Labels := by
      have ha : raw27789step2 = (fun i j => raw27789step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27789step2 raw27789step1; decide +kernel
      have hl : raw27789step2Labels = raw27789step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27789step1 raw27789step1Labels permutation31 permutation7
    mixedMoment B raw27789step2 raw27789step2Labels = mixedMoment B raw27789step3 raw27789step3Labels := by
      have ha : raw27789step3 = -raw27789step2 := by apply Matrix.ext; change ∀ i j, raw27789step3 i j = -(raw27789step2 i j); unfold raw27789step3 raw27789step2; decide +kernel
      have hl : raw27789step3Labels = raw27789step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27789step3 raw27789step3Labels = mixedMoment B raw27789step4 raw27789step4Labels := by
      have ha : raw27789step4 = raw27789step3 := by apply Matrix.ext; unfold raw27789step4 raw27789step3; decide +kernel
      have hl : raw27789step3Labels = labelEmbedding1 ∘ raw27789step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27789step3 raw27789step3Labels raw27789step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw27790 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -2, 1], ![-4, 1, 3]]
def raw27790step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27790step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27790step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27790step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27790step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27790 raw27790Labels = mixedMoment B node1651 node1651Labels := by
  calc
    mixedMoment B raw27790 raw27790Labels = mixedMoment B raw27790step0 raw27790step0Labels := by
      have hz : ∀ j, raw27790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27790step0 = (fun i j => raw27790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27790step0 raw27790; decide +kernel
      have hl : raw27790step0Labels = raw27790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27790 raw27790Labels permutation434 hz
    mixedMoment B raw27790step0 raw27790step0Labels = mixedMoment B raw27790step1 raw27790step1Labels := by
      have hz : ∀ j, raw27790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27790step1 = (fun i j => raw27790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27790step1 raw27790step0; decide +kernel
      have hl : raw27790step1Labels = raw27790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27790step0 raw27790step0Labels permutation80 hz
    mixedMoment B raw27790step1 raw27790step1Labels = mixedMoment B raw27790step2 raw27790step2Labels := by
      have ha : raw27790step2 = (fun i j => raw27790step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27790step2 raw27790step1; decide +kernel
      have hl : raw27790step2Labels = raw27790step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27790step1 raw27790step1Labels permutation31 permutation7
    mixedMoment B raw27790step2 raw27790step2Labels = mixedMoment B raw27790step3 raw27790step3Labels := by
      have ha : raw27790step3 = -raw27790step2 := by apply Matrix.ext; change ∀ i j, raw27790step3 i j = -(raw27790step2 i j); unfold raw27790step3 raw27790step2; decide +kernel
      have hl : raw27790step3Labels = raw27790step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27790step3 raw27790step3Labels = mixedMoment B raw27790step4 raw27790step4Labels := by
      have ha : raw27790step4 = raw27790step3 := by apply Matrix.ext; unfold raw27790step4 raw27790step3; decide +kernel
      have hl : raw27790step3Labels = labelEmbedding1 ∘ raw27790step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27790step3 raw27790step3Labels raw27790step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1651 node1651Labels := by rfl

def raw27791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27791step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27791step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27791 raw27791Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw27791 raw27791Labels = mixedMoment B raw27791step0 raw27791step0Labels := by
      have hz : ∀ j, raw27791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27791step0 = (fun i j => raw27791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27791step0 raw27791; decide +kernel
      have hl : raw27791step0Labels = raw27791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27791 raw27791Labels permutation434 hz
    mixedMoment B raw27791step0 raw27791step0Labels = mixedMoment B raw27791step1 raw27791step1Labels := by
      have ha : raw27791step1 = (fun i j => raw27791step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27791step1 raw27791step0; decide +kernel
      have hl : raw27791step1Labels = raw27791step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27791step0 raw27791step0Labels permutation151 permutation7
    mixedMoment B raw27791step1 raw27791step1Labels = mixedMoment B raw27791step2 raw27791step2Labels := by
      have ha : raw27791step2 = -raw27791step1 := by apply Matrix.ext; change ∀ i j, raw27791step2 i j = -(raw27791step1 i j); unfold raw27791step2 raw27791step1; decide +kernel
      have hl : raw27791step2Labels = raw27791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27791step2 raw27791step2Labels = mixedMoment B raw27791step3 raw27791step3Labels := by
      have ha : raw27791step3 = raw27791step2 := by apply Matrix.ext; unfold raw27791step3 raw27791step2; decide +kernel
      have hl : raw27791step2Labels = labelEmbedding1 ∘ raw27791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27791step2 raw27791step2Labels raw27791step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw27792 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27792step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27792 raw27792Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw27792 raw27792Labels = mixedMoment B raw27792step0 raw27792step0Labels := by
      have hz : ∀ j, raw27792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27792step0 = (fun i j => raw27792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27792step0 raw27792; decide +kernel
      have hl : raw27792step0Labels = raw27792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27792 raw27792Labels permutation434 hz
    mixedMoment B raw27792step0 raw27792step0Labels = mixedMoment B raw27792step1 raw27792step1Labels := by
      have ha : raw27792step1 = (fun i j => raw27792step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27792step1 raw27792step0; decide +kernel
      have hl : raw27792step1Labels = raw27792step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27792step0 raw27792step0Labels permutation151 permutation7
    mixedMoment B raw27792step1 raw27792step1Labels = mixedMoment B raw27792step2 raw27792step2Labels := by
      have ha : raw27792step2 = -raw27792step1 := by apply Matrix.ext; change ∀ i j, raw27792step2 i j = -(raw27792step1 i j); unfold raw27792step2 raw27792step1; decide +kernel
      have hl : raw27792step2Labels = raw27792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27792step2 raw27792step2Labels = mixedMoment B raw27792step3 raw27792step3Labels := by
      have ha : raw27792step3 = raw27792step2 := by apply Matrix.ext; unfold raw27792step3 raw27792step2; decide +kernel
      have hl : raw27792step2Labels = labelEmbedding1 ∘ raw27792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27792step2 raw27792step2Labels raw27792step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2090 node2090Labels := by rfl

def raw27793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27793 raw27793Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw27793 raw27793Labels = mixedMoment B raw27793step0 raw27793step0Labels := by
      have ha : raw27793step0 = (fun i j => raw27793 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27793step0 raw27793; decide +kernel
      have hl : raw27793step0Labels = raw27793Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27793 raw27793Labels permutation688 permutation7
    mixedMoment B raw27793step0 raw27793step0Labels = mixedMoment B raw27793step1 raw27793step1Labels := by
      have ha : raw27793step1 = -raw27793step0 := by apply Matrix.ext; change ∀ i j, raw27793step1 i j = -(raw27793step0 i j); unfold raw27793step1 raw27793step0; decide +kernel
      have hl : raw27793step1Labels = raw27793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27793step1 raw27793step1Labels = mixedMoment B raw27793step2 raw27793step2Labels := by
      have ha : raw27793step2 = raw27793step1 := by apply Matrix.ext; unfold raw27793step2 raw27793step1; decide +kernel
      have hl : raw27793step1Labels = labelEmbedding1 ∘ raw27793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27793step1 raw27793step1Labels raw27793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2071 node2071Labels := by rfl

def raw27794 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27794step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27794step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27794step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27794 raw27794Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw27794 raw27794Labels = mixedMoment B raw27794step0 raw27794step0Labels := by
      have hz : ∀ j, raw27794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27794step0 = (fun i j => raw27794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27794step0 raw27794; decide +kernel
      have hl : raw27794step0Labels = raw27794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27794 raw27794Labels permutation434 hz
    mixedMoment B raw27794step0 raw27794step0Labels = mixedMoment B raw27794step1 raw27794step1Labels := by
      have ha : raw27794step1 = (fun i j => raw27794step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27794step1 raw27794step0; decide +kernel
      have hl : raw27794step1Labels = raw27794step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27794step0 raw27794step0Labels permutation151 permutation7
    mixedMoment B raw27794step1 raw27794step1Labels = mixedMoment B raw27794step2 raw27794step2Labels := by
      have ha : raw27794step2 = -raw27794step1 := by apply Matrix.ext; change ∀ i j, raw27794step2 i j = -(raw27794step1 i j); unfold raw27794step2 raw27794step1; decide +kernel
      have hl : raw27794step2Labels = raw27794step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27794step2 raw27794step2Labels = mixedMoment B raw27794step3 raw27794step3Labels := by
      have ha : raw27794step3 = raw27794step2 := by apply Matrix.ext; unfold raw27794step3 raw27794step2; decide +kernel
      have hl : raw27794step2Labels = labelEmbedding1 ∘ raw27794step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27794step2 raw27794step2Labels raw27794step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw27795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27795step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27795 raw27795Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw27795 raw27795Labels = mixedMoment B raw27795step0 raw27795step0Labels := by
      have hz : ∀ j, raw27795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27795step0 = (fun i j => raw27795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27795step0 raw27795; decide +kernel
      have hl : raw27795step0Labels = raw27795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27795 raw27795Labels permutation434 hz
    mixedMoment B raw27795step0 raw27795step0Labels = mixedMoment B raw27795step1 raw27795step1Labels := by
      have ha : raw27795step1 = (fun i j => raw27795step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27795step1 raw27795step0; decide +kernel
      have hl : raw27795step1Labels = raw27795step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27795step0 raw27795step0Labels permutation151 permutation7
    mixedMoment B raw27795step1 raw27795step1Labels = mixedMoment B raw27795step2 raw27795step2Labels := by
      have ha : raw27795step2 = -raw27795step1 := by apply Matrix.ext; change ∀ i j, raw27795step2 i j = -(raw27795step1 i j); unfold raw27795step2 raw27795step1; decide +kernel
      have hl : raw27795step2Labels = raw27795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27795step2 raw27795step2Labels = mixedMoment B raw27795step3 raw27795step3Labels := by
      have ha : raw27795step3 = raw27795step2 := by apply Matrix.ext; unfold raw27795step3 raw27795step2; decide +kernel
      have hl : raw27795step2Labels = labelEmbedding1 ∘ raw27795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27795step2 raw27795step2Labels raw27795step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1639 node1639Labels := by rfl

def raw27796 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27796step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27796step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27796step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27796step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27796 raw27796Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw27796 raw27796Labels = mixedMoment B raw27796step0 raw27796step0Labels := by
      have hz : ∀ j, raw27796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27796step0 = (fun i j => raw27796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27796step0 raw27796; decide +kernel
      have hl : raw27796step0Labels = raw27796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27796 raw27796Labels permutation346 hz
    mixedMoment B raw27796step0 raw27796step0Labels = mixedMoment B raw27796step1 raw27796step1Labels := by
      have ha : raw27796step1 = (fun i j => raw27796step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27796step1 raw27796step0; decide +kernel
      have hl : raw27796step1Labels = raw27796step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27796step0 raw27796step0Labels permutation151 permutation7
    mixedMoment B raw27796step1 raw27796step1Labels = mixedMoment B raw27796step2 raw27796step2Labels := by
      have ha : raw27796step2 = -raw27796step1 := by apply Matrix.ext; change ∀ i j, raw27796step2 i j = -(raw27796step1 i j); unfold raw27796step2 raw27796step1; decide +kernel
      have hl : raw27796step2Labels = raw27796step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27796step2 raw27796step2Labels = mixedMoment B raw27796step3 raw27796step3Labels := by
      have ha : raw27796step3 = raw27796step2 := by apply Matrix.ext; unfold raw27796step3 raw27796step2; decide +kernel
      have hl : raw27796step2Labels = labelEmbedding1 ∘ raw27796step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27796step2 raw27796step2Labels raw27796step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw27797 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27797 raw27797Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw27797 raw27797Labels = mixedMoment B raw27797step0 raw27797step0Labels := by
      have hz : ∀ j, raw27797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27797step0 = (fun i j => raw27797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27797step0 raw27797; decide +kernel
      have hl : raw27797step0Labels = raw27797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27797 raw27797Labels permutation346 hz
    mixedMoment B raw27797step0 raw27797step0Labels = mixedMoment B raw27797step1 raw27797step1Labels := by
      have ha : raw27797step1 = (fun i j => raw27797step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27797step1 raw27797step0; decide +kernel
      have hl : raw27797step1Labels = raw27797step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27797step0 raw27797step0Labels permutation151 permutation7
    mixedMoment B raw27797step1 raw27797step1Labels = mixedMoment B raw27797step2 raw27797step2Labels := by
      have ha : raw27797step2 = -raw27797step1 := by apply Matrix.ext; change ∀ i j, raw27797step2 i j = -(raw27797step1 i j); unfold raw27797step2 raw27797step1; decide +kernel
      have hl : raw27797step2Labels = raw27797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27797step2 raw27797step2Labels = mixedMoment B raw27797step3 raw27797step3Labels := by
      have ha : raw27797step3 = raw27797step2 := by apply Matrix.ext; unfold raw27797step3 raw27797step2; decide +kernel
      have hl : raw27797step2Labels = labelEmbedding1 ∘ raw27797step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27797step2 raw27797step2Labels raw27797step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2090 node2090Labels := by rfl

def raw27798 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27798 raw27798Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw27798 raw27798Labels = mixedMoment B raw27798step0 raw27798step0Labels := by
      have ha : raw27798step0 = (fun i j => raw27798 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27798step0 raw27798; decide +kernel
      have hl : raw27798step0Labels = raw27798Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27798 raw27798Labels permutation682 permutation7
    mixedMoment B raw27798step0 raw27798step0Labels = mixedMoment B raw27798step1 raw27798step1Labels := by
      have ha : raw27798step1 = -raw27798step0 := by apply Matrix.ext; change ∀ i j, raw27798step1 i j = -(raw27798step0 i j); unfold raw27798step1 raw27798step0; decide +kernel
      have hl : raw27798step1Labels = raw27798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27798step1 raw27798step1Labels = mixedMoment B raw27798step2 raw27798step2Labels := by
      have ha : raw27798step2 = raw27798step1 := by apply Matrix.ext; unfold raw27798step2 raw27798step1; decide +kernel
      have hl : raw27798step1Labels = labelEmbedding1 ∘ raw27798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27798step1 raw27798step1Labels raw27798step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2071 node2071Labels := by rfl

def raw27799 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27799 raw27799Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw27799 raw27799Labels = mixedMoment B raw27799step0 raw27799step0Labels := by
      have hz : ∀ j, raw27799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27799step0 = (fun i j => raw27799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27799step0 raw27799; decide +kernel
      have hl : raw27799step0Labels = raw27799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27799 raw27799Labels permutation346 hz
    mixedMoment B raw27799step0 raw27799step0Labels = mixedMoment B raw27799step1 raw27799step1Labels := by
      have ha : raw27799step1 = (fun i j => raw27799step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27799step1 raw27799step0; decide +kernel
      have hl : raw27799step1Labels = raw27799step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27799step0 raw27799step0Labels permutation151 permutation7
    mixedMoment B raw27799step1 raw27799step1Labels = mixedMoment B raw27799step2 raw27799step2Labels := by
      have ha : raw27799step2 = -raw27799step1 := by apply Matrix.ext; change ∀ i j, raw27799step2 i j = -(raw27799step1 i j); unfold raw27799step2 raw27799step1; decide +kernel
      have hl : raw27799step2Labels = raw27799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27799step2 raw27799step2Labels = mixedMoment B raw27799step3 raw27799step3Labels := by
      have ha : raw27799step3 = raw27799step2 := by apply Matrix.ext; unfold raw27799step3 raw27799step2; decide +kernel
      have hl : raw27799step2Labels = labelEmbedding1 ∘ raw27799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27799step2 raw27799step2Labels raw27799step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw27800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27800step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27800step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27800step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27800 raw27800Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw27800 raw27800Labels = mixedMoment B raw27800step0 raw27800step0Labels := by
      have hz : ∀ j, raw27800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27800step0 = (fun i j => raw27800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27800step0 raw27800; decide +kernel
      have hl : raw27800step0Labels = raw27800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27800 raw27800Labels permutation346 hz
    mixedMoment B raw27800step0 raw27800step0Labels = mixedMoment B raw27800step1 raw27800step1Labels := by
      have ha : raw27800step1 = (fun i j => raw27800step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27800step1 raw27800step0; decide +kernel
      have hl : raw27800step1Labels = raw27800step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27800step0 raw27800step0Labels permutation151 permutation7
    mixedMoment B raw27800step1 raw27800step1Labels = mixedMoment B raw27800step2 raw27800step2Labels := by
      have ha : raw27800step2 = -raw27800step1 := by apply Matrix.ext; change ∀ i j, raw27800step2 i j = -(raw27800step1 i j); unfold raw27800step2 raw27800step1; decide +kernel
      have hl : raw27800step2Labels = raw27800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27800step2 raw27800step2Labels = mixedMoment B raw27800step3 raw27800step3Labels := by
      have ha : raw27800step3 = raw27800step2 := by apply Matrix.ext; unfold raw27800step3 raw27800step2; decide +kernel
      have hl : raw27800step2Labels = labelEmbedding1 ∘ raw27800step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27800step2 raw27800step2Labels raw27800step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1639 node1639Labels := by rfl

def raw27801 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-3, 0, 3]]
def raw27801step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw27801step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27801step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw27801step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27801step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw27801step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27801 raw27801Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw27801 raw27801Labels = mixedMoment B raw27801step0 raw27801step0Labels := by
      have hz : ∀ j, raw27801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27801step0 = (fun i j => raw27801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27801step0 raw27801; decide +kernel
      have hl : raw27801step0Labels = raw27801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27801 raw27801Labels permutation434 hz
    mixedMoment B raw27801step0 raw27801step0Labels = mixedMoment B raw27801step1 raw27801step1Labels := by
      have hz : ∀ j, raw27801step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27801step1 = (fun i j => raw27801step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27801step1 raw27801step0; decide +kernel
      have hl : raw27801step1Labels = raw27801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27801step0 raw27801step0Labels permutation80 hz
    mixedMoment B raw27801step1 raw27801step1Labels = mixedMoment B raw27801step2 raw27801step2Labels := by
      have ha : raw27801step2 = (fun i j => raw27801step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27801step2 raw27801step1; decide +kernel
      have hl : raw27801step2Labels = raw27801step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27801step1 raw27801step1Labels permutation31 permutation7
    mixedMoment B raw27801step2 raw27801step2Labels = mixedMoment B raw27801step3 raw27801step3Labels := by
      have ha : raw27801step3 = -raw27801step2 := by apply Matrix.ext; change ∀ i j, raw27801step3 i j = -(raw27801step2 i j); unfold raw27801step3 raw27801step2; decide +kernel
      have hl : raw27801step3Labels = raw27801step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27801step3 raw27801step3Labels = mixedMoment B raw27801step4 raw27801step4Labels := by
      have ha : raw27801step4 = raw27801step3 := by apply Matrix.ext; unfold raw27801step4 raw27801step3; decide +kernel
      have hl : raw27801step3Labels = labelEmbedding1 ∘ raw27801step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27801step3 raw27801step3Labels raw27801step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2136 node2136Labels := by rfl

def raw27802 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -3, 1], ![-3, 0, 3]]
def raw27802step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw27802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27802step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27802step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27802step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27802 raw27802Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw27802 raw27802Labels = mixedMoment B raw27802step0 raw27802step0Labels := by
      have hz : ∀ j, raw27802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27802step0 = (fun i j => raw27802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27802step0 raw27802; decide +kernel
      have hl : raw27802step0Labels = raw27802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27802 raw27802Labels permutation434 hz
    mixedMoment B raw27802step0 raw27802step0Labels = mixedMoment B raw27802step1 raw27802step1Labels := by
      have hz : ∀ j, raw27802step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27802step1 = (fun i j => raw27802step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27802step1 raw27802step0; decide +kernel
      have hl : raw27802step1Labels = raw27802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27802step0 raw27802step0Labels permutation80 hz
    mixedMoment B raw27802step1 raw27802step1Labels = mixedMoment B raw27802step2 raw27802step2Labels := by
      have ha : raw27802step2 = (fun i j => raw27802step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27802step2 raw27802step1; decide +kernel
      have hl : raw27802step2Labels = raw27802step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27802step1 raw27802step1Labels permutation31 permutation7
    mixedMoment B raw27802step2 raw27802step2Labels = mixedMoment B raw27802step3 raw27802step3Labels := by
      have ha : raw27802step3 = -raw27802step2 := by apply Matrix.ext; change ∀ i j, raw27802step3 i j = -(raw27802step2 i j); unfold raw27802step3 raw27802step2; decide +kernel
      have hl : raw27802step3Labels = raw27802step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27802step3 raw27802step3Labels = mixedMoment B raw27802step4 raw27802step4Labels := by
      have ha : raw27802step4 = raw27802step3 := by apply Matrix.ext; unfold raw27802step4 raw27802step3; decide +kernel
      have hl : raw27802step3Labels = labelEmbedding1 ∘ raw27802step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27802step3 raw27802step3Labels raw27802step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2134 node2134Labels := by rfl

def raw27803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27803step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27803step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27803step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27803 raw27803Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw27803 raw27803Labels = mixedMoment B raw27803step0 raw27803step0Labels := by
      have hz : ∀ j, raw27803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27803step0 = (fun i j => raw27803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27803step0 raw27803; decide +kernel
      have hl : raw27803step0Labels = raw27803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27803 raw27803Labels permutation434 hz
    mixedMoment B raw27803step0 raw27803step0Labels = mixedMoment B raw27803step1 raw27803step1Labels := by
      have ha : raw27803step1 = (fun i j => raw27803step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27803step1 raw27803step0; decide +kernel
      have hl : raw27803step1Labels = raw27803step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27803step0 raw27803step0Labels permutation151 permutation7
    mixedMoment B raw27803step1 raw27803step1Labels = mixedMoment B raw27803step2 raw27803step2Labels := by
      have ha : raw27803step2 = -raw27803step1 := by apply Matrix.ext; change ∀ i j, raw27803step2 i j = -(raw27803step1 i j); unfold raw27803step2 raw27803step1; decide +kernel
      have hl : raw27803step2Labels = raw27803step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27803step2 raw27803step2Labels = mixedMoment B raw27803step3 raw27803step3Labels := by
      have ha : raw27803step3 = raw27803step2 := by apply Matrix.ext; unfold raw27803step3 raw27803step2; decide +kernel
      have hl : raw27803step2Labels = labelEmbedding1 ∘ raw27803step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27803step2 raw27803step2Labels raw27803step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2121 node2121Labels := by rfl

def raw27804 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27804step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27804step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27804step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27804 raw27804Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw27804 raw27804Labels = mixedMoment B raw27804step0 raw27804step0Labels := by
      have hz : ∀ j, raw27804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27804step0 = (fun i j => raw27804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27804step0 raw27804; decide +kernel
      have hl : raw27804step0Labels = raw27804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27804 raw27804Labels permutation346 hz
    mixedMoment B raw27804step0 raw27804step0Labels = mixedMoment B raw27804step1 raw27804step1Labels := by
      have ha : raw27804step1 = (fun i j => raw27804step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27804step1 raw27804step0; decide +kernel
      have hl : raw27804step1Labels = raw27804step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27804step0 raw27804step0Labels permutation151 permutation7
    mixedMoment B raw27804step1 raw27804step1Labels = mixedMoment B raw27804step2 raw27804step2Labels := by
      have ha : raw27804step2 = -raw27804step1 := by apply Matrix.ext; change ∀ i j, raw27804step2 i j = -(raw27804step1 i j); unfold raw27804step2 raw27804step1; decide +kernel
      have hl : raw27804step2Labels = raw27804step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27804step2 raw27804step2Labels = mixedMoment B raw27804step3 raw27804step3Labels := by
      have ha : raw27804step3 = raw27804step2 := by apply Matrix.ext; unfold raw27804step3 raw27804step2; decide +kernel
      have hl : raw27804step2Labels = labelEmbedding1 ∘ raw27804step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27804step2 raw27804step2Labels raw27804step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2121 node2121Labels := by rfl

def raw27805 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw27805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw27805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -3, 1], ![-4, 1, 3]]
def raw27805step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27805step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27805step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27805step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27805step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27805step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27805 raw27805Labels = mixedMoment B node1659 node1659Labels := by
  calc
    mixedMoment B raw27805 raw27805Labels = mixedMoment B raw27805step0 raw27805step0Labels := by
      have hz : ∀ j, raw27805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27805step0 = (fun i j => raw27805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27805step0 raw27805; decide +kernel
      have hl : raw27805step0Labels = raw27805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27805 raw27805Labels permutation434 hz
    mixedMoment B raw27805step0 raw27805step0Labels = mixedMoment B raw27805step1 raw27805step1Labels := by
      have hz : ∀ j, raw27805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27805step1 = (fun i j => raw27805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27805step1 raw27805step0; decide +kernel
      have hl : raw27805step1Labels = raw27805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27805step0 raw27805step0Labels permutation80 hz
    mixedMoment B raw27805step1 raw27805step1Labels = mixedMoment B raw27805step2 raw27805step2Labels := by
      have ha : raw27805step2 = (fun i j => raw27805step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27805step2 raw27805step1; decide +kernel
      have hl : raw27805step2Labels = raw27805step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27805step1 raw27805step1Labels permutation31 permutation7
    mixedMoment B raw27805step2 raw27805step2Labels = mixedMoment B raw27805step3 raw27805step3Labels := by
      have ha : raw27805step3 = -raw27805step2 := by apply Matrix.ext; change ∀ i j, raw27805step3 i j = -(raw27805step2 i j); unfold raw27805step3 raw27805step2; decide +kernel
      have hl : raw27805step3Labels = raw27805step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27805step3 raw27805step3Labels = mixedMoment B raw27805step4 raw27805step4Labels := by
      have ha : raw27805step4 = raw27805step3 := by apply Matrix.ext; unfold raw27805step4 raw27805step3; decide +kernel
      have hl : raw27805step3Labels = labelEmbedding1 ∘ raw27805step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27805step3 raw27805step3Labels raw27805step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1659 node1659Labels := by rfl

def raw27806 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27806step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27806step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27806step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27806step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27806 raw27806Labels = mixedMoment B node2642 node2642Labels := by
  calc
    mixedMoment B raw27806 raw27806Labels = mixedMoment B raw27806step0 raw27806step0Labels := by
      have hz : ∀ j, raw27806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27806step0 = (fun i j => raw27806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27806step0 raw27806; decide +kernel
      have hl : raw27806step0Labels = raw27806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27806 raw27806Labels permutation434 hz
    mixedMoment B raw27806step0 raw27806step0Labels = mixedMoment B raw27806step1 raw27806step1Labels := by
      have hz : ∀ j, raw27806step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27806step1 = (fun i j => raw27806step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27806step1 raw27806step0; decide +kernel
      have hl : raw27806step1Labels = raw27806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27806step0 raw27806step0Labels permutation80 hz
    mixedMoment B raw27806step1 raw27806step1Labels = mixedMoment B raw27806step2 raw27806step2Labels := by
      have ha : raw27806step2 = (fun i j => raw27806step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27806step2 raw27806step1; decide +kernel
      have hl : raw27806step2Labels = raw27806step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27806step1 raw27806step1Labels permutation31 permutation7
    mixedMoment B raw27806step2 raw27806step2Labels = mixedMoment B raw27806step3 raw27806step3Labels := by
      have ha : raw27806step3 = -raw27806step2 := by apply Matrix.ext; change ∀ i j, raw27806step3 i j = -(raw27806step2 i j); unfold raw27806step3 raw27806step2; decide +kernel
      have hl : raw27806step3Labels = raw27806step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27806step3 raw27806step3Labels = mixedMoment B raw27806step4 raw27806step4Labels := by
      have ha : raw27806step4 = raw27806step3 := by apply Matrix.ext; unfold raw27806step4 raw27806step3; decide +kernel
      have hl : raw27806step3Labels = labelEmbedding1 ∘ raw27806step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27806step3 raw27806step3Labels raw27806step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2642 node2642Labels := by rfl

def raw27807 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27807step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27807step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27807step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27807step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27807step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27807step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27807step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27807 raw27807Labels = mixedMoment B node2640 node2640Labels := by
  calc
    mixedMoment B raw27807 raw27807Labels = mixedMoment B raw27807step0 raw27807step0Labels := by
      have hz : ∀ j, raw27807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27807step0 = (fun i j => raw27807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27807step0 raw27807; decide +kernel
      have hl : raw27807step0Labels = raw27807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27807 raw27807Labels permutation434 hz
    mixedMoment B raw27807step0 raw27807step0Labels = mixedMoment B raw27807step1 raw27807step1Labels := by
      have hz : ∀ j, raw27807step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27807step1 = (fun i j => raw27807step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27807step1 raw27807step0; decide +kernel
      have hl : raw27807step1Labels = raw27807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27807step0 raw27807step0Labels permutation80 hz
    mixedMoment B raw27807step1 raw27807step1Labels = mixedMoment B raw27807step2 raw27807step2Labels := by
      have ha : raw27807step2 = (fun i j => raw27807step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27807step2 raw27807step1; decide +kernel
      have hl : raw27807step2Labels = raw27807step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27807step1 raw27807step1Labels permutation31 permutation7
    mixedMoment B raw27807step2 raw27807step2Labels = mixedMoment B raw27807step3 raw27807step3Labels := by
      have ha : raw27807step3 = -raw27807step2 := by apply Matrix.ext; change ∀ i j, raw27807step3 i j = -(raw27807step2 i j); unfold raw27807step3 raw27807step2; decide +kernel
      have hl : raw27807step3Labels = raw27807step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27807step3 raw27807step3Labels = mixedMoment B raw27807step4 raw27807step4Labels := by
      have ha : raw27807step4 = raw27807step3 := by apply Matrix.ext; unfold raw27807step4 raw27807step3; decide +kernel
      have hl : raw27807step3Labels = labelEmbedding1 ∘ raw27807step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27807step3 raw27807step3Labels raw27807step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2640 node2640Labels := by rfl

def raw27808 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27808 raw27808Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw27808 raw27808Labels = mixedMoment B raw27808step0 raw27808step0Labels := by
      have hz : ∀ j, raw27808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27808step0 = (fun i j => raw27808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27808step0 raw27808; decide +kernel
      have hl : raw27808step0Labels = raw27808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27808 raw27808Labels permutation434 hz
    mixedMoment B raw27808step0 raw27808step0Labels = mixedMoment B raw27808step1 raw27808step1Labels := by
      have ha : raw27808step1 = (fun i j => raw27808step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27808step1 raw27808step0; decide +kernel
      have hl : raw27808step1Labels = raw27808step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27808step0 raw27808step0Labels permutation151 permutation7
    mixedMoment B raw27808step1 raw27808step1Labels = mixedMoment B raw27808step2 raw27808step2Labels := by
      have ha : raw27808step2 = -raw27808step1 := by apply Matrix.ext; change ∀ i j, raw27808step2 i j = -(raw27808step1 i j); unfold raw27808step2 raw27808step1; decide +kernel
      have hl : raw27808step2Labels = raw27808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27808step2 raw27808step2Labels = mixedMoment B raw27808step3 raw27808step3Labels := by
      have ha : raw27808step3 = raw27808step2 := by apply Matrix.ext; unfold raw27808step3 raw27808step2; decide +kernel
      have hl : raw27808step2Labels = labelEmbedding1 ∘ raw27808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27808step2 raw27808step2Labels raw27808step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw27809 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27809step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27809 raw27809Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw27809 raw27809Labels = mixedMoment B raw27809step0 raw27809step0Labels := by
      have hz : ∀ j, raw27809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27809step0 = (fun i j => raw27809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27809step0 raw27809; decide +kernel
      have hl : raw27809step0Labels = raw27809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27809 raw27809Labels permutation346 hz
    mixedMoment B raw27809step0 raw27809step0Labels = mixedMoment B raw27809step1 raw27809step1Labels := by
      have ha : raw27809step1 = (fun i j => raw27809step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27809step1 raw27809step0; decide +kernel
      have hl : raw27809step1Labels = raw27809step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27809step0 raw27809step0Labels permutation151 permutation7
    mixedMoment B raw27809step1 raw27809step1Labels = mixedMoment B raw27809step2 raw27809step2Labels := by
      have ha : raw27809step2 = -raw27809step1 := by apply Matrix.ext; change ∀ i j, raw27809step2 i j = -(raw27809step1 i j); unfold raw27809step2 raw27809step1; decide +kernel
      have hl : raw27809step2Labels = raw27809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27809step2 raw27809step2Labels = mixedMoment B raw27809step3 raw27809step3Labels := by
      have ha : raw27809step3 = raw27809step2 := by apply Matrix.ext; unfold raw27809step3 raw27809step2; decide +kernel
      have hl : raw27809step2Labels = labelEmbedding1 ∘ raw27809step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27809step2 raw27809step2Labels raw27809step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw27810 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27810step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27810step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27810step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27810step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27810step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27810 raw27810Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw27810 raw27810Labels = mixedMoment B raw27810step0 raw27810step0Labels := by
      have hz : ∀ j, raw27810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27810step0 = (fun i j => raw27810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27810step0 raw27810; decide +kernel
      have hl : raw27810step0Labels = raw27810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27810 raw27810Labels permutation434 hz
    mixedMoment B raw27810step0 raw27810step0Labels = mixedMoment B raw27810step1 raw27810step1Labels := by
      have hz : ∀ j, raw27810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27810step1 = (fun i j => raw27810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27810step1 raw27810step0; decide +kernel
      have hl : raw27810step1Labels = raw27810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27810step0 raw27810step0Labels permutation80 hz
    mixedMoment B raw27810step1 raw27810step1Labels = mixedMoment B raw27810step2 raw27810step2Labels := by
      have ha : raw27810step2 = (fun i j => raw27810step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27810step2 raw27810step1; decide +kernel
      have hl : raw27810step2Labels = raw27810step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27810step1 raw27810step1Labels permutation31 permutation7
    mixedMoment B raw27810step2 raw27810step2Labels = mixedMoment B raw27810step3 raw27810step3Labels := by
      have ha : raw27810step3 = -raw27810step2 := by apply Matrix.ext; change ∀ i j, raw27810step3 i j = -(raw27810step2 i j); unfold raw27810step3 raw27810step2; decide +kernel
      have hl : raw27810step3Labels = raw27810step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27810step3 raw27810step3Labels = mixedMoment B raw27810step4 raw27810step4Labels := by
      have ha : raw27810step4 = raw27810step3 := by apply Matrix.ext; unfold raw27810step4 raw27810step3; decide +kernel
      have hl : raw27810step3Labels = labelEmbedding1 ∘ raw27810step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27810step3 raw27810step3Labels raw27810step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw27811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27811 raw27811Labels = mixedMoment B node1159 node1159Labels := by
  calc
    mixedMoment B raw27811 raw27811Labels = mixedMoment B raw27811step0 raw27811step0Labels := by
      have hz : ∀ j, raw27811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27811step0 = (fun i j => raw27811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27811step0 raw27811; decide +kernel
      have hl : raw27811step0Labels = raw27811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27811 raw27811Labels permutation346 hz
    mixedMoment B raw27811step0 raw27811step0Labels = mixedMoment B raw27811step1 raw27811step1Labels := by
      have ha : raw27811step1 = (fun i j => raw27811step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27811step1 raw27811step0; decide +kernel
      have hl : raw27811step1Labels = raw27811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27811step0 raw27811step0Labels permutation34 permutation2
    _ = mixedMoment B node1159 node1159Labels := by rfl

def raw27812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27812 raw27812Labels = mixedMoment B node2355 node2355Labels := by
  calc
    mixedMoment B raw27812 raw27812Labels = mixedMoment B raw27812step0 raw27812step0Labels := by
      have hz : ∀ j, raw27812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27812step0 = (fun i j => raw27812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27812step0 raw27812; decide +kernel
      have hl : raw27812step0Labels = raw27812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27812 raw27812Labels permutation346 hz
    mixedMoment B raw27812step0 raw27812step0Labels = mixedMoment B raw27812step1 raw27812step1Labels := by
      have ha : raw27812step1 = (fun i j => raw27812step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27812step1 raw27812step0; decide +kernel
      have hl : raw27812step1Labels = raw27812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27812step0 raw27812step0Labels permutation34 permutation2
    _ = mixedMoment B node2355 node2355Labels := by rfl

def raw27813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw27813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27813 raw27813Labels = mixedMoment B node2436 node2436Labels := by
  calc
    mixedMoment B raw27813 raw27813Labels = mixedMoment B raw27813step0 raw27813step0Labels := by
      have ha : raw27813step0 = (fun i j => raw27813 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27813step0 raw27813; decide +kernel
      have hl : raw27813step0Labels = raw27813Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27813 raw27813Labels permutation662 permutation2
    mixedMoment B raw27813step0 raw27813step0Labels = mixedMoment B raw27813step1 raw27813step1Labels := by
      have ha : raw27813step1 = -raw27813step0 := by apply Matrix.ext; change ∀ i j, raw27813step1 i j = -(raw27813step0 i j); unfold raw27813step1 raw27813step0; decide +kernel
      have hl : raw27813step1Labels = raw27813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2436 node2436Labels := by rfl

def raw27814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27814 raw27814Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw27814 raw27814Labels = mixedMoment B raw27814step0 raw27814step0Labels := by
      have hz : ∀ j, raw27814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27814step0 = (fun i j => raw27814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27814step0 raw27814; decide +kernel
      have hl : raw27814step0Labels = raw27814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27814 raw27814Labels permutation346 hz
    _ = mixedMoment B node2569 node2569Labels := by rfl

def raw27815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw27815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw27815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27815 raw27815Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw27815 raw27815Labels = mixedMoment B raw27815step0 raw27815step0Labels := by
      have hz : ∀ j, raw27815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27815step0 = (fun i j => raw27815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27815step0 raw27815; decide +kernel
      have hl : raw27815step0Labels = raw27815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27815 raw27815Labels permutation346 hz
    mixedMoment B raw27815step0 raw27815step0Labels = mixedMoment B raw27815step1 raw27815step1Labels := by
      have ha : raw27815step1 = (fun i j => raw27815step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27815step1 raw27815step0; decide +kernel
      have hl : raw27815step1Labels = raw27815step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27815step0 raw27815step0Labels permutation145 permutation2
    mixedMoment B raw27815step1 raw27815step1Labels = mixedMoment B raw27815step2 raw27815step2Labels := by
      have ha : raw27815step2 = -raw27815step1 := by apply Matrix.ext; change ∀ i j, raw27815step2 i j = -(raw27815step1 i j); unfold raw27815step2 raw27815step1; decide +kernel
      have hl : raw27815step2Labels = raw27815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw27816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw27816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw27816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27816 raw27816Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw27816 raw27816Labels = mixedMoment B raw27816step0 raw27816step0Labels := by
      have hz : ∀ j, raw27816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27816step0 = (fun i j => raw27816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27816step0 raw27816; decide +kernel
      have hl : raw27816step0Labels = raw27816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27816 raw27816Labels permutation346 hz
    mixedMoment B raw27816step0 raw27816step0Labels = mixedMoment B raw27816step1 raw27816step1Labels := by
      have ha : raw27816step1 = (fun i j => raw27816step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27816step1 raw27816step0; decide +kernel
      have hl : raw27816step1Labels = raw27816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27816step0 raw27816step0Labels permutation34 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw27817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27817step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27817 raw27817Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw27817 raw27817Labels = mixedMoment B raw27817step0 raw27817step0Labels := by
      have hz : ∀ j, raw27817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27817step0 = (fun i j => raw27817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27817step0 raw27817; decide +kernel
      have hl : raw27817step0Labels = raw27817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27817 raw27817Labels permutation346 hz
    mixedMoment B raw27817step0 raw27817step0Labels = mixedMoment B raw27817step1 raw27817step1Labels := by
      have ha : raw27817step1 = (fun i j => raw27817step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27817step1 raw27817step0; decide +kernel
      have hl : raw27817step1Labels = raw27817step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27817step0 raw27817step0Labels permutation149 permutation2
    mixedMoment B raw27817step1 raw27817step1Labels = mixedMoment B raw27817step2 raw27817step2Labels := by
      have ha : raw27817step2 = -raw27817step1 := by apply Matrix.ext; change ∀ i j, raw27817step2 i j = -(raw27817step1 i j); unfold raw27817step2 raw27817step1; decide +kernel
      have hl : raw27817step2Labels = raw27817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw27818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27818 raw27818Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw27818 raw27818Labels = mixedMoment B raw27818step0 raw27818step0Labels := by
      have hz : ∀ j, raw27818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27818step0 = (fun i j => raw27818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27818step0 raw27818; decide +kernel
      have hl : raw27818step0Labels = raw27818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27818 raw27818Labels permutation346 hz
    mixedMoment B raw27818step0 raw27818step0Labels = mixedMoment B raw27818step1 raw27818step1Labels := by
      have ha : raw27818step1 = (fun i j => raw27818step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27818step1 raw27818step0; decide +kernel
      have hl : raw27818step1Labels = raw27818step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27818step0 raw27818step0Labels permutation149 permutation2
    mixedMoment B raw27818step1 raw27818step1Labels = mixedMoment B raw27818step2 raw27818step2Labels := by
      have ha : raw27818step2 = -raw27818step1 := by apply Matrix.ext; change ∀ i j, raw27818step2 i j = -(raw27818step1 i j); unfold raw27818step2 raw27818step1; decide +kernel
      have hl : raw27818step2Labels = raw27818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw27819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27819 raw27819Labels = mixedMoment B node2847 node2847Labels := by
  calc
    mixedMoment B raw27819 raw27819Labels = mixedMoment B raw27819step0 raw27819step0Labels := by
      have ha : raw27819step0 = (fun i j => raw27819 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27819step0 raw27819; decide +kernel
      have hl : raw27819step0Labels = raw27819Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27819 raw27819Labels permutation680 permutation2
    mixedMoment B raw27819step0 raw27819step0Labels = mixedMoment B raw27819step1 raw27819step1Labels := by
      have ha : raw27819step1 = -raw27819step0 := by apply Matrix.ext; change ∀ i j, raw27819step1 i j = -(raw27819step0 i j); unfold raw27819step1 raw27819step0; decide +kernel
      have hl : raw27819step1Labels = raw27819step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2847 node2847Labels := by rfl

def raw27820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27820 raw27820Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw27820 raw27820Labels = mixedMoment B raw27820step0 raw27820step0Labels := by
      have hz : ∀ j, raw27820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27820step0 = (fun i j => raw27820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27820step0 raw27820; decide +kernel
      have hl : raw27820step0Labels = raw27820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27820 raw27820Labels permutation346 hz
    mixedMoment B raw27820step0 raw27820step0Labels = mixedMoment B raw27820step1 raw27820step1Labels := by
      have ha : raw27820step1 = (fun i j => raw27820step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27820step1 raw27820step0; decide +kernel
      have hl : raw27820step1Labels = raw27820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27820step0 raw27820step0Labels permutation151 permutation2
    mixedMoment B raw27820step1 raw27820step1Labels = mixedMoment B raw27820step2 raw27820step2Labels := by
      have ha : raw27820step2 = -raw27820step1 := by apply Matrix.ext; change ∀ i j, raw27820step2 i j = -(raw27820step1 i j); unfold raw27820step2 raw27820step1; decide +kernel
      have hl : raw27820step2Labels = raw27820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw27821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27821 raw27821Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw27821 raw27821Labels = mixedMoment B raw27821step0 raw27821step0Labels := by
      have hz : ∀ j, raw27821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27821step0 = (fun i j => raw27821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27821step0 raw27821; decide +kernel
      have hl : raw27821step0Labels = raw27821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27821 raw27821Labels permutation346 hz
    mixedMoment B raw27821step0 raw27821step0Labels = mixedMoment B raw27821step1 raw27821step1Labels := by
      have ha : raw27821step1 = (fun i j => raw27821step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27821step1 raw27821step0; decide +kernel
      have hl : raw27821step1Labels = raw27821step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27821step0 raw27821step0Labels permutation149 permutation2
    mixedMoment B raw27821step1 raw27821step1Labels = mixedMoment B raw27821step2 raw27821step2Labels := by
      have ha : raw27821step2 = -raw27821step1 := by apply Matrix.ext; change ∀ i j, raw27821step2 i j = -(raw27821step1 i j); unfold raw27821step2 raw27821step1; decide +kernel
      have hl : raw27821step2Labels = raw27821step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2815 node2815Labels := by rfl

def raw27822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw27822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw27822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27822 raw27822Labels = mixedMoment B node1320 node1320Labels := by
  calc
    mixedMoment B raw27822 raw27822Labels = mixedMoment B raw27822step0 raw27822step0Labels := by
      have hz : ∀ j, raw27822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27822step0 = (fun i j => raw27822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27822step0 raw27822; decide +kernel
      have hl : raw27822step0Labels = raw27822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27822 raw27822Labels permutation346 hz
    mixedMoment B raw27822step0 raw27822step0Labels = mixedMoment B raw27822step1 raw27822step1Labels := by
      have ha : raw27822step1 = (fun i j => raw27822step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27822step1 raw27822step0; decide +kernel
      have hl : raw27822step1Labels = raw27822step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27822step0 raw27822step0Labels permutation149 permutation2
    mixedMoment B raw27822step1 raw27822step1Labels = mixedMoment B raw27822step2 raw27822step2Labels := by
      have ha : raw27822step2 = -raw27822step1 := by apply Matrix.ext; change ∀ i j, raw27822step2 i j = -(raw27822step1 i j); unfold raw27822step2 raw27822step1; decide +kernel
      have hl : raw27822step2Labels = raw27822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1320 node1320Labels := by rfl

def raw27823 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw27823Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27823step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw27823step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27823step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27823step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27823step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw27823step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27823 raw27823Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw27823 raw27823Labels = mixedMoment B raw27823step0 raw27823step0Labels := by
      have hz : ∀ j, raw27823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27823step0 = (fun i j => raw27823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27823step0 raw27823; decide +kernel
      have hl : raw27823step0Labels = raw27823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27823 raw27823Labels permutation346 hz
    mixedMoment B raw27823step0 raw27823step0Labels = mixedMoment B raw27823step1 raw27823step1Labels := by
      have ha : raw27823step1 = (fun i j => raw27823step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27823step1 raw27823step0; decide +kernel
      have hl : raw27823step1Labels = raw27823step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27823step0 raw27823step0Labels permutation122 permutation0
    mixedMoment B raw27823step1 raw27823step1Labels = mixedMoment B raw27823step2 raw27823step2Labels := by
      have ha : raw27823step2 = -raw27823step1 := by apply Matrix.ext; change ∀ i j, raw27823step2 i j = -(raw27823step1 i j); unfold raw27823step2 raw27823step1; decide +kernel
      have hl : raw27823step2Labels = raw27823step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw27824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27824 raw27824Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw27824 raw27824Labels = mixedMoment B raw27824step0 raw27824step0Labels := by
      have hz : ∀ j, raw27824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27824step0 = (fun i j => raw27824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27824step0 raw27824; decide +kernel
      have hl : raw27824step0Labels = raw27824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27824 raw27824Labels permutation346 hz
    _ = mixedMoment B node1334 node1334Labels := by rfl

def raw27825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27825 raw27825Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw27825 raw27825Labels = mixedMoment B raw27825step0 raw27825step0Labels := by
      have hz : ∀ j, raw27825 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27825step0 = (fun i j => raw27825 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27825step0 raw27825; decide +kernel
      have hl : raw27825step0Labels = raw27825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27825 raw27825Labels permutation346 hz
    mixedMoment B raw27825step0 raw27825step0Labels = mixedMoment B raw27825step1 raw27825step1Labels := by
      have ha : raw27825step1 = (fun i j => raw27825step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27825step1 raw27825step0; decide +kernel
      have hl : raw27825step1Labels = raw27825step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27825step0 raw27825step0Labels permutation151 permutation2
    mixedMoment B raw27825step1 raw27825step1Labels = mixedMoment B raw27825step2 raw27825step2Labels := by
      have ha : raw27825step2 = -raw27825step1 := by apply Matrix.ext; change ∀ i j, raw27825step2 i j = -(raw27825step1 i j); unfold raw27825step2 raw27825step1; decide +kernel
      have hl : raw27825step2Labels = raw27825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2802 node2802Labels := by rfl

def raw27826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27826 raw27826Labels = mixedMoment B node2797 node2797Labels := by
  calc
    mixedMoment B raw27826 raw27826Labels = mixedMoment B raw27826step0 raw27826step0Labels := by
      have ha : raw27826step0 = (fun i j => raw27826 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27826step0 raw27826; decide +kernel
      have hl : raw27826step0Labels = raw27826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27826 raw27826Labels permutation688 permutation2
    mixedMoment B raw27826step0 raw27826step0Labels = mixedMoment B raw27826step1 raw27826step1Labels := by
      have ha : raw27826step1 = -raw27826step0 := by apply Matrix.ext; change ∀ i j, raw27826step1 i j = -(raw27826step0 i j); unfold raw27826step1 raw27826step0; decide +kernel
      have hl : raw27826step1Labels = raw27826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2797 node2797Labels := by rfl

def raw27827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw27827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw27827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27827 raw27827Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw27827 raw27827Labels = mixedMoment B raw27827step0 raw27827step0Labels := by
      have hz : ∀ j, raw27827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27827step0 = (fun i j => raw27827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27827step0 raw27827; decide +kernel
      have hl : raw27827step0Labels = raw27827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27827 raw27827Labels permutation346 hz
    mixedMoment B raw27827step0 raw27827step0Labels = mixedMoment B raw27827step1 raw27827step1Labels := by
      have ha : raw27827step1 = (fun i j => raw27827step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27827step1 raw27827step0; decide +kernel
      have hl : raw27827step1Labels = raw27827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27827step0 raw27827step0Labels permutation33 permutation2
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw27828 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw27828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw27828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27828 raw27828Labels = mixedMoment B node2099 node2099Labels := by
  calc
    mixedMoment B raw27828 raw27828Labels = mixedMoment B raw27828step0 raw27828step0Labels := by
      have hz : ∀ j, raw27828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27828step0 = (fun i j => raw27828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27828step0 raw27828; decide +kernel
      have hl : raw27828step0Labels = raw27828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27828 raw27828Labels permutation346 hz
    mixedMoment B raw27828step0 raw27828step0Labels = mixedMoment B raw27828step1 raw27828step1Labels := by
      have ha : raw27828step1 = (fun i j => raw27828step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27828step1 raw27828step0; decide +kernel
      have hl : raw27828step1Labels = raw27828step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27828step0 raw27828step0Labels permutation44 permutation4
    mixedMoment B raw27828step1 raw27828step1Labels = mixedMoment B raw27828step2 raw27828step2Labels := by
      have ha : raw27828step2 = -raw27828step1 := by apply Matrix.ext; change ∀ i j, raw27828step2 i j = -(raw27828step1 i j); unfold raw27828step2 raw27828step1; decide +kernel
      have hl : raw27828step2Labels = raw27828step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2099 node2099Labels := by rfl

def raw27829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw27829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27829 raw27829Labels = mixedMoment B node2074 node2074Labels := by
  calc
    mixedMoment B raw27829 raw27829Labels = mixedMoment B raw27829step0 raw27829step0Labels := by
      have ha : raw27829step0 = (fun i j => raw27829 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27829step0 raw27829; decide +kernel
      have hl : raw27829step0Labels = raw27829Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27829 raw27829Labels permutation224 permutation4
    mixedMoment B raw27829step0 raw27829step0Labels = mixedMoment B raw27829step1 raw27829step1Labels := by
      have ha : raw27829step1 = -raw27829step0 := by apply Matrix.ext; change ∀ i j, raw27829step1 i j = -(raw27829step0 i j); unfold raw27829step1 raw27829step0; decide +kernel
      have hl : raw27829step1Labels = raw27829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2074 node2074Labels := by rfl

def raw27830 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw27830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw27830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27830 raw27830Labels = mixedMoment B node2081 node2081Labels := by
  calc
    mixedMoment B raw27830 raw27830Labels = mixedMoment B raw27830step0 raw27830step0Labels := by
      have hz : ∀ j, raw27830 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27830step0 = (fun i j => raw27830 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27830step0 raw27830; decide +kernel
      have hl : raw27830step0Labels = raw27830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27830 raw27830Labels permutation346 hz
    mixedMoment B raw27830step0 raw27830step0Labels = mixedMoment B raw27830step1 raw27830step1Labels := by
      have ha : raw27830step1 = (fun i j => raw27830step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27830step1 raw27830step0; decide +kernel
      have hl : raw27830step1Labels = raw27830step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27830step0 raw27830step0Labels permutation44 permutation4
    mixedMoment B raw27830step1 raw27830step1Labels = mixedMoment B raw27830step2 raw27830step2Labels := by
      have ha : raw27830step2 = -raw27830step1 := by apply Matrix.ext; change ∀ i j, raw27830step2 i j = -(raw27830step1 i j); unfold raw27830step2 raw27830step1; decide +kernel
      have hl : raw27830step2Labels = raw27830step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2081 node2081Labels := by rfl

def raw27831 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw27831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27831 raw27831Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw27831 raw27831Labels = mixedMoment B raw27831step0 raw27831step0Labels := by
      have hz : ∀ j, raw27831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27831step0 = (fun i j => raw27831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27831step0 raw27831; decide +kernel
      have hl : raw27831step0Labels = raw27831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27831 raw27831Labels permutation346 hz
    mixedMoment B raw27831step0 raw27831step0Labels = mixedMoment B raw27831step1 raw27831step1Labels := by
      have ha : raw27831step1 = (fun i j => raw27831step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27831step1 raw27831step0; decide +kernel
      have hl : raw27831step1Labels = raw27831step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27831step0 raw27831step0Labels permutation143 permutation4
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw27832 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27832 raw27832Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw27832 raw27832Labels = mixedMoment B raw27832step0 raw27832step0Labels := by
      have hz : ∀ j, raw27832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27832step0 = (fun i j => raw27832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27832step0 raw27832; decide +kernel
      have hl : raw27832step0Labels = raw27832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27832 raw27832Labels permutation346 hz
    mixedMoment B raw27832step0 raw27832step0Labels = mixedMoment B raw27832step1 raw27832step1Labels := by
      have ha : raw27832step1 = (fun i j => raw27832step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27832step1 raw27832step0; decide +kernel
      have hl : raw27832step1Labels = raw27832step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27832step0 raw27832step0Labels permutation145 permutation4
    _ = mixedMoment B node2047 node2047Labels := by rfl

def raw27833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw27833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27833 raw27833Labels = mixedMoment B node2015 node2015Labels := by
  calc
    mixedMoment B raw27833 raw27833Labels = mixedMoment B raw27833step0 raw27833step0Labels := by
      have ha : raw27833step0 = (fun i j => raw27833 (permutation654 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27833step0 raw27833; decide +kernel
      have hl : raw27833step0Labels = raw27833Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27833 raw27833Labels permutation654 permutation4
    _ = mixedMoment B node2015 node2015Labels := by rfl

def raw27834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 1, 1], ![0, -3, 3]]
def raw27834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw27834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27834 raw27834Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw27834 raw27834Labels = mixedMoment B raw27834step0 raw27834step0Labels := by
      have hz : ∀ j, raw27834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27834step0 = (fun i j => raw27834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27834step0 raw27834; decide +kernel
      have hl : raw27834step0Labels = raw27834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27834 raw27834Labels permutation434 hz
    mixedMoment B raw27834step0 raw27834step0Labels = mixedMoment B raw27834step1 raw27834step1Labels := by
      have hz : ∀ j, raw27834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27834step1 = (fun i j => raw27834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27834step1 raw27834step0; decide +kernel
      have hl : raw27834step1Labels = raw27834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27834step0 raw27834step0Labels permutation80 hz
    mixedMoment B raw27834step1 raw27834step1Labels = mixedMoment B raw27834step2 raw27834step2Labels := by
      have ha : raw27834step2 = (fun i j => raw27834step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27834step2 raw27834step1; decide +kernel
      have hl : raw27834step2Labels = raw27834step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27834step1 raw27834step1Labels permutation29 permutation4
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw27835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw27835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw27835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw27835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27835 raw27835Labels = mixedMoment B node2027 node2027Labels := by
  calc
    mixedMoment B raw27835 raw27835Labels = mixedMoment B raw27835step0 raw27835step0Labels := by
      have hz : ∀ j, raw27835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27835step0 = (fun i j => raw27835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27835step0 raw27835; decide +kernel
      have hl : raw27835step0Labels = raw27835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27835 raw27835Labels permutation346 hz
    mixedMoment B raw27835step0 raw27835step0Labels = mixedMoment B raw27835step1 raw27835step1Labels := by
      have ha : raw27835step1 = (fun i j => raw27835step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27835step1 raw27835step0; decide +kernel
      have hl : raw27835step1Labels = raw27835step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27835step0 raw27835step0Labels permutation143 permutation4
    _ = mixedMoment B node2027 node2027Labels := by rfl

def raw27836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw27836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27836 raw27836Labels = mixedMoment B node4960 node4960Labels := by
  calc
    mixedMoment B raw27836 raw27836Labels = mixedMoment B raw27836step0 raw27836step0Labels := by
      have ha : raw27836step0 = (fun i j => raw27836 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27836step0 raw27836; decide +kernel
      have hl : raw27836step0Labels = raw27836Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27836 raw27836Labels permutation158 permutation2
    _ = mixedMoment B node4960 node4960Labels := by rfl

def raw27837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27837step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27837step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27837step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27837step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27837 raw27837Labels = mixedMoment B node5027 node5027Labels := by
  calc
    mixedMoment B raw27837 raw27837Labels = mixedMoment B raw27837step0 raw27837step0Labels := by
      have ha : raw27837step0 = (fun i j => raw27837 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27837step0 raw27837; decide +kernel
      have hl : raw27837step0Labels = raw27837Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27837 raw27837Labels permutation644 permutation3
    mixedMoment B raw27837step0 raw27837step0Labels = mixedMoment B raw27837step1 raw27837step1Labels := by
      have ha : raw27837step1 = -raw27837step0 := by apply Matrix.ext; change ∀ i j, raw27837step1 i j = -(raw27837step0 i j); unfold raw27837step1 raw27837step0; decide +kernel
      have hl : raw27837step1Labels = raw27837step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27837step1 raw27837step1Labels = mixedMoment B raw27837step2 raw27837step2Labels := by
      have ha : raw27837step2 = raw27837step1 := by apply Matrix.ext; unfold raw27837step2 raw27837step1; decide +kernel
      have hl : raw27837step1Labels = labelEmbedding6 ∘ raw27837step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27837step1 raw27837step1Labels raw27837step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5027 node5027Labels := by rfl

def raw27838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw27838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw27838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27838step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27838step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27838step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27838step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27838 raw27838Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw27838 raw27838Labels = mixedMoment B raw27838step0 raw27838step0Labels := by
      have hz : ∀ j, raw27838 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27838step0 = (fun i j => raw27838 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27838step0 raw27838; decide +kernel
      have hl : raw27838step0Labels = raw27838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27838 raw27838Labels permutation520 hz
    mixedMoment B raw27838step0 raw27838step0Labels = mixedMoment B raw27838step1 raw27838step1Labels := by
      have ha : raw27838step1 = (fun i j => raw27838step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27838step1 raw27838step0; decide +kernel
      have hl : raw27838step1Labels = raw27838step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27838step0 raw27838step0Labels permutation145 permutation3
    mixedMoment B raw27838step1 raw27838step1Labels = mixedMoment B raw27838step2 raw27838step2Labels := by
      have ha : raw27838step2 = -raw27838step1 := by apply Matrix.ext; change ∀ i j, raw27838step2 i j = -(raw27838step1 i j); unfold raw27838step2 raw27838step1; decide +kernel
      have hl : raw27838step2Labels = raw27838step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27838step2 raw27838step2Labels = mixedMoment B raw27838step3 raw27838step3Labels := by
      have ha : raw27838step3 = raw27838step2 := by apply Matrix.ext; unfold raw27838step3 raw27838step2; decide +kernel
      have hl : raw27838step2Labels = labelEmbedding6 ∘ raw27838step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27838step2 raw27838step2Labels raw27838step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw27839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27839 raw27839Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw27839 raw27839Labels = mixedMoment B raw27839step0 raw27839step0Labels := by
      have hz : ∀ j, raw27839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27839step0 = (fun i j => raw27839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27839step0 raw27839; decide +kernel
      have hl : raw27839step0Labels = raw27839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27839 raw27839Labels permutation346 hz
    mixedMoment B raw27839step0 raw27839step0Labels = mixedMoment B raw27839step1 raw27839step1Labels := by
      have ha : raw27839step1 = (fun i j => raw27839step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27839step1 raw27839step0; decide +kernel
      have hl : raw27839step1Labels = raw27839step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27839step0 raw27839step0Labels permutation34 permutation2
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw27840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27840step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27840step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27840step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27840step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27840step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27840 raw27840Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw27840 raw27840Labels = mixedMoment B raw27840step0 raw27840step0Labels := by
      have ha : raw27840step0 = (fun i j => raw27840 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27840step0 raw27840; decide +kernel
      have hl : raw27840step0Labels = raw27840Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27840 raw27840Labels permutation686 permutation3
    mixedMoment B raw27840step0 raw27840step0Labels = mixedMoment B raw27840step1 raw27840step1Labels := by
      have ha : raw27840step1 = -raw27840step0 := by apply Matrix.ext; change ∀ i j, raw27840step1 i j = -(raw27840step0 i j); unfold raw27840step1 raw27840step0; decide +kernel
      have hl : raw27840step1Labels = raw27840step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27840step1 raw27840step1Labels = mixedMoment B raw27840step2 raw27840step2Labels := by
      have ha : raw27840step2 = raw27840step1 := by apply Matrix.ext; unfold raw27840step2 raw27840step1; decide +kernel
      have hl : raw27840step1Labels = labelEmbedding6 ∘ raw27840step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27840step1 raw27840step1Labels raw27840step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5037 node5037Labels := by rfl

def raw27841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw27841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27841 raw27841Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw27841 raw27841Labels = mixedMoment B raw27841step0 raw27841step0Labels := by
      have hz : ∀ j, raw27841 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27841step0 = (fun i j => raw27841 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27841step0 raw27841; decide +kernel
      have hl : raw27841step0Labels = raw27841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27841 raw27841Labels permutation520 hz
    mixedMoment B raw27841step0 raw27841step0Labels = mixedMoment B raw27841step1 raw27841step1Labels := by
      have hz : ∀ j, raw27841step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27841step1 = (fun i j => raw27841step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27841step1 raw27841step0; decide +kernel
      have hl : raw27841step1Labels = raw27841step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27841step0 raw27841step0Labels permutation80 hz
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw27842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw27842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw27842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27842step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27842step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27842step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27842step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27842 raw27842Labels = mixedMoment B node4908 node4908Labels := by
  calc
    mixedMoment B raw27842 raw27842Labels = mixedMoment B raw27842step0 raw27842step0Labels := by
      have hz : ∀ j, raw27842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27842step0 = (fun i j => raw27842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27842step0 raw27842; decide +kernel
      have hl : raw27842step0Labels = raw27842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27842 raw27842Labels permutation346 hz
    mixedMoment B raw27842step0 raw27842step0Labels = mixedMoment B raw27842step1 raw27842step1Labels := by
      have ha : raw27842step1 = (fun i j => raw27842step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27842step1 raw27842step0; decide +kernel
      have hl : raw27842step1Labels = raw27842step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27842step0 raw27842step0Labels permutation151 permutation3
    mixedMoment B raw27842step1 raw27842step1Labels = mixedMoment B raw27842step2 raw27842step2Labels := by
      have ha : raw27842step2 = -raw27842step1 := by apply Matrix.ext; change ∀ i j, raw27842step2 i j = -(raw27842step1 i j); unfold raw27842step2 raw27842step1; decide +kernel
      have hl : raw27842step2Labels = raw27842step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27842step2 raw27842step2Labels = mixedMoment B raw27842step3 raw27842step3Labels := by
      have ha : raw27842step3 = raw27842step2 := by apply Matrix.ext; unfold raw27842step3 raw27842step2; decide +kernel
      have hl : raw27842step2Labels = labelEmbedding6 ∘ raw27842step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27842step2 raw27842step2Labels raw27842step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4908 node4908Labels := by rfl

def raw27843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw27843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27843step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27843step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27843step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27843 raw27843Labels = mixedMoment B node4904 node4904Labels := by
  calc
    mixedMoment B raw27843 raw27843Labels = mixedMoment B raw27843step0 raw27843step0Labels := by
      have ha : raw27843step0 = (fun i j => raw27843 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27843step0 raw27843; decide +kernel
      have hl : raw27843step0Labels = raw27843Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27843 raw27843Labels permutation686 permutation3
    mixedMoment B raw27843step0 raw27843step0Labels = mixedMoment B raw27843step1 raw27843step1Labels := by
      have ha : raw27843step1 = -raw27843step0 := by apply Matrix.ext; change ∀ i j, raw27843step1 i j = -(raw27843step0 i j); unfold raw27843step1 raw27843step0; decide +kernel
      have hl : raw27843step1Labels = raw27843step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27843step1 raw27843step1Labels = mixedMoment B raw27843step2 raw27843step2Labels := by
      have ha : raw27843step2 = raw27843step1 := by apply Matrix.ext; unfold raw27843step2 raw27843step1; decide +kernel
      have hl : raw27843step1Labels = labelEmbedding6 ∘ raw27843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27843step1 raw27843step1Labels raw27843step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4904 node4904Labels := by rfl

def raw27844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw27844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw27844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27844step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27844step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27844step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27844step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27844 raw27844Labels = mixedMoment B node4919 node4919Labels := by
  calc
    mixedMoment B raw27844 raw27844Labels = mixedMoment B raw27844step0 raw27844step0Labels := by
      have hz : ∀ j, raw27844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27844step0 = (fun i j => raw27844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27844step0 raw27844; decide +kernel
      have hl : raw27844step0Labels = raw27844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27844 raw27844Labels permutation346 hz
    mixedMoment B raw27844step0 raw27844step0Labels = mixedMoment B raw27844step1 raw27844step1Labels := by
      have ha : raw27844step1 = (fun i j => raw27844step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27844step1 raw27844step0; decide +kernel
      have hl : raw27844step1Labels = raw27844step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27844step0 raw27844step0Labels permutation149 permutation3
    mixedMoment B raw27844step1 raw27844step1Labels = mixedMoment B raw27844step2 raw27844step2Labels := by
      have ha : raw27844step2 = -raw27844step1 := by apply Matrix.ext; change ∀ i j, raw27844step2 i j = -(raw27844step1 i j); unfold raw27844step2 raw27844step1; decide +kernel
      have hl : raw27844step2Labels = raw27844step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27844step2 raw27844step2Labels = mixedMoment B raw27844step3 raw27844step3Labels := by
      have ha : raw27844step3 = raw27844step2 := by apply Matrix.ext; unfold raw27844step3 raw27844step2; decide +kernel
      have hl : raw27844step2Labels = labelEmbedding6 ∘ raw27844step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27844step2 raw27844step2Labels raw27844step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4919 node4919Labels := by rfl

def raw27845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw27845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw27845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27845step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27845step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27845step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27845step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27845 raw27845Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw27845 raw27845Labels = mixedMoment B raw27845step0 raw27845step0Labels := by
      have hz : ∀ j, raw27845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27845step0 = (fun i j => raw27845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27845step0 raw27845; decide +kernel
      have hl : raw27845step0Labels = raw27845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27845 raw27845Labels permutation346 hz
    mixedMoment B raw27845step0 raw27845step0Labels = mixedMoment B raw27845step1 raw27845step1Labels := by
      have ha : raw27845step1 = (fun i j => raw27845step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27845step1 raw27845step0; decide +kernel
      have hl : raw27845step1Labels = raw27845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27845step0 raw27845step0Labels permutation151 permutation3
    mixedMoment B raw27845step1 raw27845step1Labels = mixedMoment B raw27845step2 raw27845step2Labels := by
      have ha : raw27845step2 = -raw27845step1 := by apply Matrix.ext; change ∀ i j, raw27845step2 i j = -(raw27845step1 i j); unfold raw27845step2 raw27845step1; decide +kernel
      have hl : raw27845step2Labels = raw27845step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27845step2 raw27845step2Labels = mixedMoment B raw27845step3 raw27845step3Labels := by
      have ha : raw27845step3 = raw27845step2 := by apply Matrix.ext; unfold raw27845step3 raw27845step2; decide +kernel
      have hl : raw27845step2Labels = labelEmbedding6 ∘ raw27845step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27845step2 raw27845step2Labels raw27845step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4296 node4296Labels := by rfl

def raw27846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw27846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27846step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27846step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27846step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27846 raw27846Labels = mixedMoment B node4290 node4290Labels := by
  calc
    mixedMoment B raw27846 raw27846Labels = mixedMoment B raw27846step0 raw27846step0Labels := by
      have ha : raw27846step0 = (fun i j => raw27846 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27846step0 raw27846; decide +kernel
      have hl : raw27846step0Labels = raw27846Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27846 raw27846Labels permutation686 permutation3
    mixedMoment B raw27846step0 raw27846step0Labels = mixedMoment B raw27846step1 raw27846step1Labels := by
      have ha : raw27846step1 = -raw27846step0 := by apply Matrix.ext; change ∀ i j, raw27846step1 i j = -(raw27846step0 i j); unfold raw27846step1 raw27846step0; decide +kernel
      have hl : raw27846step1Labels = raw27846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27846step1 raw27846step1Labels = mixedMoment B raw27846step2 raw27846step2Labels := by
      have ha : raw27846step2 = raw27846step1 := by apply Matrix.ext; unfold raw27846step2 raw27846step1; decide +kernel
      have hl : raw27846step1Labels = labelEmbedding6 ∘ raw27846step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27846step1 raw27846step1Labels raw27846step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4290 node4290Labels := by rfl

def raw27847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw27847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw27847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27847step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27847step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27847step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27847step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27847 raw27847Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw27847 raw27847Labels = mixedMoment B raw27847step0 raw27847step0Labels := by
      have hz : ∀ j, raw27847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27847step0 = (fun i j => raw27847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27847step0 raw27847; decide +kernel
      have hl : raw27847step0Labels = raw27847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27847 raw27847Labels permutation346 hz
    mixedMoment B raw27847step0 raw27847step0Labels = mixedMoment B raw27847step1 raw27847step1Labels := by
      have ha : raw27847step1 = (fun i j => raw27847step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27847step1 raw27847step0; decide +kernel
      have hl : raw27847step1Labels = raw27847step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27847step0 raw27847step0Labels permutation149 permutation3
    mixedMoment B raw27847step1 raw27847step1Labels = mixedMoment B raw27847step2 raw27847step2Labels := by
      have ha : raw27847step2 = -raw27847step1 := by apply Matrix.ext; change ∀ i j, raw27847step2 i j = -(raw27847step1 i j); unfold raw27847step2 raw27847step1; decide +kernel
      have hl : raw27847step2Labels = raw27847step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27847step2 raw27847step2Labels = mixedMoment B raw27847step3 raw27847step3Labels := by
      have ha : raw27847step3 = raw27847step2 := by apply Matrix.ext; unfold raw27847step3 raw27847step2; decide +kernel
      have hl : raw27847step2Labels = labelEmbedding6 ∘ raw27847step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27847step2 raw27847step2Labels raw27847step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw27848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw27848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw27848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw27848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27848step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27848step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27848step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27848step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27848step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27848 raw27848Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw27848 raw27848Labels = mixedMoment B raw27848step0 raw27848step0Labels := by
      have hz : ∀ j, raw27848 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27848step0 = (fun i j => raw27848 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27848step0 raw27848; decide +kernel
      have hl : raw27848step0Labels = raw27848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27848 raw27848Labels permutation520 hz
    mixedMoment B raw27848step0 raw27848step0Labels = mixedMoment B raw27848step1 raw27848step1Labels := by
      have hz : ∀ j, raw27848step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27848step1 = (fun i j => raw27848step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27848step1 raw27848step0; decide +kernel
      have hl : raw27848step1Labels = raw27848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27848step0 raw27848step0Labels permutation80 hz
    mixedMoment B raw27848step1 raw27848step1Labels = mixedMoment B raw27848step2 raw27848step2Labels := by
      have ha : raw27848step2 = (fun i j => raw27848step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27848step2 raw27848step1; decide +kernel
      have hl : raw27848step2Labels = raw27848step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27848step1 raw27848step1Labels permutation31 permutation3
    mixedMoment B raw27848step2 raw27848step2Labels = mixedMoment B raw27848step3 raw27848step3Labels := by
      have ha : raw27848step3 = -raw27848step2 := by apply Matrix.ext; change ∀ i j, raw27848step3 i j = -(raw27848step2 i j); unfold raw27848step3 raw27848step2; decide +kernel
      have hl : raw27848step3Labels = raw27848step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27848step3 raw27848step3Labels = mixedMoment B raw27848step4 raw27848step4Labels := by
      have ha : raw27848step4 = raw27848step3 := by apply Matrix.ext; unfold raw27848step4 raw27848step3; decide +kernel
      have hl : raw27848step3Labels = labelEmbedding6 ∘ raw27848step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27848step3 raw27848step3Labels raw27848step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw27849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27849 raw27849Labels = mixedMoment B node2412 node2412Labels := by
  calc
    mixedMoment B raw27849 raw27849Labels = mixedMoment B raw27849step0 raw27849step0Labels := by
      have ha : raw27849step0 = (fun i j => raw27849 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27849step0 raw27849; decide +kernel
      have hl : raw27849step0Labels = raw27849Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27849 raw27849Labels permutation646 permutation3
    mixedMoment B raw27849step0 raw27849step0Labels = mixedMoment B raw27849step1 raw27849step1Labels := by
      have ha : raw27849step1 = -raw27849step0 := by apply Matrix.ext; change ∀ i j, raw27849step1 i j = -(raw27849step0 i j); unfold raw27849step1 raw27849step0; decide +kernel
      have hl : raw27849step1Labels = raw27849step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2412 node2412Labels := by rfl

def raw27850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27850 raw27850Labels = mixedMoment B node2416 node2416Labels := by
  calc
    mixedMoment B raw27850 raw27850Labels = mixedMoment B raw27850step0 raw27850step0Labels := by
      have ha : raw27850step0 = (fun i j => raw27850 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27850step0 raw27850; decide +kernel
      have hl : raw27850step0Labels = raw27850Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27850 raw27850Labels permutation644 permutation3
    mixedMoment B raw27850step0 raw27850step0Labels = mixedMoment B raw27850step1 raw27850step1Labels := by
      have ha : raw27850step1 = -raw27850step0 := by apply Matrix.ext; change ∀ i j, raw27850step1 i j = -(raw27850step0 i j); unfold raw27850step1 raw27850step0; decide +kernel
      have hl : raw27850step1Labels = raw27850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2416 node2416Labels := by rfl

def raw27851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw27851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw27851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27851 raw27851Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27851 raw27851Labels = mixedMoment B raw27851step0 raw27851step0Labels := by
      have hz : ∀ j, raw27851 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27851step0 = (fun i j => raw27851 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27851step0 raw27851; decide +kernel
      have hl : raw27851step0Labels = raw27851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27851 raw27851Labels permutation520 hz
    mixedMoment B raw27851step0 raw27851step0Labels = mixedMoment B raw27851step1 raw27851step1Labels := by
      have ha : raw27851step1 = (fun i j => raw27851step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27851step1 raw27851step0; decide +kernel
      have hl : raw27851step1Labels = raw27851step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27851step0 raw27851step0Labels permutation145 permutation3
    mixedMoment B raw27851step1 raw27851step1Labels = mixedMoment B raw27851step2 raw27851step2Labels := by
      have ha : raw27851step2 = -raw27851step1 := by apply Matrix.ext; change ∀ i j, raw27851step2 i j = -(raw27851step1 i j); unfold raw27851step2 raw27851step1; decide +kernel
      have hl : raw27851step2Labels = raw27851step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw27852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27852 raw27852Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw27852 raw27852Labels = mixedMoment B raw27852step0 raw27852step0Labels := by
      have hz : ∀ j, raw27852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27852step0 = (fun i j => raw27852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27852step0 raw27852; decide +kernel
      have hl : raw27852step0Labels = raw27852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27852 raw27852Labels permutation346 hz
    mixedMoment B raw27852step0 raw27852step0Labels = mixedMoment B raw27852step1 raw27852step1Labels := by
      have ha : raw27852step1 = (fun i j => raw27852step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27852step1 raw27852step0; decide +kernel
      have hl : raw27852step1Labels = raw27852step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27852step0 raw27852step0Labels permutation151 permutation3
    mixedMoment B raw27852step1 raw27852step1Labels = mixedMoment B raw27852step2 raw27852step2Labels := by
      have ha : raw27852step2 = -raw27852step1 := by apply Matrix.ext; change ∀ i j, raw27852step2 i j = -(raw27852step1 i j); unfold raw27852step2 raw27852step1; decide +kernel
      have hl : raw27852step2Labels = raw27852step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw27853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27853 raw27853Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw27853 raw27853Labels = mixedMoment B raw27853step0 raw27853step0Labels := by
      have ha : raw27853step0 = (fun i j => raw27853 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27853step0 raw27853; decide +kernel
      have hl : raw27853step0Labels = raw27853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27853 raw27853Labels permutation686 permutation3
    mixedMoment B raw27853step0 raw27853step0Labels = mixedMoment B raw27853step1 raw27853step1Labels := by
      have ha : raw27853step1 = -raw27853step0 := by apply Matrix.ext; change ∀ i j, raw27853step1 i j = -(raw27853step0 i j); unfold raw27853step1 raw27853step0; decide +kernel
      have hl : raw27853step1Labels = raw27853step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw27854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw27854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27854step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27854step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27854step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27854step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27854 raw27854Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw27854 raw27854Labels = mixedMoment B raw27854step0 raw27854step0Labels := by
      have hz : ∀ j, raw27854 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27854step0 = (fun i j => raw27854 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27854step0 raw27854; decide +kernel
      have hl : raw27854step0Labels = raw27854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27854 raw27854Labels permutation520 hz
    mixedMoment B raw27854step0 raw27854step0Labels = mixedMoment B raw27854step1 raw27854step1Labels := by
      have hz : ∀ j, raw27854step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27854step1 = (fun i j => raw27854step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27854step1 raw27854step0; decide +kernel
      have hl : raw27854step1Labels = raw27854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27854step0 raw27854step0Labels permutation80 hz
    mixedMoment B raw27854step1 raw27854step1Labels = mixedMoment B raw27854step2 raw27854step2Labels := by
      have ha : raw27854step2 = (fun i j => raw27854step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27854step2 raw27854step1; decide +kernel
      have hl : raw27854step2Labels = raw27854step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27854step1 raw27854step1Labels permutation31 permutation3
    mixedMoment B raw27854step2 raw27854step2Labels = mixedMoment B raw27854step3 raw27854step3Labels := by
      have ha : raw27854step3 = -raw27854step2 := by apply Matrix.ext; change ∀ i j, raw27854step3 i j = -(raw27854step2 i j); unfold raw27854step3 raw27854step2; decide +kernel
      have hl : raw27854step3Labels = raw27854step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw27855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw27855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw27855step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27855step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27855step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27855 raw27855Labels = mixedMoment B node2301 node2301Labels := by
  calc
    mixedMoment B raw27855 raw27855Labels = mixedMoment B raw27855step0 raw27855step0Labels := by
      have hz : ∀ j, raw27855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27855step0 = (fun i j => raw27855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27855step0 raw27855; decide +kernel
      have hl : raw27855step0Labels = raw27855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27855 raw27855Labels permutation346 hz
    mixedMoment B raw27855step0 raw27855step0Labels = mixedMoment B raw27855step1 raw27855step1Labels := by
      have ha : raw27855step1 = (fun i j => raw27855step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27855step1 raw27855step0; decide +kernel
      have hl : raw27855step1Labels = raw27855step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27855step0 raw27855step0Labels permutation151 permutation3
    mixedMoment B raw27855step1 raw27855step1Labels = mixedMoment B raw27855step2 raw27855step2Labels := by
      have ha : raw27855step2 = -raw27855step1 := by apply Matrix.ext; change ∀ i j, raw27855step2 i j = -(raw27855step1 i j); unfold raw27855step2 raw27855step1; decide +kernel
      have hl : raw27855step2Labels = raw27855step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2301 node2301Labels := by rfl

def raw27856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw27856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27856 raw27856Labels = mixedMoment B node2297 node2297Labels := by
  calc
    mixedMoment B raw27856 raw27856Labels = mixedMoment B raw27856step0 raw27856step0Labels := by
      have ha : raw27856step0 = (fun i j => raw27856 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27856step0 raw27856; decide +kernel
      have hl : raw27856step0Labels = raw27856Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27856 raw27856Labels permutation686 permutation3
    mixedMoment B raw27856step0 raw27856step0Labels = mixedMoment B raw27856step1 raw27856step1Labels := by
      have ha : raw27856step1 = -raw27856step0 := by apply Matrix.ext; change ∀ i j, raw27856step1 i j = -(raw27856step0 i j); unfold raw27856step1 raw27856step0; decide +kernel
      have hl : raw27856step1Labels = raw27856step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2297 node2297Labels := by rfl

def raw27857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw27857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw27857step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27857 raw27857Labels = mixedMoment B node2310 node2310Labels := by
  calc
    mixedMoment B raw27857 raw27857Labels = mixedMoment B raw27857step0 raw27857step0Labels := by
      have hz : ∀ j, raw27857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27857step0 = (fun i j => raw27857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27857step0 raw27857; decide +kernel
      have hl : raw27857step0Labels = raw27857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27857 raw27857Labels permutation346 hz
    mixedMoment B raw27857step0 raw27857step0Labels = mixedMoment B raw27857step1 raw27857step1Labels := by
      have ha : raw27857step1 = (fun i j => raw27857step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27857step1 raw27857step0; decide +kernel
      have hl : raw27857step1Labels = raw27857step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27857step0 raw27857step0Labels permutation149 permutation3
    mixedMoment B raw27857step1 raw27857step1Labels = mixedMoment B raw27857step2 raw27857step2Labels := by
      have ha : raw27857step2 = -raw27857step1 := by apply Matrix.ext; change ∀ i j, raw27857step2 i j = -(raw27857step1 i j); unfold raw27857step2 raw27857step1; decide +kernel
      have hl : raw27857step2Labels = raw27857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2310 node2310Labels := by rfl

def raw27858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw27858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw27858step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27858 raw27858Labels = mixedMoment B node874 node874Labels := by
  calc
    mixedMoment B raw27858 raw27858Labels = mixedMoment B raw27858step0 raw27858step0Labels := by
      have hz : ∀ j, raw27858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27858step0 = (fun i j => raw27858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27858step0 raw27858; decide +kernel
      have hl : raw27858step0Labels = raw27858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27858 raw27858Labels permutation346 hz
    mixedMoment B raw27858step0 raw27858step0Labels = mixedMoment B raw27858step1 raw27858step1Labels := by
      have ha : raw27858step1 = (fun i j => raw27858step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27858step1 raw27858step0; decide +kernel
      have hl : raw27858step1Labels = raw27858step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27858step0 raw27858step0Labels permutation151 permutation3
    mixedMoment B raw27858step1 raw27858step1Labels = mixedMoment B raw27858step2 raw27858step2Labels := by
      have ha : raw27858step2 = -raw27858step1 := by apply Matrix.ext; change ∀ i j, raw27858step2 i j = -(raw27858step1 i j); unfold raw27858step2 raw27858step1; decide +kernel
      have hl : raw27858step2Labels = raw27858step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node874 node874Labels := by rfl

def raw27859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw27859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27859 raw27859Labels = mixedMoment B node868 node868Labels := by
  calc
    mixedMoment B raw27859 raw27859Labels = mixedMoment B raw27859step0 raw27859step0Labels := by
      have ha : raw27859step0 = (fun i j => raw27859 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27859step0 raw27859; decide +kernel
      have hl : raw27859step0Labels = raw27859Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27859 raw27859Labels permutation686 permutation3
    mixedMoment B raw27859step0 raw27859step0Labels = mixedMoment B raw27859step1 raw27859step1Labels := by
      have ha : raw27859step1 = -raw27859step0 := by apply Matrix.ext; change ∀ i j, raw27859step1 i j = -(raw27859step0 i j); unfold raw27859step1 raw27859step0; decide +kernel
      have hl : raw27859step1Labels = raw27859step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node868 node868Labels := by rfl

def raw27860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw27860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw27860step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27860 raw27860Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw27860 raw27860Labels = mixedMoment B raw27860step0 raw27860step0Labels := by
      have hz : ∀ j, raw27860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27860step0 = (fun i j => raw27860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27860step0 raw27860; decide +kernel
      have hl : raw27860step0Labels = raw27860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27860 raw27860Labels permutation346 hz
    mixedMoment B raw27860step0 raw27860step0Labels = mixedMoment B raw27860step1 raw27860step1Labels := by
      have ha : raw27860step1 = (fun i j => raw27860step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27860step1 raw27860step0; decide +kernel
      have hl : raw27860step1Labels = raw27860step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27860step0 raw27860step0Labels permutation149 permutation3
    mixedMoment B raw27860step1 raw27860step1Labels = mixedMoment B raw27860step2 raw27860step2Labels := by
      have ha : raw27860step2 = -raw27860step1 := by apply Matrix.ext; change ∀ i j, raw27860step2 i j = -(raw27860step1 i j); unfold raw27860step2 raw27860step1; decide +kernel
      have hl : raw27860step2Labels = raw27860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node887 node887Labels := by rfl

def raw27861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw27861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw27861step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw27861step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27861step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27861 raw27861Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw27861 raw27861Labels = mixedMoment B raw27861step0 raw27861step0Labels := by
      have hz : ∀ j, raw27861 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27861step0 = (fun i j => raw27861 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27861step0 raw27861; decide +kernel
      have hl : raw27861step0Labels = raw27861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27861 raw27861Labels permutation520 hz
    mixedMoment B raw27861step0 raw27861step0Labels = mixedMoment B raw27861step1 raw27861step1Labels := by
      have hz : ∀ j, raw27861step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27861step1 = (fun i j => raw27861step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27861step1 raw27861step0; decide +kernel
      have hl : raw27861step1Labels = raw27861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27861step0 raw27861step0Labels permutation80 hz
    mixedMoment B raw27861step1 raw27861step1Labels = mixedMoment B raw27861step2 raw27861step2Labels := by
      have ha : raw27861step2 = (fun i j => raw27861step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27861step2 raw27861step1; decide +kernel
      have hl : raw27861step2Labels = raw27861step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27861step1 raw27861step1Labels permutation31 permutation3
    mixedMoment B raw27861step2 raw27861step2Labels = mixedMoment B raw27861step3 raw27861step3Labels := by
      have ha : raw27861step3 = -raw27861step2 := by apply Matrix.ext; change ∀ i j, raw27861step3 i j = -(raw27861step2 i j); unfold raw27861step3 raw27861step2; decide +kernel
      have hl : raw27861step3Labels = raw27861step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw27862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27862 raw27862Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw27862 raw27862Labels = mixedMoment B raw27862step0 raw27862step0Labels := by
      have hz : ∀ j, raw27862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27862step0 = (fun i j => raw27862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27862step0 raw27862; decide +kernel
      have hl : raw27862step0Labels = raw27862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27862 raw27862Labels permutation346 hz
    mixedMoment B raw27862step0 raw27862step0Labels = mixedMoment B raw27862step1 raw27862step1Labels := by
      have ha : raw27862step1 = (fun i j => raw27862step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27862step1 raw27862step0; decide +kernel
      have hl : raw27862step1Labels = raw27862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27862step0 raw27862step0Labels permutation151 permutation2
    mixedMoment B raw27862step1 raw27862step1Labels = mixedMoment B raw27862step2 raw27862step2Labels := by
      have ha : raw27862step2 = -raw27862step1 := by apply Matrix.ext; change ∀ i j, raw27862step2 i j = -(raw27862step1 i j); unfold raw27862step2 raw27862step1; decide +kernel
      have hl : raw27862step2Labels = raw27862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw27863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27863step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27863 raw27863Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw27863 raw27863Labels = mixedMoment B raw27863step0 raw27863step0Labels := by
      have hz : ∀ j, raw27863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27863step0 = (fun i j => raw27863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27863step0 raw27863; decide +kernel
      have hl : raw27863step0Labels = raw27863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27863 raw27863Labels permutation346 hz
    mixedMoment B raw27863step0 raw27863step0Labels = mixedMoment B raw27863step1 raw27863step1Labels := by
      have ha : raw27863step1 = (fun i j => raw27863step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27863step1 raw27863step0; decide +kernel
      have hl : raw27863step1Labels = raw27863step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27863step0 raw27863step0Labels permutation32 permutation3
    mixedMoment B raw27863step1 raw27863step1Labels = mixedMoment B raw27863step2 raw27863step2Labels := by
      have ha : raw27863step2 = raw27863step1 := by apply Matrix.ext; unfold raw27863step2 raw27863step1; decide +kernel
      have hl : raw27863step1Labels = labelEmbedding6 ∘ raw27863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27863step1 raw27863step1Labels raw27863step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw27864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27864 raw27864Labels = mixedMoment B node5065 node5065Labels := by
  calc
    mixedMoment B raw27864 raw27864Labels = mixedMoment B raw27864step0 raw27864step0Labels := by
      have ha : raw27864step0 = (fun i j => raw27864 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27864step0 raw27864; decide +kernel
      have hl : raw27864step0Labels = raw27864Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27864 raw27864Labels permutation676 permutation2
    mixedMoment B raw27864step0 raw27864step0Labels = mixedMoment B raw27864step1 raw27864step1Labels := by
      have ha : raw27864step1 = -raw27864step0 := by apply Matrix.ext; change ∀ i j, raw27864step1 i j = -(raw27864step0 i j); unfold raw27864step1 raw27864step0; decide +kernel
      have hl : raw27864step1Labels = raw27864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5065 node5065Labels := by rfl

def raw27865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27865 raw27865Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw27865 raw27865Labels = mixedMoment B raw27865step0 raw27865step0Labels := by
      have hz : ∀ j, raw27865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27865step0 = (fun i j => raw27865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27865step0 raw27865; decide +kernel
      have hl : raw27865step0Labels = raw27865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27865 raw27865Labels permutation346 hz
    mixedMoment B raw27865step0 raw27865step0Labels = mixedMoment B raw27865step1 raw27865step1Labels := by
      have ha : raw27865step1 = (fun i j => raw27865step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27865step1 raw27865step0; decide +kernel
      have hl : raw27865step1Labels = raw27865step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27865step0 raw27865step0Labels permutation149 permutation2
    mixedMoment B raw27865step1 raw27865step1Labels = mixedMoment B raw27865step2 raw27865step2Labels := by
      have ha : raw27865step2 = -raw27865step1 := by apply Matrix.ext; change ∀ i j, raw27865step2 i j = -(raw27865step1 i j); unfold raw27865step2 raw27865step1; decide +kernel
      have hl : raw27865step2Labels = raw27865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw27866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw27866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27866step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27866 raw27866Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw27866 raw27866Labels = mixedMoment B raw27866step0 raw27866step0Labels := by
      have hz : ∀ j, raw27866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27866step0 = (fun i j => raw27866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27866step0 raw27866; decide +kernel
      have hl : raw27866step0Labels = raw27866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27866 raw27866Labels permutation346 hz
    mixedMoment B raw27866step0 raw27866step0Labels = mixedMoment B raw27866step1 raw27866step1Labels := by
      have ha : raw27866step1 = (fun i j => raw27866step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27866step1 raw27866step0; decide +kernel
      have hl : raw27866step1Labels = raw27866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27866step0 raw27866step0Labels permutation149 permutation2
    mixedMoment B raw27866step1 raw27866step1Labels = mixedMoment B raw27866step2 raw27866step2Labels := by
      have ha : raw27866step2 = -raw27866step1 := by apply Matrix.ext; change ∀ i j, raw27866step2 i j = -(raw27866step1 i j); unfold raw27866step2 raw27866step1; decide +kernel
      have hl : raw27866step2Labels = raw27866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw27867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27867step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27867 raw27867Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw27867 raw27867Labels = mixedMoment B raw27867step0 raw27867step0Labels := by
      have ha : raw27867step0 = (fun i j => raw27867 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27867step0 raw27867; decide +kernel
      have hl : raw27867step0Labels = raw27867Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27867 raw27867Labels permutation160 permutation3
    mixedMoment B raw27867step0 raw27867step0Labels = mixedMoment B raw27867step1 raw27867step1Labels := by
      have ha : raw27867step1 = raw27867step0 := by apply Matrix.ext; unfold raw27867step1 raw27867step0; decide +kernel
      have hl : raw27867step0Labels = labelEmbedding6 ∘ raw27867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27867step0 raw27867step0Labels raw27867step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4327 node4327Labels := by rfl

def raw27868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27868step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27868 raw27868Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw27868 raw27868Labels = mixedMoment B raw27868step0 raw27868step0Labels := by
      have ha : raw27868step0 = (fun i j => raw27868 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27868step0 raw27868; decide +kernel
      have hl : raw27868step0Labels = raw27868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27868 raw27868Labels permutation160 permutation3
    mixedMoment B raw27868step0 raw27868step0Labels = mixedMoment B raw27868step1 raw27868step1Labels := by
      have ha : raw27868step1 = raw27868step0 := by apply Matrix.ext; unfold raw27868step1 raw27868step0; decide +kernel
      have hl : raw27868step0Labels = labelEmbedding6 ∘ raw27868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27868step0 raw27868step0Labels raw27868step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw27869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27869 raw27869Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw27869 raw27869Labels = mixedMoment B raw27869step0 raw27869step0Labels := by
      have ha : raw27869step0 = (fun i j => raw27869 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27869step0 raw27869; decide +kernel
      have hl : raw27869step0Labels = raw27869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27869 raw27869Labels permutation680 permutation2
    mixedMoment B raw27869step0 raw27869step0Labels = mixedMoment B raw27869step1 raw27869step1Labels := by
      have ha : raw27869step1 = -raw27869step0 := by apply Matrix.ext; change ∀ i j, raw27869step1 i j = -(raw27869step0 i j); unfold raw27869step1 raw27869step0; decide +kernel
      have hl : raw27869step1Labels = raw27869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5037 node5037Labels := by rfl

def raw27870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27870 raw27870Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw27870 raw27870Labels = mixedMoment B raw27870step0 raw27870step0Labels := by
      have ha : raw27870step0 = (fun i j => raw27870 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27870step0 raw27870; decide +kernel
      have hl : raw27870step0Labels = raw27870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27870 raw27870Labels permutation646 permutation2
    mixedMoment B raw27870step0 raw27870step0Labels = mixedMoment B raw27870step1 raw27870step1Labels := by
      have ha : raw27870step1 = -raw27870step0 := by apply Matrix.ext; change ∀ i j, raw27870step1 i j = -(raw27870step0 i j); unfold raw27870step1 raw27870step0; decide +kernel
      have hl : raw27870step1Labels = raw27870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw27871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27871step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27871 raw27871Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw27871 raw27871Labels = mixedMoment B raw27871step0 raw27871step0Labels := by
      have hz : ∀ j, raw27871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27871step0 = (fun i j => raw27871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27871step0 raw27871; decide +kernel
      have hl : raw27871step0Labels = raw27871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27871 raw27871Labels permutation346 hz
    mixedMoment B raw27871step0 raw27871step0Labels = mixedMoment B raw27871step1 raw27871step1Labels := by
      have ha : raw27871step1 = (fun i j => raw27871step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27871step1 raw27871step0; decide +kernel
      have hl : raw27871step1Labels = raw27871step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27871step0 raw27871step0Labels permutation34 permutation3
    mixedMoment B raw27871step1 raw27871step1Labels = mixedMoment B raw27871step2 raw27871step2Labels := by
      have ha : raw27871step2 = raw27871step1 := by apply Matrix.ext; unfold raw27871step2 raw27871step1; decide +kernel
      have hl : raw27871step1Labels = labelEmbedding6 ∘ raw27871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27871step1 raw27871step1Labels raw27871step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw27872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27872step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27872step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27872 raw27872Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw27872 raw27872Labels = mixedMoment B raw27872step0 raw27872step0Labels := by
      have hz : ∀ j, raw27872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27872step0 = (fun i j => raw27872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27872step0 raw27872; decide +kernel
      have hl : raw27872step0Labels = raw27872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27872 raw27872Labels permutation346 hz
    mixedMoment B raw27872step0 raw27872step0Labels = mixedMoment B raw27872step1 raw27872step1Labels := by
      have ha : raw27872step1 = (fun i j => raw27872step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27872step1 raw27872step0; decide +kernel
      have hl : raw27872step1Labels = raw27872step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27872step0 raw27872step0Labels permutation34 permutation3
    mixedMoment B raw27872step1 raw27872step1Labels = mixedMoment B raw27872step2 raw27872step2Labels := by
      have ha : raw27872step2 = raw27872step1 := by apply Matrix.ext; unfold raw27872step2 raw27872step1; decide +kernel
      have hl : raw27872step1Labels = labelEmbedding6 ∘ raw27872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27872step1 raw27872step1Labels raw27872step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw27873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27873step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27873 raw27873Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw27873 raw27873Labels = mixedMoment B raw27873step0 raw27873step0Labels := by
      have ha : raw27873step0 = (fun i j => raw27873 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27873step0 raw27873; decide +kernel
      have hl : raw27873step0Labels = raw27873Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27873 raw27873Labels permutation178 permutation3
    mixedMoment B raw27873step0 raw27873step0Labels = mixedMoment B raw27873step1 raw27873step1Labels := by
      have ha : raw27873step1 = raw27873step0 := by apply Matrix.ext; unfold raw27873step1 raw27873step0; decide +kernel
      have hl : raw27873step0Labels = labelEmbedding6 ∘ raw27873step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27873step0 raw27873step0Labels raw27873step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5034 node5034Labels := by rfl

def raw27874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27874step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27874 raw27874Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw27874 raw27874Labels = mixedMoment B raw27874step0 raw27874step0Labels := by
      have hz : ∀ j, raw27874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27874step0 = (fun i j => raw27874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27874step0 raw27874; decide +kernel
      have hl : raw27874step0Labels = raw27874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27874 raw27874Labels permutation346 hz
    mixedMoment B raw27874step0 raw27874step0Labels = mixedMoment B raw27874step1 raw27874step1Labels := by
      have ha : raw27874step1 = (fun i j => raw27874step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27874step1 raw27874step0; decide +kernel
      have hl : raw27874step1Labels = raw27874step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27874step0 raw27874step0Labels permutation34 permutation3
    mixedMoment B raw27874step1 raw27874step1Labels = mixedMoment B raw27874step2 raw27874step2Labels := by
      have ha : raw27874step2 = raw27874step1 := by apply Matrix.ext; unfold raw27874step2 raw27874step1; decide +kernel
      have hl : raw27874step1Labels = labelEmbedding6 ∘ raw27874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27874step1 raw27874step1Labels raw27874step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw27875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27875step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27875 raw27875Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw27875 raw27875Labels = mixedMoment B raw27875step0 raw27875step0Labels := by
      have hz : ∀ j, raw27875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27875step0 = (fun i j => raw27875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27875step0 raw27875; decide +kernel
      have hl : raw27875step0Labels = raw27875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27875 raw27875Labels permutation346 hz
    mixedMoment B raw27875step0 raw27875step0Labels = mixedMoment B raw27875step1 raw27875step1Labels := by
      have ha : raw27875step1 = (fun i j => raw27875step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27875step1 raw27875step0; decide +kernel
      have hl : raw27875step1Labels = raw27875step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27875step0 raw27875step0Labels permutation32 permutation3
    mixedMoment B raw27875step1 raw27875step1Labels = mixedMoment B raw27875step2 raw27875step2Labels := by
      have ha : raw27875step2 = raw27875step1 := by apply Matrix.ext; unfold raw27875step2 raw27875step1; decide +kernel
      have hl : raw27875step1Labels = labelEmbedding6 ∘ raw27875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27875step1 raw27875step1Labels raw27875step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw27876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27876 raw27876Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw27876 raw27876Labels = mixedMoment B raw27876step0 raw27876step0Labels := by
      have hz : ∀ j, raw27876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27876step0 = (fun i j => raw27876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27876step0 raw27876; decide +kernel
      have hl : raw27876step0Labels = raw27876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27876 raw27876Labels permutation346 hz
    mixedMoment B raw27876step0 raw27876step0Labels = mixedMoment B raw27876step1 raw27876step1Labels := by
      have ha : raw27876step1 = (fun i j => raw27876step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27876step1 raw27876step0; decide +kernel
      have hl : raw27876step1Labels = raw27876step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27876step0 raw27876step0Labels permutation151 permutation2
    mixedMoment B raw27876step1 raw27876step1Labels = mixedMoment B raw27876step2 raw27876step2Labels := by
      have ha : raw27876step2 = -raw27876step1 := by apply Matrix.ext; change ∀ i j, raw27876step2 i j = -(raw27876step1 i j); unfold raw27876step2 raw27876step1; decide +kernel
      have hl : raw27876step2Labels = raw27876step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4935 node4935Labels := by rfl

def raw27877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27877 raw27877Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw27877 raw27877Labels = mixedMoment B raw27877step0 raw27877step0Labels := by
      have ha : raw27877step0 = (fun i j => raw27877 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27877step0 raw27877; decide +kernel
      have hl : raw27877step0Labels = raw27877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27877 raw27877Labels permutation688 permutation2
    mixedMoment B raw27877step0 raw27877step0Labels = mixedMoment B raw27877step1 raw27877step1Labels := by
      have ha : raw27877step1 = -raw27877step0 := by apply Matrix.ext; change ∀ i j, raw27877step1 i j = -(raw27877step0 i j); unfold raw27877step1 raw27877step0; decide +kernel
      have hl : raw27877step1Labels = raw27877step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw27878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27878 raw27878Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw27878 raw27878Labels = mixedMoment B raw27878step0 raw27878step0Labels := by
      have hz : ∀ j, raw27878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27878step0 = (fun i j => raw27878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27878step0 raw27878; decide +kernel
      have hl : raw27878step0Labels = raw27878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27878 raw27878Labels permutation346 hz
    mixedMoment B raw27878step0 raw27878step0Labels = mixedMoment B raw27878step1 raw27878step1Labels := by
      have ha : raw27878step1 = (fun i j => raw27878step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27878step1 raw27878step0; decide +kernel
      have hl : raw27878step1Labels = raw27878step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27878step0 raw27878step0Labels permutation149 permutation2
    mixedMoment B raw27878step1 raw27878step1Labels = mixedMoment B raw27878step2 raw27878step2Labels := by
      have ha : raw27878step2 = -raw27878step1 := by apply Matrix.ext; change ∀ i j, raw27878step2 i j = -(raw27878step1 i j); unfold raw27878step2 raw27878step1; decide +kernel
      have hl : raw27878step2Labels = raw27878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4948 node4948Labels := by rfl

def raw27879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw27879step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw27879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27879 raw27879Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw27879 raw27879Labels = mixedMoment B raw27879step0 raw27879step0Labels := by
      have hz : ∀ j, raw27879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27879step0 = (fun i j => raw27879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27879step0 raw27879; decide +kernel
      have hl : raw27879step0Labels = raw27879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27879 raw27879Labels permutation346 hz
    mixedMoment B raw27879step0 raw27879step0Labels = mixedMoment B raw27879step1 raw27879step1Labels := by
      have ha : raw27879step1 = (fun i j => raw27879step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27879step1 raw27879step0; decide +kernel
      have hl : raw27879step1Labels = raw27879step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27879step0 raw27879step0Labels permutation32 permutation3
    mixedMoment B raw27879step1 raw27879step1Labels = mixedMoment B raw27879step2 raw27879step2Labels := by
      have ha : raw27879step2 = raw27879step1 := by apply Matrix.ext; unfold raw27879step2 raw27879step1; decide +kernel
      have hl : raw27879step1Labels = labelEmbedding6 ∘ raw27879step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27879step1 raw27879step1Labels raw27879step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw27880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27880 raw27880Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw27880 raw27880Labels = mixedMoment B raw27880step0 raw27880step0Labels := by
      have hz : ∀ j, raw27880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27880step0 = (fun i j => raw27880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27880step0 raw27880; decide +kernel
      have hl : raw27880step0Labels = raw27880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27880 raw27880Labels permutation346 hz
    mixedMoment B raw27880step0 raw27880step0Labels = mixedMoment B raw27880step1 raw27880step1Labels := by
      have ha : raw27880step1 = (fun i j => raw27880step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27880step1 raw27880step0; decide +kernel
      have hl : raw27880step1Labels = raw27880step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27880step0 raw27880step0Labels permutation151 permutation2
    mixedMoment B raw27880step1 raw27880step1Labels = mixedMoment B raw27880step2 raw27880step2Labels := by
      have ha : raw27880step2 = -raw27880step1 := by apply Matrix.ext; change ∀ i j, raw27880step2 i j = -(raw27880step1 i j); unfold raw27880step2 raw27880step1; decide +kernel
      have hl : raw27880step2Labels = raw27880step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4535 node4535Labels := by rfl

def raw27881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27881 raw27881Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw27881 raw27881Labels = mixedMoment B raw27881step0 raw27881step0Labels := by
      have ha : raw27881step0 = (fun i j => raw27881 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27881step0 raw27881; decide +kernel
      have hl : raw27881step0Labels = raw27881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27881 raw27881Labels permutation688 permutation2
    mixedMoment B raw27881step0 raw27881step0Labels = mixedMoment B raw27881step1 raw27881step1Labels := by
      have ha : raw27881step1 = -raw27881step0 := by apply Matrix.ext; change ∀ i j, raw27881step1 i j = -(raw27881step0 i j); unfold raw27881step1 raw27881step0; decide +kernel
      have hl : raw27881step1Labels = raw27881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4528 node4528Labels := by rfl

def raw27882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27882step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27882 raw27882Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw27882 raw27882Labels = mixedMoment B raw27882step0 raw27882step0Labels := by
      have hz : ∀ j, raw27882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27882step0 = (fun i j => raw27882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27882step0 raw27882; decide +kernel
      have hl : raw27882step0Labels = raw27882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27882 raw27882Labels permutation346 hz
    mixedMoment B raw27882step0 raw27882step0Labels = mixedMoment B raw27882step1 raw27882step1Labels := by
      have ha : raw27882step1 = (fun i j => raw27882step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27882step1 raw27882step0; decide +kernel
      have hl : raw27882step1Labels = raw27882step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27882step0 raw27882step0Labels permutation149 permutation2
    mixedMoment B raw27882step1 raw27882step1Labels = mixedMoment B raw27882step2 raw27882step2Labels := by
      have ha : raw27882step2 = -raw27882step1 := by apply Matrix.ext; change ∀ i j, raw27882step2 i j = -(raw27882step1 i j); unfold raw27882step2 raw27882step1; decide +kernel
      have hl : raw27882step2Labels = raw27882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw27883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27883step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27883step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27883step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27883step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27883 raw27883Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw27883 raw27883Labels = mixedMoment B raw27883step0 raw27883step0Labels := by
      have hz : ∀ j, raw27883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27883step0 = (fun i j => raw27883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27883step0 raw27883; decide +kernel
      have hl : raw27883step0Labels = raw27883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27883 raw27883Labels permutation346 hz
    mixedMoment B raw27883step0 raw27883step0Labels = mixedMoment B raw27883step1 raw27883step1Labels := by
      have ha : raw27883step1 = (fun i j => raw27883step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27883step1 raw27883step0; decide +kernel
      have hl : raw27883step1Labels = raw27883step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27883step0 raw27883step0Labels permutation145 permutation3
    mixedMoment B raw27883step1 raw27883step1Labels = mixedMoment B raw27883step2 raw27883step2Labels := by
      have ha : raw27883step2 = -raw27883step1 := by apply Matrix.ext; change ∀ i j, raw27883step2 i j = -(raw27883step1 i j); unfold raw27883step2 raw27883step1; decide +kernel
      have hl : raw27883step2Labels = raw27883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27883step2 raw27883step2Labels = mixedMoment B raw27883step3 raw27883step3Labels := by
      have ha : raw27883step3 = raw27883step2 := by apply Matrix.ext; unfold raw27883step3 raw27883step2; decide +kernel
      have hl : raw27883step2Labels = labelEmbedding6 ∘ raw27883step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27883step2 raw27883step2Labels raw27883step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw27884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw27884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27884 raw27884Labels = mixedMoment B node2991 node2991Labels := by
  calc
    mixedMoment B raw27884 raw27884Labels = mixedMoment B raw27884step0 raw27884step0Labels := by
      have hz : ∀ j, raw27884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27884step0 = (fun i j => raw27884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27884step0 raw27884; decide +kernel
      have hl : raw27884step0Labels = raw27884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27884 raw27884Labels permutation346 hz
    mixedMoment B raw27884step0 raw27884step0Labels = mixedMoment B raw27884step1 raw27884step1Labels := by
      have ha : raw27884step1 = (fun i j => raw27884step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27884step1 raw27884step0; decide +kernel
      have hl : raw27884step1Labels = raw27884step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27884step0 raw27884step0Labels permutation150 permutation3
    mixedMoment B raw27884step1 raw27884step1Labels = mixedMoment B raw27884step2 raw27884step2Labels := by
      have ha : raw27884step2 = -raw27884step1 := by apply Matrix.ext; change ∀ i j, raw27884step2 i j = -(raw27884step1 i j); unfold raw27884step2 raw27884step1; decide +kernel
      have hl : raw27884step2Labels = raw27884step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2991 node2991Labels := by rfl

def raw27885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27885 raw27885Labels = mixedMoment B node2987 node2987Labels := by
  calc
    mixedMoment B raw27885 raw27885Labels = mixedMoment B raw27885step0 raw27885step0Labels := by
      have ha : raw27885step0 = (fun i j => raw27885 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27885step0 raw27885; decide +kernel
      have hl : raw27885step0Labels = raw27885Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27885 raw27885Labels permutation686 permutation3
    mixedMoment B raw27885step0 raw27885step0Labels = mixedMoment B raw27885step1 raw27885step1Labels := by
      have ha : raw27885step1 = -raw27885step0 := by apply Matrix.ext; change ∀ i j, raw27885step1 i j = -(raw27885step0 i j); unfold raw27885step1 raw27885step0; decide +kernel
      have hl : raw27885step1Labels = raw27885step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2987 node2987Labels := by rfl

def raw27886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27886step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw27886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw27886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27886 raw27886Labels = mixedMoment B node3000 node3000Labels := by
  calc
    mixedMoment B raw27886 raw27886Labels = mixedMoment B raw27886step0 raw27886step0Labels := by
      have hz : ∀ j, raw27886 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27886step0 = (fun i j => raw27886 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27886step0 raw27886; decide +kernel
      have hl : raw27886step0Labels = raw27886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27886 raw27886Labels permutation346 hz
    mixedMoment B raw27886step0 raw27886step0Labels = mixedMoment B raw27886step1 raw27886step1Labels := by
      have ha : raw27886step1 = (fun i j => raw27886step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27886step1 raw27886step0; decide +kernel
      have hl : raw27886step1Labels = raw27886step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27886step0 raw27886step0Labels permutation149 permutation3
    mixedMoment B raw27886step1 raw27886step1Labels = mixedMoment B raw27886step2 raw27886step2Labels := by
      have ha : raw27886step2 = -raw27886step1 := by apply Matrix.ext; change ∀ i j, raw27886step2 i j = -(raw27886step1 i j); unfold raw27886step2 raw27886step1; decide +kernel
      have hl : raw27886step2Labels = raw27886step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3000 node3000Labels := by rfl

def raw27887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27887step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw27887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27887 raw27887Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw27887 raw27887Labels = mixedMoment B raw27887step0 raw27887step0Labels := by
      have hz : ∀ j, raw27887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27887step0 = (fun i j => raw27887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27887step0 raw27887; decide +kernel
      have hl : raw27887step0Labels = raw27887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27887 raw27887Labels permutation346 hz
    mixedMoment B raw27887step0 raw27887step0Labels = mixedMoment B raw27887step1 raw27887step1Labels := by
      have ha : raw27887step1 = (fun i j => raw27887step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27887step1 raw27887step0; decide +kernel
      have hl : raw27887step1Labels = raw27887step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27887step0 raw27887step0Labels permutation145 permutation3
    mixedMoment B raw27887step1 raw27887step1Labels = mixedMoment B raw27887step2 raw27887step2Labels := by
      have ha : raw27887step2 = -raw27887step1 := by apply Matrix.ext; change ∀ i j, raw27887step2 i j = -(raw27887step1 i j); unfold raw27887step2 raw27887step1; decide +kernel
      have hl : raw27887step2Labels = raw27887step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw27888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27888step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27888 raw27888Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw27888 raw27888Labels = mixedMoment B raw27888step0 raw27888step0Labels := by
      have hz : ∀ j, raw27888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27888step0 = (fun i j => raw27888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27888step0 raw27888; decide +kernel
      have hl : raw27888step0Labels = raw27888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27888 raw27888Labels permutation346 hz
    mixedMoment B raw27888step0 raw27888step0Labels = mixedMoment B raw27888step1 raw27888step1Labels := by
      have ha : raw27888step1 = (fun i j => raw27888step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27888step1 raw27888step0; decide +kernel
      have hl : raw27888step1Labels = raw27888step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27888step0 raw27888step0Labels permutation32 permutation3
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw27889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27889 raw27889Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw27889 raw27889Labels = mixedMoment B raw27889step0 raw27889step0Labels := by
      have hz : ∀ j, raw27889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27889step0 = (fun i j => raw27889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27889step0 raw27889; decide +kernel
      have hl : raw27889step0Labels = raw27889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27889 raw27889Labels permutation346 hz
    mixedMoment B raw27889step0 raw27889step0Labels = mixedMoment B raw27889step1 raw27889step1Labels := by
      have ha : raw27889step1 = (fun i j => raw27889step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27889step1 raw27889step0; decide +kernel
      have hl : raw27889step1Labels = raw27889step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27889step0 raw27889step0Labels permutation32 permutation3
    _ = mixedMoment B node1022 node1022Labels := by rfl

def raw27890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27890 raw27890Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw27890 raw27890Labels = mixedMoment B raw27890step0 raw27890step0Labels := by
      have ha : raw27890step0 = (fun i j => raw27890 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27890step0 raw27890; decide +kernel
      have hl : raw27890step0Labels = raw27890Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27890 raw27890Labels permutation176 permutation3
    _ = mixedMoment B node2470 node2470Labels := by rfl

def raw27891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27891Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27891step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27891 raw27891Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw27891 raw27891Labels = mixedMoment B raw27891step0 raw27891step0Labels := by
      have hz : ∀ j, raw27891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27891step0 = (fun i j => raw27891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27891step0 raw27891; decide +kernel
      have hl : raw27891step0Labels = raw27891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27891 raw27891Labels permutation346 hz
    mixedMoment B raw27891step0 raw27891step0Labels = mixedMoment B raw27891step1 raw27891step1Labels := by
      have ha : raw27891step1 = (fun i j => raw27891step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27891step1 raw27891step0; decide +kernel
      have hl : raw27891step1Labels = raw27891step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27891step0 raw27891step0Labels permutation38 permutation3
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw27892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27892Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27892step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27892 raw27892Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw27892 raw27892Labels = mixedMoment B raw27892step0 raw27892step0Labels := by
      have hz : ∀ j, raw27892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27892step0 = (fun i j => raw27892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27892step0 raw27892; decide +kernel
      have hl : raw27892step0Labels = raw27892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27892 raw27892Labels permutation346 hz
    mixedMoment B raw27892step0 raw27892step0Labels = mixedMoment B raw27892step1 raw27892step1Labels := by
      have ha : raw27892step1 = (fun i j => raw27892step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27892step1 raw27892step0; decide +kernel
      have hl : raw27892step1Labels = raw27892step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27892step0 raw27892step0Labels permutation44 permutation3
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw27893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27893step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27893 raw27893Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw27893 raw27893Labels = mixedMoment B raw27893step0 raw27893step0Labels := by
      have hz : ∀ j, raw27893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27893step0 = (fun i j => raw27893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27893step0 raw27893; decide +kernel
      have hl : raw27893step0Labels = raw27893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27893 raw27893Labels permutation346 hz
    mixedMoment B raw27893step0 raw27893step0Labels = mixedMoment B raw27893step1 raw27893step1Labels := by
      have ha : raw27893step1 = (fun i j => raw27893step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27893step1 raw27893step0; decide +kernel
      have hl : raw27893step1Labels = raw27893step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27893step0 raw27893step0Labels permutation32 permutation3
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw27894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27894 raw27894Labels = mixedMoment B node905 node905Labels := by
  calc
    mixedMoment B raw27894 raw27894Labels = mixedMoment B raw27894step0 raw27894step0Labels := by
      have ha : raw27894step0 = (fun i j => raw27894 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27894step0 raw27894; decide +kernel
      have hl : raw27894step0Labels = raw27894Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27894 raw27894Labels permutation160 permutation3
    _ = mixedMoment B node905 node905Labels := by rfl

def raw27895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27895 raw27895Labels = mixedMoment B node2320 node2320Labels := by
  calc
    mixedMoment B raw27895 raw27895Labels = mixedMoment B raw27895step0 raw27895step0Labels := by
      have ha : raw27895step0 = (fun i j => raw27895 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27895step0 raw27895; decide +kernel
      have hl : raw27895step0Labels = raw27895Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27895 raw27895Labels permutation160 permutation3
    _ = mixedMoment B node2320 node2320Labels := by rfl

def raw27896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27896 raw27896Labels = mixedMoment B node2526 node2526Labels := by
  calc
    mixedMoment B raw27896 raw27896Labels = mixedMoment B raw27896step0 raw27896step0Labels := by
      have ha : raw27896step0 = (fun i j => raw27896 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27896step0 raw27896; decide +kernel
      have hl : raw27896step0Labels = raw27896Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27896 raw27896Labels permutation160 permutation3
    _ = mixedMoment B node2526 node2526Labels := by rfl

def raw27897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27897 raw27897Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw27897 raw27897Labels = mixedMoment B raw27897step0 raw27897step0Labels := by
      have ha : raw27897step0 = (fun i j => raw27897 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27897step0 raw27897; decide +kernel
      have hl : raw27897step0Labels = raw27897Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27897 raw27897Labels permutation166 permutation3
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw27898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw27898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27898 raw27898Labels = mixedMoment B node2570 node2570Labels := by
  calc
    mixedMoment B raw27898 raw27898Labels = mixedMoment B raw27898step0 raw27898step0Labels := by
      have ha : raw27898step0 = (fun i j => raw27898 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27898step0 raw27898; decide +kernel
      have hl : raw27898step0Labels = raw27898Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27898 raw27898Labels permutation160 permutation3
    _ = mixedMoment B node2570 node2570Labels := by rfl

def raw27899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27899step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27899 raw27899Labels = mixedMoment B node925 node925Labels := by
  calc
    mixedMoment B raw27899 raw27899Labels = mixedMoment B raw27899step0 raw27899step0Labels := by
      have hz : ∀ j, raw27899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27899step0 = (fun i j => raw27899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27899step0 raw27899; decide +kernel
      have hl : raw27899step0Labels = raw27899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27899 raw27899Labels permutation346 hz
    mixedMoment B raw27899step0 raw27899step0Labels = mixedMoment B raw27899step1 raw27899step1Labels := by
      have ha : raw27899step1 = (fun i j => raw27899step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27899step1 raw27899step0; decide +kernel
      have hl : raw27899step1Labels = raw27899step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27899step0 raw27899step0Labels permutation34 permutation3
    _ = mixedMoment B node925 node925Labels := by rfl

def raw27900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27900step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27900 raw27900Labels = mixedMoment B node2335 node2335Labels := by
  calc
    mixedMoment B raw27900 raw27900Labels = mixedMoment B raw27900step0 raw27900step0Labels := by
      have hz : ∀ j, raw27900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27900step0 = (fun i j => raw27900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27900step0 raw27900; decide +kernel
      have hl : raw27900step0Labels = raw27900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27900 raw27900Labels permutation346 hz
    mixedMoment B raw27900step0 raw27900step0Labels = mixedMoment B raw27900step1 raw27900step1Labels := by
      have ha : raw27900step1 = (fun i j => raw27900step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27900step1 raw27900step0; decide +kernel
      have hl : raw27900step1Labels = raw27900step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27900step0 raw27900step0Labels permutation34 permutation3
    _ = mixedMoment B node2335 node2335Labels := by rfl

def raw27901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27901 raw27901Labels = mixedMoment B node2426 node2426Labels := by
  calc
    mixedMoment B raw27901 raw27901Labels = mixedMoment B raw27901step0 raw27901step0Labels := by
      have ha : raw27901step0 = (fun i j => raw27901 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27901step0 raw27901; decide +kernel
      have hl : raw27901step0Labels = raw27901Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27901 raw27901Labels permutation178 permutation3
    _ = mixedMoment B node2426 node2426Labels := by rfl

def raw27902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27902step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27902 raw27902Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw27902 raw27902Labels = mixedMoment B raw27902step0 raw27902step0Labels := by
      have hz : ∀ j, raw27902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27902step0 = (fun i j => raw27902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27902step0 raw27902; decide +kernel
      have hl : raw27902step0Labels = raw27902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27902 raw27902Labels permutation346 hz
    mixedMoment B raw27902step0 raw27902step0Labels = mixedMoment B raw27902step1 raw27902step1Labels := by
      have ha : raw27902step1 = (fun i j => raw27902step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27902step1 raw27902step0; decide +kernel
      have hl : raw27902step1Labels = raw27902step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27902step0 raw27902step0Labels permutation34 permutation3
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw27903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27903step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw27903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27903 raw27903Labels = mixedMoment B node2596 node2596Labels := by
  calc
    mixedMoment B raw27903 raw27903Labels = mixedMoment B raw27903step0 raw27903step0Labels := by
      have hz : ∀ j, raw27903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27903step0 = (fun i j => raw27903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27903step0 raw27903; decide +kernel
      have hl : raw27903step0Labels = raw27903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27903 raw27903Labels permutation346 hz
    mixedMoment B raw27903step0 raw27903step0Labels = mixedMoment B raw27903step1 raw27903step1Labels := by
      have ha : raw27903step1 = (fun i j => raw27903step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27903step1 raw27903step0; decide +kernel
      have hl : raw27903step1Labels = raw27903step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27903step0 raw27903step0Labels permutation34 permutation3
    _ = mixedMoment B node2596 node2596Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
