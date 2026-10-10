import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35072 raw35072Labels = mixedMoment B node2298 node2298Labels := by
  calc
    mixedMoment B raw35072 raw35072Labels = mixedMoment B raw35072step0 raw35072step0Labels := by
      have ha : raw35072step0 = (fun i j => raw35072 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35072step0 raw35072; decide +kernel
      have hl : raw35072step0Labels = raw35072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35072 raw35072Labels permutation687 permutation2
    mixedMoment B raw35072step0 raw35072step0Labels = mixedMoment B raw35072step1 raw35072step1Labels := by
      have ha : raw35072step1 = -raw35072step0 := by apply Matrix.ext; change ∀ i j, raw35072step1 i j = -(raw35072step0 i j); unfold raw35072step1 raw35072step0; decide +kernel
      have hl : raw35072step1Labels = raw35072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2298 node2298Labels := by rfl

def raw35073 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw35073Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35073step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw35073step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35073step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw35073step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35073step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw35073step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35073 raw35073Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw35073 raw35073Labels = mixedMoment B raw35073step0 raw35073step0Labels := by
      have hz : ∀ j, raw35073 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw35073step0 = (fun i j => raw35073 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw35073step0 raw35073; decide +kernel
      have hl : raw35073step0Labels = raw35073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35073 raw35073Labels permutation152 hz
    mixedMoment B raw35073step0 raw35073step0Labels = mixedMoment B raw35073step1 raw35073step1Labels := by
      have ha : raw35073step1 = (fun i j => raw35073step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35073step1 raw35073step0; decide +kernel
      have hl : raw35073step1Labels = raw35073step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35073step0 raw35073step0Labels permutation125 permutation0
    mixedMoment B raw35073step1 raw35073step1Labels = mixedMoment B raw35073step2 raw35073step2Labels := by
      have ha : raw35073step2 = -raw35073step1 := by apply Matrix.ext; change ∀ i j, raw35073step2 i j = -(raw35073step1 i j); unfold raw35073step2 raw35073step1; decide +kernel
      have hl : raw35073step2Labels = raw35073step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw35074 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35074 raw35074Labels = mixedMoment B node3656 node3656Labels := by
  calc
    mixedMoment B raw35074 raw35074Labels = mixedMoment B raw35074step0 raw35074step0Labels := by
      have ha : raw35074step0 = (fun i j => raw35074 (permutation572 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35074step0 raw35074; decide +kernel
      have hl : raw35074step0Labels = raw35074Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35074 raw35074Labels permutation572 permutation2
    _ = mixedMoment B node3656 node3656Labels := by rfl

def raw35075 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35075 raw35075Labels = mixedMoment B node3663 node3663Labels := by
  calc
    mixedMoment B raw35075 raw35075Labels = mixedMoment B raw35075step0 raw35075step0Labels := by
      have ha : raw35075step0 = (fun i j => raw35075 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35075step0 raw35075; decide +kernel
      have hl : raw35075step0Labels = raw35075Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35075 raw35075Labels permutation583 permutation2
    _ = mixedMoment B node3663 node3663Labels := by rfl

def raw35076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35076 raw35076Labels = mixedMoment B node3664 node3664Labels := by
  calc
    mixedMoment B raw35076 raw35076Labels = mixedMoment B raw35076step0 raw35076step0Labels := by
      have hz : ∀ j, raw35076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35076step0 = (fun i j => raw35076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35076step0 raw35076; decide +kernel
      have hl : raw35076step0Labels = raw35076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35076 raw35076Labels permutation346 hz
    mixedMoment B raw35076step0 raw35076step0Labels = mixedMoment B raw35076step1 raw35076step1Labels := by
      have ha : raw35076step1 = (fun i j => raw35076step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35076step1 raw35076step0; decide +kernel
      have hl : raw35076step1Labels = raw35076step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35076step0 raw35076step0Labels permutation126 permutation2
    _ = mixedMoment B node3664 node3664Labels := by rfl

def raw35077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35077 raw35077Labels = mixedMoment B node3664 node3664Labels := by
  calc
    mixedMoment B raw35077 raw35077Labels = mixedMoment B raw35077step0 raw35077step0Labels := by
      have hz : ∀ j, raw35077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35077step0 = (fun i j => raw35077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35077step0 raw35077; decide +kernel
      have hl : raw35077step0Labels = raw35077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35077 raw35077Labels permutation434 hz
    mixedMoment B raw35077step0 raw35077step0Labels = mixedMoment B raw35077step1 raw35077step1Labels := by
      have ha : raw35077step1 = (fun i j => raw35077step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35077step1 raw35077step0; decide +kernel
      have hl : raw35077step1Labels = raw35077step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35077step0 raw35077step0Labels permutation126 permutation2
    _ = mixedMoment B node3664 node3664Labels := by rfl

def raw35078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-2, 0, 2]]
def raw35078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35078 raw35078Labels = mixedMoment B node2303 node2303Labels := by
  calc
    mixedMoment B raw35078 raw35078Labels = mixedMoment B raw35078step0 raw35078step0Labels := by
      have ha : raw35078step0 = (fun i j => raw35078 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35078step0 raw35078; decide +kernel
      have hl : raw35078step0Labels = raw35078Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35078 raw35078Labels permutation583 permutation2
    _ = mixedMoment B node2303 node2303Labels := by rfl

def raw35079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw35079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35079 raw35079Labels = mixedMoment B node2303 node2303Labels := by
  calc
    mixedMoment B raw35079 raw35079Labels = mixedMoment B raw35079step0 raw35079step0Labels := by
      have ha : raw35079step0 = (fun i j => raw35079 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35079step0 raw35079; decide +kernel
      have hl : raw35079step0Labels = raw35079Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35079 raw35079Labels permutation681 permutation2
    _ = mixedMoment B node2303 node2303Labels := by rfl

def raw35080 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![0, 0], ![0, 0], ![-2, 2], ![-2, 2]]
def raw35080Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35080step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![0, 0], ![-2, 2], ![-2, 2]]
def raw35080step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35080step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-2, 2], ![-2, 2]]
def raw35080step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35080step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw35080step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35080 raw35080Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw35080 raw35080Labels = mixedMoment B raw35080step0 raw35080step0Labels := by
      have hz : ∀ j, raw35080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35080step0 = (fun i j => raw35080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35080step0 raw35080; decide +kernel
      have hl : raw35080step0Labels = raw35080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35080 raw35080Labels permutation434 hz
    mixedMoment B raw35080step0 raw35080step0Labels = mixedMoment B raw35080step1 raw35080step1Labels := by
      have hz : ∀ j, raw35080step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35080step1 = (fun i j => raw35080step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35080step1 raw35080step0; decide +kernel
      have hl : raw35080step1Labels = raw35080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35080step0 raw35080step0Labels permutation80 hz
    mixedMoment B raw35080step1 raw35080step1Labels = mixedMoment B raw35080step2 raw35080step2Labels := by
      have ha : raw35080step2 = (fun i j => raw35080step1 (permutation24 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35080step2 raw35080step1; decide +kernel
      have hl : raw35080step2Labels = raw35080step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35080step1 raw35080step1Labels permutation24 permutation0
    _ = mixedMoment B node4089 node4089Labels := by rfl

def raw35081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35081step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35081step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35081step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35081step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35081 raw35081Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw35081 raw35081Labels = mixedMoment B raw35081step0 raw35081step0Labels := by
      have hz : ∀ j, raw35081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35081step0 = (fun i j => raw35081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35081step0 raw35081; decide +kernel
      have hl : raw35081step0Labels = raw35081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35081 raw35081Labels permutation434 hz
    mixedMoment B raw35081step0 raw35081step0Labels = mixedMoment B raw35081step1 raw35081step1Labels := by
      have hz : ∀ j, raw35081step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35081step1 = (fun i j => raw35081step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35081step1 raw35081step0; decide +kernel
      have hl : raw35081step1Labels = raw35081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35081step0 raw35081step0Labels permutation80 hz
    mixedMoment B raw35081step1 raw35081step1Labels = mixedMoment B raw35081step2 raw35081step2Labels := by
      have ha : raw35081step2 = (fun i j => raw35081step1 (permutation15 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35081step2 raw35081step1; decide +kernel
      have hl : raw35081step2Labels = raw35081step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35081step1 raw35081step1Labels permutation15 permutation5
    mixedMoment B raw35081step2 raw35081step2Labels = mixedMoment B raw35081step3 raw35081step3Labels := by
      have ha : raw35081step3 = -raw35081step2 := by apply Matrix.ext; change ∀ i j, raw35081step3 i j = -(raw35081step2 i j); unfold raw35081step3 raw35081step2; decide +kernel
      have hl : raw35081step3Labels = raw35081step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35081step3 raw35081step3Labels = mixedMoment B raw35081step4 raw35081step4Labels := by
      have ha : raw35081step4 = raw35081step3 := by apply Matrix.ext; unfold raw35081step4 raw35081step3; decide +kernel
      have hl : raw35081step3Labels = labelEmbedding8 ∘ raw35081step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35081step3 raw35081step3Labels raw35081step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw35082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35082step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35082step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35082step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35082step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35082 raw35082Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw35082 raw35082Labels = mixedMoment B raw35082step0 raw35082step0Labels := by
      have hz : ∀ j, raw35082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35082step0 = (fun i j => raw35082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35082step0 raw35082; decide +kernel
      have hl : raw35082step0Labels = raw35082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35082 raw35082Labels permutation434 hz
    mixedMoment B raw35082step0 raw35082step0Labels = mixedMoment B raw35082step1 raw35082step1Labels := by
      have ha : raw35082step1 = (fun i j => raw35082step0 (permutation63 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35082step1 raw35082step0; decide +kernel
      have hl : raw35082step1Labels = raw35082step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35082step0 raw35082step0Labels permutation63 permutation5
    mixedMoment B raw35082step1 raw35082step1Labels = mixedMoment B raw35082step2 raw35082step2Labels := by
      have ha : raw35082step2 = -raw35082step1 := by apply Matrix.ext; change ∀ i j, raw35082step2 i j = -(raw35082step1 i j); unfold raw35082step2 raw35082step1; decide +kernel
      have hl : raw35082step2Labels = raw35082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35082step2 raw35082step2Labels = mixedMoment B raw35082step3 raw35082step3Labels := by
      have ha : raw35082step3 = raw35082step2 := by apply Matrix.ext; unfold raw35082step3 raw35082step2; decide +kernel
      have hl : raw35082step2Labels = labelEmbedding8 ∘ raw35082step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35082step2 raw35082step2Labels raw35082step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw35083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35083step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35083step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35083step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35083step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35083 raw35083Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw35083 raw35083Labels = mixedMoment B raw35083step0 raw35083step0Labels := by
      have hz : ∀ j, raw35083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35083step0 = (fun i j => raw35083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35083step0 raw35083; decide +kernel
      have hl : raw35083step0Labels = raw35083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35083 raw35083Labels permutation346 hz
    mixedMoment B raw35083step0 raw35083step0Labels = mixedMoment B raw35083step1 raw35083step1Labels := by
      have ha : raw35083step1 = (fun i j => raw35083step0 (permutation63 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35083step1 raw35083step0; decide +kernel
      have hl : raw35083step1Labels = raw35083step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35083step0 raw35083step0Labels permutation63 permutation5
    mixedMoment B raw35083step1 raw35083step1Labels = mixedMoment B raw35083step2 raw35083step2Labels := by
      have ha : raw35083step2 = -raw35083step1 := by apply Matrix.ext; change ∀ i j, raw35083step2 i j = -(raw35083step1 i j); unfold raw35083step2 raw35083step1; decide +kernel
      have hl : raw35083step2Labels = raw35083step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35083step2 raw35083step2Labels = mixedMoment B raw35083step3 raw35083step3Labels := by
      have ha : raw35083step3 = raw35083step2 := by apply Matrix.ext; unfold raw35083step3 raw35083step2; decide +kernel
      have hl : raw35083step2Labels = labelEmbedding8 ∘ raw35083step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35083step2 raw35083step2Labels raw35083step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw35084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw35084step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35084step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35084step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35084step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35084step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35084 raw35084Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw35084 raw35084Labels = mixedMoment B raw35084step0 raw35084step0Labels := by
      have hz : ∀ j, raw35084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35084step0 = (fun i j => raw35084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35084step0 raw35084; decide +kernel
      have hl : raw35084step0Labels = raw35084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35084 raw35084Labels permutation434 hz
    mixedMoment B raw35084step0 raw35084step0Labels = mixedMoment B raw35084step1 raw35084step1Labels := by
      have hz : ∀ j, raw35084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35084step1 = (fun i j => raw35084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35084step1 raw35084step0; decide +kernel
      have hl : raw35084step1Labels = raw35084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35084step0 raw35084step0Labels permutation80 hz
    mixedMoment B raw35084step1 raw35084step1Labels = mixedMoment B raw35084step2 raw35084step2Labels := by
      have ha : raw35084step2 = (fun i j => raw35084step1 (permutation18 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35084step2 raw35084step1; decide +kernel
      have hl : raw35084step2Labels = raw35084step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35084step1 raw35084step1Labels permutation18 permutation5
    mixedMoment B raw35084step2 raw35084step2Labels = mixedMoment B raw35084step3 raw35084step3Labels := by
      have ha : raw35084step3 = -raw35084step2 := by apply Matrix.ext; change ∀ i j, raw35084step3 i j = -(raw35084step2 i j); unfold raw35084step3 raw35084step2; decide +kernel
      have hl : raw35084step3Labels = raw35084step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35084step3 raw35084step3Labels = mixedMoment B raw35084step4 raw35084step4Labels := by
      have ha : raw35084step4 = raw35084step3 := by apply Matrix.ext; unfold raw35084step4 raw35084step3; decide +kernel
      have hl : raw35084step3Labels = labelEmbedding8 ∘ raw35084step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35084step3 raw35084step3Labels raw35084step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw35085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35085step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35085step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35085step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35085step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35085 raw35085Labels = mixedMoment B node4381 node4381Labels := by
  calc
    mixedMoment B raw35085 raw35085Labels = mixedMoment B raw35085step0 raw35085step0Labels := by
      have hz : ∀ j, raw35085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35085step0 = (fun i j => raw35085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35085step0 raw35085; decide +kernel
      have hl : raw35085step0Labels = raw35085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35085 raw35085Labels permutation434 hz
    mixedMoment B raw35085step0 raw35085step0Labels = mixedMoment B raw35085step1 raw35085step1Labels := by
      have ha : raw35085step1 = (fun i j => raw35085step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35085step1 raw35085step0; decide +kernel
      have hl : raw35085step1Labels = raw35085step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35085step0 raw35085step0Labels permutation57 permutation5
    mixedMoment B raw35085step1 raw35085step1Labels = mixedMoment B raw35085step2 raw35085step2Labels := by
      have ha : raw35085step2 = -raw35085step1 := by apply Matrix.ext; change ∀ i j, raw35085step2 i j = -(raw35085step1 i j); unfold raw35085step2 raw35085step1; decide +kernel
      have hl : raw35085step2Labels = raw35085step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35085step2 raw35085step2Labels = mixedMoment B raw35085step3 raw35085step3Labels := by
      have ha : raw35085step3 = raw35085step2 := by apply Matrix.ext; unfold raw35085step3 raw35085step2; decide +kernel
      have hl : raw35085step2Labels = labelEmbedding8 ∘ raw35085step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35085step2 raw35085step2Labels raw35085step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4381 node4381Labels := by rfl

def raw35086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35086step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35086step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35086 raw35086Labels = mixedMoment B node5046 node5046Labels := by
  calc
    mixedMoment B raw35086 raw35086Labels = mixedMoment B raw35086step0 raw35086step0Labels := by
      have ha : raw35086step0 = (fun i j => raw35086 (permutation306 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35086step0 raw35086; decide +kernel
      have hl : raw35086step0Labels = raw35086Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35086 raw35086Labels permutation306 permutation5
    mixedMoment B raw35086step0 raw35086step0Labels = mixedMoment B raw35086step1 raw35086step1Labels := by
      have ha : raw35086step1 = -raw35086step0 := by apply Matrix.ext; change ∀ i j, raw35086step1 i j = -(raw35086step0 i j); unfold raw35086step1 raw35086step0; decide +kernel
      have hl : raw35086step1Labels = raw35086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35086step1 raw35086step1Labels = mixedMoment B raw35086step2 raw35086step2Labels := by
      have ha : raw35086step2 = raw35086step1 := by apply Matrix.ext; unfold raw35086step2 raw35086step1; decide +kernel
      have hl : raw35086step1Labels = labelEmbedding8 ∘ raw35086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35086step1 raw35086step1Labels raw35086step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5046 node5046Labels := by rfl

def raw35087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35087step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35087step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35087step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35087step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35087 raw35087Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35087 raw35087Labels = mixedMoment B raw35087step0 raw35087step0Labels := by
      have hz : ∀ j, raw35087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35087step0 = (fun i j => raw35087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35087step0 raw35087; decide +kernel
      have hl : raw35087step0Labels = raw35087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35087 raw35087Labels permutation434 hz
    mixedMoment B raw35087step0 raw35087step0Labels = mixedMoment B raw35087step1 raw35087step1Labels := by
      have ha : raw35087step1 = (fun i j => raw35087step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35087step1 raw35087step0; decide +kernel
      have hl : raw35087step1Labels = raw35087step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35087step0 raw35087step0Labels permutation60 permutation5
    mixedMoment B raw35087step1 raw35087step1Labels = mixedMoment B raw35087step2 raw35087step2Labels := by
      have ha : raw35087step2 = -raw35087step1 := by apply Matrix.ext; change ∀ i j, raw35087step2 i j = -(raw35087step1 i j); unfold raw35087step2 raw35087step1; decide +kernel
      have hl : raw35087step2Labels = raw35087step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35087step2 raw35087step2Labels = mixedMoment B raw35087step3 raw35087step3Labels := by
      have ha : raw35087step3 = raw35087step2 := by apply Matrix.ext; unfold raw35087step3 raw35087step2; decide +kernel
      have hl : raw35087step2Labels = labelEmbedding8 ∘ raw35087step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35087step2 raw35087step2Labels raw35087step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw35088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35088step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35088step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35088step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35088 raw35088Labels = mixedMoment B node4381 node4381Labels := by
  calc
    mixedMoment B raw35088 raw35088Labels = mixedMoment B raw35088step0 raw35088step0Labels := by
      have hz : ∀ j, raw35088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35088step0 = (fun i j => raw35088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35088step0 raw35088; decide +kernel
      have hl : raw35088step0Labels = raw35088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35088 raw35088Labels permutation346 hz
    mixedMoment B raw35088step0 raw35088step0Labels = mixedMoment B raw35088step1 raw35088step1Labels := by
      have ha : raw35088step1 = (fun i j => raw35088step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35088step1 raw35088step0; decide +kernel
      have hl : raw35088step1Labels = raw35088step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35088step0 raw35088step0Labels permutation57 permutation5
    mixedMoment B raw35088step1 raw35088step1Labels = mixedMoment B raw35088step2 raw35088step2Labels := by
      have ha : raw35088step2 = -raw35088step1 := by apply Matrix.ext; change ∀ i j, raw35088step2 i j = -(raw35088step1 i j); unfold raw35088step2 raw35088step1; decide +kernel
      have hl : raw35088step2Labels = raw35088step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35088step2 raw35088step2Labels = mixedMoment B raw35088step3 raw35088step3Labels := by
      have ha : raw35088step3 = raw35088step2 := by apply Matrix.ext; unfold raw35088step3 raw35088step2; decide +kernel
      have hl : raw35088step2Labels = labelEmbedding8 ∘ raw35088step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35088step2 raw35088step2Labels raw35088step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4381 node4381Labels := by rfl

def raw35089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35089step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35089step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35089step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35089 raw35089Labels = mixedMoment B node5046 node5046Labels := by
  calc
    mixedMoment B raw35089 raw35089Labels = mixedMoment B raw35089step0 raw35089step0Labels := by
      have ha : raw35089step0 = (fun i j => raw35089 (permutation290 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35089step0 raw35089; decide +kernel
      have hl : raw35089step0Labels = raw35089Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35089 raw35089Labels permutation290 permutation5
    mixedMoment B raw35089step0 raw35089step0Labels = mixedMoment B raw35089step1 raw35089step1Labels := by
      have ha : raw35089step1 = -raw35089step0 := by apply Matrix.ext; change ∀ i j, raw35089step1 i j = -(raw35089step0 i j); unfold raw35089step1 raw35089step0; decide +kernel
      have hl : raw35089step1Labels = raw35089step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35089step1 raw35089step1Labels = mixedMoment B raw35089step2 raw35089step2Labels := by
      have ha : raw35089step2 = raw35089step1 := by apply Matrix.ext; unfold raw35089step2 raw35089step1; decide +kernel
      have hl : raw35089step1Labels = labelEmbedding8 ∘ raw35089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35089step1 raw35089step1Labels raw35089step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5046 node5046Labels := by rfl

def raw35090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35090step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35090step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35090step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35090step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35090 raw35090Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35090 raw35090Labels = mixedMoment B raw35090step0 raw35090step0Labels := by
      have hz : ∀ j, raw35090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35090step0 = (fun i j => raw35090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35090step0 raw35090; decide +kernel
      have hl : raw35090step0Labels = raw35090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35090 raw35090Labels permutation346 hz
    mixedMoment B raw35090step0 raw35090step0Labels = mixedMoment B raw35090step1 raw35090step1Labels := by
      have ha : raw35090step1 = (fun i j => raw35090step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35090step1 raw35090step0; decide +kernel
      have hl : raw35090step1Labels = raw35090step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35090step0 raw35090step0Labels permutation60 permutation5
    mixedMoment B raw35090step1 raw35090step1Labels = mixedMoment B raw35090step2 raw35090step2Labels := by
      have ha : raw35090step2 = -raw35090step1 := by apply Matrix.ext; change ∀ i j, raw35090step2 i j = -(raw35090step1 i j); unfold raw35090step2 raw35090step1; decide +kernel
      have hl : raw35090step2Labels = raw35090step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35090step2 raw35090step2Labels = mixedMoment B raw35090step3 raw35090step3Labels := by
      have ha : raw35090step3 = raw35090step2 := by apply Matrix.ext; unfold raw35090step3 raw35090step2; decide +kernel
      have hl : raw35090step2Labels = labelEmbedding8 ∘ raw35090step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35090step2 raw35090step2Labels raw35090step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw35091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![-1, -1, 2], ![-3, 0, 3]]
def raw35091step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw35091step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35091step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw35091step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35091 raw35091Labels = mixedMoment B node4382 node4382Labels := by
  calc
    mixedMoment B raw35091 raw35091Labels = mixedMoment B raw35091step0 raw35091step0Labels := by
      have hz : ∀ j, raw35091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35091step0 = (fun i j => raw35091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35091step0 raw35091; decide +kernel
      have hl : raw35091step0Labels = raw35091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35091 raw35091Labels permutation434 hz
    mixedMoment B raw35091step0 raw35091step0Labels = mixedMoment B raw35091step1 raw35091step1Labels := by
      have hz : ∀ j, raw35091step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35091step1 = (fun i j => raw35091step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35091step1 raw35091step0; decide +kernel
      have hl : raw35091step1Labels = raw35091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35091step0 raw35091step0Labels permutation80 hz
    mixedMoment B raw35091step1 raw35091step1Labels = mixedMoment B raw35091step2 raw35091step2Labels := by
      have ha : raw35091step2 = (fun i j => raw35091step1 (permutation15 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35091step2 raw35091step1; decide +kernel
      have hl : raw35091step2Labels = raw35091step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35091step1 raw35091step1Labels permutation15 permutation5
    mixedMoment B raw35091step2 raw35091step2Labels = mixedMoment B raw35091step3 raw35091step3Labels := by
      have ha : raw35091step3 = -raw35091step2 := by apply Matrix.ext; change ∀ i j, raw35091step3 i j = -(raw35091step2 i j); unfold raw35091step3 raw35091step2; decide +kernel
      have hl : raw35091step3Labels = raw35091step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35091step3 raw35091step3Labels = mixedMoment B raw35091step4 raw35091step4Labels := by
      have ha : raw35091step4 = raw35091step3 := by apply Matrix.ext; unfold raw35091step4 raw35091step3; decide +kernel
      have hl : raw35091step3Labels = labelEmbedding8 ∘ raw35091step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35091step3 raw35091step3Labels raw35091step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4382 node4382Labels := by rfl

def raw35092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35092step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35092step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35092step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35092 raw35092Labels = mixedMoment B node4651 node4651Labels := by
  calc
    mixedMoment B raw35092 raw35092Labels = mixedMoment B raw35092step0 raw35092step0Labels := by
      have hz : ∀ j, raw35092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35092step0 = (fun i j => raw35092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35092step0 raw35092; decide +kernel
      have hl : raw35092step0Labels = raw35092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35092 raw35092Labels permutation434 hz
    mixedMoment B raw35092step0 raw35092step0Labels = mixedMoment B raw35092step1 raw35092step1Labels := by
      have ha : raw35092step1 = (fun i j => raw35092step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35092step1 raw35092step0; decide +kernel
      have hl : raw35092step1Labels = raw35092step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35092step0 raw35092step0Labels permutation126 permutation3
    mixedMoment B raw35092step1 raw35092step1Labels = mixedMoment B raw35092step2 raw35092step2Labels := by
      have ha : raw35092step2 = -raw35092step1 := by apply Matrix.ext; change ∀ i j, raw35092step2 i j = -(raw35092step1 i j); unfold raw35092step2 raw35092step1; decide +kernel
      have hl : raw35092step2Labels = raw35092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35092step2 raw35092step2Labels = mixedMoment B raw35092step3 raw35092step3Labels := by
      have ha : raw35092step3 = raw35092step2 := by apply Matrix.ext; unfold raw35092step3 raw35092step2; decide +kernel
      have hl : raw35092step2Labels = labelEmbedding6 ∘ raw35092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35092step2 raw35092step2Labels raw35092step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4651 node4651Labels := by rfl

def raw35093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35093step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35093step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35093step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35093step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35093 raw35093Labels = mixedMoment B node4651 node4651Labels := by
  calc
    mixedMoment B raw35093 raw35093Labels = mixedMoment B raw35093step0 raw35093step0Labels := by
      have hz : ∀ j, raw35093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35093step0 = (fun i j => raw35093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35093step0 raw35093; decide +kernel
      have hl : raw35093step0Labels = raw35093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35093 raw35093Labels permutation346 hz
    mixedMoment B raw35093step0 raw35093step0Labels = mixedMoment B raw35093step1 raw35093step1Labels := by
      have ha : raw35093step1 = (fun i j => raw35093step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35093step1 raw35093step0; decide +kernel
      have hl : raw35093step1Labels = raw35093step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35093step0 raw35093step0Labels permutation126 permutation3
    mixedMoment B raw35093step1 raw35093step1Labels = mixedMoment B raw35093step2 raw35093step2Labels := by
      have ha : raw35093step2 = -raw35093step1 := by apply Matrix.ext; change ∀ i j, raw35093step2 i j = -(raw35093step1 i j); unfold raw35093step2 raw35093step1; decide +kernel
      have hl : raw35093step2Labels = raw35093step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35093step2 raw35093step2Labels = mixedMoment B raw35093step3 raw35093step3Labels := by
      have ha : raw35093step3 = raw35093step2 := by apply Matrix.ext; unfold raw35093step3 raw35093step2; decide +kernel
      have hl : raw35093step2Labels = labelEmbedding6 ∘ raw35093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35093step2 raw35093step2Labels raw35093step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4651 node4651Labels := by rfl

def raw35094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 0, -1]]
def raw35094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![3, -3, 0], ![1, 0, -1]]
def raw35094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![3, -3, 0], ![1, 0, -1]]
def raw35094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw35094step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35094step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35094step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35094step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35094 raw35094Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw35094 raw35094Labels = mixedMoment B raw35094step0 raw35094step0Labels := by
      have hz : ∀ j, raw35094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35094step0 = (fun i j => raw35094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35094step0 raw35094; decide +kernel
      have hl : raw35094step0Labels = raw35094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35094 raw35094Labels permutation434 hz
    mixedMoment B raw35094step0 raw35094step0Labels = mixedMoment B raw35094step1 raw35094step1Labels := by
      have hz : ∀ j, raw35094step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35094step1 = (fun i j => raw35094step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35094step1 raw35094step0; decide +kernel
      have hl : raw35094step1Labels = raw35094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35094step0 raw35094step0Labels permutation80 hz
    mixedMoment B raw35094step1 raw35094step1Labels = mixedMoment B raw35094step2 raw35094step2Labels := by
      have ha : raw35094step2 = (fun i j => raw35094step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35094step2 raw35094step1; decide +kernel
      have hl : raw35094step2Labels = raw35094step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35094step1 raw35094step1Labels permutation24 permutation3
    mixedMoment B raw35094step2 raw35094step2Labels = mixedMoment B raw35094step3 raw35094step3Labels := by
      have ha : raw35094step3 = -raw35094step2 := by apply Matrix.ext; change ∀ i j, raw35094step3 i j = -(raw35094step2 i j); unfold raw35094step3 raw35094step2; decide +kernel
      have hl : raw35094step3Labels = raw35094step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35094step3 raw35094step3Labels = mixedMoment B raw35094step4 raw35094step4Labels := by
      have ha : raw35094step4 = raw35094step3 := by apply Matrix.ext; unfold raw35094step4 raw35094step3; decide +kernel
      have hl : raw35094step3Labels = labelEmbedding6 ∘ raw35094step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35094step3 raw35094step3Labels raw35094step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw35095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![-2, 0, 2], ![-2, -1, 3]]
def raw35095step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35095step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw35095step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35095step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw35095step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35095 raw35095Labels = mixedMoment B node4383 node4383Labels := by
  calc
    mixedMoment B raw35095 raw35095Labels = mixedMoment B raw35095step0 raw35095step0Labels := by
      have hz : ∀ j, raw35095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35095step0 = (fun i j => raw35095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35095step0 raw35095; decide +kernel
      have hl : raw35095step0Labels = raw35095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35095 raw35095Labels permutation434 hz
    mixedMoment B raw35095step0 raw35095step0Labels = mixedMoment B raw35095step1 raw35095step1Labels := by
      have hz : ∀ j, raw35095step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35095step1 = (fun i j => raw35095step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35095step1 raw35095step0; decide +kernel
      have hl : raw35095step1Labels = raw35095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35095step0 raw35095step0Labels permutation80 hz
    mixedMoment B raw35095step1 raw35095step1Labels = mixedMoment B raw35095step2 raw35095step2Labels := by
      have ha : raw35095step2 = (fun i j => raw35095step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35095step2 raw35095step1; decide +kernel
      have hl : raw35095step2Labels = raw35095step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35095step1 raw35095step1Labels permutation14 permutation5
    mixedMoment B raw35095step2 raw35095step2Labels = mixedMoment B raw35095step3 raw35095step3Labels := by
      have ha : raw35095step3 = -raw35095step2 := by apply Matrix.ext; change ∀ i j, raw35095step3 i j = -(raw35095step2 i j); unfold raw35095step3 raw35095step2; decide +kernel
      have hl : raw35095step3Labels = raw35095step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35095step3 raw35095step3Labels = mixedMoment B raw35095step4 raw35095step4Labels := by
      have ha : raw35095step4 = raw35095step3 := by apply Matrix.ext; unfold raw35095step4 raw35095step3; decide +kernel
      have hl : raw35095step3Labels = labelEmbedding8 ∘ raw35095step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35095step3 raw35095step3Labels raw35095step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4383 node4383Labels := by rfl

def raw35096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35096step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35096step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35096step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35096step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35096 raw35096Labels = mixedMoment B node4920 node4920Labels := by
  calc
    mixedMoment B raw35096 raw35096Labels = mixedMoment B raw35096step0 raw35096step0Labels := by
      have hz : ∀ j, raw35096 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35096step0 = (fun i j => raw35096 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35096step0 raw35096; decide +kernel
      have hl : raw35096step0Labels = raw35096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35096 raw35096Labels permutation434 hz
    mixedMoment B raw35096step0 raw35096step0Labels = mixedMoment B raw35096step1 raw35096step1Labels := by
      have ha : raw35096step1 = (fun i j => raw35096step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35096step1 raw35096step0; decide +kernel
      have hl : raw35096step1Labels = raw35096step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35096step0 raw35096step0Labels permutation150 permutation3
    mixedMoment B raw35096step1 raw35096step1Labels = mixedMoment B raw35096step2 raw35096step2Labels := by
      have ha : raw35096step2 = -raw35096step1 := by apply Matrix.ext; change ∀ i j, raw35096step2 i j = -(raw35096step1 i j); unfold raw35096step2 raw35096step1; decide +kernel
      have hl : raw35096step2Labels = raw35096step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35096step2 raw35096step2Labels = mixedMoment B raw35096step3 raw35096step3Labels := by
      have ha : raw35096step3 = raw35096step2 := by apply Matrix.ext; unfold raw35096step3 raw35096step2; decide +kernel
      have hl : raw35096step2Labels = labelEmbedding6 ∘ raw35096step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35096step2 raw35096step2Labels raw35096step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4920 node4920Labels := by rfl

def raw35097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35097step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35097step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35097step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35097step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35097 raw35097Labels = mixedMoment B node4920 node4920Labels := by
  calc
    mixedMoment B raw35097 raw35097Labels = mixedMoment B raw35097step0 raw35097step0Labels := by
      have hz : ∀ j, raw35097 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35097step0 = (fun i j => raw35097 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35097step0 raw35097; decide +kernel
      have hl : raw35097step0Labels = raw35097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35097 raw35097Labels permutation346 hz
    mixedMoment B raw35097step0 raw35097step0Labels = mixedMoment B raw35097step1 raw35097step1Labels := by
      have ha : raw35097step1 = (fun i j => raw35097step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35097step1 raw35097step0; decide +kernel
      have hl : raw35097step1Labels = raw35097step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35097step0 raw35097step0Labels permutation150 permutation3
    mixedMoment B raw35097step1 raw35097step1Labels = mixedMoment B raw35097step2 raw35097step2Labels := by
      have ha : raw35097step2 = -raw35097step1 := by apply Matrix.ext; change ∀ i j, raw35097step2 i j = -(raw35097step1 i j); unfold raw35097step2 raw35097step1; decide +kernel
      have hl : raw35097step2Labels = raw35097step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35097step2 raw35097step2Labels = mixedMoment B raw35097step3 raw35097step3Labels := by
      have ha : raw35097step3 = raw35097step2 := by apply Matrix.ext; unfold raw35097step3 raw35097step2; decide +kernel
      have hl : raw35097step2Labels = labelEmbedding6 ∘ raw35097step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35097step2 raw35097step2Labels raw35097step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4920 node4920Labels := by rfl

def raw35098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35098step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35098step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35098 raw35098Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw35098 raw35098Labels = mixedMoment B raw35098step0 raw35098step0Labels := by
      have hz : ∀ j, raw35098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35098step0 = (fun i j => raw35098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35098step0 raw35098; decide +kernel
      have hl : raw35098step0Labels = raw35098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35098 raw35098Labels permutation434 hz
    mixedMoment B raw35098step0 raw35098step0Labels = mixedMoment B raw35098step1 raw35098step1Labels := by
      have hz : ∀ j, raw35098step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35098step1 = (fun i j => raw35098step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35098step1 raw35098step0; decide +kernel
      have hl : raw35098step1Labels = raw35098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35098step0 raw35098step0Labels permutation80 hz
    mixedMoment B raw35098step1 raw35098step1Labels = mixedMoment B raw35098step2 raw35098step2Labels := by
      have ha : raw35098step2 = (fun i j => raw35098step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35098step2 raw35098step1; decide +kernel
      have hl : raw35098step2Labels = raw35098step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35098step1 raw35098step1Labels permutation15 permutation3
    _ = mixedMoment B node1653 node1653Labels := by rfl

def raw35099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35099step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35099 raw35099Labels = mixedMoment B node3448 node3448Labels := by
  calc
    mixedMoment B raw35099 raw35099Labels = mixedMoment B raw35099step0 raw35099step0Labels := by
      have hz : ∀ j, raw35099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35099step0 = (fun i j => raw35099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35099step0 raw35099; decide +kernel
      have hl : raw35099step0Labels = raw35099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35099 raw35099Labels permutation434 hz
    mixedMoment B raw35099step0 raw35099step0Labels = mixedMoment B raw35099step1 raw35099step1Labels := by
      have ha : raw35099step1 = (fun i j => raw35099step0 (permutation63 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35099step1 raw35099step0; decide +kernel
      have hl : raw35099step1Labels = raw35099step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35099step0 raw35099step0Labels permutation63 permutation3
    _ = mixedMoment B node3448 node3448Labels := by rfl

def raw35100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35100 raw35100Labels = mixedMoment B node3448 node3448Labels := by
  calc
    mixedMoment B raw35100 raw35100Labels = mixedMoment B raw35100step0 raw35100step0Labels := by
      have hz : ∀ j, raw35100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35100step0 = (fun i j => raw35100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35100step0 raw35100; decide +kernel
      have hl : raw35100step0Labels = raw35100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35100 raw35100Labels permutation346 hz
    mixedMoment B raw35100step0 raw35100step0Labels = mixedMoment B raw35100step1 raw35100step1Labels := by
      have ha : raw35100step1 = (fun i j => raw35100step0 (permutation63 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35100step1 raw35100step0; decide +kernel
      have hl : raw35100step1Labels = raw35100step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35100step0 raw35100step0Labels permutation63 permutation3
    _ = mixedMoment B node3448 node3448Labels := by rfl

def raw35101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35101step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35101step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35101 raw35101Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw35101 raw35101Labels = mixedMoment B raw35101step0 raw35101step0Labels := by
      have hz : ∀ j, raw35101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35101step0 = (fun i j => raw35101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35101step0 raw35101; decide +kernel
      have hl : raw35101step0Labels = raw35101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35101 raw35101Labels permutation434 hz
    mixedMoment B raw35101step0 raw35101step0Labels = mixedMoment B raw35101step1 raw35101step1Labels := by
      have hz : ∀ j, raw35101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35101step1 = (fun i j => raw35101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35101step1 raw35101step0; decide +kernel
      have hl : raw35101step1Labels = raw35101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35101step0 raw35101step0Labels permutation80 hz
    mixedMoment B raw35101step1 raw35101step1Labels = mixedMoment B raw35101step2 raw35101step2Labels := by
      have ha : raw35101step2 = (fun i j => raw35101step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35101step2 raw35101step1; decide +kernel
      have hl : raw35101step2Labels = raw35101step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35101step1 raw35101step1Labels permutation15 permutation3
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw35102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35102 raw35102Labels = mixedMoment B node1547 node1547Labels := by
  calc
    mixedMoment B raw35102 raw35102Labels = mixedMoment B raw35102step0 raw35102step0Labels := by
      have hz : ∀ j, raw35102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35102step0 = (fun i j => raw35102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35102step0 raw35102; decide +kernel
      have hl : raw35102step0Labels = raw35102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35102 raw35102Labels permutation434 hz
    mixedMoment B raw35102step0 raw35102step0Labels = mixedMoment B raw35102step1 raw35102step1Labels := by
      have ha : raw35102step1 = (fun i j => raw35102step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35102step1 raw35102step0; decide +kernel
      have hl : raw35102step1Labels = raw35102step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35102step0 raw35102step0Labels permutation57 permutation3
    _ = mixedMoment B node1547 node1547Labels := by rfl

def raw35103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35103 raw35103Labels = mixedMoment B node3363 node3363Labels := by
  calc
    mixedMoment B raw35103 raw35103Labels = mixedMoment B raw35103step0 raw35103step0Labels := by
      have ha : raw35103step0 = (fun i j => raw35103 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35103step0 raw35103; decide +kernel
      have hl : raw35103step0Labels = raw35103Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35103 raw35103Labels permutation272 permutation3
    _ = mixedMoment B node3363 node3363Labels := by rfl

def raw35104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35104 raw35104Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw35104 raw35104Labels = mixedMoment B raw35104step0 raw35104step0Labels := by
      have hz : ∀ j, raw35104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35104step0 = (fun i j => raw35104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35104step0 raw35104; decide +kernel
      have hl : raw35104step0Labels = raw35104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35104 raw35104Labels permutation434 hz
    mixedMoment B raw35104step0 raw35104step0Labels = mixedMoment B raw35104step1 raw35104step1Labels := by
      have ha : raw35104step1 = (fun i j => raw35104step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35104step1 raw35104step0; decide +kernel
      have hl : raw35104step1Labels = raw35104step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35104step0 raw35104step0Labels permutation60 permutation3
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw35105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35105 raw35105Labels = mixedMoment B node1547 node1547Labels := by
  calc
    mixedMoment B raw35105 raw35105Labels = mixedMoment B raw35105step0 raw35105step0Labels := by
      have hz : ∀ j, raw35105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35105step0 = (fun i j => raw35105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35105step0 raw35105; decide +kernel
      have hl : raw35105step0Labels = raw35105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35105 raw35105Labels permutation346 hz
    mixedMoment B raw35105step0 raw35105step0Labels = mixedMoment B raw35105step1 raw35105step1Labels := by
      have ha : raw35105step1 = (fun i j => raw35105step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35105step1 raw35105step0; decide +kernel
      have hl : raw35105step1Labels = raw35105step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35105step0 raw35105step0Labels permutation57 permutation3
    _ = mixedMoment B node1547 node1547Labels := by rfl

def raw35106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35106 raw35106Labels = mixedMoment B node3363 node3363Labels := by
  calc
    mixedMoment B raw35106 raw35106Labels = mixedMoment B raw35106step0 raw35106step0Labels := by
      have ha : raw35106step0 = (fun i j => raw35106 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35106step0 raw35106; decide +kernel
      have hl : raw35106step0Labels = raw35106Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35106 raw35106Labels permutation266 permutation3
    _ = mixedMoment B node3363 node3363Labels := by rfl

def raw35107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw35107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35107 raw35107Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw35107 raw35107Labels = mixedMoment B raw35107step0 raw35107step0Labels := by
      have hz : ∀ j, raw35107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35107step0 = (fun i j => raw35107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35107step0 raw35107; decide +kernel
      have hl : raw35107step0Labels = raw35107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35107 raw35107Labels permutation346 hz
    mixedMoment B raw35107step0 raw35107step0Labels = mixedMoment B raw35107step1 raw35107step1Labels := by
      have ha : raw35107step1 = (fun i j => raw35107step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35107step1 raw35107step0; decide +kernel
      have hl : raw35107step1Labels = raw35107step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35107step0 raw35107step0Labels permutation60 permutation3
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw35108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35108step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, -1, -1], ![3, 0, -3]]
def raw35108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35108 raw35108Labels = mixedMoment B node1548 node1548Labels := by
  calc
    mixedMoment B raw35108 raw35108Labels = mixedMoment B raw35108step0 raw35108step0Labels := by
      have hz : ∀ j, raw35108 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35108step0 = (fun i j => raw35108 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35108step0 raw35108; decide +kernel
      have hl : raw35108step0Labels = raw35108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35108 raw35108Labels permutation434 hz
    mixedMoment B raw35108step0 raw35108step0Labels = mixedMoment B raw35108step1 raw35108step1Labels := by
      have hz : ∀ j, raw35108step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35108step1 = (fun i j => raw35108step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35108step1 raw35108step0; decide +kernel
      have hl : raw35108step1Labels = raw35108step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35108step0 raw35108step0Labels permutation80 hz
    mixedMoment B raw35108step1 raw35108step1Labels = mixedMoment B raw35108step2 raw35108step2Labels := by
      have ha : raw35108step2 = (fun i j => raw35108step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35108step2 raw35108step1; decide +kernel
      have hl : raw35108step2Labels = raw35108step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35108step1 raw35108step1Labels permutation15 permutation3
    _ = mixedMoment B node1548 node1548Labels := by rfl

def raw35109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35109 raw35109Labels = mixedMoment B node1779 node1779Labels := by
  calc
    mixedMoment B raw35109 raw35109Labels = mixedMoment B raw35109step0 raw35109step0Labels := by
      have hz : ∀ j, raw35109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35109step0 = (fun i j => raw35109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35109step0 raw35109; decide +kernel
      have hl : raw35109step0Labels = raw35109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35109 raw35109Labels permutation434 hz
    mixedMoment B raw35109step0 raw35109step0Labels = mixedMoment B raw35109step1 raw35109step1Labels := by
      have ha : raw35109step1 = (fun i j => raw35109step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35109step1 raw35109step0; decide +kernel
      have hl : raw35109step1Labels = raw35109step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35109step0 raw35109step0Labels permutation126 permutation3
    mixedMoment B raw35109step1 raw35109step1Labels = mixedMoment B raw35109step2 raw35109step2Labels := by
      have ha : raw35109step2 = -raw35109step1 := by apply Matrix.ext; change ∀ i j, raw35109step2 i j = -(raw35109step1 i j); unfold raw35109step2 raw35109step1; decide +kernel
      have hl : raw35109step2Labels = raw35109step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1779 node1779Labels := by rfl

def raw35110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw35110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35110 raw35110Labels = mixedMoment B node1779 node1779Labels := by
  calc
    mixedMoment B raw35110 raw35110Labels = mixedMoment B raw35110step0 raw35110step0Labels := by
      have hz : ∀ j, raw35110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35110step0 = (fun i j => raw35110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35110step0 raw35110; decide +kernel
      have hl : raw35110step0Labels = raw35110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35110 raw35110Labels permutation346 hz
    mixedMoment B raw35110step0 raw35110step0Labels = mixedMoment B raw35110step1 raw35110step1Labels := by
      have ha : raw35110step1 = (fun i j => raw35110step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35110step1 raw35110step0; decide +kernel
      have hl : raw35110step1Labels = raw35110step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35110step0 raw35110step0Labels permutation126 permutation3
    mixedMoment B raw35110step1 raw35110step1Labels = mixedMoment B raw35110step2 raw35110step2Labels := by
      have ha : raw35110step2 = -raw35110step1 := by apply Matrix.ext; change ∀ i j, raw35110step2 i j = -(raw35110step1 i j); unfold raw35110step2 raw35110step1; decide +kernel
      have hl : raw35110step2Labels = raw35110step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1779 node1779Labels := by rfl

def raw35111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 0, -1]]
def raw35111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![3, -3, 0], ![1, 0, -1]]
def raw35111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![3, -3, 0], ![1, 0, -1]]
def raw35111step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw35111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35111step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35111 raw35111Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw35111 raw35111Labels = mixedMoment B raw35111step0 raw35111step0Labels := by
      have hz : ∀ j, raw35111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35111step0 = (fun i j => raw35111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35111step0 raw35111; decide +kernel
      have hl : raw35111step0Labels = raw35111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35111 raw35111Labels permutation434 hz
    mixedMoment B raw35111step0 raw35111step0Labels = mixedMoment B raw35111step1 raw35111step1Labels := by
      have hz : ∀ j, raw35111step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35111step1 = (fun i j => raw35111step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35111step1 raw35111step0; decide +kernel
      have hl : raw35111step1Labels = raw35111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35111step0 raw35111step0Labels permutation80 hz
    mixedMoment B raw35111step1 raw35111step1Labels = mixedMoment B raw35111step2 raw35111step2Labels := by
      have ha : raw35111step2 = (fun i j => raw35111step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35111step2 raw35111step1; decide +kernel
      have hl : raw35111step2Labels = raw35111step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35111step1 raw35111step1Labels permutation24 permutation3
    mixedMoment B raw35111step2 raw35111step2Labels = mixedMoment B raw35111step3 raw35111step3Labels := by
      have ha : raw35111step3 = -raw35111step2 := by apply Matrix.ext; change ∀ i j, raw35111step3 i j = -(raw35111step2 i j); unfold raw35111step3 raw35111step2; decide +kernel
      have hl : raw35111step3Labels = raw35111step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw35112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35112step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, 0, -2], ![3, -1, -2]]
def raw35112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35112 raw35112Labels = mixedMoment B node1549 node1549Labels := by
  calc
    mixedMoment B raw35112 raw35112Labels = mixedMoment B raw35112step0 raw35112step0Labels := by
      have hz : ∀ j, raw35112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35112step0 = (fun i j => raw35112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35112step0 raw35112; decide +kernel
      have hl : raw35112step0Labels = raw35112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35112 raw35112Labels permutation434 hz
    mixedMoment B raw35112step0 raw35112step0Labels = mixedMoment B raw35112step1 raw35112step1Labels := by
      have hz : ∀ j, raw35112step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35112step1 = (fun i j => raw35112step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35112step1 raw35112step0; decide +kernel
      have hl : raw35112step1Labels = raw35112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35112step0 raw35112step0Labels permutation80 hz
    mixedMoment B raw35112step1 raw35112step1Labels = mixedMoment B raw35112step2 raw35112step2Labels := by
      have ha : raw35112step2 = (fun i j => raw35112step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35112step2 raw35112step1; decide +kernel
      have hl : raw35112step2Labels = raw35112step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35112step1 raw35112step1Labels permutation14 permutation3
    _ = mixedMoment B node1549 node1549Labels := by rfl

def raw35113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35113 raw35113Labels = mixedMoment B node2311 node2311Labels := by
  calc
    mixedMoment B raw35113 raw35113Labels = mixedMoment B raw35113step0 raw35113step0Labels := by
      have hz : ∀ j, raw35113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35113step0 = (fun i j => raw35113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35113step0 raw35113; decide +kernel
      have hl : raw35113step0Labels = raw35113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35113 raw35113Labels permutation434 hz
    mixedMoment B raw35113step0 raw35113step0Labels = mixedMoment B raw35113step1 raw35113step1Labels := by
      have ha : raw35113step1 = (fun i j => raw35113step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35113step1 raw35113step0; decide +kernel
      have hl : raw35113step1Labels = raw35113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35113step0 raw35113step0Labels permutation150 permutation3
    mixedMoment B raw35113step1 raw35113step1Labels = mixedMoment B raw35113step2 raw35113step2Labels := by
      have ha : raw35113step2 = -raw35113step1 := by apply Matrix.ext; change ∀ i j, raw35113step2 i j = -(raw35113step1 i j); unfold raw35113step2 raw35113step1; decide +kernel
      have hl : raw35113step2Labels = raw35113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2311 node2311Labels := by rfl

def raw35114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw35114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35114 raw35114Labels = mixedMoment B node2311 node2311Labels := by
  calc
    mixedMoment B raw35114 raw35114Labels = mixedMoment B raw35114step0 raw35114step0Labels := by
      have hz : ∀ j, raw35114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35114step0 = (fun i j => raw35114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35114step0 raw35114; decide +kernel
      have hl : raw35114step0Labels = raw35114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35114 raw35114Labels permutation346 hz
    mixedMoment B raw35114step0 raw35114step0Labels = mixedMoment B raw35114step1 raw35114step1Labels := by
      have ha : raw35114step1 = (fun i j => raw35114step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35114step1 raw35114step0; decide +kernel
      have hl : raw35114step1Labels = raw35114step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35114step0 raw35114step0Labels permutation150 permutation3
    mixedMoment B raw35114step1 raw35114step1Labels = mixedMoment B raw35114step2 raw35114step2Labels := by
      have ha : raw35114step2 = -raw35114step1 := by apply Matrix.ext; change ∀ i j, raw35114step2 i j = -(raw35114step1 i j); unfold raw35114step2 raw35114step1; decide +kernel
      have hl : raw35114step2Labels = raw35114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2311 node2311Labels := by rfl

def raw35115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35115step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35115 raw35115Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw35115 raw35115Labels = mixedMoment B raw35115step0 raw35115step0Labels := by
      have hz : ∀ j, raw35115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35115step0 = (fun i j => raw35115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35115step0 raw35115; decide +kernel
      have hl : raw35115step0Labels = raw35115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35115 raw35115Labels permutation434 hz
    mixedMoment B raw35115step0 raw35115step0Labels = mixedMoment B raw35115step1 raw35115step1Labels := by
      have hz : ∀ j, raw35115step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35115step1 = (fun i j => raw35115step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35115step1 raw35115step0; decide +kernel
      have hl : raw35115step1Labels = raw35115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35115step0 raw35115step0Labels permutation80 hz
    mixedMoment B raw35115step1 raw35115step1Labels = mixedMoment B raw35115step2 raw35115step2Labels := by
      have ha : raw35115step2 = (fun i j => raw35115step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35115step2 raw35115step1; decide +kernel
      have hl : raw35115step2Labels = raw35115step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35115step1 raw35115step1Labels permutation15 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw35116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35116step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35116step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35116step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35116step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35116 raw35116Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw35116 raw35116Labels = mixedMoment B raw35116step0 raw35116step0Labels := by
      have hz : ∀ j, raw35116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35116step0 = (fun i j => raw35116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35116step0 raw35116; decide +kernel
      have hl : raw35116step0Labels = raw35116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35116 raw35116Labels permutation434 hz
    mixedMoment B raw35116step0 raw35116step0Labels = mixedMoment B raw35116step1 raw35116step1Labels := by
      have ha : raw35116step1 = (fun i j => raw35116step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35116step1 raw35116step0; decide +kernel
      have hl : raw35116step1Labels = raw35116step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35116step0 raw35116step0Labels permutation57 permutation7
    mixedMoment B raw35116step1 raw35116step1Labels = mixedMoment B raw35116step2 raw35116step2Labels := by
      have ha : raw35116step2 = -raw35116step1 := by apply Matrix.ext; change ∀ i j, raw35116step2 i j = -(raw35116step1 i j); unfold raw35116step2 raw35116step1; decide +kernel
      have hl : raw35116step2Labels = raw35116step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35116step2 raw35116step2Labels = mixedMoment B raw35116step3 raw35116step3Labels := by
      have ha : raw35116step3 = raw35116step2 := by apply Matrix.ext; unfold raw35116step3 raw35116step2; decide +kernel
      have hl : raw35116step2Labels = labelEmbedding10 ∘ raw35116step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35116step2 raw35116step2Labels raw35116step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw35117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35117step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35117step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35117step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35117step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35117 raw35117Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw35117 raw35117Labels = mixedMoment B raw35117step0 raw35117step0Labels := by
      have hz : ∀ j, raw35117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35117step0 = (fun i j => raw35117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35117step0 raw35117; decide +kernel
      have hl : raw35117step0Labels = raw35117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35117 raw35117Labels permutation346 hz
    mixedMoment B raw35117step0 raw35117step0Labels = mixedMoment B raw35117step1 raw35117step1Labels := by
      have ha : raw35117step1 = (fun i j => raw35117step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35117step1 raw35117step0; decide +kernel
      have hl : raw35117step1Labels = raw35117step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35117step0 raw35117step0Labels permutation57 permutation7
    mixedMoment B raw35117step1 raw35117step1Labels = mixedMoment B raw35117step2 raw35117step2Labels := by
      have ha : raw35117step2 = -raw35117step1 := by apply Matrix.ext; change ∀ i j, raw35117step2 i j = -(raw35117step1 i j); unfold raw35117step2 raw35117step1; decide +kernel
      have hl : raw35117step2Labels = raw35117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35117step2 raw35117step2Labels = mixedMoment B raw35117step3 raw35117step3Labels := by
      have ha : raw35117step3 = raw35117step2 := by apply Matrix.ext; unfold raw35117step3 raw35117step2; decide +kernel
      have hl : raw35117step2Labels = labelEmbedding10 ∘ raw35117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35117step2 raw35117step2Labels raw35117step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw35118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35118step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35118step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35118step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35118step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35118step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35118 raw35118Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw35118 raw35118Labels = mixedMoment B raw35118step0 raw35118step0Labels := by
      have hz : ∀ j, raw35118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35118step0 = (fun i j => raw35118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35118step0 raw35118; decide +kernel
      have hl : raw35118step0Labels = raw35118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35118 raw35118Labels permutation434 hz
    mixedMoment B raw35118step0 raw35118step0Labels = mixedMoment B raw35118step1 raw35118step1Labels := by
      have hz : ∀ j, raw35118step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35118step1 = (fun i j => raw35118step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35118step1 raw35118step0; decide +kernel
      have hl : raw35118step1Labels = raw35118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35118step0 raw35118step0Labels permutation80 hz
    mixedMoment B raw35118step1 raw35118step1Labels = mixedMoment B raw35118step2 raw35118step2Labels := by
      have ha : raw35118step2 = (fun i j => raw35118step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35118step2 raw35118step1; decide +kernel
      have hl : raw35118step2Labels = raw35118step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35118step1 raw35118step1Labels permutation15 permutation7
    mixedMoment B raw35118step2 raw35118step2Labels = mixedMoment B raw35118step3 raw35118step3Labels := by
      have ha : raw35118step3 = -raw35118step2 := by apply Matrix.ext; change ∀ i j, raw35118step3 i j = -(raw35118step2 i j); unfold raw35118step3 raw35118step2; decide +kernel
      have hl : raw35118step3Labels = raw35118step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35118step3 raw35118step3Labels = mixedMoment B raw35118step4 raw35118step4Labels := by
      have ha : raw35118step4 = raw35118step3 := by apply Matrix.ext; unfold raw35118step4 raw35118step3; decide +kernel
      have hl : raw35118step3Labels = labelEmbedding10 ∘ raw35118step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35118step3 raw35118step3Labels raw35118step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw35119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35119step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35119step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35119step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35119step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35119step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35119 raw35119Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw35119 raw35119Labels = mixedMoment B raw35119step0 raw35119step0Labels := by
      have hz : ∀ j, raw35119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35119step0 = (fun i j => raw35119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35119step0 raw35119; decide +kernel
      have hl : raw35119step0Labels = raw35119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35119 raw35119Labels permutation434 hz
    mixedMoment B raw35119step0 raw35119step0Labels = mixedMoment B raw35119step1 raw35119step1Labels := by
      have hz : ∀ j, raw35119step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35119step1 = (fun i j => raw35119step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35119step1 raw35119step0; decide +kernel
      have hl : raw35119step1Labels = raw35119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35119step0 raw35119step0Labels permutation80 hz
    mixedMoment B raw35119step1 raw35119step1Labels = mixedMoment B raw35119step2 raw35119step2Labels := by
      have ha : raw35119step2 = (fun i j => raw35119step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35119step2 raw35119step1; decide +kernel
      have hl : raw35119step2Labels = raw35119step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35119step1 raw35119step1Labels permutation15 permutation7
    mixedMoment B raw35119step2 raw35119step2Labels = mixedMoment B raw35119step3 raw35119step3Labels := by
      have ha : raw35119step3 = -raw35119step2 := by apply Matrix.ext; change ∀ i j, raw35119step3 i j = -(raw35119step2 i j); unfold raw35119step3 raw35119step2; decide +kernel
      have hl : raw35119step3Labels = raw35119step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35119step3 raw35119step3Labels = mixedMoment B raw35119step4 raw35119step4Labels := by
      have ha : raw35119step4 = raw35119step3 := by apply Matrix.ext; unfold raw35119step4 raw35119step3; decide +kernel
      have hl : raw35119step3Labels = labelEmbedding10 ∘ raw35119step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35119step3 raw35119step3Labels raw35119step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw35120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35120step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35120step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35120 raw35120Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw35120 raw35120Labels = mixedMoment B raw35120step0 raw35120step0Labels := by
      have hz : ∀ j, raw35120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35120step0 = (fun i j => raw35120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35120step0 raw35120; decide +kernel
      have hl : raw35120step0Labels = raw35120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35120 raw35120Labels permutation434 hz
    mixedMoment B raw35120step0 raw35120step0Labels = mixedMoment B raw35120step1 raw35120step1Labels := by
      have hz : ∀ j, raw35120step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35120step1 = (fun i j => raw35120step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35120step1 raw35120step0; decide +kernel
      have hl : raw35120step1Labels = raw35120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35120step0 raw35120step0Labels permutation80 hz
    mixedMoment B raw35120step1 raw35120step1Labels = mixedMoment B raw35120step2 raw35120step2Labels := by
      have ha : raw35120step2 = (fun i j => raw35120step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35120step2 raw35120step1; decide +kernel
      have hl : raw35120step2Labels = raw35120step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35120step1 raw35120step1Labels permutation8 permutation3
    mixedMoment B raw35120step2 raw35120step2Labels = mixedMoment B raw35120step3 raw35120step3Labels := by
      have ha : raw35120step3 = raw35120step2 := by apply Matrix.ext; unfold raw35120step3 raw35120step2; decide +kernel
      have hl : raw35120step2Labels = labelEmbedding6 ∘ raw35120step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35120step2 raw35120step2Labels raw35120step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4884 node4884Labels := by rfl

def raw35121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35121step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35121step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35121step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35121step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35121 raw35121Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw35121 raw35121Labels = mixedMoment B raw35121step0 raw35121step0Labels := by
      have hz : ∀ j, raw35121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35121step0 = (fun i j => raw35121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35121step0 raw35121; decide +kernel
      have hl : raw35121step0Labels = raw35121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35121 raw35121Labels permutation434 hz
    mixedMoment B raw35121step0 raw35121step0Labels = mixedMoment B raw35121step1 raw35121step1Labels := by
      have ha : raw35121step1 = (fun i j => raw35121step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35121step1 raw35121step0; decide +kernel
      have hl : raw35121step1Labels = raw35121step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35121step0 raw35121step0Labels permutation63 permutation6
    mixedMoment B raw35121step1 raw35121step1Labels = mixedMoment B raw35121step2 raw35121step2Labels := by
      have ha : raw35121step2 = -raw35121step1 := by apply Matrix.ext; change ∀ i j, raw35121step2 i j = -(raw35121step1 i j); unfold raw35121step2 raw35121step1; decide +kernel
      have hl : raw35121step2Labels = raw35121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35121step2 raw35121step2Labels = mixedMoment B raw35121step3 raw35121step3Labels := by
      have ha : raw35121step3 = raw35121step2 := by apply Matrix.ext; unfold raw35121step3 raw35121step2; decide +kernel
      have hl : raw35121step2Labels = labelEmbedding9 ∘ raw35121step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35121step2 raw35121step2Labels raw35121step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw35122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35122step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35122step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35122step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35122step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35122 raw35122Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw35122 raw35122Labels = mixedMoment B raw35122step0 raw35122step0Labels := by
      have hz : ∀ j, raw35122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35122step0 = (fun i j => raw35122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35122step0 raw35122; decide +kernel
      have hl : raw35122step0Labels = raw35122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35122 raw35122Labels permutation346 hz
    mixedMoment B raw35122step0 raw35122step0Labels = mixedMoment B raw35122step1 raw35122step1Labels := by
      have ha : raw35122step1 = (fun i j => raw35122step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35122step1 raw35122step0; decide +kernel
      have hl : raw35122step1Labels = raw35122step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35122step0 raw35122step0Labels permutation63 permutation6
    mixedMoment B raw35122step1 raw35122step1Labels = mixedMoment B raw35122step2 raw35122step2Labels := by
      have ha : raw35122step2 = -raw35122step1 := by apply Matrix.ext; change ∀ i j, raw35122step2 i j = -(raw35122step1 i j); unfold raw35122step2 raw35122step1; decide +kernel
      have hl : raw35122step2Labels = raw35122step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35122step2 raw35122step2Labels = mixedMoment B raw35122step3 raw35122step3Labels := by
      have ha : raw35122step3 = raw35122step2 := by apply Matrix.ext; unfold raw35122step3 raw35122step2; decide +kernel
      have hl : raw35122step2Labels = labelEmbedding9 ∘ raw35122step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35122step2 raw35122step2Labels raw35122step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw35123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35123step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35123step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35123step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35123step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35123step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35123 raw35123Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw35123 raw35123Labels = mixedMoment B raw35123step0 raw35123step0Labels := by
      have hz : ∀ j, raw35123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35123step0 = (fun i j => raw35123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35123step0 raw35123; decide +kernel
      have hl : raw35123step0Labels = raw35123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35123 raw35123Labels permutation434 hz
    mixedMoment B raw35123step0 raw35123step0Labels = mixedMoment B raw35123step1 raw35123step1Labels := by
      have hz : ∀ j, raw35123step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35123step1 = (fun i j => raw35123step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35123step1 raw35123step0; decide +kernel
      have hl : raw35123step1Labels = raw35123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35123step0 raw35123step0Labels permutation80 hz
    mixedMoment B raw35123step1 raw35123step1Labels = mixedMoment B raw35123step2 raw35123step2Labels := by
      have ha : raw35123step2 = (fun i j => raw35123step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35123step2 raw35123step1; decide +kernel
      have hl : raw35123step2Labels = raw35123step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35123step1 raw35123step1Labels permutation15 permutation6
    mixedMoment B raw35123step2 raw35123step2Labels = mixedMoment B raw35123step3 raw35123step3Labels := by
      have ha : raw35123step3 = -raw35123step2 := by apply Matrix.ext; change ∀ i j, raw35123step3 i j = -(raw35123step2 i j); unfold raw35123step3 raw35123step2; decide +kernel
      have hl : raw35123step3Labels = raw35123step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35123step3 raw35123step3Labels = mixedMoment B raw35123step4 raw35123step4Labels := by
      have ha : raw35123step4 = raw35123step3 := by apply Matrix.ext; unfold raw35123step4 raw35123step3; decide +kernel
      have hl : raw35123step3Labels = labelEmbedding9 ∘ raw35123step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35123step3 raw35123step3Labels raw35123step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw35124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw35124step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35124step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw35124step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35124step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw35124step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35124 raw35124Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw35124 raw35124Labels = mixedMoment B raw35124step0 raw35124step0Labels := by
      have hz : ∀ j, raw35124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35124step0 = (fun i j => raw35124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35124step0 raw35124; decide +kernel
      have hl : raw35124step0Labels = raw35124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35124 raw35124Labels permutation434 hz
    mixedMoment B raw35124step0 raw35124step0Labels = mixedMoment B raw35124step1 raw35124step1Labels := by
      have hz : ∀ j, raw35124step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35124step1 = (fun i j => raw35124step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35124step1 raw35124step0; decide +kernel
      have hl : raw35124step1Labels = raw35124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35124step0 raw35124step0Labels permutation80 hz
    mixedMoment B raw35124step1 raw35124step1Labels = mixedMoment B raw35124step2 raw35124step2Labels := by
      have ha : raw35124step2 = (fun i j => raw35124step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35124step2 raw35124step1; decide +kernel
      have hl : raw35124step2Labels = raw35124step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35124step1 raw35124step1Labels permutation15 permutation6
    mixedMoment B raw35124step2 raw35124step2Labels = mixedMoment B raw35124step3 raw35124step3Labels := by
      have ha : raw35124step3 = -raw35124step2 := by apply Matrix.ext; change ∀ i j, raw35124step3 i j = -(raw35124step2 i j); unfold raw35124step3 raw35124step2; decide +kernel
      have hl : raw35124step3Labels = raw35124step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35124step3 raw35124step3Labels = mixedMoment B raw35124step4 raw35124step4Labels := by
      have ha : raw35124step4 = raw35124step3 := by apply Matrix.ext; unfold raw35124step4 raw35124step3; decide +kernel
      have hl : raw35124step3Labels = labelEmbedding9 ∘ raw35124step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35124step3 raw35124step3Labels raw35124step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw35125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35125step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35125 raw35125Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw35125 raw35125Labels = mixedMoment B raw35125step0 raw35125step0Labels := by
      have hz : ∀ j, raw35125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35125step0 = (fun i j => raw35125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35125step0 raw35125; decide +kernel
      have hl : raw35125step0Labels = raw35125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35125 raw35125Labels permutation434 hz
    mixedMoment B raw35125step0 raw35125step0Labels = mixedMoment B raw35125step1 raw35125step1Labels := by
      have ha : raw35125step1 = (fun i j => raw35125step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35125step1 raw35125step0; decide +kernel
      have hl : raw35125step1Labels = raw35125step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35125step0 raw35125step0Labels permutation32 permutation3
    mixedMoment B raw35125step1 raw35125step1Labels = mixedMoment B raw35125step2 raw35125step2Labels := by
      have ha : raw35125step2 = raw35125step1 := by apply Matrix.ext; unfold raw35125step2 raw35125step1; decide +kernel
      have hl : raw35125step1Labels = labelEmbedding6 ∘ raw35125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35125step1 raw35125step1Labels raw35125step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4703 node4703Labels := by rfl

def raw35126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35126 raw35126Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw35126 raw35126Labels = mixedMoment B raw35126step0 raw35126step0Labels := by
      have hz : ∀ j, raw35126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35126step0 = (fun i j => raw35126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35126step0 raw35126; decide +kernel
      have hl : raw35126step0Labels = raw35126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35126 raw35126Labels permutation434 hz
    mixedMoment B raw35126step0 raw35126step0Labels = mixedMoment B raw35126step1 raw35126step1Labels := by
      have ha : raw35126step1 = (fun i j => raw35126step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35126step1 raw35126step0; decide +kernel
      have hl : raw35126step1Labels = raw35126step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35126step0 raw35126step0Labels permutation57 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw35127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35127step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35127step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35127 raw35127Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw35127 raw35127Labels = mixedMoment B raw35127step0 raw35127step0Labels := by
      have ha : raw35127step0 = (fun i j => raw35127 (permutation272 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35127step0 raw35127; decide +kernel
      have hl : raw35127step0Labels = raw35127Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35127 raw35127Labels permutation272 permutation7
    mixedMoment B raw35127step0 raw35127step0Labels = mixedMoment B raw35127step1 raw35127step1Labels := by
      have ha : raw35127step1 = -raw35127step0 := by apply Matrix.ext; change ∀ i j, raw35127step1 i j = -(raw35127step0 i j); unfold raw35127step1 raw35127step0; decide +kernel
      have hl : raw35127step1Labels = raw35127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35127step1 raw35127step1Labels = mixedMoment B raw35127step2 raw35127step2Labels := by
      have ha : raw35127step2 = raw35127step1 := by apply Matrix.ext; unfold raw35127step2 raw35127step1; decide +kernel
      have hl : raw35127step1Labels = labelEmbedding10 ∘ raw35127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35127step1 raw35127step1Labels raw35127step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

def raw35128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35128step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35128step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35128 raw35128Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw35128 raw35128Labels = mixedMoment B raw35128step0 raw35128step0Labels := by
      have hz : ∀ j, raw35128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35128step0 = (fun i j => raw35128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35128step0 raw35128; decide +kernel
      have hl : raw35128step0Labels = raw35128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35128 raw35128Labels permutation434 hz
    mixedMoment B raw35128step0 raw35128step0Labels = mixedMoment B raw35128step1 raw35128step1Labels := by
      have ha : raw35128step1 = (fun i j => raw35128step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35128step1 raw35128step0; decide +kernel
      have hl : raw35128step1Labels = raw35128step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35128step0 raw35128step0Labels permutation57 permutation7
    mixedMoment B raw35128step1 raw35128step1Labels = mixedMoment B raw35128step2 raw35128step2Labels := by
      have ha : raw35128step2 = -raw35128step1 := by apply Matrix.ext; change ∀ i j, raw35128step2 i j = -(raw35128step1 i j); unfold raw35128step2 raw35128step1; decide +kernel
      have hl : raw35128step2Labels = raw35128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35128step2 raw35128step2Labels = mixedMoment B raw35128step3 raw35128step3Labels := by
      have ha : raw35128step3 = raw35128step2 := by apply Matrix.ext; unfold raw35128step3 raw35128step2; decide +kernel
      have hl : raw35128step2Labels = labelEmbedding10 ∘ raw35128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35128step2 raw35128step2Labels raw35128step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw35129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35129step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35129step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35129step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35129step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35129 raw35129Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35129 raw35129Labels = mixedMoment B raw35129step0 raw35129step0Labels := by
      have hz : ∀ j, raw35129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35129step0 = (fun i j => raw35129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35129step0 raw35129; decide +kernel
      have hl : raw35129step0Labels = raw35129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35129 raw35129Labels permutation434 hz
    mixedMoment B raw35129step0 raw35129step0Labels = mixedMoment B raw35129step1 raw35129step1Labels := by
      have ha : raw35129step1 = (fun i j => raw35129step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35129step1 raw35129step0; decide +kernel
      have hl : raw35129step1Labels = raw35129step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35129step0 raw35129step0Labels permutation57 permutation7
    mixedMoment B raw35129step1 raw35129step1Labels = mixedMoment B raw35129step2 raw35129step2Labels := by
      have ha : raw35129step2 = -raw35129step1 := by apply Matrix.ext; change ∀ i j, raw35129step2 i j = -(raw35129step1 i j); unfold raw35129step2 raw35129step1; decide +kernel
      have hl : raw35129step2Labels = raw35129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35129step2 raw35129step2Labels = mixedMoment B raw35129step3 raw35129step3Labels := by
      have ha : raw35129step3 = raw35129step2 := by apply Matrix.ext; unfold raw35129step3 raw35129step2; decide +kernel
      have hl : raw35129step2Labels = labelEmbedding10 ∘ raw35129step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35129step2 raw35129step2Labels raw35129step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw35130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35130step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35130 raw35130Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw35130 raw35130Labels = mixedMoment B raw35130step0 raw35130step0Labels := by
      have hz : ∀ j, raw35130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35130step0 = (fun i j => raw35130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35130step0 raw35130; decide +kernel
      have hl : raw35130step0Labels = raw35130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35130 raw35130Labels permutation346 hz
    mixedMoment B raw35130step0 raw35130step0Labels = mixedMoment B raw35130step1 raw35130step1Labels := by
      have ha : raw35130step1 = (fun i j => raw35130step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35130step1 raw35130step0; decide +kernel
      have hl : raw35130step1Labels = raw35130step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35130step0 raw35130step0Labels permutation32 permutation3
    mixedMoment B raw35130step1 raw35130step1Labels = mixedMoment B raw35130step2 raw35130step2Labels := by
      have ha : raw35130step2 = raw35130step1 := by apply Matrix.ext; unfold raw35130step2 raw35130step1; decide +kernel
      have hl : raw35130step1Labels = labelEmbedding6 ∘ raw35130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35130step1 raw35130step1Labels raw35130step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4703 node4703Labels := by rfl

def raw35131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35131 raw35131Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw35131 raw35131Labels = mixedMoment B raw35131step0 raw35131step0Labels := by
      have hz : ∀ j, raw35131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35131step0 = (fun i j => raw35131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35131step0 raw35131; decide +kernel
      have hl : raw35131step0Labels = raw35131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35131 raw35131Labels permutation346 hz
    mixedMoment B raw35131step0 raw35131step0Labels = mixedMoment B raw35131step1 raw35131step1Labels := by
      have ha : raw35131step1 = (fun i j => raw35131step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35131step1 raw35131step0; decide +kernel
      have hl : raw35131step1Labels = raw35131step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35131step0 raw35131step0Labels permutation57 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw35132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35132step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35132step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35132 raw35132Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw35132 raw35132Labels = mixedMoment B raw35132step0 raw35132step0Labels := by
      have ha : raw35132step0 = (fun i j => raw35132 (permutation266 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35132step0 raw35132; decide +kernel
      have hl : raw35132step0Labels = raw35132Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35132 raw35132Labels permutation266 permutation7
    mixedMoment B raw35132step0 raw35132step0Labels = mixedMoment B raw35132step1 raw35132step1Labels := by
      have ha : raw35132step1 = -raw35132step0 := by apply Matrix.ext; change ∀ i j, raw35132step1 i j = -(raw35132step0 i j); unfold raw35132step1 raw35132step0; decide +kernel
      have hl : raw35132step1Labels = raw35132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35132step1 raw35132step1Labels = mixedMoment B raw35132step2 raw35132step2Labels := by
      have ha : raw35132step2 = raw35132step1 := by apply Matrix.ext; unfold raw35132step2 raw35132step1; decide +kernel
      have hl : raw35132step1Labels = labelEmbedding10 ∘ raw35132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35132step1 raw35132step1Labels raw35132step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

def raw35133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35133step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35133step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35133step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35133 raw35133Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw35133 raw35133Labels = mixedMoment B raw35133step0 raw35133step0Labels := by
      have hz : ∀ j, raw35133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35133step0 = (fun i j => raw35133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35133step0 raw35133; decide +kernel
      have hl : raw35133step0Labels = raw35133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35133 raw35133Labels permutation346 hz
    mixedMoment B raw35133step0 raw35133step0Labels = mixedMoment B raw35133step1 raw35133step1Labels := by
      have ha : raw35133step1 = (fun i j => raw35133step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35133step1 raw35133step0; decide +kernel
      have hl : raw35133step1Labels = raw35133step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35133step0 raw35133step0Labels permutation57 permutation7
    mixedMoment B raw35133step1 raw35133step1Labels = mixedMoment B raw35133step2 raw35133step2Labels := by
      have ha : raw35133step2 = -raw35133step1 := by apply Matrix.ext; change ∀ i j, raw35133step2 i j = -(raw35133step1 i j); unfold raw35133step2 raw35133step1; decide +kernel
      have hl : raw35133step2Labels = raw35133step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35133step2 raw35133step2Labels = mixedMoment B raw35133step3 raw35133step3Labels := by
      have ha : raw35133step3 = raw35133step2 := by apply Matrix.ext; unfold raw35133step3 raw35133step2; decide +kernel
      have hl : raw35133step2Labels = labelEmbedding10 ∘ raw35133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35133step2 raw35133step2Labels raw35133step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw35134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35134step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35134step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35134step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35134step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35134 raw35134Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35134 raw35134Labels = mixedMoment B raw35134step0 raw35134step0Labels := by
      have hz : ∀ j, raw35134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35134step0 = (fun i j => raw35134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35134step0 raw35134; decide +kernel
      have hl : raw35134step0Labels = raw35134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35134 raw35134Labels permutation346 hz
    mixedMoment B raw35134step0 raw35134step0Labels = mixedMoment B raw35134step1 raw35134step1Labels := by
      have ha : raw35134step1 = (fun i j => raw35134step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35134step1 raw35134step0; decide +kernel
      have hl : raw35134step1Labels = raw35134step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35134step0 raw35134step0Labels permutation57 permutation7
    mixedMoment B raw35134step1 raw35134step1Labels = mixedMoment B raw35134step2 raw35134step2Labels := by
      have ha : raw35134step2 = -raw35134step1 := by apply Matrix.ext; change ∀ i j, raw35134step2 i j = -(raw35134step1 i j); unfold raw35134step2 raw35134step1; decide +kernel
      have hl : raw35134step2Labels = raw35134step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35134step2 raw35134step2Labels = mixedMoment B raw35134step3 raw35134step3Labels := by
      have ha : raw35134step3 = raw35134step2 := by apply Matrix.ext; unfold raw35134step3 raw35134step2; decide +kernel
      have hl : raw35134step2Labels = labelEmbedding10 ∘ raw35134step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35134step2 raw35134step2Labels raw35134step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw35135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw35135step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35135step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw35135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35135 raw35135Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw35135 raw35135Labels = mixedMoment B raw35135step0 raw35135step0Labels := by
      have hz : ∀ j, raw35135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35135step0 = (fun i j => raw35135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35135step0 raw35135; decide +kernel
      have hl : raw35135step0Labels = raw35135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35135 raw35135Labels permutation434 hz
    mixedMoment B raw35135step0 raw35135step0Labels = mixedMoment B raw35135step1 raw35135step1Labels := by
      have hz : ∀ j, raw35135step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35135step1 = (fun i j => raw35135step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35135step1 raw35135step0; decide +kernel
      have hl : raw35135step1Labels = raw35135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35135step0 raw35135step0Labels permutation80 hz
    mixedMoment B raw35135step1 raw35135step1Labels = mixedMoment B raw35135step2 raw35135step2Labels := by
      have ha : raw35135step2 = (fun i j => raw35135step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35135step2 raw35135step1; decide +kernel
      have hl : raw35135step2Labels = raw35135step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35135step1 raw35135step1Labels permutation9 permutation3
    mixedMoment B raw35135step2 raw35135step2Labels = mixedMoment B raw35135step3 raw35135step3Labels := by
      have ha : raw35135step3 = raw35135step2 := by apply Matrix.ext; unfold raw35135step3 raw35135step2; decide +kernel
      have hl : raw35135step2Labels = labelEmbedding6 ∘ raw35135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35135step2 raw35135step2Labels raw35135step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4705 node4705Labels := by rfl

def raw35136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35136step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw35136step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35136 raw35136Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw35136 raw35136Labels = mixedMoment B raw35136step0 raw35136step0Labels := by
      have hz : ∀ j, raw35136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35136step0 = (fun i j => raw35136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35136step0 raw35136; decide +kernel
      have hl : raw35136step0Labels = raw35136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35136 raw35136Labels permutation434 hz
    mixedMoment B raw35136step0 raw35136step0Labels = mixedMoment B raw35136step1 raw35136step1Labels := by
      have hz : ∀ j, raw35136step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35136step1 = (fun i j => raw35136step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35136step1 raw35136step0; decide +kernel
      have hl : raw35136step1Labels = raw35136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35136step0 raw35136step0Labels permutation80 hz
    mixedMoment B raw35136step1 raw35136step1Labels = mixedMoment B raw35136step2 raw35136step2Labels := by
      have ha : raw35136step2 = (fun i j => raw35136step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35136step2 raw35136step1; decide +kernel
      have hl : raw35136step2Labels = raw35136step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35136step1 raw35136step1Labels permutation15 permutation2
    _ = mixedMoment B node4692 node4692Labels := by rfl

def raw35137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw35137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35137step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35137 raw35137Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw35137 raw35137Labels = mixedMoment B raw35137step0 raw35137step0Labels := by
      have hz : ∀ j, raw35137 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35137step0 = (fun i j => raw35137 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35137step0 raw35137; decide +kernel
      have hl : raw35137step0Labels = raw35137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35137 raw35137Labels permutation434 hz
    mixedMoment B raw35137step0 raw35137step0Labels = mixedMoment B raw35137step1 raw35137step1Labels := by
      have ha : raw35137step1 = (fun i j => raw35137step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35137step1 raw35137step0; decide +kernel
      have hl : raw35137step1Labels = raw35137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35137step0 raw35137step0Labels permutation126 permutation2
    mixedMoment B raw35137step1 raw35137step1Labels = mixedMoment B raw35137step2 raw35137step2Labels := by
      have ha : raw35137step2 = -raw35137step1 := by apply Matrix.ext; change ∀ i j, raw35137step2 i j = -(raw35137step1 i j); unfold raw35137step2 raw35137step1; decide +kernel
      have hl : raw35137step2Labels = raw35137step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw35138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw35138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35138 raw35138Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw35138 raw35138Labels = mixedMoment B raw35138step0 raw35138step0Labels := by
      have hz : ∀ j, raw35138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35138step0 = (fun i j => raw35138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35138step0 raw35138; decide +kernel
      have hl : raw35138step0Labels = raw35138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35138 raw35138Labels permutation346 hz
    mixedMoment B raw35138step0 raw35138step0Labels = mixedMoment B raw35138step1 raw35138step1Labels := by
      have ha : raw35138step1 = (fun i j => raw35138step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35138step1 raw35138step0; decide +kernel
      have hl : raw35138step1Labels = raw35138step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35138step0 raw35138step0Labels permutation126 permutation2
    mixedMoment B raw35138step1 raw35138step1Labels = mixedMoment B raw35138step2 raw35138step2Labels := by
      have ha : raw35138step2 = -raw35138step1 := by apply Matrix.ext; change ∀ i j, raw35138step2 i j = -(raw35138step1 i j); unfold raw35138step2 raw35138step1; decide +kernel
      have hl : raw35138step2Labels = raw35138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw35139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw35139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35139step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw35139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35139 raw35139Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw35139 raw35139Labels = mixedMoment B raw35139step0 raw35139step0Labels := by
      have hz : ∀ j, raw35139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35139step0 = (fun i j => raw35139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35139step0 raw35139; decide +kernel
      have hl : raw35139step0Labels = raw35139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35139 raw35139Labels permutation434 hz
    mixedMoment B raw35139step0 raw35139step0Labels = mixedMoment B raw35139step1 raw35139step1Labels := by
      have hz : ∀ j, raw35139step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35139step1 = (fun i j => raw35139step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35139step1 raw35139step0; decide +kernel
      have hl : raw35139step1Labels = raw35139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35139step0 raw35139step0Labels permutation80 hz
    mixedMoment B raw35139step1 raw35139step1Labels = mixedMoment B raw35139step2 raw35139step2Labels := by
      have ha : raw35139step2 = (fun i j => raw35139step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35139step2 raw35139step1; decide +kernel
      have hl : raw35139step2Labels = raw35139step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35139step1 raw35139step1Labels permutation24 permutation2
    mixedMoment B raw35139step2 raw35139step2Labels = mixedMoment B raw35139step3 raw35139step3Labels := by
      have ha : raw35139step3 = -raw35139step2 := by apply Matrix.ext; change ∀ i j, raw35139step3 i j = -(raw35139step2 i j); unfold raw35139step3 raw35139step2; decide +kernel
      have hl : raw35139step3Labels = raw35139step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw35140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35140step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35140step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35140step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35140step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35140 raw35140Labels = mixedMoment B node4704 node4704Labels := by
  calc
    mixedMoment B raw35140 raw35140Labels = mixedMoment B raw35140step0 raw35140step0Labels := by
      have hz : ∀ j, raw35140 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35140step0 = (fun i j => raw35140 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35140step0 raw35140; decide +kernel
      have hl : raw35140step0Labels = raw35140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35140 raw35140Labels permutation434 hz
    mixedMoment B raw35140step0 raw35140step0Labels = mixedMoment B raw35140step1 raw35140step1Labels := by
      have hz : ∀ j, raw35140step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35140step1 = (fun i j => raw35140step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35140step1 raw35140step0; decide +kernel
      have hl : raw35140step1Labels = raw35140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35140step0 raw35140step0Labels permutation80 hz
    mixedMoment B raw35140step1 raw35140step1Labels = mixedMoment B raw35140step2 raw35140step2Labels := by
      have ha : raw35140step2 = (fun i j => raw35140step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35140step2 raw35140step1; decide +kernel
      have hl : raw35140step2Labels = raw35140step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35140step1 raw35140step1Labels permutation8 permutation3
    mixedMoment B raw35140step2 raw35140step2Labels = mixedMoment B raw35140step3 raw35140step3Labels := by
      have ha : raw35140step3 = raw35140step2 := by apply Matrix.ext; unfold raw35140step3 raw35140step2; decide +kernel
      have hl : raw35140step2Labels = labelEmbedding6 ∘ raw35140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35140step2 raw35140step2Labels raw35140step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4704 node4704Labels := by rfl

def raw35141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35141 raw35141Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw35141 raw35141Labels = mixedMoment B raw35141step0 raw35141step0Labels := by
      have hz : ∀ j, raw35141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35141step0 = (fun i j => raw35141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35141step0 raw35141; decide +kernel
      have hl : raw35141step0Labels = raw35141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35141 raw35141Labels permutation434 hz
    mixedMoment B raw35141step0 raw35141step0Labels = mixedMoment B raw35141step1 raw35141step1Labels := by
      have hz : ∀ j, raw35141step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35141step1 = (fun i j => raw35141step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35141step1 raw35141step0; decide +kernel
      have hl : raw35141step1Labels = raw35141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35141step0 raw35141step0Labels permutation80 hz
    mixedMoment B raw35141step1 raw35141step1Labels = mixedMoment B raw35141step2 raw35141step2Labels := by
      have ha : raw35141step2 = (fun i j => raw35141step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35141step2 raw35141step1; decide +kernel
      have hl : raw35141step2Labels = raw35141step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35141step1 raw35141step1Labels permutation14 permutation2
    _ = mixedMoment B node4693 node4693Labels := by rfl

def raw35142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35142step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35142step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35142 raw35142Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw35142 raw35142Labels = mixedMoment B raw35142step0 raw35142step0Labels := by
      have hz : ∀ j, raw35142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35142step0 = (fun i j => raw35142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35142step0 raw35142; decide +kernel
      have hl : raw35142step0Labels = raw35142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35142 raw35142Labels permutation434 hz
    mixedMoment B raw35142step0 raw35142step0Labels = mixedMoment B raw35142step1 raw35142step1Labels := by
      have ha : raw35142step1 = (fun i j => raw35142step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35142step1 raw35142step0; decide +kernel
      have hl : raw35142step1Labels = raw35142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35142step0 raw35142step0Labels permutation151 permutation3
    mixedMoment B raw35142step1 raw35142step1Labels = mixedMoment B raw35142step2 raw35142step2Labels := by
      have ha : raw35142step2 = -raw35142step1 := by apply Matrix.ext; change ∀ i j, raw35142step2 i j = -(raw35142step1 i j); unfold raw35142step2 raw35142step1; decide +kernel
      have hl : raw35142step2Labels = raw35142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35142step2 raw35142step2Labels = mixedMoment B raw35142step3 raw35142step3Labels := by
      have ha : raw35142step3 = raw35142step2 := by apply Matrix.ext; unfold raw35142step3 raw35142step2; decide +kernel
      have hl : raw35142step2Labels = labelEmbedding6 ∘ raw35142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35142step2 raw35142step2Labels raw35142step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4976 node4976Labels := by rfl

def raw35143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35143step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35143step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35143step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35143 raw35143Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw35143 raw35143Labels = mixedMoment B raw35143step0 raw35143step0Labels := by
      have hz : ∀ j, raw35143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35143step0 = (fun i j => raw35143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35143step0 raw35143; decide +kernel
      have hl : raw35143step0Labels = raw35143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35143 raw35143Labels permutation346 hz
    mixedMoment B raw35143step0 raw35143step0Labels = mixedMoment B raw35143step1 raw35143step1Labels := by
      have ha : raw35143step1 = (fun i j => raw35143step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35143step1 raw35143step0; decide +kernel
      have hl : raw35143step1Labels = raw35143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35143step0 raw35143step0Labels permutation151 permutation3
    mixedMoment B raw35143step1 raw35143step1Labels = mixedMoment B raw35143step2 raw35143step2Labels := by
      have ha : raw35143step2 = -raw35143step1 := by apply Matrix.ext; change ∀ i j, raw35143step2 i j = -(raw35143step1 i j); unfold raw35143step2 raw35143step1; decide +kernel
      have hl : raw35143step2Labels = raw35143step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35143step2 raw35143step2Labels = mixedMoment B raw35143step3 raw35143step3Labels := by
      have ha : raw35143step3 = raw35143step2 := by apply Matrix.ext; unfold raw35143step3 raw35143step2; decide +kernel
      have hl : raw35143step2Labels = labelEmbedding6 ∘ raw35143step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35143step2 raw35143step2Labels raw35143step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4976 node4976Labels := by rfl

def raw35144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw35144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35144step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35144step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35144step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35144step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35144step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35144step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35144 raw35144Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw35144 raw35144Labels = mixedMoment B raw35144step0 raw35144step0Labels := by
      have hz : ∀ j, raw35144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35144step0 = (fun i j => raw35144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35144step0 raw35144; decide +kernel
      have hl : raw35144step0Labels = raw35144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35144 raw35144Labels permutation434 hz
    mixedMoment B raw35144step0 raw35144step0Labels = mixedMoment B raw35144step1 raw35144step1Labels := by
      have hz : ∀ j, raw35144step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35144step1 = (fun i j => raw35144step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35144step1 raw35144step0; decide +kernel
      have hl : raw35144step1Labels = raw35144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35144step0 raw35144step0Labels permutation80 hz
    mixedMoment B raw35144step1 raw35144step1Labels = mixedMoment B raw35144step2 raw35144step2Labels := by
      have ha : raw35144step2 = (fun i j => raw35144step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35144step2 raw35144step1; decide +kernel
      have hl : raw35144step2Labels = raw35144step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35144step1 raw35144step1Labels permutation31 permutation3
    mixedMoment B raw35144step2 raw35144step2Labels = mixedMoment B raw35144step3 raw35144step3Labels := by
      have ha : raw35144step3 = -raw35144step2 := by apply Matrix.ext; change ∀ i j, raw35144step3 i j = -(raw35144step2 i j); unfold raw35144step3 raw35144step2; decide +kernel
      have hl : raw35144step3Labels = raw35144step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35144step3 raw35144step3Labels = mixedMoment B raw35144step4 raw35144step4Labels := by
      have ha : raw35144step4 = raw35144step3 := by apply Matrix.ext; unfold raw35144step4 raw35144step3; decide +kernel
      have hl : raw35144step3Labels = labelEmbedding6 ∘ raw35144step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35144step3 raw35144step3Labels raw35144step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw35145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35145step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35145step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw35145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35145 raw35145Labels = mixedMoment B node3216 node3216Labels := by
  calc
    mixedMoment B raw35145 raw35145Labels = mixedMoment B raw35145step0 raw35145step0Labels := by
      have hz : ∀ j, raw35145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35145step0 = (fun i j => raw35145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35145step0 raw35145; decide +kernel
      have hl : raw35145step0Labels = raw35145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35145 raw35145Labels permutation434 hz
    mixedMoment B raw35145step0 raw35145step0Labels = mixedMoment B raw35145step1 raw35145step1Labels := by
      have hz : ∀ j, raw35145step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35145step1 = (fun i j => raw35145step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35145step1 raw35145step0; decide +kernel
      have hl : raw35145step1Labels = raw35145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35145step0 raw35145step0Labels permutation80 hz
    mixedMoment B raw35145step1 raw35145step1Labels = mixedMoment B raw35145step2 raw35145step2Labels := by
      have ha : raw35145step2 = (fun i j => raw35145step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35145step2 raw35145step1; decide +kernel
      have hl : raw35145step2Labels = raw35145step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35145step1 raw35145step1Labels permutation14 permutation3
    _ = mixedMoment B node3216 node3216Labels := by rfl

def raw35146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35146step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw35146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw35146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35146 raw35146Labels = mixedMoment B node3106 node3106Labels := by
  calc
    mixedMoment B raw35146 raw35146Labels = mixedMoment B raw35146step0 raw35146step0Labels := by
      have hz : ∀ j, raw35146 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35146step0 = (fun i j => raw35146 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35146step0 raw35146; decide +kernel
      have hl : raw35146step0Labels = raw35146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35146 raw35146Labels permutation434 hz
    mixedMoment B raw35146step0 raw35146step0Labels = mixedMoment B raw35146step1 raw35146step1Labels := by
      have ha : raw35146step1 = (fun i j => raw35146step0 (permutation57 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35146step1 raw35146step0; decide +kernel
      have hl : raw35146step1Labels = raw35146step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35146step0 raw35146step0Labels permutation57 permutation6
    mixedMoment B raw35146step1 raw35146step1Labels = mixedMoment B raw35146step2 raw35146step2Labels := by
      have ha : raw35146step2 = -raw35146step1 := by apply Matrix.ext; change ∀ i j, raw35146step2 i j = -(raw35146step1 i j); unfold raw35146step2 raw35146step1; decide +kernel
      have hl : raw35146step2Labels = raw35146step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3106 node3106Labels := by rfl

def raw35147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35147step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw35147step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw35147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35147 raw35147Labels = mixedMoment B node3106 node3106Labels := by
  calc
    mixedMoment B raw35147 raw35147Labels = mixedMoment B raw35147step0 raw35147step0Labels := by
      have hz : ∀ j, raw35147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35147step0 = (fun i j => raw35147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35147step0 raw35147; decide +kernel
      have hl : raw35147step0Labels = raw35147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35147 raw35147Labels permutation346 hz
    mixedMoment B raw35147step0 raw35147step0Labels = mixedMoment B raw35147step1 raw35147step1Labels := by
      have ha : raw35147step1 = (fun i j => raw35147step0 (permutation57 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35147step1 raw35147step0; decide +kernel
      have hl : raw35147step1Labels = raw35147step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35147step0 raw35147step0Labels permutation57 permutation6
    mixedMoment B raw35147step1 raw35147step1Labels = mixedMoment B raw35147step2 raw35147step2Labels := by
      have ha : raw35147step2 = -raw35147step1 := by apply Matrix.ext; change ∀ i j, raw35147step2 i j = -(raw35147step1 i j); unfold raw35147step2 raw35147step1; decide +kernel
      have hl : raw35147step2Labels = raw35147step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3106 node3106Labels := by rfl

def raw35148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35148step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35148step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw35148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35148step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35148step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35148 raw35148Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw35148 raw35148Labels = mixedMoment B raw35148step0 raw35148step0Labels := by
      have hz : ∀ j, raw35148 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35148step0 = (fun i j => raw35148 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35148step0 raw35148; decide +kernel
      have hl : raw35148step0Labels = raw35148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35148 raw35148Labels permutation434 hz
    mixedMoment B raw35148step0 raw35148step0Labels = mixedMoment B raw35148step1 raw35148step1Labels := by
      have hz : ∀ j, raw35148step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35148step1 = (fun i j => raw35148step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35148step1 raw35148step0; decide +kernel
      have hl : raw35148step1Labels = raw35148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35148step0 raw35148step0Labels permutation80 hz
    mixedMoment B raw35148step1 raw35148step1Labels = mixedMoment B raw35148step2 raw35148step2Labels := by
      have ha : raw35148step2 = (fun i j => raw35148step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35148step2 raw35148step1; decide +kernel
      have hl : raw35148step2Labels = raw35148step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35148step1 raw35148step1Labels permutation15 permutation6
    mixedMoment B raw35148step2 raw35148step2Labels = mixedMoment B raw35148step3 raw35148step3Labels := by
      have ha : raw35148step3 = -raw35148step2 := by apply Matrix.ext; change ∀ i j, raw35148step3 i j = -(raw35148step2 i j); unfold raw35148step3 raw35148step2; decide +kernel
      have hl : raw35148step3Labels = raw35148step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw35149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35149step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35149step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw35149step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35149step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw35149step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35149 raw35149Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw35149 raw35149Labels = mixedMoment B raw35149step0 raw35149step0Labels := by
      have hz : ∀ j, raw35149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35149step0 = (fun i j => raw35149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35149step0 raw35149; decide +kernel
      have hl : raw35149step0Labels = raw35149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35149 raw35149Labels permutation434 hz
    mixedMoment B raw35149step0 raw35149step0Labels = mixedMoment B raw35149step1 raw35149step1Labels := by
      have hz : ∀ j, raw35149step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35149step1 = (fun i j => raw35149step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35149step1 raw35149step0; decide +kernel
      have hl : raw35149step1Labels = raw35149step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35149step0 raw35149step0Labels permutation80 hz
    mixedMoment B raw35149step1 raw35149step1Labels = mixedMoment B raw35149step2 raw35149step2Labels := by
      have ha : raw35149step2 = (fun i j => raw35149step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35149step2 raw35149step1; decide +kernel
      have hl : raw35149step2Labels = raw35149step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35149step1 raw35149step1Labels permutation15 permutation6
    mixedMoment B raw35149step2 raw35149step2Labels = mixedMoment B raw35149step3 raw35149step3Labels := by
      have ha : raw35149step3 = -raw35149step2 := by apply Matrix.ext; change ∀ i j, raw35149step3 i j = -(raw35149step2 i j); unfold raw35149step3 raw35149step2; decide +kernel
      have hl : raw35149step3Labels = raw35149step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw35150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35150step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35150step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35150step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35150 raw35150Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw35150 raw35150Labels = mixedMoment B raw35150step0 raw35150step0Labels := by
      have hz : ∀ j, raw35150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35150step0 = (fun i j => raw35150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35150step0 raw35150; decide +kernel
      have hl : raw35150step0Labels = raw35150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35150 raw35150Labels permutation434 hz
    mixedMoment B raw35150step0 raw35150step0Labels = mixedMoment B raw35150step1 raw35150step1Labels := by
      have hz : ∀ j, raw35150step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35150step1 = (fun i j => raw35150step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35150step1 raw35150step0; decide +kernel
      have hl : raw35150step1Labels = raw35150step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35150step0 raw35150step0Labels permutation80 hz
    mixedMoment B raw35150step1 raw35150step1Labels = mixedMoment B raw35150step2 raw35150step2Labels := by
      have ha : raw35150step2 = (fun i j => raw35150step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35150step2 raw35150step1; decide +kernel
      have hl : raw35150step2Labels = raw35150step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35150step1 raw35150step1Labels permutation8 permutation3
    _ = mixedMoment B node2138 node2138Labels := by rfl

def raw35151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35151step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35151 raw35151Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw35151 raw35151Labels = mixedMoment B raw35151step0 raw35151step0Labels := by
      have hz : ∀ j, raw35151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35151step0 = (fun i j => raw35151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35151step0 raw35151; decide +kernel
      have hl : raw35151step0Labels = raw35151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35151 raw35151Labels permutation434 hz
    mixedMoment B raw35151step0 raw35151step0Labels = mixedMoment B raw35151step1 raw35151step1Labels := by
      have ha : raw35151step1 = (fun i j => raw35151step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35151step1 raw35151step0; decide +kernel
      have hl : raw35151step1Labels = raw35151step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35151step0 raw35151step0Labels permutation63 permutation6
    mixedMoment B raw35151step1 raw35151step1Labels = mixedMoment B raw35151step2 raw35151step2Labels := by
      have ha : raw35151step2 = -raw35151step1 := by apply Matrix.ext; change ∀ i j, raw35151step2 i j = -(raw35151step1 i j); unfold raw35151step2 raw35151step1; decide +kernel
      have hl : raw35151step2Labels = raw35151step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2758 node2758Labels := by rfl

def raw35152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35152step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35152 raw35152Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw35152 raw35152Labels = mixedMoment B raw35152step0 raw35152step0Labels := by
      have hz : ∀ j, raw35152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35152step0 = (fun i j => raw35152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35152step0 raw35152; decide +kernel
      have hl : raw35152step0Labels = raw35152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35152 raw35152Labels permutation346 hz
    mixedMoment B raw35152step0 raw35152step0Labels = mixedMoment B raw35152step1 raw35152step1Labels := by
      have ha : raw35152step1 = (fun i j => raw35152step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35152step1 raw35152step0; decide +kernel
      have hl : raw35152step1Labels = raw35152step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35152step0 raw35152step0Labels permutation63 permutation6
    mixedMoment B raw35152step1 raw35152step1Labels = mixedMoment B raw35152step2 raw35152step2Labels := by
      have ha : raw35152step2 = -raw35152step1 := by apply Matrix.ext; change ∀ i j, raw35152step2 i j = -(raw35152step1 i j); unfold raw35152step2 raw35152step1; decide +kernel
      have hl : raw35152step2Labels = raw35152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2758 node2758Labels := by rfl

def raw35153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35153step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35153step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35153step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35153step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35153step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35153 raw35153Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw35153 raw35153Labels = mixedMoment B raw35153step0 raw35153step0Labels := by
      have hz : ∀ j, raw35153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35153step0 = (fun i j => raw35153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35153step0 raw35153; decide +kernel
      have hl : raw35153step0Labels = raw35153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35153 raw35153Labels permutation434 hz
    mixedMoment B raw35153step0 raw35153step0Labels = mixedMoment B raw35153step1 raw35153step1Labels := by
      have hz : ∀ j, raw35153step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35153step1 = (fun i j => raw35153step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35153step1 raw35153step0; decide +kernel
      have hl : raw35153step1Labels = raw35153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35153step0 raw35153step0Labels permutation80 hz
    mixedMoment B raw35153step1 raw35153step1Labels = mixedMoment B raw35153step2 raw35153step2Labels := by
      have ha : raw35153step2 = (fun i j => raw35153step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35153step2 raw35153step1; decide +kernel
      have hl : raw35153step2Labels = raw35153step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35153step1 raw35153step1Labels permutation15 permutation6
    mixedMoment B raw35153step2 raw35153step2Labels = mixedMoment B raw35153step3 raw35153step3Labels := by
      have ha : raw35153step3 = -raw35153step2 := by apply Matrix.ext; change ∀ i j, raw35153step3 i j = -(raw35153step2 i j); unfold raw35153step3 raw35153step2; decide +kernel
      have hl : raw35153step3Labels = raw35153step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw35154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35154step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35154step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw35154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35154step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw35154step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35154 raw35154Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw35154 raw35154Labels = mixedMoment B raw35154step0 raw35154step0Labels := by
      have hz : ∀ j, raw35154 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35154step0 = (fun i j => raw35154 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35154step0 raw35154; decide +kernel
      have hl : raw35154step0Labels = raw35154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35154 raw35154Labels permutation434 hz
    mixedMoment B raw35154step0 raw35154step0Labels = mixedMoment B raw35154step1 raw35154step1Labels := by
      have hz : ∀ j, raw35154step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35154step1 = (fun i j => raw35154step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35154step1 raw35154step0; decide +kernel
      have hl : raw35154step1Labels = raw35154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35154step0 raw35154step0Labels permutation80 hz
    mixedMoment B raw35154step1 raw35154step1Labels = mixedMoment B raw35154step2 raw35154step2Labels := by
      have ha : raw35154step2 = (fun i j => raw35154step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35154step2 raw35154step1; decide +kernel
      have hl : raw35154step2Labels = raw35154step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35154step1 raw35154step1Labels permutation15 permutation6
    mixedMoment B raw35154step2 raw35154step2Labels = mixedMoment B raw35154step3 raw35154step3Labels := by
      have ha : raw35154step3 = -raw35154step2 := by apply Matrix.ext; change ∀ i j, raw35154step3 i j = -(raw35154step2 i j); unfold raw35154step3 raw35154step2; decide +kernel
      have hl : raw35154step3Labels = raw35154step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw35155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35155step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35155step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35155 raw35155Labels = mixedMoment B node1829 node1829Labels := by
  calc
    mixedMoment B raw35155 raw35155Labels = mixedMoment B raw35155step0 raw35155step0Labels := by
      have hz : ∀ j, raw35155 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35155step0 = (fun i j => raw35155 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35155step0 raw35155; decide +kernel
      have hl : raw35155step0Labels = raw35155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35155 raw35155Labels permutation434 hz
    mixedMoment B raw35155step0 raw35155step0Labels = mixedMoment B raw35155step1 raw35155step1Labels := by
      have ha : raw35155step1 = (fun i j => raw35155step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35155step1 raw35155step0; decide +kernel
      have hl : raw35155step1Labels = raw35155step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35155step0 raw35155step0Labels permutation32 permutation3
    _ = mixedMoment B node1829 node1829Labels := by rfl

def raw35156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35156 raw35156Labels = mixedMoment B node3144 node3144Labels := by
  calc
    mixedMoment B raw35156 raw35156Labels = mixedMoment B raw35156step0 raw35156step0Labels := by
      have hz : ∀ j, raw35156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35156step0 = (fun i j => raw35156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35156step0 raw35156; decide +kernel
      have hl : raw35156step0Labels = raw35156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35156 raw35156Labels permutation434 hz
    mixedMoment B raw35156step0 raw35156step0Labels = mixedMoment B raw35156step1 raw35156step1Labels := by
      have ha : raw35156step1 = (fun i j => raw35156step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35156step1 raw35156step0; decide +kernel
      have hl : raw35156step1Labels = raw35156step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35156step0 raw35156step0Labels permutation56 permutation3
    _ = mixedMoment B node3144 node3144Labels := by rfl

def raw35157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35157 raw35157Labels = mixedMoment B node3083 node3083Labels := by
  calc
    mixedMoment B raw35157 raw35157Labels = mixedMoment B raw35157step0 raw35157step0Labels := by
      have ha : raw35157step0 = (fun i j => raw35157 (permutation296 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35157step0 raw35157; decide +kernel
      have hl : raw35157step0Labels = raw35157Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35157 raw35157Labels permutation296 permutation6
    mixedMoment B raw35157step0 raw35157step0Labels = mixedMoment B raw35157step1 raw35157step1Labels := by
      have ha : raw35157step1 = -raw35157step0 := by apply Matrix.ext; change ∀ i j, raw35157step1 i j = -(raw35157step0 i j); unfold raw35157step1 raw35157step0; decide +kernel
      have hl : raw35157step1Labels = raw35157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3083 node3083Labels := by rfl

def raw35158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35158 raw35158Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw35158 raw35158Labels = mixedMoment B raw35158step0 raw35158step0Labels := by
      have hz : ∀ j, raw35158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35158step0 = (fun i j => raw35158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35158step0 raw35158; decide +kernel
      have hl : raw35158step0Labels = raw35158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35158 raw35158Labels permutation434 hz
    mixedMoment B raw35158step0 raw35158step0Labels = mixedMoment B raw35158step1 raw35158step1Labels := by
      have ha : raw35158step1 = (fun i j => raw35158step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35158step1 raw35158step0; decide +kernel
      have hl : raw35158step1Labels = raw35158step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35158step0 raw35158step0Labels permutation63 permutation6
    mixedMoment B raw35158step1 raw35158step1Labels = mixedMoment B raw35158step2 raw35158step2Labels := by
      have ha : raw35158step2 = -raw35158step1 := by apply Matrix.ext; change ∀ i j, raw35158step2 i j = -(raw35158step1 i j); unfold raw35158step2 raw35158step1; decide +kernel
      have hl : raw35158step2Labels = raw35158step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw35159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw35159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw35159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35159 raw35159Labels = mixedMoment B node3094 node3094Labels := by
  calc
    mixedMoment B raw35159 raw35159Labels = mixedMoment B raw35159step0 raw35159step0Labels := by
      have hz : ∀ j, raw35159 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35159step0 = (fun i j => raw35159 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35159step0 raw35159; decide +kernel
      have hl : raw35159step0Labels = raw35159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35159 raw35159Labels permutation434 hz
    mixedMoment B raw35159step0 raw35159step0Labels = mixedMoment B raw35159step1 raw35159step1Labels := by
      have ha : raw35159step1 = (fun i j => raw35159step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35159step1 raw35159step0; decide +kernel
      have hl : raw35159step1Labels = raw35159step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35159step0 raw35159step0Labels permutation63 permutation6
    mixedMoment B raw35159step1 raw35159step1Labels = mixedMoment B raw35159step2 raw35159step2Labels := by
      have ha : raw35159step2 = -raw35159step1 := by apply Matrix.ext; change ∀ i j, raw35159step2 i j = -(raw35159step1 i j); unfold raw35159step2 raw35159step1; decide +kernel
      have hl : raw35159step2Labels = raw35159step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3094 node3094Labels := by rfl

def raw35160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35160 raw35160Labels = mixedMoment B node1829 node1829Labels := by
  calc
    mixedMoment B raw35160 raw35160Labels = mixedMoment B raw35160step0 raw35160step0Labels := by
      have hz : ∀ j, raw35160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35160step0 = (fun i j => raw35160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35160step0 raw35160; decide +kernel
      have hl : raw35160step0Labels = raw35160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35160 raw35160Labels permutation346 hz
    mixedMoment B raw35160step0 raw35160step0Labels = mixedMoment B raw35160step1 raw35160step1Labels := by
      have ha : raw35160step1 = (fun i j => raw35160step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35160step1 raw35160step0; decide +kernel
      have hl : raw35160step1Labels = raw35160step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35160step0 raw35160step0Labels permutation32 permutation3
    _ = mixedMoment B node1829 node1829Labels := by rfl

def raw35161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35161 raw35161Labels = mixedMoment B node3144 node3144Labels := by
  calc
    mixedMoment B raw35161 raw35161Labels = mixedMoment B raw35161step0 raw35161step0Labels := by
      have hz : ∀ j, raw35161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35161step0 = (fun i j => raw35161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35161step0 raw35161; decide +kernel
      have hl : raw35161step0Labels = raw35161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35161 raw35161Labels permutation346 hz
    mixedMoment B raw35161step0 raw35161step0Labels = mixedMoment B raw35161step1 raw35161step1Labels := by
      have ha : raw35161step1 = (fun i j => raw35161step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35161step1 raw35161step0; decide +kernel
      have hl : raw35161step1Labels = raw35161step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35161step0 raw35161step0Labels permutation56 permutation3
    _ = mixedMoment B node3144 node3144Labels := by rfl

def raw35162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw35162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35162 raw35162Labels = mixedMoment B node3083 node3083Labels := by
  calc
    mixedMoment B raw35162 raw35162Labels = mixedMoment B raw35162step0 raw35162step0Labels := by
      have ha : raw35162step0 = (fun i j => raw35162 (permutation311 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35162step0 raw35162; decide +kernel
      have hl : raw35162step0Labels = raw35162Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35162 raw35162Labels permutation311 permutation6
    mixedMoment B raw35162step0 raw35162step0Labels = mixedMoment B raw35162step1 raw35162step1Labels := by
      have ha : raw35162step1 = -raw35162step0 := by apply Matrix.ext; change ∀ i j, raw35162step1 i j = -(raw35162step0 i j); unfold raw35162step1 raw35162step0; decide +kernel
      have hl : raw35162step1Labels = raw35162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3083 node3083Labels := by rfl

def raw35163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35163 raw35163Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw35163 raw35163Labels = mixedMoment B raw35163step0 raw35163step0Labels := by
      have hz : ∀ j, raw35163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35163step0 = (fun i j => raw35163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35163step0 raw35163; decide +kernel
      have hl : raw35163step0Labels = raw35163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35163 raw35163Labels permutation346 hz
    mixedMoment B raw35163step0 raw35163step0Labels = mixedMoment B raw35163step1 raw35163step1Labels := by
      have ha : raw35163step1 = (fun i j => raw35163step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35163step1 raw35163step0; decide +kernel
      have hl : raw35163step1Labels = raw35163step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35163step0 raw35163step0Labels permutation63 permutation6
    mixedMoment B raw35163step1 raw35163step1Labels = mixedMoment B raw35163step2 raw35163step2Labels := by
      have ha : raw35163step2 = -raw35163step1 := by apply Matrix.ext; change ∀ i j, raw35163step2 i j = -(raw35163step1 i j); unfold raw35163step2 raw35163step1; decide +kernel
      have hl : raw35163step2Labels = raw35163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw35164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw35164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw35164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35164 raw35164Labels = mixedMoment B node3094 node3094Labels := by
  calc
    mixedMoment B raw35164 raw35164Labels = mixedMoment B raw35164step0 raw35164step0Labels := by
      have hz : ∀ j, raw35164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35164step0 = (fun i j => raw35164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35164step0 raw35164; decide +kernel
      have hl : raw35164step0Labels = raw35164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35164 raw35164Labels permutation346 hz
    mixedMoment B raw35164step0 raw35164step0Labels = mixedMoment B raw35164step1 raw35164step1Labels := by
      have ha : raw35164step1 = (fun i j => raw35164step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35164step1 raw35164step0; decide +kernel
      have hl : raw35164step1Labels = raw35164step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35164step0 raw35164step0Labels permutation63 permutation6
    mixedMoment B raw35164step1 raw35164step1Labels = mixedMoment B raw35164step2 raw35164step2Labels := by
      have ha : raw35164step2 = -raw35164step1 := by apply Matrix.ext; change ∀ i j, raw35164step2 i j = -(raw35164step1 i j); unfold raw35164step2 raw35164step1; decide +kernel
      have hl : raw35164step2Labels = raw35164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3094 node3094Labels := by rfl

def raw35165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35165step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw35165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35165 raw35165Labels = mixedMoment B node1831 node1831Labels := by
  calc
    mixedMoment B raw35165 raw35165Labels = mixedMoment B raw35165step0 raw35165step0Labels := by
      have hz : ∀ j, raw35165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35165step0 = (fun i j => raw35165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35165step0 raw35165; decide +kernel
      have hl : raw35165step0Labels = raw35165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35165 raw35165Labels permutation434 hz
    mixedMoment B raw35165step0 raw35165step0Labels = mixedMoment B raw35165step1 raw35165step1Labels := by
      have hz : ∀ j, raw35165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35165step1 = (fun i j => raw35165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35165step1 raw35165step0; decide +kernel
      have hl : raw35165step1Labels = raw35165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35165step0 raw35165step0Labels permutation80 hz
    mixedMoment B raw35165step1 raw35165step1Labels = mixedMoment B raw35165step2 raw35165step2Labels := by
      have ha : raw35165step2 = (fun i j => raw35165step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35165step2 raw35165step1; decide +kernel
      have hl : raw35165step2Labels = raw35165step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35165step1 raw35165step1Labels permutation9 permutation3
    _ = mixedMoment B node1831 node1831Labels := by rfl

def raw35166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-2, 0, 2], ![-3, 3, 0]]
def raw35166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw35166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35166 raw35166Labels = mixedMoment B node2832 node2832Labels := by
  calc
    mixedMoment B raw35166 raw35166Labels = mixedMoment B raw35166step0 raw35166step0Labels := by
      have hz : ∀ j, raw35166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35166step0 = (fun i j => raw35166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35166step0 raw35166; decide +kernel
      have hl : raw35166step0Labels = raw35166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35166 raw35166Labels permutation434 hz
    mixedMoment B raw35166step0 raw35166step0Labels = mixedMoment B raw35166step1 raw35166step1Labels := by
      have hz : ∀ j, raw35166step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35166step1 = (fun i j => raw35166step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35166step1 raw35166step0; decide +kernel
      have hl : raw35166step1Labels = raw35166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35166step0 raw35166step0Labels permutation80 hz
    mixedMoment B raw35166step1 raw35166step1Labels = mixedMoment B raw35166step2 raw35166step2Labels := by
      have ha : raw35166step2 = (fun i j => raw35166step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35166step2 raw35166step1; decide +kernel
      have hl : raw35166step2Labels = raw35166step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35166step1 raw35166step1Labels permutation24 permutation3
    mixedMoment B raw35166step2 raw35166step2Labels = mixedMoment B raw35166step3 raw35166step3Labels := by
      have ha : raw35166step3 = -raw35166step2 := by apply Matrix.ext; change ∀ i j, raw35166step3 i j = -(raw35166step2 i j); unfold raw35166step3 raw35166step2; decide +kernel
      have hl : raw35166step3Labels = raw35166step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2832 node2832Labels := by rfl

def raw35167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35167 raw35167Labels = mixedMoment B node2831 node2831Labels := by
  calc
    mixedMoment B raw35167 raw35167Labels = mixedMoment B raw35167step0 raw35167step0Labels := by
      have hz : ∀ j, raw35167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35167step0 = (fun i j => raw35167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35167step0 raw35167; decide +kernel
      have hl : raw35167step0Labels = raw35167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35167 raw35167Labels permutation434 hz
    mixedMoment B raw35167step0 raw35167step0Labels = mixedMoment B raw35167step1 raw35167step1Labels := by
      have ha : raw35167step1 = (fun i j => raw35167step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35167step1 raw35167step0; decide +kernel
      have hl : raw35167step1Labels = raw35167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35167step0 raw35167step0Labels permutation127 permutation3
    mixedMoment B raw35167step1 raw35167step1Labels = mixedMoment B raw35167step2 raw35167step2Labels := by
      have ha : raw35167step2 = -raw35167step1 := by apply Matrix.ext; change ∀ i j, raw35167step2 i j = -(raw35167step1 i j); unfold raw35167step2 raw35167step1; decide +kernel
      have hl : raw35167step2Labels = raw35167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2831 node2831Labels := by rfl

def raw35168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35168 raw35168Labels = mixedMoment B node2831 node2831Labels := by
  calc
    mixedMoment B raw35168 raw35168Labels = mixedMoment B raw35168step0 raw35168step0Labels := by
      have hz : ∀ j, raw35168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35168step0 = (fun i j => raw35168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35168step0 raw35168; decide +kernel
      have hl : raw35168step0Labels = raw35168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35168 raw35168Labels permutation346 hz
    mixedMoment B raw35168step0 raw35168step0Labels = mixedMoment B raw35168step1 raw35168step1Labels := by
      have ha : raw35168step1 = (fun i j => raw35168step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35168step1 raw35168step0; decide +kernel
      have hl : raw35168step1Labels = raw35168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35168step0 raw35168step0Labels permutation127 permutation3
    mixedMoment B raw35168step1 raw35168step1Labels = mixedMoment B raw35168step2 raw35168step2Labels := by
      have ha : raw35168step2 = -raw35168step1 := by apply Matrix.ext; change ∀ i j, raw35168step2 i j = -(raw35168step1 i j); unfold raw35168step2 raw35168step1; decide +kernel
      have hl : raw35168step2Labels = raw35168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2831 node2831Labels := by rfl

def raw35169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw35169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![-2, 3, -1], ![-2, 0, 2]]
def raw35169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35169step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw35169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35169 raw35169Labels = mixedMoment B node3005 node3005Labels := by
  calc
    mixedMoment B raw35169 raw35169Labels = mixedMoment B raw35169step0 raw35169step0Labels := by
      have hz : ∀ j, raw35169 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35169step0 = (fun i j => raw35169 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35169step0 raw35169; decide +kernel
      have hl : raw35169step0Labels = raw35169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35169 raw35169Labels permutation434 hz
    mixedMoment B raw35169step0 raw35169step0Labels = mixedMoment B raw35169step1 raw35169step1Labels := by
      have hz : ∀ j, raw35169step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35169step1 = (fun i j => raw35169step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35169step1 raw35169step0; decide +kernel
      have hl : raw35169step1Labels = raw35169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35169step0 raw35169step0Labels permutation80 hz
    mixedMoment B raw35169step1 raw35169step1Labels = mixedMoment B raw35169step2 raw35169step2Labels := by
      have ha : raw35169step2 = (fun i j => raw35169step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35169step2 raw35169step1; decide +kernel
      have hl : raw35169step2Labels = raw35169step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35169step1 raw35169step1Labels permutation25 permutation3
    mixedMoment B raw35169step2 raw35169step2Labels = mixedMoment B raw35169step3 raw35169step3Labels := by
      have ha : raw35169step3 = -raw35169step2 := by apply Matrix.ext; change ∀ i j, raw35169step3 i j = -(raw35169step2 i j); unfold raw35169step3 raw35169step2; decide +kernel
      have hl : raw35169step3Labels = raw35169step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3005 node3005Labels := by rfl

def raw35170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35170step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw35170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35170 raw35170Labels = mixedMoment B node1830 node1830Labels := by
  calc
    mixedMoment B raw35170 raw35170Labels = mixedMoment B raw35170step0 raw35170step0Labels := by
      have hz : ∀ j, raw35170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35170step0 = (fun i j => raw35170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35170step0 raw35170; decide +kernel
      have hl : raw35170step0Labels = raw35170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35170 raw35170Labels permutation434 hz
    mixedMoment B raw35170step0 raw35170step0Labels = mixedMoment B raw35170step1 raw35170step1Labels := by
      have hz : ∀ j, raw35170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35170step1 = (fun i j => raw35170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35170step1 raw35170step0; decide +kernel
      have hl : raw35170step1Labels = raw35170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35170step0 raw35170step0Labels permutation80 hz
    mixedMoment B raw35170step1 raw35170step1Labels = mixedMoment B raw35170step2 raw35170step2Labels := by
      have ha : raw35170step2 = (fun i j => raw35170step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35170step2 raw35170step1; decide +kernel
      have hl : raw35170step2Labels = raw35170step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35170step1 raw35170step1Labels permutation8 permutation3
    _ = mixedMoment B node1830 node1830Labels := by rfl

def raw35171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, 0, -2], ![3, -2, -1]]
def raw35171step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-2, 0, 2], ![-3, 3, 0]]
def raw35171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35171step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw35171step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35171 raw35171Labels = mixedMoment B node2363 node2363Labels := by
  calc
    mixedMoment B raw35171 raw35171Labels = mixedMoment B raw35171step0 raw35171step0Labels := by
      have hz : ∀ j, raw35171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35171step0 = (fun i j => raw35171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35171step0 raw35171; decide +kernel
      have hl : raw35171step0Labels = raw35171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35171 raw35171Labels permutation434 hz
    mixedMoment B raw35171step0 raw35171step0Labels = mixedMoment B raw35171step1 raw35171step1Labels := by
      have hz : ∀ j, raw35171step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35171step1 = (fun i j => raw35171step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35171step1 raw35171step0; decide +kernel
      have hl : raw35171step1Labels = raw35171step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35171step0 raw35171step0Labels permutation80 hz
    mixedMoment B raw35171step1 raw35171step1Labels = mixedMoment B raw35171step2 raw35171step2Labels := by
      have ha : raw35171step2 = (fun i j => raw35171step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35171step2 raw35171step1; decide +kernel
      have hl : raw35171step2Labels = raw35171step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35171step1 raw35171step1Labels permutation30 permutation3
    mixedMoment B raw35171step2 raw35171step2Labels = mixedMoment B raw35171step3 raw35171step3Labels := by
      have ha : raw35171step3 = -raw35171step2 := by apply Matrix.ext; change ∀ i j, raw35171step3 i j = -(raw35171step2 i j); unfold raw35171step3 raw35171step2; decide +kernel
      have hl : raw35171step3Labels = raw35171step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2363 node2363Labels := by rfl

def raw35172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35172 raw35172Labels = mixedMoment B node2362 node2362Labels := by
  calc
    mixedMoment B raw35172 raw35172Labels = mixedMoment B raw35172step0 raw35172step0Labels := by
      have hz : ∀ j, raw35172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35172step0 = (fun i j => raw35172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35172step0 raw35172; decide +kernel
      have hl : raw35172step0Labels = raw35172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35172 raw35172Labels permutation434 hz
    mixedMoment B raw35172step0 raw35172step0Labels = mixedMoment B raw35172step1 raw35172step1Labels := by
      have ha : raw35172step1 = (fun i j => raw35172step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35172step1 raw35172step0; decide +kernel
      have hl : raw35172step1Labels = raw35172step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35172step0 raw35172step0Labels permutation151 permutation3
    mixedMoment B raw35172step1 raw35172step1Labels = mixedMoment B raw35172step2 raw35172step2Labels := by
      have ha : raw35172step2 = -raw35172step1 := by apply Matrix.ext; change ∀ i j, raw35172step2 i j = -(raw35172step1 i j); unfold raw35172step2 raw35172step1; decide +kernel
      have hl : raw35172step2Labels = raw35172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2362 node2362Labels := by rfl

def raw35173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35173 raw35173Labels = mixedMoment B node2362 node2362Labels := by
  calc
    mixedMoment B raw35173 raw35173Labels = mixedMoment B raw35173step0 raw35173step0Labels := by
      have hz : ∀ j, raw35173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35173step0 = (fun i j => raw35173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35173step0 raw35173; decide +kernel
      have hl : raw35173step0Labels = raw35173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35173 raw35173Labels permutation346 hz
    mixedMoment B raw35173step0 raw35173step0Labels = mixedMoment B raw35173step1 raw35173step1Labels := by
      have ha : raw35173step1 = (fun i j => raw35173step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35173step1 raw35173step0; decide +kernel
      have hl : raw35173step1Labels = raw35173step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35173step0 raw35173step0Labels permutation151 permutation3
    mixedMoment B raw35173step1 raw35173step1Labels = mixedMoment B raw35173step2 raw35173step2Labels := by
      have ha : raw35173step2 = -raw35173step1 := by apply Matrix.ext; change ∀ i j, raw35173step2 i j = -(raw35173step1 i j); unfold raw35173step2 raw35173step1; decide +kernel
      have hl : raw35173step2Labels = raw35173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2362 node2362Labels := by rfl

def raw35174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw35174step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35174step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35174step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35174 raw35174Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw35174 raw35174Labels = mixedMoment B raw35174step0 raw35174step0Labels := by
      have hz : ∀ j, raw35174 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35174step0 = (fun i j => raw35174 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35174step0 raw35174; decide +kernel
      have hl : raw35174step0Labels = raw35174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35174 raw35174Labels permutation434 hz
    mixedMoment B raw35174step0 raw35174step0Labels = mixedMoment B raw35174step1 raw35174step1Labels := by
      have hz : ∀ j, raw35174step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35174step1 = (fun i j => raw35174step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35174step1 raw35174step0; decide +kernel
      have hl : raw35174step1Labels = raw35174step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35174step0 raw35174step0Labels permutation80 hz
    mixedMoment B raw35174step1 raw35174step1Labels = mixedMoment B raw35174step2 raw35174step2Labels := by
      have ha : raw35174step2 = (fun i j => raw35174step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35174step2 raw35174step1; decide +kernel
      have hl : raw35174step2Labels = raw35174step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35174step1 raw35174step1Labels permutation31 permutation3
    mixedMoment B raw35174step2 raw35174step2Labels = mixedMoment B raw35174step3 raw35174step3Labels := by
      have ha : raw35174step3 = -raw35174step2 := by apply Matrix.ext; change ∀ i j, raw35174step3 i j = -(raw35174step2 i j); unfold raw35174step3 raw35174step2; decide +kernel
      have hl : raw35174step3Labels = raw35174step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2643 node2643Labels := by rfl

def raw35175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35175step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35175step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35175step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35175step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35175step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35175 raw35175Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw35175 raw35175Labels = mixedMoment B raw35175step0 raw35175step0Labels := by
      have hz : ∀ j, raw35175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35175step0 = (fun i j => raw35175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35175step0 raw35175; decide +kernel
      have hl : raw35175step0Labels = raw35175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35175 raw35175Labels permutation434 hz
    mixedMoment B raw35175step0 raw35175step0Labels = mixedMoment B raw35175step1 raw35175step1Labels := by
      have hz : ∀ j, raw35175step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35175step1 = (fun i j => raw35175step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35175step1 raw35175step0; decide +kernel
      have hl : raw35175step1Labels = raw35175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35175step0 raw35175step0Labels permutation80 hz
    mixedMoment B raw35175step1 raw35175step1Labels = mixedMoment B raw35175step2 raw35175step2Labels := by
      have ha : raw35175step2 = (fun i j => raw35175step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35175step2 raw35175step1; decide +kernel
      have hl : raw35175step2Labels = raw35175step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35175step1 raw35175step1Labels permutation15 permutation7
    mixedMoment B raw35175step2 raw35175step2Labels = mixedMoment B raw35175step3 raw35175step3Labels := by
      have ha : raw35175step3 = -raw35175step2 := by apply Matrix.ext; change ∀ i j, raw35175step3 i j = -(raw35175step2 i j); unfold raw35175step3 raw35175step2; decide +kernel
      have hl : raw35175step3Labels = raw35175step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35175step3 raw35175step3Labels = mixedMoment B raw35175step4 raw35175step4Labels := by
      have ha : raw35175step4 = raw35175step3 := by apply Matrix.ext; unfold raw35175step4 raw35175step3; decide +kernel
      have hl : raw35175step3Labels = labelEmbedding1 ∘ raw35175step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35175step3 raw35175step3Labels raw35175step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw35176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35176 raw35176Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw35176 raw35176Labels = mixedMoment B raw35176step0 raw35176step0Labels := by
      have hz : ∀ j, raw35176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35176step0 = (fun i j => raw35176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35176step0 raw35176; decide +kernel
      have hl : raw35176step0Labels = raw35176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35176 raw35176Labels permutation434 hz
    mixedMoment B raw35176step0 raw35176step0Labels = mixedMoment B raw35176step1 raw35176step1Labels := by
      have ha : raw35176step1 = (fun i j => raw35176step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35176step1 raw35176step0; decide +kernel
      have hl : raw35176step1Labels = raw35176step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35176step0 raw35176step0Labels permutation57 permutation7
    mixedMoment B raw35176step1 raw35176step1Labels = mixedMoment B raw35176step2 raw35176step2Labels := by
      have ha : raw35176step2 = -raw35176step1 := by apply Matrix.ext; change ∀ i j, raw35176step2 i j = -(raw35176step1 i j); unfold raw35176step2 raw35176step1; decide +kernel
      have hl : raw35176step2Labels = raw35176step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35176step2 raw35176step2Labels = mixedMoment B raw35176step3 raw35176step3Labels := by
      have ha : raw35176step3 = raw35176step2 := by apply Matrix.ext; unfold raw35176step3 raw35176step2; decide +kernel
      have hl : raw35176step2Labels = labelEmbedding1 ∘ raw35176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35176step2 raw35176step2Labels raw35176step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw35177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35177step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35177step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35177 raw35177Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw35177 raw35177Labels = mixedMoment B raw35177step0 raw35177step0Labels := by
      have hz : ∀ j, raw35177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35177step0 = (fun i j => raw35177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35177step0 raw35177; decide +kernel
      have hl : raw35177step0Labels = raw35177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35177 raw35177Labels permutation346 hz
    mixedMoment B raw35177step0 raw35177step0Labels = mixedMoment B raw35177step1 raw35177step1Labels := by
      have ha : raw35177step1 = (fun i j => raw35177step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35177step1 raw35177step0; decide +kernel
      have hl : raw35177step1Labels = raw35177step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35177step0 raw35177step0Labels permutation57 permutation7
    mixedMoment B raw35177step1 raw35177step1Labels = mixedMoment B raw35177step2 raw35177step2Labels := by
      have ha : raw35177step2 = -raw35177step1 := by apply Matrix.ext; change ∀ i j, raw35177step2 i j = -(raw35177step1 i j); unfold raw35177step2 raw35177step1; decide +kernel
      have hl : raw35177step2Labels = raw35177step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35177step2 raw35177step2Labels = mixedMoment B raw35177step3 raw35177step3Labels := by
      have ha : raw35177step3 = raw35177step2 := by apply Matrix.ext; unfold raw35177step3 raw35177step2; decide +kernel
      have hl : raw35177step2Labels = labelEmbedding1 ∘ raw35177step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35177step2 raw35177step2Labels raw35177step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw35178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35178step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35178step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35178step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35178step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35178step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35178step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35178 raw35178Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw35178 raw35178Labels = mixedMoment B raw35178step0 raw35178step0Labels := by
      have hz : ∀ j, raw35178 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35178step0 = (fun i j => raw35178 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35178step0 raw35178; decide +kernel
      have hl : raw35178step0Labels = raw35178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35178 raw35178Labels permutation434 hz
    mixedMoment B raw35178step0 raw35178step0Labels = mixedMoment B raw35178step1 raw35178step1Labels := by
      have hz : ∀ j, raw35178step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35178step1 = (fun i j => raw35178step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35178step1 raw35178step0; decide +kernel
      have hl : raw35178step1Labels = raw35178step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35178step0 raw35178step0Labels permutation80 hz
    mixedMoment B raw35178step1 raw35178step1Labels = mixedMoment B raw35178step2 raw35178step2Labels := by
      have ha : raw35178step2 = (fun i j => raw35178step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35178step2 raw35178step1; decide +kernel
      have hl : raw35178step2Labels = raw35178step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35178step1 raw35178step1Labels permutation15 permutation7
    mixedMoment B raw35178step2 raw35178step2Labels = mixedMoment B raw35178step3 raw35178step3Labels := by
      have ha : raw35178step3 = -raw35178step2 := by apply Matrix.ext; change ∀ i j, raw35178step3 i j = -(raw35178step2 i j); unfold raw35178step3 raw35178step2; decide +kernel
      have hl : raw35178step3Labels = raw35178step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35178step3 raw35178step3Labels = mixedMoment B raw35178step4 raw35178step4Labels := by
      have ha : raw35178step4 = raw35178step3 := by apply Matrix.ext; unfold raw35178step4 raw35178step3; decide +kernel
      have hl : raw35178step3Labels = labelEmbedding1 ∘ raw35178step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35178step3 raw35178step3Labels raw35178step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw35179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35179step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35179step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35179step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35179step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35179step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35179step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35179 raw35179Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw35179 raw35179Labels = mixedMoment B raw35179step0 raw35179step0Labels := by
      have hz : ∀ j, raw35179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35179step0 = (fun i j => raw35179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35179step0 raw35179; decide +kernel
      have hl : raw35179step0Labels = raw35179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35179 raw35179Labels permutation434 hz
    mixedMoment B raw35179step0 raw35179step0Labels = mixedMoment B raw35179step1 raw35179step1Labels := by
      have hz : ∀ j, raw35179step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35179step1 = (fun i j => raw35179step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35179step1 raw35179step0; decide +kernel
      have hl : raw35179step1Labels = raw35179step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35179step0 raw35179step0Labels permutation80 hz
    mixedMoment B raw35179step1 raw35179step1Labels = mixedMoment B raw35179step2 raw35179step2Labels := by
      have ha : raw35179step2 = (fun i j => raw35179step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35179step2 raw35179step1; decide +kernel
      have hl : raw35179step2Labels = raw35179step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35179step1 raw35179step1Labels permutation15 permutation7
    mixedMoment B raw35179step2 raw35179step2Labels = mixedMoment B raw35179step3 raw35179step3Labels := by
      have ha : raw35179step3 = -raw35179step2 := by apply Matrix.ext; change ∀ i j, raw35179step3 i j = -(raw35179step2 i j); unfold raw35179step3 raw35179step2; decide +kernel
      have hl : raw35179step3Labels = raw35179step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35179step3 raw35179step3Labels = mixedMoment B raw35179step4 raw35179step4Labels := by
      have ha : raw35179step4 = raw35179step3 := by apply Matrix.ext; unfold raw35179step4 raw35179step3; decide +kernel
      have hl : raw35179step3Labels = labelEmbedding1 ∘ raw35179step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35179step3 raw35179step3Labels raw35179step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw35180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, 0, -2], ![2, -1, -1]]
def raw35180step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35180step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw35180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35180step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw35180step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35180step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw35180step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35180 raw35180Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw35180 raw35180Labels = mixedMoment B raw35180step0 raw35180step0Labels := by
      have hz : ∀ j, raw35180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35180step0 = (fun i j => raw35180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35180step0 raw35180; decide +kernel
      have hl : raw35180step0Labels = raw35180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35180 raw35180Labels permutation434 hz
    mixedMoment B raw35180step0 raw35180step0Labels = mixedMoment B raw35180step1 raw35180step1Labels := by
      have hz : ∀ j, raw35180step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35180step1 = (fun i j => raw35180step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35180step1 raw35180step0; decide +kernel
      have hl : raw35180step1Labels = raw35180step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35180step0 raw35180step0Labels permutation80 hz
    mixedMoment B raw35180step1 raw35180step1Labels = mixedMoment B raw35180step2 raw35180step2Labels := by
      have ha : raw35180step2 = (fun i j => raw35180step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35180step2 raw35180step1; decide +kernel
      have hl : raw35180step2Labels = raw35180step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35180step1 raw35180step1Labels permutation11 permutation5
    mixedMoment B raw35180step2 raw35180step2Labels = mixedMoment B raw35180step3 raw35180step3Labels := by
      have ha : raw35180step3 = -raw35180step2 := by apply Matrix.ext; change ∀ i j, raw35180step3 i j = -(raw35180step2 i j); unfold raw35180step3 raw35180step2; decide +kernel
      have hl : raw35180step3Labels = raw35180step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35180step3 raw35180step3Labels = mixedMoment B raw35180step4 raw35180step4Labels := by
      have ha : raw35180step4 = raw35180step3 := by apply Matrix.ext; unfold raw35180step4 raw35180step3; decide +kernel
      have hl : raw35180step3Labels = labelEmbedding1 ∘ raw35180step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35180step3 raw35180step3Labels raw35180step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw35181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35181step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35181step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35181step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35181step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35181 raw35181Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw35181 raw35181Labels = mixedMoment B raw35181step0 raw35181step0Labels := by
      have hz : ∀ j, raw35181 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35181step0 = (fun i j => raw35181 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35181step0 raw35181; decide +kernel
      have hl : raw35181step0Labels = raw35181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35181 raw35181Labels permutation434 hz
    mixedMoment B raw35181step0 raw35181step0Labels = mixedMoment B raw35181step1 raw35181step1Labels := by
      have ha : raw35181step1 = (fun i j => raw35181step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35181step1 raw35181step0; decide +kernel
      have hl : raw35181step1Labels = raw35181step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35181step0 raw35181step0Labels permutation57 permutation7
    mixedMoment B raw35181step1 raw35181step1Labels = mixedMoment B raw35181step2 raw35181step2Labels := by
      have ha : raw35181step2 = -raw35181step1 := by apply Matrix.ext; change ∀ i j, raw35181step2 i j = -(raw35181step1 i j); unfold raw35181step2 raw35181step1; decide +kernel
      have hl : raw35181step2Labels = raw35181step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35181step2 raw35181step2Labels = mixedMoment B raw35181step3 raw35181step3Labels := by
      have ha : raw35181step3 = raw35181step2 := by apply Matrix.ext; unfold raw35181step3 raw35181step2; decide +kernel
      have hl : raw35181step2Labels = labelEmbedding1 ∘ raw35181step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35181step2 raw35181step2Labels raw35181step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw35182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35182step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35182step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35182 raw35182Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw35182 raw35182Labels = mixedMoment B raw35182step0 raw35182step0Labels := by
      have hz : ∀ j, raw35182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35182step0 = (fun i j => raw35182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35182step0 raw35182; decide +kernel
      have hl : raw35182step0Labels = raw35182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35182 raw35182Labels permutation346 hz
    mixedMoment B raw35182step0 raw35182step0Labels = mixedMoment B raw35182step1 raw35182step1Labels := by
      have ha : raw35182step1 = (fun i j => raw35182step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35182step1 raw35182step0; decide +kernel
      have hl : raw35182step1Labels = raw35182step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35182step0 raw35182step0Labels permutation57 permutation7
    mixedMoment B raw35182step1 raw35182step1Labels = mixedMoment B raw35182step2 raw35182step2Labels := by
      have ha : raw35182step2 = -raw35182step1 := by apply Matrix.ext; change ∀ i j, raw35182step2 i j = -(raw35182step1 i j); unfold raw35182step2 raw35182step1; decide +kernel
      have hl : raw35182step2Labels = raw35182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35182step2 raw35182step2Labels = mixedMoment B raw35182step3 raw35182step3Labels := by
      have ha : raw35182step3 = raw35182step2 := by apply Matrix.ext; unfold raw35182step3 raw35182step2; decide +kernel
      have hl : raw35182step2Labels = labelEmbedding1 ∘ raw35182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35182step2 raw35182step2Labels raw35182step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw35183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![2, -1, -1]]
def raw35183step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw35183step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35183step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw35183step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35183step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw35183step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35183 raw35183Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw35183 raw35183Labels = mixedMoment B raw35183step0 raw35183step0Labels := by
      have hz : ∀ j, raw35183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35183step0 = (fun i j => raw35183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35183step0 raw35183; decide +kernel
      have hl : raw35183step0Labels = raw35183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35183 raw35183Labels permutation434 hz
    mixedMoment B raw35183step0 raw35183step0Labels = mixedMoment B raw35183step1 raw35183step1Labels := by
      have hz : ∀ j, raw35183step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35183step1 = (fun i j => raw35183step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35183step1 raw35183step0; decide +kernel
      have hl : raw35183step1Labels = raw35183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35183step0 raw35183step0Labels permutation80 hz
    mixedMoment B raw35183step1 raw35183step1Labels = mixedMoment B raw35183step2 raw35183step2Labels := by
      have ha : raw35183step2 = (fun i j => raw35183step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35183step2 raw35183step1; decide +kernel
      have hl : raw35183step2Labels = raw35183step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35183step1 raw35183step1Labels permutation15 permutation7
    mixedMoment B raw35183step2 raw35183step2Labels = mixedMoment B raw35183step3 raw35183step3Labels := by
      have ha : raw35183step3 = -raw35183step2 := by apply Matrix.ext; change ∀ i j, raw35183step3 i j = -(raw35183step2 i j); unfold raw35183step3 raw35183step2; decide +kernel
      have hl : raw35183step3Labels = raw35183step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35183step3 raw35183step3Labels = mixedMoment B raw35183step4 raw35183step4Labels := by
      have ha : raw35183step4 = raw35183step3 := by apply Matrix.ext; unfold raw35183step4 raw35183step3; decide +kernel
      have hl : raw35183step3Labels = labelEmbedding1 ∘ raw35183step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35183step3 raw35183step3Labels raw35183step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw35184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![2, 0, -2], ![1, 0, -1]]
def raw35184step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw35184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw35184step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35184step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw35184step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35184 raw35184Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw35184 raw35184Labels = mixedMoment B raw35184step0 raw35184step0Labels := by
      have hz : ∀ j, raw35184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35184step0 = (fun i j => raw35184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35184step0 raw35184; decide +kernel
      have hl : raw35184step0Labels = raw35184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35184 raw35184Labels permutation434 hz
    mixedMoment B raw35184step0 raw35184step0Labels = mixedMoment B raw35184step1 raw35184step1Labels := by
      have hz : ∀ j, raw35184step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35184step1 = (fun i j => raw35184step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35184step1 raw35184step0; decide +kernel
      have hl : raw35184step1Labels = raw35184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35184step0 raw35184step0Labels permutation80 hz
    mixedMoment B raw35184step1 raw35184step1Labels = mixedMoment B raw35184step2 raw35184step2Labels := by
      have ha : raw35184step2 = (fun i j => raw35184step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35184step2 raw35184step1; decide +kernel
      have hl : raw35184step2Labels = raw35184step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35184step1 raw35184step1Labels permutation15 permutation7
    mixedMoment B raw35184step2 raw35184step2Labels = mixedMoment B raw35184step3 raw35184step3Labels := by
      have ha : raw35184step3 = -raw35184step2 := by apply Matrix.ext; change ∀ i j, raw35184step3 i j = -(raw35184step2 i j); unfold raw35184step3 raw35184step2; decide +kernel
      have hl : raw35184step3Labels = raw35184step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35184step3 raw35184step3Labels = mixedMoment B raw35184step4 raw35184step4Labels := by
      have ha : raw35184step4 = raw35184step3 := by apply Matrix.ext; unfold raw35184step4 raw35184step3; decide +kernel
      have hl : raw35184step3Labels = labelEmbedding1 ∘ raw35184step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35184step3 raw35184step3Labels raw35184step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw35185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw35185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35185step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35185 raw35185Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw35185 raw35185Labels = mixedMoment B raw35185step0 raw35185step0Labels := by
      have hz : ∀ j, raw35185 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35185step0 = (fun i j => raw35185 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35185step0 raw35185; decide +kernel
      have hl : raw35185step0Labels = raw35185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35185 raw35185Labels permutation434 hz
    mixedMoment B raw35185step0 raw35185step0Labels = mixedMoment B raw35185step1 raw35185step1Labels := by
      have ha : raw35185step1 = (fun i j => raw35185step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35185step1 raw35185step0; decide +kernel
      have hl : raw35185step1Labels = raw35185step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35185step0 raw35185step0Labels permutation44 permutation5
    mixedMoment B raw35185step1 raw35185step1Labels = mixedMoment B raw35185step2 raw35185step2Labels := by
      have ha : raw35185step2 = -raw35185step1 := by apply Matrix.ext; change ∀ i j, raw35185step2 i j = -(raw35185step1 i j); unfold raw35185step2 raw35185step1; decide +kernel
      have hl : raw35185step2Labels = raw35185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35185step2 raw35185step2Labels = mixedMoment B raw35185step3 raw35185step3Labels := by
      have ha : raw35185step3 = raw35185step2 := by apply Matrix.ext; unfold raw35185step3 raw35185step2; decide +kernel
      have hl : raw35185step2Labels = labelEmbedding1 ∘ raw35185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35185step2 raw35185step2Labels raw35185step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

def raw35186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35186 raw35186Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw35186 raw35186Labels = mixedMoment B raw35186step0 raw35186step0Labels := by
      have hz : ∀ j, raw35186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35186step0 = (fun i j => raw35186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35186step0 raw35186; decide +kernel
      have hl : raw35186step0Labels = raw35186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35186 raw35186Labels permutation434 hz
    mixedMoment B raw35186step0 raw35186step0Labels = mixedMoment B raw35186step1 raw35186step1Labels := by
      have ha : raw35186step1 = (fun i j => raw35186step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35186step1 raw35186step0; decide +kernel
      have hl : raw35186step1Labels = raw35186step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35186step0 raw35186step0Labels permutation57 permutation7
    mixedMoment B raw35186step1 raw35186step1Labels = mixedMoment B raw35186step2 raw35186step2Labels := by
      have ha : raw35186step2 = -raw35186step1 := by apply Matrix.ext; change ∀ i j, raw35186step2 i j = -(raw35186step1 i j); unfold raw35186step2 raw35186step1; decide +kernel
      have hl : raw35186step2Labels = raw35186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35186step2 raw35186step2Labels = mixedMoment B raw35186step3 raw35186step3Labels := by
      have ha : raw35186step3 = raw35186step2 := by apply Matrix.ext; unfold raw35186step3 raw35186step2; decide +kernel
      have hl : raw35186step2Labels = labelEmbedding1 ∘ raw35186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35186step2 raw35186step2Labels raw35186step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

def raw35187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35187 raw35187Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw35187 raw35187Labels = mixedMoment B raw35187step0 raw35187step0Labels := by
      have ha : raw35187step0 = (fun i j => raw35187 (permutation272 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35187step0 raw35187; decide +kernel
      have hl : raw35187step0Labels = raw35187Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35187 raw35187Labels permutation272 permutation7
    mixedMoment B raw35187step0 raw35187step0Labels = mixedMoment B raw35187step1 raw35187step1Labels := by
      have ha : raw35187step1 = -raw35187step0 := by apply Matrix.ext; change ∀ i j, raw35187step1 i j = -(raw35187step0 i j); unfold raw35187step1 raw35187step0; decide +kernel
      have hl : raw35187step1Labels = raw35187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35187step1 raw35187step1Labels = mixedMoment B raw35187step2 raw35187step2Labels := by
      have ha : raw35187step2 = raw35187step1 := by apply Matrix.ext; unfold raw35187step2 raw35187step1; decide +kernel
      have hl : raw35187step1Labels = labelEmbedding1 ∘ raw35187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35187step1 raw35187step1Labels raw35187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

def raw35188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35188 raw35188Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw35188 raw35188Labels = mixedMoment B raw35188step0 raw35188step0Labels := by
      have hz : ∀ j, raw35188 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35188step0 = (fun i j => raw35188 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35188step0 raw35188; decide +kernel
      have hl : raw35188step0Labels = raw35188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35188 raw35188Labels permutation434 hz
    mixedMoment B raw35188step0 raw35188step0Labels = mixedMoment B raw35188step1 raw35188step1Labels := by
      have ha : raw35188step1 = (fun i j => raw35188step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35188step1 raw35188step0; decide +kernel
      have hl : raw35188step1Labels = raw35188step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35188step0 raw35188step0Labels permutation57 permutation7
    mixedMoment B raw35188step1 raw35188step1Labels = mixedMoment B raw35188step2 raw35188step2Labels := by
      have ha : raw35188step2 = -raw35188step1 := by apply Matrix.ext; change ∀ i j, raw35188step2 i j = -(raw35188step1 i j); unfold raw35188step2 raw35188step1; decide +kernel
      have hl : raw35188step2Labels = raw35188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35188step2 raw35188step2Labels = mixedMoment B raw35188step3 raw35188step3Labels := by
      have ha : raw35188step3 = raw35188step2 := by apply Matrix.ext; unfold raw35188step3 raw35188step2; decide +kernel
      have hl : raw35188step2Labels = labelEmbedding1 ∘ raw35188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35188step2 raw35188step2Labels raw35188step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw35189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35189 raw35189Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw35189 raw35189Labels = mixedMoment B raw35189step0 raw35189step0Labels := by
      have hz : ∀ j, raw35189 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35189step0 = (fun i j => raw35189 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35189step0 raw35189; decide +kernel
      have hl : raw35189step0Labels = raw35189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35189 raw35189Labels permutation434 hz
    mixedMoment B raw35189step0 raw35189step0Labels = mixedMoment B raw35189step1 raw35189step1Labels := by
      have ha : raw35189step1 = (fun i j => raw35189step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35189step1 raw35189step0; decide +kernel
      have hl : raw35189step1Labels = raw35189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35189step0 raw35189step0Labels permutation57 permutation7
    mixedMoment B raw35189step1 raw35189step1Labels = mixedMoment B raw35189step2 raw35189step2Labels := by
      have ha : raw35189step2 = -raw35189step1 := by apply Matrix.ext; change ∀ i j, raw35189step2 i j = -(raw35189step1 i j); unfold raw35189step2 raw35189step1; decide +kernel
      have hl : raw35189step2Labels = raw35189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35189step2 raw35189step2Labels = mixedMoment B raw35189step3 raw35189step3Labels := by
      have ha : raw35189step3 = raw35189step2 := by apply Matrix.ext; unfold raw35189step3 raw35189step2; decide +kernel
      have hl : raw35189step2Labels = labelEmbedding1 ∘ raw35189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35189step2 raw35189step2Labels raw35189step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw35190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw35190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35190 raw35190Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw35190 raw35190Labels = mixedMoment B raw35190step0 raw35190step0Labels := by
      have hz : ∀ j, raw35190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35190step0 = (fun i j => raw35190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35190step0 raw35190; decide +kernel
      have hl : raw35190step0Labels = raw35190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35190 raw35190Labels permutation346 hz
    mixedMoment B raw35190step0 raw35190step0Labels = mixedMoment B raw35190step1 raw35190step1Labels := by
      have ha : raw35190step1 = (fun i j => raw35190step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35190step1 raw35190step0; decide +kernel
      have hl : raw35190step1Labels = raw35190step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35190step0 raw35190step0Labels permutation44 permutation5
    mixedMoment B raw35190step1 raw35190step1Labels = mixedMoment B raw35190step2 raw35190step2Labels := by
      have ha : raw35190step2 = -raw35190step1 := by apply Matrix.ext; change ∀ i j, raw35190step2 i j = -(raw35190step1 i j); unfold raw35190step2 raw35190step1; decide +kernel
      have hl : raw35190step2Labels = raw35190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35190step2 raw35190step2Labels = mixedMoment B raw35190step3 raw35190step3Labels := by
      have ha : raw35190step3 = raw35190step2 := by apply Matrix.ext; unfold raw35190step3 raw35190step2; decide +kernel
      have hl : raw35190step2Labels = labelEmbedding1 ∘ raw35190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35190step2 raw35190step2Labels raw35190step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

def raw35191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35191step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35191 raw35191Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw35191 raw35191Labels = mixedMoment B raw35191step0 raw35191step0Labels := by
      have hz : ∀ j, raw35191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35191step0 = (fun i j => raw35191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35191step0 raw35191; decide +kernel
      have hl : raw35191step0Labels = raw35191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35191 raw35191Labels permutation346 hz
    mixedMoment B raw35191step0 raw35191step0Labels = mixedMoment B raw35191step1 raw35191step1Labels := by
      have ha : raw35191step1 = (fun i j => raw35191step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35191step1 raw35191step0; decide +kernel
      have hl : raw35191step1Labels = raw35191step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35191step0 raw35191step0Labels permutation57 permutation7
    mixedMoment B raw35191step1 raw35191step1Labels = mixedMoment B raw35191step2 raw35191step2Labels := by
      have ha : raw35191step2 = -raw35191step1 := by apply Matrix.ext; change ∀ i j, raw35191step2 i j = -(raw35191step1 i j); unfold raw35191step2 raw35191step1; decide +kernel
      have hl : raw35191step2Labels = raw35191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35191step2 raw35191step2Labels = mixedMoment B raw35191step3 raw35191step3Labels := by
      have ha : raw35191step3 = raw35191step2 := by apply Matrix.ext; unfold raw35191step3 raw35191step2; decide +kernel
      have hl : raw35191step2Labels = labelEmbedding1 ∘ raw35191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35191step2 raw35191step2Labels raw35191step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

def raw35192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35192 raw35192Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw35192 raw35192Labels = mixedMoment B raw35192step0 raw35192step0Labels := by
      have ha : raw35192step0 = (fun i j => raw35192 (permutation266 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35192step0 raw35192; decide +kernel
      have hl : raw35192step0Labels = raw35192Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35192 raw35192Labels permutation266 permutation7
    mixedMoment B raw35192step0 raw35192step0Labels = mixedMoment B raw35192step1 raw35192step1Labels := by
      have ha : raw35192step1 = -raw35192step0 := by apply Matrix.ext; change ∀ i j, raw35192step1 i j = -(raw35192step0 i j); unfold raw35192step1 raw35192step0; decide +kernel
      have hl : raw35192step1Labels = raw35192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35192step1 raw35192step1Labels = mixedMoment B raw35192step2 raw35192step2Labels := by
      have ha : raw35192step2 = raw35192step1 := by apply Matrix.ext; unfold raw35192step2 raw35192step1; decide +kernel
      have hl : raw35192step1Labels = labelEmbedding1 ∘ raw35192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35192step1 raw35192step1Labels raw35192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

def raw35193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35193 raw35193Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw35193 raw35193Labels = mixedMoment B raw35193step0 raw35193step0Labels := by
      have hz : ∀ j, raw35193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35193step0 = (fun i j => raw35193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35193step0 raw35193; decide +kernel
      have hl : raw35193step0Labels = raw35193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35193 raw35193Labels permutation346 hz
    mixedMoment B raw35193step0 raw35193step0Labels = mixedMoment B raw35193step1 raw35193step1Labels := by
      have ha : raw35193step1 = (fun i j => raw35193step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35193step1 raw35193step0; decide +kernel
      have hl : raw35193step1Labels = raw35193step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35193step0 raw35193step0Labels permutation57 permutation7
    mixedMoment B raw35193step1 raw35193step1Labels = mixedMoment B raw35193step2 raw35193step2Labels := by
      have ha : raw35193step2 = -raw35193step1 := by apply Matrix.ext; change ∀ i j, raw35193step2 i j = -(raw35193step1 i j); unfold raw35193step2 raw35193step1; decide +kernel
      have hl : raw35193step2Labels = raw35193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35193step2 raw35193step2Labels = mixedMoment B raw35193step3 raw35193step3Labels := by
      have ha : raw35193step3 = raw35193step2 := by apply Matrix.ext; unfold raw35193step3 raw35193step2; decide +kernel
      have hl : raw35193step2Labels = labelEmbedding1 ∘ raw35193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35193step2 raw35193step2Labels raw35193step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw35194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35194step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35194step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35194step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35194 raw35194Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw35194 raw35194Labels = mixedMoment B raw35194step0 raw35194step0Labels := by
      have hz : ∀ j, raw35194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35194step0 = (fun i j => raw35194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35194step0 raw35194; decide +kernel
      have hl : raw35194step0Labels = raw35194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35194 raw35194Labels permutation346 hz
    mixedMoment B raw35194step0 raw35194step0Labels = mixedMoment B raw35194step1 raw35194step1Labels := by
      have ha : raw35194step1 = (fun i j => raw35194step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35194step1 raw35194step0; decide +kernel
      have hl : raw35194step1Labels = raw35194step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35194step0 raw35194step0Labels permutation57 permutation7
    mixedMoment B raw35194step1 raw35194step1Labels = mixedMoment B raw35194step2 raw35194step2Labels := by
      have ha : raw35194step2 = -raw35194step1 := by apply Matrix.ext; change ∀ i j, raw35194step2 i j = -(raw35194step1 i j); unfold raw35194step2 raw35194step1; decide +kernel
      have hl : raw35194step2Labels = raw35194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35194step2 raw35194step2Labels = mixedMoment B raw35194step3 raw35194step3Labels := by
      have ha : raw35194step3 = raw35194step2 := by apply Matrix.ext; unfold raw35194step3 raw35194step2; decide +kernel
      have hl : raw35194step2Labels = labelEmbedding1 ∘ raw35194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35194step2 raw35194step2Labels raw35194step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw35195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35195step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw35195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35195step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw35195step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35195step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw35195step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35195 raw35195Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw35195 raw35195Labels = mixedMoment B raw35195step0 raw35195step0Labels := by
      have hz : ∀ j, raw35195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35195step0 = (fun i j => raw35195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35195step0 raw35195; decide +kernel
      have hl : raw35195step0Labels = raw35195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35195 raw35195Labels permutation434 hz
    mixedMoment B raw35195step0 raw35195step0Labels = mixedMoment B raw35195step1 raw35195step1Labels := by
      have hz : ∀ j, raw35195step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35195step1 = (fun i j => raw35195step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35195step1 raw35195step0; decide +kernel
      have hl : raw35195step1Labels = raw35195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35195step0 raw35195step0Labels permutation80 hz
    mixedMoment B raw35195step1 raw35195step1Labels = mixedMoment B raw35195step2 raw35195step2Labels := by
      have ha : raw35195step2 = (fun i j => raw35195step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35195step2 raw35195step1; decide +kernel
      have hl : raw35195step2Labels = raw35195step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35195step1 raw35195step1Labels permutation9 permutation5
    mixedMoment B raw35195step2 raw35195step2Labels = mixedMoment B raw35195step3 raw35195step3Labels := by
      have ha : raw35195step3 = -raw35195step2 := by apply Matrix.ext; change ∀ i j, raw35195step3 i j = -(raw35195step2 i j); unfold raw35195step3 raw35195step2; decide +kernel
      have hl : raw35195step3Labels = raw35195step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35195step3 raw35195step3Labels = mixedMoment B raw35195step4 raw35195step4Labels := by
      have ha : raw35195step4 = raw35195step3 := by apply Matrix.ext; unfold raw35195step4 raw35195step3; decide +kernel
      have hl : raw35195step3Labels = labelEmbedding1 ∘ raw35195step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35195step3 raw35195step3Labels raw35195step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

def raw35196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![3, -1, -2], ![2, -1, -1]]
def raw35196step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35196step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw35196step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35196step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw35196step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35196step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw35196step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35196 raw35196Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw35196 raw35196Labels = mixedMoment B raw35196step0 raw35196step0Labels := by
      have hz : ∀ j, raw35196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35196step0 = (fun i j => raw35196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35196step0 raw35196; decide +kernel
      have hl : raw35196step0Labels = raw35196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35196 raw35196Labels permutation434 hz
    mixedMoment B raw35196step0 raw35196step0Labels = mixedMoment B raw35196step1 raw35196step1Labels := by
      have hz : ∀ j, raw35196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35196step1 = (fun i j => raw35196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35196step1 raw35196step0; decide +kernel
      have hl : raw35196step1Labels = raw35196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35196step0 raw35196step0Labels permutation80 hz
    mixedMoment B raw35196step1 raw35196step1Labels = mixedMoment B raw35196step2 raw35196step2Labels := by
      have ha : raw35196step2 = (fun i j => raw35196step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35196step2 raw35196step1; decide +kernel
      have hl : raw35196step2Labels = raw35196step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35196step1 raw35196step1Labels permutation15 permutation7
    mixedMoment B raw35196step2 raw35196step2Labels = mixedMoment B raw35196step3 raw35196step3Labels := by
      have ha : raw35196step3 = -raw35196step2 := by apply Matrix.ext; change ∀ i j, raw35196step3 i j = -(raw35196step2 i j); unfold raw35196step3 raw35196step2; decide +kernel
      have hl : raw35196step3Labels = raw35196step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35196step3 raw35196step3Labels = mixedMoment B raw35196step4 raw35196step4Labels := by
      have ha : raw35196step4 = raw35196step3 := by apply Matrix.ext; unfold raw35196step4 raw35196step3; decide +kernel
      have hl : raw35196step3Labels = labelEmbedding1 ∘ raw35196step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35196step3 raw35196step3Labels raw35196step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

def raw35197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw35197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw35197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35197step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw35197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35197 raw35197Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw35197 raw35197Labels = mixedMoment B raw35197step0 raw35197step0Labels := by
      have hz : ∀ j, raw35197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35197step0 = (fun i j => raw35197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35197step0 raw35197; decide +kernel
      have hl : raw35197step0Labels = raw35197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35197 raw35197Labels permutation434 hz
    mixedMoment B raw35197step0 raw35197step0Labels = mixedMoment B raw35197step1 raw35197step1Labels := by
      have ha : raw35197step1 = (fun i j => raw35197step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35197step1 raw35197step0; decide +kernel
      have hl : raw35197step1Labels = raw35197step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35197step0 raw35197step0Labels permutation57 permutation7
    mixedMoment B raw35197step1 raw35197step1Labels = mixedMoment B raw35197step2 raw35197step2Labels := by
      have ha : raw35197step2 = -raw35197step1 := by apply Matrix.ext; change ∀ i j, raw35197step2 i j = -(raw35197step1 i j); unfold raw35197step2 raw35197step1; decide +kernel
      have hl : raw35197step2Labels = raw35197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35197step2 raw35197step2Labels = mixedMoment B raw35197step3 raw35197step3Labels := by
      have ha : raw35197step3 = raw35197step2 := by apply Matrix.ext; unfold raw35197step3 raw35197step2; decide +kernel
      have hl : raw35197step2Labels = labelEmbedding1 ∘ raw35197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35197step2 raw35197step2Labels raw35197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw35198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw35198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw35198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw35198step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35198 raw35198Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw35198 raw35198Labels = mixedMoment B raw35198step0 raw35198step0Labels := by
      have hz : ∀ j, raw35198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35198step0 = (fun i j => raw35198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35198step0 raw35198; decide +kernel
      have hl : raw35198step0Labels = raw35198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35198 raw35198Labels permutation346 hz
    mixedMoment B raw35198step0 raw35198step0Labels = mixedMoment B raw35198step1 raw35198step1Labels := by
      have ha : raw35198step1 = (fun i j => raw35198step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35198step1 raw35198step0; decide +kernel
      have hl : raw35198step1Labels = raw35198step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35198step0 raw35198step0Labels permutation57 permutation7
    mixedMoment B raw35198step1 raw35198step1Labels = mixedMoment B raw35198step2 raw35198step2Labels := by
      have ha : raw35198step2 = -raw35198step1 := by apply Matrix.ext; change ∀ i j, raw35198step2 i j = -(raw35198step1 i j); unfold raw35198step2 raw35198step1; decide +kernel
      have hl : raw35198step2Labels = raw35198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35198step2 raw35198step2Labels = mixedMoment B raw35198step3 raw35198step3Labels := by
      have ha : raw35198step3 = raw35198step2 := by apply Matrix.ext; unfold raw35198step3 raw35198step2; decide +kernel
      have hl : raw35198step2Labels = labelEmbedding1 ∘ raw35198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35198step2 raw35198step2Labels raw35198step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw35199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw35199step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-2, -1, 3]]
def raw35199step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35199step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw35199step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35199step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw35199step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35199 raw35199Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw35199 raw35199Labels = mixedMoment B raw35199step0 raw35199step0Labels := by
      have hz : ∀ j, raw35199 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35199step0 = (fun i j => raw35199 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35199step0 raw35199; decide +kernel
      have hl : raw35199step0Labels = raw35199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35199 raw35199Labels permutation434 hz
    mixedMoment B raw35199step0 raw35199step0Labels = mixedMoment B raw35199step1 raw35199step1Labels := by
      have hz : ∀ j, raw35199step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35199step1 = (fun i j => raw35199step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35199step1 raw35199step0; decide +kernel
      have hl : raw35199step1Labels = raw35199step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35199step0 raw35199step0Labels permutation80 hz
    mixedMoment B raw35199step1 raw35199step1Labels = mixedMoment B raw35199step2 raw35199step2Labels := by
      have ha : raw35199step2 = (fun i j => raw35199step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35199step2 raw35199step1; decide +kernel
      have hl : raw35199step2Labels = raw35199step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35199step1 raw35199step1Labels permutation15 permutation7
    mixedMoment B raw35199step2 raw35199step2Labels = mixedMoment B raw35199step3 raw35199step3Labels := by
      have ha : raw35199step3 = -raw35199step2 := by apply Matrix.ext; change ∀ i j, raw35199step3 i j = -(raw35199step2 i j); unfold raw35199step3 raw35199step2; decide +kernel
      have hl : raw35199step3Labels = raw35199step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35199step3 raw35199step3Labels = mixedMoment B raw35199step4 raw35199step4Labels := by
      have ha : raw35199step4 = raw35199step3 := by apply Matrix.ext; unfold raw35199step4 raw35199step3; decide +kernel
      have hl : raw35199step3Labels = labelEmbedding1 ∘ raw35199step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35199step3 raw35199step3Labels raw35199step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
