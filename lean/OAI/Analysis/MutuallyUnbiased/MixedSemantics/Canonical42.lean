import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5376 raw5376Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw5376 raw5376Labels = mixedMoment B raw5376step0 raw5376step0Labels := by
      have ha : raw5376step0 = (fun i j => raw5376 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5376step0 raw5376; decide +kernel
      have hl : raw5376step0Labels = raw5376Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5376 raw5376Labels permutation208 permutation3
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw5377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5377 raw5377Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw5377 raw5377Labels = mixedMoment B raw5377step0 raw5377step0Labels := by
      have ha : raw5377step0 = (fun i j => raw5377 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5377step0 raw5377; decide +kernel
      have hl : raw5377step0Labels = raw5377Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5377 raw5377Labels permutation232 permutation3
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw5378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5378 raw5378Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5378 raw5378Labels = mixedMoment B raw5378step0 raw5378step0Labels := by
      have ha : raw5378step0 = (fun i j => raw5378 (permutation187 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5378step0 raw5378; decide +kernel
      have hl : raw5378step0Labels = raw5378Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5378 raw5378Labels permutation187 permutation3
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw5379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5379 raw5379Labels = mixedMoment B node825 node825Labels := by
  calc
    mixedMoment B raw5379 raw5379Labels = mixedMoment B raw5379step0 raw5379step0Labels := by
      have hz : ∀ j, raw5379 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5379step0 = (fun i j => raw5379 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5379step0 raw5379; decide +kernel
      have hl : raw5379step0Labels = raw5379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5379 raw5379Labels permutation265 hz
    mixedMoment B raw5379step0 raw5379step0Labels = mixedMoment B raw5379step1 raw5379step1Labels := by
      have ha : raw5379step1 = (fun i j => raw5379step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5379step1 raw5379step0; decide +kernel
      have hl : raw5379step1Labels = raw5379step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5379step0 raw5379step0Labels permutation40 permutation3
    _ = mixedMoment B node825 node825Labels := by rfl

def raw5380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5380 raw5380Labels = mixedMoment B node1923 node1923Labels := by
  calc
    mixedMoment B raw5380 raw5380Labels = mixedMoment B raw5380step0 raw5380step0Labels := by
      have ha : raw5380step0 = (fun i j => raw5380 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5380step0 raw5380; decide +kernel
      have hl : raw5380step0Labels = raw5380Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5380 raw5380Labels permutation160 permutation3
    _ = mixedMoment B node1923 node1923Labels := by rfl

def raw5381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5381 raw5381Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw5381 raw5381Labels = mixedMoment B raw5381step0 raw5381step0Labels := by
      have hz : ∀ j, raw5381 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5381step0 = (fun i j => raw5381 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5381step0 raw5381; decide +kernel
      have hl : raw5381step0Labels = raw5381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5381 raw5381Labels permutation265 hz
    mixedMoment B raw5381step0 raw5381step0Labels = mixedMoment B raw5381step1 raw5381step1Labels := by
      have ha : raw5381step1 = (fun i j => raw5381step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5381step1 raw5381step0; decide +kernel
      have hl : raw5381step1Labels = raw5381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5381step0 raw5381step0Labels permutation40 permutation3
    _ = mixedMoment B node2108 node2108Labels := by rfl

def raw5382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw5382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5382 raw5382Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw5382 raw5382Labels = mixedMoment B raw5382step0 raw5382step0Labels := by
      have hz : ∀ j, raw5382 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5382step0 = (fun i j => raw5382 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5382step0 raw5382; decide +kernel
      have hl : raw5382step0Labels = raw5382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5382 raw5382Labels permutation265 hz
    mixedMoment B raw5382step0 raw5382step0Labels = mixedMoment B raw5382step1 raw5382step1Labels := by
      have ha : raw5382step1 = (fun i j => raw5382step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5382step1 raw5382step0; decide +kernel
      have hl : raw5382step1Labels = raw5382step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5382step0 raw5382step0Labels permutation46 permutation3
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw5383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5383 raw5383Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw5383 raw5383Labels = mixedMoment B raw5383step0 raw5383step0Labels := by
      have hz : ∀ j, raw5383 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5383step0 = (fun i j => raw5383 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5383step0 raw5383; decide +kernel
      have hl : raw5383step0Labels = raw5383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5383 raw5383Labels permutation265 hz
    mixedMoment B raw5383step0 raw5383step0Labels = mixedMoment B raw5383step1 raw5383step1Labels := by
      have ha : raw5383step1 = (fun i j => raw5383step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5383step1 raw5383step0; decide +kernel
      have hl : raw5383step1Labels = raw5383step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5383step0 raw5383step0Labels permutation43 permutation3
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw5384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5384 raw5384Labels = mixedMoment B node808 node808Labels := by
  calc
    mixedMoment B raw5384 raw5384Labels = mixedMoment B raw5384step0 raw5384step0Labels := by
      have hz : ∀ j, raw5384 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5384step0 = (fun i j => raw5384 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5384step0 raw5384; decide +kernel
      have hl : raw5384step0Labels = raw5384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5384 raw5384Labels permutation265 hz
    mixedMoment B raw5384step0 raw5384step0Labels = mixedMoment B raw5384step1 raw5384step1Labels := by
      have ha : raw5384step1 = (fun i j => raw5384step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5384step1 raw5384step0; decide +kernel
      have hl : raw5384step1Labels = raw5384step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5384step0 raw5384step0Labels permutation34 permutation3
    _ = mixedMoment B node808 node808Labels := by rfl

def raw5385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5385 raw5385Labels = mixedMoment B node1910 node1910Labels := by
  calc
    mixedMoment B raw5385 raw5385Labels = mixedMoment B raw5385step0 raw5385step0Labels := by
      have ha : raw5385step0 = (fun i j => raw5385 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5385step0 raw5385; decide +kernel
      have hl : raw5385step0Labels = raw5385Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5385 raw5385Labels permutation154 permutation3
    _ = mixedMoment B node1910 node1910Labels := by rfl

def raw5386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5386 raw5386Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw5386 raw5386Labels = mixedMoment B raw5386step0 raw5386step0Labels := by
      have hz : ∀ j, raw5386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5386step0 = (fun i j => raw5386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5386step0 raw5386; decide +kernel
      have hl : raw5386step0Labels = raw5386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5386 raw5386Labels permutation265 hz
    mixedMoment B raw5386step0 raw5386step0Labels = mixedMoment B raw5386step1 raw5386step1Labels := by
      have ha : raw5386step1 = (fun i j => raw5386step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5386step1 raw5386step0; decide +kernel
      have hl : raw5386step1Labels = raw5386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5386step0 raw5386step0Labels permutation34 permutation3
    _ = mixedMoment B node2055 node2055Labels := by rfl

def raw5387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5387 raw5387Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw5387 raw5387Labels = mixedMoment B raw5387step0 raw5387step0Labels := by
      have hz : ∀ j, raw5387 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5387step0 = (fun i j => raw5387 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5387step0 raw5387; decide +kernel
      have hl : raw5387step0Labels = raw5387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5387 raw5387Labels permutation265 hz
    mixedMoment B raw5387step0 raw5387step0Labels = mixedMoment B raw5387step1 raw5387step1Labels := by
      have ha : raw5387step1 = (fun i j => raw5387step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5387step1 raw5387step0; decide +kernel
      have hl : raw5387step1Labels = raw5387step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5387step0 raw5387step0Labels permutation44 permutation3
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw5388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw5388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5388 raw5388Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw5388 raw5388Labels = mixedMoment B raw5388step0 raw5388step0Labels := by
      have hz : ∀ j, raw5388 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5388step0 = (fun i j => raw5388 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5388step0 raw5388; decide +kernel
      have hl : raw5388step0Labels = raw5388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5388 raw5388Labels permutation265 hz
    mixedMoment B raw5388step0 raw5388step0Labels = mixedMoment B raw5388step1 raw5388step1Labels := by
      have ha : raw5388step1 = (fun i j => raw5388step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5388step1 raw5388step0; decide +kernel
      have hl : raw5388step1Labels = raw5388step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5388step0 raw5388step0Labels permutation37 permutation3
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw5389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5389 raw5389Labels = mixedMoment B node796 node796Labels := by
  calc
    mixedMoment B raw5389 raw5389Labels = mixedMoment B raw5389step0 raw5389step0Labels := by
      have hz : ∀ j, raw5389 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5389step0 = (fun i j => raw5389 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5389step0 raw5389; decide +kernel
      have hl : raw5389step0Labels = raw5389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5389 raw5389Labels permutation265 hz
    mixedMoment B raw5389step0 raw5389step0Labels = mixedMoment B raw5389step1 raw5389step1Labels := by
      have ha : raw5389step1 = (fun i j => raw5389step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5389step1 raw5389step0; decide +kernel
      have hl : raw5389step1Labels = raw5389step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5389step0 raw5389step0Labels permutation33 permutation3
    _ = mixedMoment B node796 node796Labels := by rfl

def raw5390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5390 raw5390Labels = mixedMoment B node1904 node1904Labels := by
  calc
    mixedMoment B raw5390 raw5390Labels = mixedMoment B raw5390step0 raw5390step0Labels := by
      have ha : raw5390step0 = (fun i j => raw5390 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5390step0 raw5390; decide +kernel
      have hl : raw5390step0Labels = raw5390Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5390 raw5390Labels permutation153 permutation3
    _ = mixedMoment B node1904 node1904Labels := by rfl

def raw5391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5391 raw5391Labels = mixedMoment B node2039 node2039Labels := by
  calc
    mixedMoment B raw5391 raw5391Labels = mixedMoment B raw5391step0 raw5391step0Labels := by
      have hz : ∀ j, raw5391 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5391step0 = (fun i j => raw5391 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5391step0 raw5391; decide +kernel
      have hl : raw5391step0Labels = raw5391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5391 raw5391Labels permutation265 hz
    mixedMoment B raw5391step0 raw5391step0Labels = mixedMoment B raw5391step1 raw5391step1Labels := by
      have ha : raw5391step1 = (fun i j => raw5391step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5391step1 raw5391step0; decide +kernel
      have hl : raw5391step1Labels = raw5391step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5391step0 raw5391step0Labels permutation33 permutation3
    _ = mixedMoment B node2039 node2039Labels := by rfl

def raw5392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5392 raw5392Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw5392 raw5392Labels = mixedMoment B raw5392step0 raw5392step0Labels := by
      have hz : ∀ j, raw5392 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5392step0 = (fun i j => raw5392 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5392step0 raw5392; decide +kernel
      have hl : raw5392step0Labels = raw5392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5392 raw5392Labels permutation265 hz
    mixedMoment B raw5392step0 raw5392step0Labels = mixedMoment B raw5392step1 raw5392step1Labels := by
      have ha : raw5392step1 = (fun i j => raw5392step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5392step1 raw5392step0; decide +kernel
      have hl : raw5392step1Labels = raw5392step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5392step0 raw5392step0Labels permutation39 permutation3
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw5393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw5393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw5393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw5393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5393 raw5393Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw5393 raw5393Labels = mixedMoment B raw5393step0 raw5393step0Labels := by
      have hz : ∀ j, raw5393 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5393step0 = (fun i j => raw5393 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5393step0 raw5393; decide +kernel
      have hl : raw5393step0Labels = raw5393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5393 raw5393Labels permutation265 hz
    mixedMoment B raw5393step0 raw5393step0Labels = mixedMoment B raw5393step1 raw5393step1Labels := by
      have ha : raw5393step1 = (fun i j => raw5393step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5393step1 raw5393step0; decide +kernel
      have hl : raw5393step1Labels = raw5393step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5393step0 raw5393step0Labels permutation33 permutation3
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw5394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5394 raw5394Labels = mixedMoment B node794 node794Labels := by
  calc
    mixedMoment B raw5394 raw5394Labels = mixedMoment B raw5394step0 raw5394step0Labels := by
      have hz : ∀ j, raw5394 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5394step0 = (fun i j => raw5394 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5394step0 raw5394; decide +kernel
      have hl : raw5394step0Labels = raw5394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5394 raw5394Labels permutation265 hz
    mixedMoment B raw5394step0 raw5394step0Labels = mixedMoment B raw5394step1 raw5394step1Labels := by
      have ha : raw5394step1 = (fun i j => raw5394step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5394step1 raw5394step0; decide +kernel
      have hl : raw5394step1Labels = raw5394step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5394step0 raw5394step0Labels permutation32 permutation3
    _ = mixedMoment B node794 node794Labels := by rfl

def raw5395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5395 raw5395Labels = mixedMoment B node1902 node1902Labels := by
  calc
    mixedMoment B raw5395 raw5395Labels = mixedMoment B raw5395step0 raw5395step0Labels := by
      have ha : raw5395step0 = (fun i j => raw5395 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5395step0 raw5395; decide +kernel
      have hl : raw5395step0Labels = raw5395Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5395 raw5395Labels permutation152 permutation3
    _ = mixedMoment B node1902 node1902Labels := by rfl

def raw5396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5396 raw5396Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw5396 raw5396Labels = mixedMoment B raw5396step0 raw5396step0Labels := by
      have hz : ∀ j, raw5396 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5396step0 = (fun i j => raw5396 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5396step0 raw5396; decide +kernel
      have hl : raw5396step0Labels = raw5396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5396 raw5396Labels permutation265 hz
    mixedMoment B raw5396step0 raw5396step0Labels = mixedMoment B raw5396step1 raw5396step1Labels := by
      have ha : raw5396step1 = (fun i j => raw5396step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5396step1 raw5396step0; decide +kernel
      have hl : raw5396step1Labels = raw5396step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5396step0 raw5396step0Labels permutation32 permutation3
    _ = mixedMoment B node2035 node2035Labels := by rfl

def raw5397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5397 raw5397Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw5397 raw5397Labels = mixedMoment B raw5397step0 raw5397step0Labels := by
      have hz : ∀ j, raw5397 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5397step0 = (fun i j => raw5397 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5397step0 raw5397; decide +kernel
      have hl : raw5397step0Labels = raw5397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5397 raw5397Labels permutation265 hz
    mixedMoment B raw5397step0 raw5397step0Labels = mixedMoment B raw5397step1 raw5397step1Labels := by
      have ha : raw5397step1 = (fun i j => raw5397step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5397step1 raw5397step0; decide +kernel
      have hl : raw5397step1Labels = raw5397step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5397step0 raw5397step0Labels permutation38 permutation3
    _ = mixedMoment B node2090 node2090Labels := by rfl

def raw5398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw5398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw5398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw5398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5398 raw5398Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw5398 raw5398Labels = mixedMoment B raw5398step0 raw5398step0Labels := by
      have hz : ∀ j, raw5398 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5398step0 = (fun i j => raw5398 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5398step0 raw5398; decide +kernel
      have hl : raw5398step0Labels = raw5398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5398 raw5398Labels permutation265 hz
    mixedMoment B raw5398step0 raw5398step0Labels = mixedMoment B raw5398step1 raw5398step1Labels := by
      have ha : raw5398step1 = (fun i j => raw5398step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5398step1 raw5398step0; decide +kernel
      have hl : raw5398step1Labels = raw5398step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5398step0 raw5398step0Labels permutation44 permutation3
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw5399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5399 raw5399Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5399 raw5399Labels = mixedMoment B raw5399step0 raw5399step0Labels := by
      have hz : ∀ j, raw5399 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5399step0 = (fun i j => raw5399 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5399step0 raw5399; decide +kernel
      have hl : raw5399step0Labels = raw5399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5399 raw5399Labels permutation265 hz
    mixedMoment B raw5399step0 raw5399step0Labels = mixedMoment B raw5399step1 raw5399step1Labels := by
      have ha : raw5399step1 = (fun i j => raw5399step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5399step1 raw5399step0; decide +kernel
      have hl : raw5399step1Labels = raw5399step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5399step0 raw5399step0Labels permutation38 permutation2
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw5400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5400 raw5400Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw5400 raw5400Labels = mixedMoment B raw5400step0 raw5400step0Labels := by
      have ha : raw5400step0 = (fun i j => raw5400 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5400step0 raw5400; decide +kernel
      have hl : raw5400step0Labels = raw5400Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5400 raw5400Labels permutation682 permutation2
    mixedMoment B raw5400step0 raw5400step0Labels = mixedMoment B raw5400step1 raw5400step1Labels := by
      have ha : raw5400step1 = -raw5400step0 := by apply Matrix.ext; change ∀ i j, raw5400step1 i j = -(raw5400step0 i j); unfold raw5400step1 raw5400step0; decide +kernel
      have hl : raw5400step1Labels = raw5400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw5401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5401 raw5401Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw5401 raw5401Labels = mixedMoment B raw5401step0 raw5401step0Labels := by
      have hz : ∀ j, raw5401 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5401step0 = (fun i j => raw5401 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5401step0 raw5401; decide +kernel
      have hl : raw5401step0Labels = raw5401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5401 raw5401Labels permutation265 hz
    mixedMoment B raw5401step0 raw5401step0Labels = mixedMoment B raw5401step1 raw5401step1Labels := by
      have ha : raw5401step1 = (fun i j => raw5401step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5401step1 raw5401step0; decide +kernel
      have hl : raw5401step1Labels = raw5401step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5401step0 raw5401step0Labels permutation151 permutation2
    mixedMoment B raw5401step1 raw5401step1Labels = mixedMoment B raw5401step2 raw5401step2Labels := by
      have ha : raw5401step2 = -raw5401step1 := by apply Matrix.ext; change ∀ i j, raw5401step2 i j = -(raw5401step1 i j); unfold raw5401step2 raw5401step1; decide +kernel
      have hl : raw5401step2Labels = raw5401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw5402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw5402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5402 raw5402Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw5402 raw5402Labels = mixedMoment B raw5402step0 raw5402step0Labels := by
      have hz : ∀ j, raw5402 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5402step0 = (fun i j => raw5402 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5402step0 raw5402; decide +kernel
      have hl : raw5402step0Labels = raw5402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5402 raw5402Labels permutation265 hz
    mixedMoment B raw5402step0 raw5402step0Labels = mixedMoment B raw5402step1 raw5402step1Labels := by
      have ha : raw5402step1 = (fun i j => raw5402step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5402step1 raw5402step0; decide +kernel
      have hl : raw5402step1Labels = raw5402step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5402step0 raw5402step0Labels permutation149 permutation2
    mixedMoment B raw5402step1 raw5402step1Labels = mixedMoment B raw5402step2 raw5402step2Labels := by
      have ha : raw5402step2 = -raw5402step1 := by apply Matrix.ext; change ∀ i j, raw5402step2 i j = -(raw5402step1 i j); unfold raw5402step2 raw5402step1; decide +kernel
      have hl : raw5402step2Labels = raw5402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw5403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5403 raw5403Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw5403 raw5403Labels = mixedMoment B raw5403step0 raw5403step0Labels := by
      have hz : ∀ j, raw5403 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5403step0 = (fun i j => raw5403 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5403step0 raw5403; decide +kernel
      have hl : raw5403step0Labels = raw5403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5403 raw5403Labels permutation265 hz
    mixedMoment B raw5403step0 raw5403step0Labels = mixedMoment B raw5403step1 raw5403step1Labels := by
      have ha : raw5403step1 = (fun i j => raw5403step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5403step1 raw5403step0; decide +kernel
      have hl : raw5403step1Labels = raw5403step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5403step0 raw5403step0Labels permutation91 permutation4
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw5404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5404 raw5404Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw5404 raw5404Labels = mixedMoment B raw5404step0 raw5404step0Labels := by
      have hz : ∀ j, raw5404 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5404step0 = (fun i j => raw5404 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5404step0 raw5404; decide +kernel
      have hl : raw5404step0Labels = raw5404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5404 raw5404Labels permutation265 hz
    mixedMoment B raw5404step0 raw5404step0Labels = mixedMoment B raw5404step1 raw5404step1Labels := by
      have ha : raw5404step1 = (fun i j => raw5404step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5404step1 raw5404step0; decide +kernel
      have hl : raw5404step1Labels = raw5404step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5404step0 raw5404step0Labels permutation89 permutation4
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw5405 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw5405Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5405step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw5405step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5405step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw5405step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5405step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw5405step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5405 raw5405Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw5405 raw5405Labels = mixedMoment B raw5405step0 raw5405step0Labels := by
      have hz : ∀ j, raw5405 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5405step0 = (fun i j => raw5405 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5405step0 raw5405; decide +kernel
      have hl : raw5405step0Labels = raw5405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5405 raw5405Labels permutation265 hz
    mixedMoment B raw5405step0 raw5405step0Labels = mixedMoment B raw5405step1 raw5405step1Labels := by
      have hz : ∀ j, raw5405step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw5405step1 = (fun i j => raw5405step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw5405step1 raw5405step0; decide +kernel
      have hl : raw5405step1Labels = raw5405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5405step0 raw5405step0Labels permutation32 hz
    mixedMoment B raw5405step1 raw5405step1Labels = mixedMoment B raw5405step2 raw5405step2Labels := by
      have ha : raw5405step2 = (fun i j => raw5405step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5405step2 raw5405step1; decide +kernel
      have hl : raw5405step2Labels = raw5405step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5405step1 raw5405step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw5406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5406 raw5406Labels = mixedMoment B node1463 node1463Labels := by
  calc
    mixedMoment B raw5406 raw5406Labels = mixedMoment B raw5406step0 raw5406step0Labels := by
      have ha : raw5406step0 = (fun i j => raw5406 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5406step0 raw5406; decide +kernel
      have hl : raw5406step0Labels = raw5406Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5406 raw5406Labels permutation206 permutation2
    _ = mixedMoment B node1463 node1463Labels := by rfl

def raw5407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw5407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5407 raw5407Labels = mixedMoment B node1466 node1466Labels := by
  calc
    mixedMoment B raw5407 raw5407Labels = mixedMoment B raw5407step0 raw5407step0Labels := by
      have hz : ∀ j, raw5407 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5407step0 = (fun i j => raw5407 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5407step0 raw5407; decide +kernel
      have hl : raw5407step0Labels = raw5407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5407 raw5407Labels permutation265 hz
    mixedMoment B raw5407step0 raw5407step0Labels = mixedMoment B raw5407step1 raw5407step1Labels := by
      have ha : raw5407step1 = (fun i j => raw5407step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5407step1 raw5407step0; decide +kernel
      have hl : raw5407step1Labels = raw5407step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5407step0 raw5407step0Labels permutation54 permutation4
    mixedMoment B raw5407step1 raw5407step1Labels = mixedMoment B raw5407step2 raw5407step2Labels := by
      have ha : raw5407step2 = -raw5407step1 := by apply Matrix.ext; change ∀ i j, raw5407step2 i j = -(raw5407step1 i j); unfold raw5407step2 raw5407step1; decide +kernel
      have hl : raw5407step2Labels = raw5407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1466 node1466Labels := by rfl

def raw5408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw5408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5408 raw5408Labels = mixedMoment B node1465 node1465Labels := by
  calc
    mixedMoment B raw5408 raw5408Labels = mixedMoment B raw5408step0 raw5408step0Labels := by
      have hz : ∀ j, raw5408 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5408step0 = (fun i j => raw5408 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5408step0 raw5408; decide +kernel
      have hl : raw5408step0Labels = raw5408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5408 raw5408Labels permutation265 hz
    mixedMoment B raw5408step0 raw5408step0Labels = mixedMoment B raw5408step1 raw5408step1Labels := by
      have ha : raw5408step1 = (fun i j => raw5408step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5408step1 raw5408step0; decide +kernel
      have hl : raw5408step1Labels = raw5408step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5408step0 raw5408step0Labels permutation54 permutation4
    mixedMoment B raw5408step1 raw5408step1Labels = mixedMoment B raw5408step2 raw5408step2Labels := by
      have ha : raw5408step2 = -raw5408step1 := by apply Matrix.ext; change ∀ i j, raw5408step2 i j = -(raw5408step1 i j); unfold raw5408step2 raw5408step1; decide +kernel
      have hl : raw5408step2Labels = raw5408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1465 node1465Labels := by rfl

def raw5409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5409 raw5409Labels = mixedMoment B node1466 node1466Labels := by
  calc
    mixedMoment B raw5409 raw5409Labels = mixedMoment B raw5409step0 raw5409step0Labels := by
      have hz : ∀ j, raw5409 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5409step0 = (fun i j => raw5409 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5409step0 raw5409; decide +kernel
      have hl : raw5409step0Labels = raw5409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5409 raw5409Labels permutation265 hz
    mixedMoment B raw5409step0 raw5409step0Labels = mixedMoment B raw5409step1 raw5409step1Labels := by
      have ha : raw5409step1 = (fun i j => raw5409step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5409step1 raw5409step0; decide +kernel
      have hl : raw5409step1Labels = raw5409step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5409step0 raw5409step0Labels permutation38 permutation2
    _ = mixedMoment B node1466 node1466Labels := by rfl

def raw5410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5410 raw5410Labels = mixedMoment B node1465 node1465Labels := by
  calc
    mixedMoment B raw5410 raw5410Labels = mixedMoment B raw5410step0 raw5410step0Labels := by
      have hz : ∀ j, raw5410 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5410step0 = (fun i j => raw5410 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5410step0 raw5410; decide +kernel
      have hl : raw5410step0Labels = raw5410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5410 raw5410Labels permutation265 hz
    mixedMoment B raw5410step0 raw5410step0Labels = mixedMoment B raw5410step1 raw5410step1Labels := by
      have ha : raw5410step1 = (fun i j => raw5410step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5410step1 raw5410step0; decide +kernel
      have hl : raw5410step1Labels = raw5410step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5410step0 raw5410step0Labels permutation38 permutation2
    _ = mixedMoment B node1465 node1465Labels := by rfl

def raw5411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5411 raw5411Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw5411 raw5411Labels = mixedMoment B raw5411step0 raw5411step0Labels := by
      have ha : raw5411step0 = (fun i j => raw5411 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5411step0 raw5411; decide +kernel
      have hl : raw5411step0Labels = raw5411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5411 raw5411Labels permutation182 permutation2
    _ = mixedMoment B node3196 node3196Labels := by rfl

def raw5412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5412 raw5412Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw5412 raw5412Labels = mixedMoment B raw5412step0 raw5412step0Labels := by
      have ha : raw5412step0 = (fun i j => raw5412 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5412step0 raw5412; decide +kernel
      have hl : raw5412step0Labels = raw5412Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5412 raw5412Labels permutation206 permutation2
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw5413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5413 raw5413Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw5413 raw5413Labels = mixedMoment B raw5413step0 raw5413step0Labels := by
      have ha : raw5413step0 = (fun i j => raw5413 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5413step0 raw5413; decide +kernel
      have hl : raw5413step0Labels = raw5413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5413 raw5413Labels permutation240 permutation4
    mixedMoment B raw5413step0 raw5413step0Labels = mixedMoment B raw5413step1 raw5413step1Labels := by
      have ha : raw5413step1 = -raw5413step0 := by apply Matrix.ext; change ∀ i j, raw5413step1 i j = -(raw5413step0 i j); unfold raw5413step1 raw5413step0; decide +kernel
      have hl : raw5413step1Labels = raw5413step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3196 node3196Labels := by rfl

def raw5414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5414 raw5414Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw5414 raw5414Labels = mixedMoment B raw5414step0 raw5414step0Labels := by
      have ha : raw5414step0 = (fun i j => raw5414 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5414step0 raw5414; decide +kernel
      have hl : raw5414step0Labels = raw5414Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5414 raw5414Labels permutation260 permutation4
    mixedMoment B raw5414step0 raw5414step0Labels = mixedMoment B raw5414step1 raw5414step1Labels := by
      have ha : raw5414step1 = -raw5414step0 := by apply Matrix.ext; change ∀ i j, raw5414step1 i j = -(raw5414step0 i j); unfold raw5414step1 raw5414step0; decide +kernel
      have hl : raw5414step1Labels = raw5414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw5415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, -1, 0], ![0, 2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw5415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5415 raw5415Labels = mixedMoment B node3217 node3217Labels := by
  calc
    mixedMoment B raw5415 raw5415Labels = mixedMoment B raw5415step0 raw5415step0Labels := by
      have ha : raw5415step0 = (fun i j => raw5415 (permutation174 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5415step0 raw5415; decide +kernel
      have hl : raw5415step0Labels = raw5415Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5415 raw5415Labels permutation174 permutation4
    mixedMoment B raw5415step0 raw5415step0Labels = mixedMoment B raw5415step1 raw5415step1Labels := by
      have ha : raw5415step1 = -raw5415step0 := by apply Matrix.ext; change ∀ i j, raw5415step1 i j = -(raw5415step0 i j); unfold raw5415step1 raw5415step0; decide +kernel
      have hl : raw5415step1Labels = raw5415step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3217 node3217Labels := by rfl

def raw5416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5416 raw5416Labels = mixedMoment B node2474 node2474Labels := by
  calc
    mixedMoment B raw5416 raw5416Labels = mixedMoment B raw5416step0 raw5416step0Labels := by
      have ha : raw5416step0 = (fun i j => raw5416 (permutation480 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5416step0 raw5416; decide +kernel
      have hl : raw5416step0Labels = raw5416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5416 raw5416Labels permutation480 permutation4
    _ = mixedMoment B node2474 node2474Labels := by rfl

def raw5417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5417 raw5417Labels = mixedMoment B node3217 node3217Labels := by
  calc
    mixedMoment B raw5417 raw5417Labels = mixedMoment B raw5417step0 raw5417step0Labels := by
      have ha : raw5417step0 = (fun i j => raw5417 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5417step0 raw5417; decide +kernel
      have hl : raw5417step0Labels = raw5417Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5417 raw5417Labels permutation158 permutation2
    _ = mixedMoment B node3217 node3217Labels := by rfl

def raw5418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 3, 0]]
def raw5418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5418 raw5418Labels = mixedMoment B node2474 node2474Labels := by
  calc
    mixedMoment B raw5418 raw5418Labels = mixedMoment B raw5418step0 raw5418step0Labels := by
      have ha : raw5418step0 = (fun i j => raw5418 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5418step0 raw5418; decide +kernel
      have hl : raw5418step0Labels = raw5418Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5418 raw5418Labels permutation682 permutation2
    mixedMoment B raw5418step0 raw5418step0Labels = mixedMoment B raw5418step1 raw5418step1Labels := by
      have ha : raw5418step1 = -raw5418step0 := by apply Matrix.ext; change ∀ i j, raw5418step1 i j = -(raw5418step0 i j); unfold raw5418step1 raw5418step0; decide +kernel
      have hl : raw5418step1Labels = raw5418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2474 node2474Labels := by rfl

def raw5419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5419 raw5419Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw5419 raw5419Labels = mixedMoment B raw5419step0 raw5419step0Labels := by
      have hz : ∀ j, raw5419 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5419step0 = (fun i j => raw5419 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5419step0 raw5419; decide +kernel
      have hl : raw5419step0Labels = raw5419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5419 raw5419Labels permutation265 hz
    mixedMoment B raw5419step0 raw5419step0Labels = mixedMoment B raw5419step1 raw5419step1Labels := by
      have ha : raw5419step1 = (fun i j => raw5419step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5419step1 raw5419step0; decide +kernel
      have hl : raw5419step1Labels = raw5419step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5419step0 raw5419step0Labels permutation38 permutation2
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw5420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw5420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5420 raw5420Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw5420 raw5420Labels = mixedMoment B raw5420step0 raw5420step0Labels := by
      have hz : ∀ j, raw5420 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5420step0 = (fun i j => raw5420 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5420step0 raw5420; decide +kernel
      have hl : raw5420step0Labels = raw5420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5420 raw5420Labels permutation265 hz
    mixedMoment B raw5420step0 raw5420step0Labels = mixedMoment B raw5420step1 raw5420step1Labels := by
      have ha : raw5420step1 = (fun i j => raw5420step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5420step1 raw5420step0; decide +kernel
      have hl : raw5420step1Labels = raw5420step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5420step0 raw5420step0Labels permutation48 permutation4
    mixedMoment B raw5420step1 raw5420step1Labels = mixedMoment B raw5420step2 raw5420step2Labels := by
      have ha : raw5420step2 = -raw5420step1 := by apply Matrix.ext; change ∀ i j, raw5420step2 i j = -(raw5420step1 i j); unfold raw5420step2 raw5420step1; decide +kernel
      have hl : raw5420step2Labels = raw5420step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3198 node3198Labels := by rfl

def raw5421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw5421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5421 raw5421Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw5421 raw5421Labels = mixedMoment B raw5421step0 raw5421step0Labels := by
      have hz : ∀ j, raw5421 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5421step0 = (fun i j => raw5421 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5421step0 raw5421; decide +kernel
      have hl : raw5421step0Labels = raw5421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5421 raw5421Labels permutation265 hz
    mixedMoment B raw5421step0 raw5421step0Labels = mixedMoment B raw5421step1 raw5421step1Labels := by
      have ha : raw5421step1 = (fun i j => raw5421step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5421step1 raw5421step0; decide +kernel
      have hl : raw5421step1Labels = raw5421step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5421step0 raw5421step0Labels permutation54 permutation4
    mixedMoment B raw5421step1 raw5421step1Labels = mixedMoment B raw5421step2 raw5421step2Labels := by
      have ha : raw5421step2 = -raw5421step1 := by apply Matrix.ext; change ∀ i j, raw5421step2 i j = -(raw5421step1 i j); unfold raw5421step2 raw5421step1; decide +kernel
      have hl : raw5421step2Labels = raw5421step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3174 node3174Labels := by rfl

def raw5422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5422 raw5422Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw5422 raw5422Labels = mixedMoment B raw5422step0 raw5422step0Labels := by
      have hz : ∀ j, raw5422 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5422step0 = (fun i j => raw5422 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5422step0 raw5422; decide +kernel
      have hl : raw5422step0Labels = raw5422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5422 raw5422Labels permutation265 hz
    mixedMoment B raw5422step0 raw5422step0Labels = mixedMoment B raw5422step1 raw5422step1Labels := by
      have ha : raw5422step1 = (fun i j => raw5422step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5422step1 raw5422step0; decide +kernel
      have hl : raw5422step1Labels = raw5422step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5422step0 raw5422step0Labels permutation89 permutation4
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw5423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5423 raw5423Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw5423 raw5423Labels = mixedMoment B raw5423step0 raw5423step0Labels := by
      have hz : ∀ j, raw5423 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5423step0 = (fun i j => raw5423 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5423step0 raw5423; decide +kernel
      have hl : raw5423step0Labels = raw5423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5423 raw5423Labels permutation265 hz
    _ = mixedMoment B node3198 node3198Labels := by rfl

def raw5424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw5424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw5424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5424 raw5424Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw5424 raw5424Labels = mixedMoment B raw5424step0 raw5424step0Labels := by
      have hz : ∀ j, raw5424 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5424step0 = (fun i j => raw5424 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5424step0 raw5424; decide +kernel
      have hl : raw5424step0Labels = raw5424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5424 raw5424Labels permutation265 hz
    mixedMoment B raw5424step0 raw5424step0Labels = mixedMoment B raw5424step1 raw5424step1Labels := by
      have ha : raw5424step1 = (fun i j => raw5424step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5424step1 raw5424step0; decide +kernel
      have hl : raw5424step1Labels = raw5424step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5424step0 raw5424step0Labels permutation151 permutation2
    mixedMoment B raw5424step1 raw5424step1Labels = mixedMoment B raw5424step2 raw5424step2Labels := by
      have ha : raw5424step2 = -raw5424step1 := by apply Matrix.ext; change ∀ i j, raw5424step2 i j = -(raw5424step1 i j); unfold raw5424step2 raw5424step1; decide +kernel
      have hl : raw5424step2Labels = raw5424step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw5425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw5425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5425 raw5425Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw5425 raw5425Labels = mixedMoment B raw5425step0 raw5425step0Labels := by
      have hz : ∀ j, raw5425 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5425step0 = (fun i j => raw5425 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5425step0 raw5425; decide +kernel
      have hl : raw5425step0Labels = raw5425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5425 raw5425Labels permutation265 hz
    mixedMoment B raw5425step0 raw5425step0Labels = mixedMoment B raw5425step1 raw5425step1Labels := by
      have ha : raw5425step1 = (fun i j => raw5425step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5425step1 raw5425step0; decide +kernel
      have hl : raw5425step1Labels = raw5425step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5425step0 raw5425step0Labels permutation91 permutation4
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw5426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5426 raw5426Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw5426 raw5426Labels = mixedMoment B raw5426step0 raw5426step0Labels := by
      have hz : ∀ j, raw5426 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5426step0 = (fun i j => raw5426 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5426step0 raw5426; decide +kernel
      have hl : raw5426step0Labels = raw5426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5426 raw5426Labels permutation265 hz
    mixedMoment B raw5426step0 raw5426step0Labels = mixedMoment B raw5426step1 raw5426step1Labels := by
      have ha : raw5426step1 = (fun i j => raw5426step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5426step1 raw5426step0; decide +kernel
      have hl : raw5426step1Labels = raw5426step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5426step0 raw5426step0Labels permutation89 permutation4
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw5427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw5427step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5427step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5427step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5427 raw5427Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw5427 raw5427Labels = mixedMoment B raw5427step0 raw5427step0Labels := by
      have ha : raw5427step0 = (fun i j => raw5427 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5427step0 raw5427; decide +kernel
      have hl : raw5427step0Labels = raw5427Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5427 raw5427Labels permutation240 permutation7
    mixedMoment B raw5427step0 raw5427step0Labels = mixedMoment B raw5427step1 raw5427step1Labels := by
      have ha : raw5427step1 = -raw5427step0 := by apply Matrix.ext; change ∀ i j, raw5427step1 i j = -(raw5427step0 i j); unfold raw5427step1 raw5427step0; decide +kernel
      have hl : raw5427step1Labels = raw5427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5427step1 raw5427step1Labels = mixedMoment B raw5427step2 raw5427step2Labels := by
      have ha : raw5427step2 = raw5427step1 := by apply Matrix.ext; unfold raw5427step2 raw5427step1; decide +kernel
      have hl : raw5427step1Labels = labelEmbedding10 ∘ raw5427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5427step1 raw5427step1Labels raw5427step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw5428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw5428step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5428step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5428step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5428 raw5428Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw5428 raw5428Labels = mixedMoment B raw5428step0 raw5428step0Labels := by
      have ha : raw5428step0 = (fun i j => raw5428 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5428step0 raw5428; decide +kernel
      have hl : raw5428step0Labels = raw5428Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5428 raw5428Labels permutation242 permutation7
    mixedMoment B raw5428step0 raw5428step0Labels = mixedMoment B raw5428step1 raw5428step1Labels := by
      have ha : raw5428step1 = -raw5428step0 := by apply Matrix.ext; change ∀ i j, raw5428step1 i j = -(raw5428step0 i j); unfold raw5428step1 raw5428step0; decide +kernel
      have hl : raw5428step1Labels = raw5428step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5428step1 raw5428step1Labels = mixedMoment B raw5428step2 raw5428step2Labels := by
      have ha : raw5428step2 = raw5428step1 := by apply Matrix.ext; unfold raw5428step2 raw5428step1; decide +kernel
      have hl : raw5428step1Labels = labelEmbedding10 ∘ raw5428step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5428step1 raw5428step1Labels raw5428step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw5429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw5429step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5429step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5429step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5429 raw5429Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw5429 raw5429Labels = mixedMoment B raw5429step0 raw5429step0Labels := by
      have ha : raw5429step0 = (fun i j => raw5429 (permutation244 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5429step0 raw5429; decide +kernel
      have hl : raw5429step0Labels = raw5429Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5429 raw5429Labels permutation244 permutation7
    mixedMoment B raw5429step0 raw5429step0Labels = mixedMoment B raw5429step1 raw5429step1Labels := by
      have ha : raw5429step1 = -raw5429step0 := by apply Matrix.ext; change ∀ i j, raw5429step1 i j = -(raw5429step0 i j); unfold raw5429step1 raw5429step0; decide +kernel
      have hl : raw5429step1Labels = raw5429step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5429step1 raw5429step1Labels = mixedMoment B raw5429step2 raw5429step2Labels := by
      have ha : raw5429step2 = raw5429step1 := by apply Matrix.ext; unfold raw5429step2 raw5429step1; decide +kernel
      have hl : raw5429step1Labels = labelEmbedding10 ∘ raw5429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5429step1 raw5429step1Labels raw5429step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw5430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5430step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5430step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5430step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5430step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5430 raw5430Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw5430 raw5430Labels = mixedMoment B raw5430step0 raw5430step0Labels := by
      have hz : ∀ j, raw5430 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5430step0 = (fun i j => raw5430 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5430step0 raw5430; decide +kernel
      have hl : raw5430step0Labels = raw5430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5430 raw5430Labels permutation520 hz
    mixedMoment B raw5430step0 raw5430step0Labels = mixedMoment B raw5430step1 raw5430step1Labels := by
      have ha : raw5430step1 = (fun i j => raw5430step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5430step1 raw5430step0; decide +kernel
      have hl : raw5430step1Labels = raw5430step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5430step0 raw5430step0Labels permutation50 permutation7
    mixedMoment B raw5430step1 raw5430step1Labels = mixedMoment B raw5430step2 raw5430step2Labels := by
      have ha : raw5430step2 = -raw5430step1 := by apply Matrix.ext; change ∀ i j, raw5430step2 i j = -(raw5430step1 i j); unfold raw5430step2 raw5430step1; decide +kernel
      have hl : raw5430step2Labels = raw5430step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5430step2 raw5430step2Labels = mixedMoment B raw5430step3 raw5430step3Labels := by
      have ha : raw5430step3 = raw5430step2 := by apply Matrix.ext; unfold raw5430step3 raw5430step2; decide +kernel
      have hl : raw5430step2Labels = labelEmbedding10 ∘ raw5430step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5430step2 raw5430step2Labels raw5430step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw5431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5431step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5431step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5431step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5431step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5431 raw5431Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw5431 raw5431Labels = mixedMoment B raw5431step0 raw5431step0Labels := by
      have ha : raw5431step0 = (fun i j => raw5431 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5431step0 raw5431; decide +kernel
      have hl : raw5431step0Labels = raw5431Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5431 raw5431Labels permutation240 permutation7
    mixedMoment B raw5431step0 raw5431step0Labels = mixedMoment B raw5431step1 raw5431step1Labels := by
      have ha : raw5431step1 = -raw5431step0 := by apply Matrix.ext; change ∀ i j, raw5431step1 i j = -(raw5431step0 i j); unfold raw5431step1 raw5431step0; decide +kernel
      have hl : raw5431step1Labels = raw5431step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5431step1 raw5431step1Labels = mixedMoment B raw5431step2 raw5431step2Labels := by
      have ha : raw5431step2 = raw5431step1 := by apply Matrix.ext; unfold raw5431step2 raw5431step1; decide +kernel
      have hl : raw5431step1Labels = labelEmbedding10 ∘ raw5431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5431step1 raw5431step1Labels raw5431step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5283 node5283Labels := by rfl

def raw5432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5432 raw5432Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw5432 raw5432Labels = mixedMoment B raw5432step0 raw5432step0Labels := by
      have ha : raw5432step0 = (fun i j => raw5432 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5432step0 raw5432; decide +kernel
      have hl : raw5432step0Labels = raw5432Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5432 raw5432Labels permutation184 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw5433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5433 raw5433Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw5433 raw5433Labels = mixedMoment B raw5433step0 raw5433step0Labels := by
      have ha : raw5433step0 = (fun i j => raw5433 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5433step0 raw5433; decide +kernel
      have hl : raw5433step0Labels = raw5433Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5433 raw5433Labels permutation184 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw5434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5434 raw5434Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw5434 raw5434Labels = mixedMoment B raw5434step0 raw5434step0Labels := by
      have ha : raw5434step0 = (fun i j => raw5434 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5434step0 raw5434; decide +kernel
      have hl : raw5434step0Labels = raw5434Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5434 raw5434Labels permutation208 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw5435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5435 raw5435Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw5435 raw5435Labels = mixedMoment B raw5435step0 raw5435step0Labels := by
      have hz : ∀ j, raw5435 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5435step0 = (fun i j => raw5435 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5435step0 raw5435; decide +kernel
      have hl : raw5435step0Labels = raw5435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5435 raw5435Labels permutation520 hz
    mixedMoment B raw5435step0 raw5435step0Labels = mixedMoment B raw5435step1 raw5435step1Labels := by
      have ha : raw5435step1 = (fun i j => raw5435step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5435step1 raw5435step0; decide +kernel
      have hl : raw5435step1Labels = raw5435step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5435step0 raw5435step0Labels permutation40 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw5436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5436 raw5436Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw5436 raw5436Labels = mixedMoment B raw5436step0 raw5436step0Labels := by
      have ha : raw5436step0 = (fun i j => raw5436 (permutation185 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5436step0 raw5436; decide +kernel
      have hl : raw5436step0Labels = raw5436Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5436 raw5436Labels permutation185 permutation2
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw5437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5437 raw5437Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw5437 raw5437Labels = mixedMoment B raw5437step0 raw5437step0Labels := by
      have ha : raw5437step0 = (fun i j => raw5437 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5437step0 raw5437; decide +kernel
      have hl : raw5437step0Labels = raw5437Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5437 raw5437Labels permutation160 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw5438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5438 raw5438Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw5438 raw5438Labels = mixedMoment B raw5438step0 raw5438step0Labels := by
      have ha : raw5438step0 = (fun i j => raw5438 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5438step0 raw5438; decide +kernel
      have hl : raw5438step0Labels = raw5438Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5438 raw5438Labels permutation160 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw5439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5439 raw5439Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw5439 raw5439Labels = mixedMoment B raw5439step0 raw5439step0Labels := by
      have ha : raw5439step0 = (fun i j => raw5439 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5439step0 raw5439; decide +kernel
      have hl : raw5439step0Labels = raw5439Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5439 raw5439Labels permutation202 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw5440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5440 raw5440Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw5440 raw5440Labels = mixedMoment B raw5440step0 raw5440step0Labels := by
      have hz : ∀ j, raw5440 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5440step0 = (fun i j => raw5440 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5440step0 raw5440; decide +kernel
      have hl : raw5440step0Labels = raw5440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5440 raw5440Labels permutation520 hz
    mixedMoment B raw5440step0 raw5440step0Labels = mixedMoment B raw5440step1 raw5440step1Labels := by
      have ha : raw5440step1 = (fun i j => raw5440step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5440step1 raw5440step0; decide +kernel
      have hl : raw5440step1Labels = raw5440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5440step0 raw5440step0Labels permutation34 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw5441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5441 raw5441Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw5441 raw5441Labels = mixedMoment B raw5441step0 raw5441step0Labels := by
      have ha : raw5441step0 = (fun i j => raw5441 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5441step0 raw5441; decide +kernel
      have hl : raw5441step0Labels = raw5441Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5441 raw5441Labels permutation161 permutation2
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw5442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5442 raw5442Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw5442 raw5442Labels = mixedMoment B raw5442step0 raw5442step0Labels := by
      have ha : raw5442step0 = (fun i j => raw5442 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5442step0 raw5442; decide +kernel
      have hl : raw5442step0Labels = raw5442Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5442 raw5442Labels permutation154 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw5443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5443 raw5443Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw5443 raw5443Labels = mixedMoment B raw5443step0 raw5443step0Labels := by
      have ha : raw5443step0 = (fun i j => raw5443 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5443step0 raw5443; decide +kernel
      have hl : raw5443step0Labels = raw5443Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5443 raw5443Labels permutation154 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw5444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5444 raw5444Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw5444 raw5444Labels = mixedMoment B raw5444step0 raw5444step0Labels := by
      have ha : raw5444step0 = (fun i j => raw5444 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5444step0 raw5444; decide +kernel
      have hl : raw5444step0Labels = raw5444Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5444 raw5444Labels permutation178 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw5445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5445 raw5445Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw5445 raw5445Labels = mixedMoment B raw5445step0 raw5445step0Labels := by
      have hz : ∀ j, raw5445 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5445step0 = (fun i j => raw5445 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5445step0 raw5445; decide +kernel
      have hl : raw5445step0Labels = raw5445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5445 raw5445Labels permutation520 hz
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw5446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5446 raw5446Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw5446 raw5446Labels = mixedMoment B raw5446step0 raw5446step0Labels := by
      have ha : raw5446step0 = (fun i j => raw5446 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5446step0 raw5446; decide +kernel
      have hl : raw5446step0Labels = raw5446Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5446 raw5446Labels permutation155 permutation2
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw5447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5447 raw5447Labels = mixedMoment B node4434 node4434Labels := by
  calc
    _ = mixedMoment B node4434 node4434Labels := by rfl

def raw5448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5448 raw5448Labels = mixedMoment B node4847 node4847Labels := by
  calc
    _ = mixedMoment B node4847 node4847Labels := by rfl

def raw5449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5449 raw5449Labels = mixedMoment B node4847 node4847Labels := by
  calc
    mixedMoment B raw5449 raw5449Labels = mixedMoment B raw5449step0 raw5449step0Labels := by
      have ha : raw5449step0 = (fun i j => raw5449 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5449step0 raw5449; decide +kernel
      have hl : raw5449step0Labels = raw5449Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5449 raw5449Labels permutation176 permutation2
    _ = mixedMoment B node4847 node4847Labels := by rfl

def raw5450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5450 raw5450Labels = mixedMoment B node4847 node4847Labels := by
  calc
    mixedMoment B raw5450 raw5450Labels = mixedMoment B raw5450step0 raw5450step0Labels := by
      have ha : raw5450step0 = (fun i j => raw5450 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5450step0 raw5450; decide +kernel
      have hl : raw5450step0Labels = raw5450Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5450 raw5450Labels permutation200 permutation2
    _ = mixedMoment B node4847 node4847Labels := by rfl

def raw5451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw5451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5451 raw5451Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw5451 raw5451Labels = mixedMoment B raw5451step0 raw5451step0Labels := by
      have ha : raw5451step0 = (fun i j => raw5451 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5451step0 raw5451; decide +kernel
      have hl : raw5451step0Labels = raw5451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5451 raw5451Labels permutation153 permutation2
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw5452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5452 raw5452Labels = mixedMoment B node4433 node4433Labels := by
  calc
    _ = mixedMoment B node4433 node4433Labels := by rfl

def raw5453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw5453step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5453step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5453step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5453step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5453 raw5453Labels = mixedMoment B node4730 node4730Labels := by
  calc
    mixedMoment B raw5453 raw5453Labels = mixedMoment B raw5453step0 raw5453step0Labels := by
      have ha : raw5453step0 = (fun i j => raw5453 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5453step0 raw5453; decide +kernel
      have hl : raw5453step0Labels = raw5453Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5453 raw5453Labels permutation682 permutation3
    mixedMoment B raw5453step0 raw5453step0Labels = mixedMoment B raw5453step1 raw5453step1Labels := by
      have ha : raw5453step1 = -raw5453step0 := by apply Matrix.ext; change ∀ i j, raw5453step1 i j = -(raw5453step0 i j); unfold raw5453step1 raw5453step0; decide +kernel
      have hl : raw5453step1Labels = raw5453step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5453step1 raw5453step1Labels = mixedMoment B raw5453step2 raw5453step2Labels := by
      have ha : raw5453step2 = raw5453step1 := by apply Matrix.ext; unfold raw5453step2 raw5453step1; decide +kernel
      have hl : raw5453step1Labels = labelEmbedding6 ∘ raw5453step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5453step1 raw5453step1Labels raw5453step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4730 node4730Labels := by rfl

def raw5454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw5454step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5454step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5454step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5454step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5454 raw5454Labels = mixedMoment B node4730 node4730Labels := by
  calc
    mixedMoment B raw5454 raw5454Labels = mixedMoment B raw5454step0 raw5454step0Labels := by
      have ha : raw5454step0 = (fun i j => raw5454 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5454step0 raw5454; decide +kernel
      have hl : raw5454step0Labels = raw5454Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5454 raw5454Labels permutation676 permutation3
    mixedMoment B raw5454step0 raw5454step0Labels = mixedMoment B raw5454step1 raw5454step1Labels := by
      have ha : raw5454step1 = -raw5454step0 := by apply Matrix.ext; change ∀ i j, raw5454step1 i j = -(raw5454step0 i j); unfold raw5454step1 raw5454step0; decide +kernel
      have hl : raw5454step1Labels = raw5454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5454step1 raw5454step1Labels = mixedMoment B raw5454step2 raw5454step2Labels := by
      have ha : raw5454step2 = raw5454step1 := by apply Matrix.ext; unfold raw5454step2 raw5454step1; decide +kernel
      have hl : raw5454step1Labels = labelEmbedding6 ∘ raw5454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5454step1 raw5454step1Labels raw5454step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4730 node4730Labels := by rfl

def raw5455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw5455step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5455step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5455step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5455 raw5455Labels = mixedMoment B node4730 node4730Labels := by
  calc
    mixedMoment B raw5455 raw5455Labels = mixedMoment B raw5455step0 raw5455step0Labels := by
      have ha : raw5455step0 = (fun i j => raw5455 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5455step0 raw5455; decide +kernel
      have hl : raw5455step0Labels = raw5455Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5455 raw5455Labels permutation674 permutation3
    mixedMoment B raw5455step0 raw5455step0Labels = mixedMoment B raw5455step1 raw5455step1Labels := by
      have ha : raw5455step1 = -raw5455step0 := by apply Matrix.ext; change ∀ i j, raw5455step1 i j = -(raw5455step0 i j); unfold raw5455step1 raw5455step0; decide +kernel
      have hl : raw5455step1Labels = raw5455step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5455step1 raw5455step1Labels = mixedMoment B raw5455step2 raw5455step2Labels := by
      have ha : raw5455step2 = raw5455step1 := by apply Matrix.ext; unfold raw5455step2 raw5455step1; decide +kernel
      have hl : raw5455step1Labels = labelEmbedding6 ∘ raw5455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5455step1 raw5455step1Labels raw5455step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4730 node4730Labels := by rfl

def raw5456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw5456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5456 raw5456Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw5456 raw5456Labels = mixedMoment B raw5456step0 raw5456step0Labels := by
      have hz : ∀ j, raw5456 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5456step0 = (fun i j => raw5456 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5456step0 raw5456; decide +kernel
      have hl : raw5456step0Labels = raw5456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5456 raw5456Labels permutation520 hz
    _ = mixedMoment B node4886 node4886Labels := by rfl

def raw5457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw5457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw5457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5457 raw5457Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw5457 raw5457Labels = mixedMoment B raw5457step0 raw5457step0Labels := by
      have ha : raw5457step0 = (fun i j => raw5457 (permutation263 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5457step0 raw5457; decide +kernel
      have hl : raw5457step0Labels = raw5457Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5457 raw5457Labels permutation263 permutation6
    mixedMoment B raw5457step0 raw5457step0Labels = mixedMoment B raw5457step1 raw5457step1Labels := by
      have ha : raw5457step1 = -raw5457step0 := by apply Matrix.ext; change ∀ i j, raw5457step1 i j = -(raw5457step0 i j); unfold raw5457step1 raw5457step0; decide +kernel
      have hl : raw5457step1Labels = raw5457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw5458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw5458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw5458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5458 raw5458Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw5458 raw5458Labels = mixedMoment B raw5458step0 raw5458step0Labels := by
      have ha : raw5458step0 = (fun i j => raw5458 (permutation261 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5458step0 raw5458; decide +kernel
      have hl : raw5458step0Labels = raw5458Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5458 raw5458Labels permutation261 permutation6
    mixedMoment B raw5458step0 raw5458step0Labels = mixedMoment B raw5458step1 raw5458step1Labels := by
      have ha : raw5458step1 = -raw5458step0 := by apply Matrix.ext; change ∀ i j, raw5458step1 i j = -(raw5458step0 i j); unfold raw5458step1 raw5458step0; decide +kernel
      have hl : raw5458step1Labels = raw5458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw5459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw5459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw5459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5459 raw5459Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw5459 raw5459Labels = mixedMoment B raw5459step0 raw5459step0Labels := by
      have ha : raw5459step0 = (fun i j => raw5459 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5459step0 raw5459; decide +kernel
      have hl : raw5459step0Labels = raw5459Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5459 raw5459Labels permutation260 permutation6
    mixedMoment B raw5459step0 raw5459step0Labels = mixedMoment B raw5459step1 raw5459step1Labels := by
      have ha : raw5459step1 = -raw5459step0 := by apply Matrix.ext; change ∀ i j, raw5459step1 i j = -(raw5459step0 i j); unfold raw5459step1 raw5459step0; decide +kernel
      have hl : raw5459step1Labels = raw5459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw5460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5460step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5460 raw5460Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw5460 raw5460Labels = mixedMoment B raw5460step0 raw5460step0Labels := by
      have hz : ∀ j, raw5460 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5460step0 = (fun i j => raw5460 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5460step0 raw5460; decide +kernel
      have hl : raw5460step0Labels = raw5460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5460 raw5460Labels permutation520 hz
    mixedMoment B raw5460step0 raw5460step0Labels = mixedMoment B raw5460step1 raw5460step1Labels := by
      have ha : raw5460step1 = (fun i j => raw5460step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5460step1 raw5460step0; decide +kernel
      have hl : raw5460step1Labels = raw5460step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5460step0 raw5460step0Labels permutation50 permutation6
    mixedMoment B raw5460step1 raw5460step1Labels = mixedMoment B raw5460step2 raw5460step2Labels := by
      have ha : raw5460step2 = -raw5460step1 := by apply Matrix.ext; change ∀ i j, raw5460step2 i j = -(raw5460step1 i j); unfold raw5460step2 raw5460step1; decide +kernel
      have hl : raw5460step2Labels = raw5460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw5461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5461 raw5461Labels = mixedMoment B node3076 node3076Labels := by
  calc
    mixedMoment B raw5461 raw5461Labels = mixedMoment B raw5461step0 raw5461step0Labels := by
      have ha : raw5461step0 = (fun i j => raw5461 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5461step0 raw5461; decide +kernel
      have hl : raw5461step0Labels = raw5461Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5461 raw5461Labels permutation240 permutation6
    mixedMoment B raw5461step0 raw5461step0Labels = mixedMoment B raw5461step1 raw5461step1Labels := by
      have ha : raw5461step1 = -raw5461step0 := by apply Matrix.ext; change ∀ i j, raw5461step1 i j = -(raw5461step0 i j); unfold raw5461step1 raw5461step0; decide +kernel
      have hl : raw5461step1Labels = raw5461step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3076 node3076Labels := by rfl

def raw5462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5462 raw5462Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw5462 raw5462Labels = mixedMoment B raw5462step0 raw5462step0Labels := by
      have ha : raw5462step0 = (fun i j => raw5462 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5462step0 raw5462; decide +kernel
      have hl : raw5462step0Labels = raw5462Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5462 raw5462Labels permutation182 permutation3
    _ = mixedMoment B node1383 node1383Labels := by rfl

def raw5463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5463 raw5463Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw5463 raw5463Labels = mixedMoment B raw5463step0 raw5463step0Labels := by
      have ha : raw5463step0 = (fun i j => raw5463 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5463step0 raw5463; decide +kernel
      have hl : raw5463step0Labels = raw5463Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5463 raw5463Labels permutation182 permutation3
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw5464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5464 raw5464Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw5464 raw5464Labels = mixedMoment B raw5464step0 raw5464step0Labels := by
      have ha : raw5464step0 = (fun i j => raw5464 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5464step0 raw5464; decide +kernel
      have hl : raw5464step0Labels = raw5464Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5464 raw5464Labels permutation206 permutation3
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw5465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5465step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw5465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5465 raw5465Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw5465 raw5465Labels = mixedMoment B raw5465step0 raw5465step0Labels := by
      have hz : ∀ j, raw5465 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5465step0 = (fun i j => raw5465 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5465step0 raw5465; decide +kernel
      have hl : raw5465step0Labels = raw5465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5465 raw5465Labels permutation520 hz
    mixedMoment B raw5465step0 raw5465step0Labels = mixedMoment B raw5465step1 raw5465step1Labels := by
      have ha : raw5465step1 = (fun i j => raw5465step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5465step1 raw5465step0; decide +kernel
      have hl : raw5465step1Labels = raw5465step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5465step0 raw5465step0Labels permutation50 permutation6
    mixedMoment B raw5465step1 raw5465step1Labels = mixedMoment B raw5465step2 raw5465step2Labels := by
      have ha : raw5465step2 = -raw5465step1 := by apply Matrix.ext; change ∀ i j, raw5465step2 i j = -(raw5465step1 i j); unfold raw5465step2 raw5465step1; decide +kernel
      have hl : raw5465step2Labels = raw5465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw5466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5466 raw5466Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw5466 raw5466Labels = mixedMoment B raw5466step0 raw5466step0Labels := by
      have ha : raw5466step0 = (fun i j => raw5466 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5466step0 raw5466; decide +kernel
      have hl : raw5466step0Labels = raw5466Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5466 raw5466Labels permutation182 permutation3
    _ = mixedMoment B node3226 node3226Labels := by rfl

def raw5467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5467 raw5467Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw5467 raw5467Labels = mixedMoment B raw5467step0 raw5467step0Labels := by
      have ha : raw5467step0 = (fun i j => raw5467 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5467step0 raw5467; decide +kernel
      have hl : raw5467step0Labels = raw5467Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5467 raw5467Labels permutation158 permutation3
    _ = mixedMoment B node1383 node1383Labels := by rfl

def raw5468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5468 raw5468Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw5468 raw5468Labels = mixedMoment B raw5468step0 raw5468step0Labels := by
      have ha : raw5468step0 = (fun i j => raw5468 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5468step0 raw5468; decide +kernel
      have hl : raw5468step0Labels = raw5468Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5468 raw5468Labels permutation158 permutation3
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw5469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5469 raw5469Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw5469 raw5469Labels = mixedMoment B raw5469step0 raw5469step0Labels := by
      have ha : raw5469step0 = (fun i j => raw5469 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5469step0 raw5469; decide +kernel
      have hl : raw5469step0Labels = raw5469Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5469 raw5469Labels permutation200 permutation3
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw5470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5470step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw5470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5470 raw5470Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw5470 raw5470Labels = mixedMoment B raw5470step0 raw5470step0Labels := by
      have hz : ∀ j, raw5470 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5470step0 = (fun i j => raw5470 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5470step0 raw5470; decide +kernel
      have hl : raw5470step0Labels = raw5470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5470 raw5470Labels permutation520 hz
    mixedMoment B raw5470step0 raw5470step0Labels = mixedMoment B raw5470step1 raw5470step1Labels := by
      have ha : raw5470step1 = (fun i j => raw5470step0 (permutation52 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5470step1 raw5470step0; decide +kernel
      have hl : raw5470step1Labels = raw5470step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5470step0 raw5470step0Labels permutation52 permutation6
    mixedMoment B raw5470step1 raw5470step1Labels = mixedMoment B raw5470step2 raw5470step2Labels := by
      have ha : raw5470step2 = -raw5470step1 := by apply Matrix.ext; change ∀ i j, raw5470step2 i j = -(raw5470step1 i j); unfold raw5470step2 raw5470step1; decide +kernel
      have hl : raw5470step2Labels = raw5470step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw5471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5471Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5471 raw5471Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw5471 raw5471Labels = mixedMoment B raw5471step0 raw5471step0Labels := by
      have ha : raw5471step0 = (fun i j => raw5471 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5471step0 raw5471; decide +kernel
      have hl : raw5471step0Labels = raw5471Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5471 raw5471Labels permutation158 permutation3
    _ = mixedMoment B node3226 node3226Labels := by rfl

def raw5472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5472 raw5472Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw5472 raw5472Labels = mixedMoment B raw5472step0 raw5472step0Labels := by
      have ha : raw5472step0 = (fun i j => raw5472 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5472step0 raw5472; decide +kernel
      have hl : raw5472step0Labels = raw5472Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5472 raw5472Labels permutation152 permutation3
    _ = mixedMoment B node1383 node1383Labels := by rfl

def raw5473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5473 raw5473Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw5473 raw5473Labels = mixedMoment B raw5473step0 raw5473step0Labels := by
      have ha : raw5473step0 = (fun i j => raw5473 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5473step0 raw5473; decide +kernel
      have hl : raw5473step0Labels = raw5473Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5473 raw5473Labels permutation152 permutation3
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw5474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5474 raw5474Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw5474 raw5474Labels = mixedMoment B raw5474step0 raw5474step0Labels := by
      have ha : raw5474step0 = (fun i j => raw5474 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5474step0 raw5474; decide +kernel
      have hl : raw5474step0Labels = raw5474Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5474 raw5474Labels permutation176 permutation3
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw5475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5475step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw5475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5475 raw5475Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw5475 raw5475Labels = mixedMoment B raw5475step0 raw5475step0Labels := by
      have hz : ∀ j, raw5475 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5475step0 = (fun i j => raw5475 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5475step0 raw5475; decide +kernel
      have hl : raw5475step0Labels = raw5475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5475 raw5475Labels permutation520 hz
    mixedMoment B raw5475step0 raw5475step0Labels = mixedMoment B raw5475step1 raw5475step1Labels := by
      have ha : raw5475step1 = (fun i j => raw5475step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5475step1 raw5475step0; decide +kernel
      have hl : raw5475step1Labels = raw5475step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5475step0 raw5475step0Labels permutation54 permutation6
    mixedMoment B raw5475step1 raw5475step1Labels = mixedMoment B raw5475step2 raw5475step2Labels := by
      have ha : raw5475step2 = -raw5475step1 := by apply Matrix.ext; change ∀ i j, raw5475step2 i j = -(raw5475step1 i j); unfold raw5475step2 raw5475step1; decide +kernel
      have hl : raw5475step2Labels = raw5475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw5476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5476 raw5476Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw5476 raw5476Labels = mixedMoment B raw5476step0 raw5476step0Labels := by
      have ha : raw5476step0 = (fun i j => raw5476 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5476step0 raw5476; decide +kernel
      have hl : raw5476step0Labels = raw5476Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5476 raw5476Labels permutation152 permutation3
    _ = mixedMoment B node3226 node3226Labels := by rfl

def raw5477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw5477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5477 raw5477Labels = mixedMoment B node1377 node1377Labels := by
  calc
    mixedMoment B raw5477 raw5477Labels = mixedMoment B raw5477step0 raw5477step0Labels := by
      have ha : raw5477step0 = (fun i j => raw5477 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5477step0 raw5477; decide +kernel
      have hl : raw5477step0Labels = raw5477Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5477 raw5477Labels permutation152 permutation3
    _ = mixedMoment B node1377 node1377Labels := by rfl

def raw5478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw5478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5478 raw5478Labels = mixedMoment B node3167 node3167Labels := by
  calc
    mixedMoment B raw5478 raw5478Labels = mixedMoment B raw5478step0 raw5478step0Labels := by
      have ha : raw5478step0 = (fun i j => raw5478 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5478step0 raw5478; decide +kernel
      have hl : raw5478step0Labels = raw5478Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5478 raw5478Labels permutation152 permutation3
    _ = mixedMoment B node3167 node3167Labels := by rfl

def raw5479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw5479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5479 raw5479Labels = mixedMoment B node3167 node3167Labels := by
  calc
    mixedMoment B raw5479 raw5479Labels = mixedMoment B raw5479step0 raw5479step0Labels := by
      have ha : raw5479step0 = (fun i j => raw5479 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5479step0 raw5479; decide +kernel
      have hl : raw5479step0Labels = raw5479Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5479 raw5479Labels permutation176 permutation3
    _ = mixedMoment B node3167 node3167Labels := by rfl

def raw5480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw5480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5480 raw5480Labels = mixedMoment B node3167 node3167Labels := by
  calc
    mixedMoment B raw5480 raw5480Labels = mixedMoment B raw5480step0 raw5480step0Labels := by
      have ha : raw5480step0 = (fun i j => raw5480 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5480step0 raw5480; decide +kernel
      have hl : raw5480step0Labels = raw5480Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5480 raw5480Labels permutation200 permutation3
    _ = mixedMoment B node3167 node3167Labels := by rfl

def raw5481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw5481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5481 raw5481Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw5481 raw5481Labels = mixedMoment B raw5481step0 raw5481step0Labels := by
      have ha : raw5481step0 = (fun i j => raw5481 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5481step0 raw5481; decide +kernel
      have hl : raw5481step0Labels = raw5481Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5481 raw5481Labels permutation240 permutation6
    mixedMoment B raw5481step0 raw5481step0Labels = mixedMoment B raw5481step1 raw5481step1Labels := by
      have ha : raw5481step1 = -raw5481step0 := by apply Matrix.ext; change ∀ i j, raw5481step1 i j = -(raw5481step0 i j); unfold raw5481step1 raw5481step0; decide +kernel
      have hl : raw5481step1Labels = raw5481step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw5482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw5482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5482 raw5482Labels = mixedMoment B node1376 node1376Labels := by
  calc
    mixedMoment B raw5482 raw5482Labels = mixedMoment B raw5482step0 raw5482step0Labels := by
      have ha : raw5482step0 = (fun i j => raw5482 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5482step0 raw5482; decide +kernel
      have hl : raw5482step0Labels = raw5482Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5482 raw5482Labels permutation152 permutation3
    _ = mixedMoment B node1376 node1376Labels := by rfl

def raw5483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw5483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5483step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5483 raw5483Labels = mixedMoment B node1899 node1899Labels := by
  calc
    mixedMoment B raw5483 raw5483Labels = mixedMoment B raw5483step0 raw5483step0Labels := by
      have ha : raw5483step0 = (fun i j => raw5483 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5483step0 raw5483; decide +kernel
      have hl : raw5483step0Labels = raw5483Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5483 raw5483Labels permutation682 permutation3
    mixedMoment B raw5483step0 raw5483step0Labels = mixedMoment B raw5483step1 raw5483step1Labels := by
      have ha : raw5483step1 = -raw5483step0 := by apply Matrix.ext; change ∀ i j, raw5483step1 i j = -(raw5483step0 i j); unfold raw5483step1 raw5483step0; decide +kernel
      have hl : raw5483step1Labels = raw5483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1899 node1899Labels := by rfl

def raw5484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw5484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5484 raw5484Labels = mixedMoment B node1899 node1899Labels := by
  calc
    mixedMoment B raw5484 raw5484Labels = mixedMoment B raw5484step0 raw5484step0Labels := by
      have ha : raw5484step0 = (fun i j => raw5484 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5484step0 raw5484; decide +kernel
      have hl : raw5484step0Labels = raw5484Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5484 raw5484Labels permutation676 permutation3
    mixedMoment B raw5484step0 raw5484step0Labels = mixedMoment B raw5484step1 raw5484step1Labels := by
      have ha : raw5484step1 = -raw5484step0 := by apply Matrix.ext; change ∀ i j, raw5484step1 i j = -(raw5484step0 i j); unfold raw5484step1 raw5484step0; decide +kernel
      have hl : raw5484step1Labels = raw5484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1899 node1899Labels := by rfl

def raw5485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw5485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5485 raw5485Labels = mixedMoment B node1899 node1899Labels := by
  calc
    mixedMoment B raw5485 raw5485Labels = mixedMoment B raw5485step0 raw5485step0Labels := by
      have ha : raw5485step0 = (fun i j => raw5485 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5485step0 raw5485; decide +kernel
      have hl : raw5485step0Labels = raw5485Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5485 raw5485Labels permutation674 permutation3
    mixedMoment B raw5485step0 raw5485step0Labels = mixedMoment B raw5485step1 raw5485step1Labels := by
      have ha : raw5485step1 = -raw5485step0 := by apply Matrix.ext; change ∀ i j, raw5485step1 i j = -(raw5485step0 i j); unfold raw5485step1 raw5485step0; decide +kernel
      have hl : raw5485step1Labels = raw5485step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1899 node1899Labels := by rfl

def raw5486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw5486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw5486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5486 raw5486Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw5486 raw5486Labels = mixedMoment B raw5486step0 raw5486step0Labels := by
      have hz : ∀ j, raw5486 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5486step0 = (fun i j => raw5486 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5486step0 raw5486; decide +kernel
      have hl : raw5486step0Labels = raw5486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5486 raw5486Labels permutation520 hz
    mixedMoment B raw5486step0 raw5486step0Labels = mixedMoment B raw5486step1 raw5486step1Labels := by
      have ha : raw5486step1 = (fun i j => raw5486step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5486step1 raw5486step0; decide +kernel
      have hl : raw5486step1Labels = raw5486step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5486step0 raw5486step0Labels permutation137 permutation3
    mixedMoment B raw5486step1 raw5486step1Labels = mixedMoment B raw5486step2 raw5486step2Labels := by
      have ha : raw5486step2 = -raw5486step1 := by apply Matrix.ext; change ∀ i j, raw5486step2 i j = -(raw5486step1 i j); unfold raw5486step2 raw5486step1; decide +kernel
      have hl : raw5486step2Labels = raw5486step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw5487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5487Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw5487step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5487step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5487step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5487 raw5487Labels = mixedMoment B node2757 node2757Labels := by
  calc
    mixedMoment B raw5487 raw5487Labels = mixedMoment B raw5487step0 raw5487step0Labels := by
      have ha : raw5487step0 = (fun i j => raw5487 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5487step0 raw5487; decide +kernel
      have hl : raw5487step0Labels = raw5487Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5487 raw5487Labels permutation240 permutation7
    mixedMoment B raw5487step0 raw5487step0Labels = mixedMoment B raw5487step1 raw5487step1Labels := by
      have ha : raw5487step1 = -raw5487step0 := by apply Matrix.ext; change ∀ i j, raw5487step1 i j = -(raw5487step0 i j); unfold raw5487step1 raw5487step0; decide +kernel
      have hl : raw5487step1Labels = raw5487step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5487step1 raw5487step1Labels = mixedMoment B raw5487step2 raw5487step2Labels := by
      have ha : raw5487step2 = raw5487step1 := by apply Matrix.ext; unfold raw5487step2 raw5487step1; decide +kernel
      have hl : raw5487step1Labels = labelEmbedding1 ∘ raw5487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5487step1 raw5487step1Labels raw5487step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2757 node2757Labels := by rfl

def raw5488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5488Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw5488step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5488step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5488step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5488 raw5488Labels = mixedMoment B node2757 node2757Labels := by
  calc
    mixedMoment B raw5488 raw5488Labels = mixedMoment B raw5488step0 raw5488step0Labels := by
      have ha : raw5488step0 = (fun i j => raw5488 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5488step0 raw5488; decide +kernel
      have hl : raw5488step0Labels = raw5488Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5488 raw5488Labels permutation242 permutation7
    mixedMoment B raw5488step0 raw5488step0Labels = mixedMoment B raw5488step1 raw5488step1Labels := by
      have ha : raw5488step1 = -raw5488step0 := by apply Matrix.ext; change ∀ i j, raw5488step1 i j = -(raw5488step0 i j); unfold raw5488step1 raw5488step0; decide +kernel
      have hl : raw5488step1Labels = raw5488step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5488step1 raw5488step1Labels = mixedMoment B raw5488step2 raw5488step2Labels := by
      have ha : raw5488step2 = raw5488step1 := by apply Matrix.ext; unfold raw5488step2 raw5488step1; decide +kernel
      have hl : raw5488step1Labels = labelEmbedding1 ∘ raw5488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5488step1 raw5488step1Labels raw5488step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2757 node2757Labels := by rfl

def raw5489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5489Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw5489step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5489step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5489 raw5489Labels = mixedMoment B node2757 node2757Labels := by
  calc
    mixedMoment B raw5489 raw5489Labels = mixedMoment B raw5489step0 raw5489step0Labels := by
      have ha : raw5489step0 = (fun i j => raw5489 (permutation244 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5489step0 raw5489; decide +kernel
      have hl : raw5489step0Labels = raw5489Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5489 raw5489Labels permutation244 permutation7
    mixedMoment B raw5489step0 raw5489step0Labels = mixedMoment B raw5489step1 raw5489step1Labels := by
      have ha : raw5489step1 = -raw5489step0 := by apply Matrix.ext; change ∀ i j, raw5489step1 i j = -(raw5489step0 i j); unfold raw5489step1 raw5489step0; decide +kernel
      have hl : raw5489step1Labels = raw5489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5489step1 raw5489step1Labels = mixedMoment B raw5489step2 raw5489step2Labels := by
      have ha : raw5489step2 = raw5489step1 := by apply Matrix.ext; unfold raw5489step2 raw5489step1; decide +kernel
      have hl : raw5489step1Labels = labelEmbedding1 ∘ raw5489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5489step1 raw5489step1Labels raw5489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2757 node2757Labels := by rfl

def raw5490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5490step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5490step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5490step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5490step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5490 raw5490Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw5490 raw5490Labels = mixedMoment B raw5490step0 raw5490step0Labels := by
      have hz : ∀ j, raw5490 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5490step0 = (fun i j => raw5490 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5490step0 raw5490; decide +kernel
      have hl : raw5490step0Labels = raw5490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5490 raw5490Labels permutation520 hz
    mixedMoment B raw5490step0 raw5490step0Labels = mixedMoment B raw5490step1 raw5490step1Labels := by
      have ha : raw5490step1 = (fun i j => raw5490step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5490step1 raw5490step0; decide +kernel
      have hl : raw5490step1Labels = raw5490step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5490step0 raw5490step0Labels permutation50 permutation7
    mixedMoment B raw5490step1 raw5490step1Labels = mixedMoment B raw5490step2 raw5490step2Labels := by
      have ha : raw5490step2 = -raw5490step1 := by apply Matrix.ext; change ∀ i j, raw5490step2 i j = -(raw5490step1 i j); unfold raw5490step2 raw5490step1; decide +kernel
      have hl : raw5490step2Labels = raw5490step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5490step2 raw5490step2Labels = mixedMoment B raw5490step3 raw5490step3Labels := by
      have ha : raw5490step3 = raw5490step2 := by apply Matrix.ext; unfold raw5490step3 raw5490step2; decide +kernel
      have hl : raw5490step2Labels = labelEmbedding1 ∘ raw5490step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5490step2 raw5490step2Labels raw5490step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

def raw5491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5491step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5491step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5491step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5491step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5491 raw5491Labels = mixedMoment B node2752 node2752Labels := by
  calc
    mixedMoment B raw5491 raw5491Labels = mixedMoment B raw5491step0 raw5491step0Labels := by
      have ha : raw5491step0 = (fun i j => raw5491 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5491step0 raw5491; decide +kernel
      have hl : raw5491step0Labels = raw5491Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5491 raw5491Labels permutation240 permutation7
    mixedMoment B raw5491step0 raw5491step0Labels = mixedMoment B raw5491step1 raw5491step1Labels := by
      have ha : raw5491step1 = -raw5491step0 := by apply Matrix.ext; change ∀ i j, raw5491step1 i j = -(raw5491step0 i j); unfold raw5491step1 raw5491step0; decide +kernel
      have hl : raw5491step1Labels = raw5491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5491step1 raw5491step1Labels = mixedMoment B raw5491step2 raw5491step2Labels := by
      have ha : raw5491step2 = raw5491step1 := by apply Matrix.ext; unfold raw5491step2 raw5491step1; decide +kernel
      have hl : raw5491step1Labels = labelEmbedding1 ∘ raw5491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5491step1 raw5491step1Labels raw5491step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2752 node2752Labels := by rfl

def raw5492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5492step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5492step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5492 raw5492Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw5492 raw5492Labels = mixedMoment B raw5492step0 raw5492step0Labels := by
      have ha : raw5492step0 = (fun i j => raw5492 (permutation243 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5492step0 raw5492; decide +kernel
      have hl : raw5492step0Labels = raw5492Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5492 raw5492Labels permutation243 permutation7
    mixedMoment B raw5492step0 raw5492step0Labels = mixedMoment B raw5492step1 raw5492step1Labels := by
      have ha : raw5492step1 = -raw5492step0 := by apply Matrix.ext; change ∀ i j, raw5492step1 i j = -(raw5492step0 i j); unfold raw5492step1 raw5492step0; decide +kernel
      have hl : raw5492step1Labels = raw5492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5492step1 raw5492step1Labels = mixedMoment B raw5492step2 raw5492step2Labels := by
      have ha : raw5492step2 = raw5492step1 := by apply Matrix.ext; unfold raw5492step2 raw5492step1; decide +kernel
      have hl : raw5492step1Labels = labelEmbedding1 ∘ raw5492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5492step1 raw5492step1Labels raw5492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw5493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw5493step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5493step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5493step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5493 raw5493Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5493 raw5493Labels = mixedMoment B raw5493step0 raw5493step0Labels := by
      have ha : raw5493step0 = (fun i j => raw5493 (permutation243 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5493step0 raw5493; decide +kernel
      have hl : raw5493step0Labels = raw5493Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5493 raw5493Labels permutation243 permutation7
    mixedMoment B raw5493step0 raw5493step0Labels = mixedMoment B raw5493step1 raw5493step1Labels := by
      have ha : raw5493step1 = -raw5493step0 := by apply Matrix.ext; change ∀ i j, raw5493step1 i j = -(raw5493step0 i j); unfold raw5493step1 raw5493step0; decide +kernel
      have hl : raw5493step1Labels = raw5493step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5493step1 raw5493step1Labels = mixedMoment B raw5493step2 raw5493step2Labels := by
      have ha : raw5493step2 = raw5493step1 := by apply Matrix.ext; unfold raw5493step2 raw5493step1; decide +kernel
      have hl : raw5493step1Labels = labelEmbedding1 ∘ raw5493step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5493step1 raw5493step1Labels raw5493step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw5494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw5494step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5494step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5494step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5494 raw5494Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5494 raw5494Labels = mixedMoment B raw5494step0 raw5494step0Labels := by
      have ha : raw5494step0 = (fun i j => raw5494 (permutation245 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5494step0 raw5494; decide +kernel
      have hl : raw5494step0Labels = raw5494Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5494 raw5494Labels permutation245 permutation7
    mixedMoment B raw5494step0 raw5494step0Labels = mixedMoment B raw5494step1 raw5494step1Labels := by
      have ha : raw5494step1 = -raw5494step0 := by apply Matrix.ext; change ∀ i j, raw5494step1 i j = -(raw5494step0 i j); unfold raw5494step1 raw5494step0; decide +kernel
      have hl : raw5494step1Labels = raw5494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5494step1 raw5494step1Labels = mixedMoment B raw5494step2 raw5494step2Labels := by
      have ha : raw5494step2 = raw5494step1 := by apply Matrix.ext; unfold raw5494step2 raw5494step1; decide +kernel
      have hl : raw5494step1Labels = labelEmbedding1 ∘ raw5494step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5494step1 raw5494step1Labels raw5494step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw5495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5495step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5495step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5495step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5495step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5495 raw5495Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5495 raw5495Labels = mixedMoment B raw5495step0 raw5495step0Labels := by
      have hz : ∀ j, raw5495 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5495step0 = (fun i j => raw5495 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5495step0 raw5495; decide +kernel
      have hl : raw5495step0Labels = raw5495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5495 raw5495Labels permutation520 hz
    mixedMoment B raw5495step0 raw5495step0Labels = mixedMoment B raw5495step1 raw5495step1Labels := by
      have ha : raw5495step1 = (fun i j => raw5495step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5495step1 raw5495step0; decide +kernel
      have hl : raw5495step1Labels = raw5495step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5495step0 raw5495step0Labels permutation53 permutation7
    mixedMoment B raw5495step1 raw5495step1Labels = mixedMoment B raw5495step2 raw5495step2Labels := by
      have ha : raw5495step2 = -raw5495step1 := by apply Matrix.ext; change ∀ i j, raw5495step2 i j = -(raw5495step1 i j); unfold raw5495step2 raw5495step1; decide +kernel
      have hl : raw5495step2Labels = raw5495step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5495step2 raw5495step2Labels = mixedMoment B raw5495step3 raw5495step3Labels := by
      have ha : raw5495step3 = raw5495step2 := by apply Matrix.ext; unfold raw5495step3 raw5495step2; decide +kernel
      have hl : raw5495step2Labels = labelEmbedding1 ∘ raw5495step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5495step2 raw5495step2Labels raw5495step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw5496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5496step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5496 raw5496Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5496 raw5496Labels = mixedMoment B raw5496step0 raw5496step0Labels := by
      have ha : raw5496step0 = (fun i j => raw5496 (permutation243 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5496step0 raw5496; decide +kernel
      have hl : raw5496step0Labels = raw5496Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5496 raw5496Labels permutation243 permutation7
    mixedMoment B raw5496step0 raw5496step0Labels = mixedMoment B raw5496step1 raw5496step1Labels := by
      have ha : raw5496step1 = -raw5496step0 := by apply Matrix.ext; change ∀ i j, raw5496step1 i j = -(raw5496step0 i j); unfold raw5496step1 raw5496step0; decide +kernel
      have hl : raw5496step1Labels = raw5496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5496step1 raw5496step1Labels = mixedMoment B raw5496step2 raw5496step2Labels := by
      have ha : raw5496step2 = raw5496step1 := by apply Matrix.ext; unfold raw5496step2 raw5496step1; decide +kernel
      have hl : raw5496step1Labels = labelEmbedding1 ∘ raw5496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5496step1 raw5496step1Labels raw5496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw5497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5497step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5497step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5497 raw5497Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw5497 raw5497Labels = mixedMoment B raw5497step0 raw5497step0Labels := by
      have ha : raw5497step0 = (fun i j => raw5497 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5497step0 raw5497; decide +kernel
      have hl : raw5497step0Labels = raw5497Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5497 raw5497Labels permutation241 permutation7
    mixedMoment B raw5497step0 raw5497step0Labels = mixedMoment B raw5497step1 raw5497step1Labels := by
      have ha : raw5497step1 = -raw5497step0 := by apply Matrix.ext; change ∀ i j, raw5497step1 i j = -(raw5497step0 i j); unfold raw5497step1 raw5497step0; decide +kernel
      have hl : raw5497step1Labels = raw5497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5497step1 raw5497step1Labels = mixedMoment B raw5497step2 raw5497step2Labels := by
      have ha : raw5497step2 = raw5497step1 := by apply Matrix.ext; unfold raw5497step2 raw5497step1; decide +kernel
      have hl : raw5497step1Labels = labelEmbedding1 ∘ raw5497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5497step1 raw5497step1Labels raw5497step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw5498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw5498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5498step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5498 raw5498Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5498 raw5498Labels = mixedMoment B raw5498step0 raw5498step0Labels := by
      have ha : raw5498step0 = (fun i j => raw5498 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5498step0 raw5498; decide +kernel
      have hl : raw5498step0Labels = raw5498Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5498 raw5498Labels permutation241 permutation7
    mixedMoment B raw5498step0 raw5498step0Labels = mixedMoment B raw5498step1 raw5498step1Labels := by
      have ha : raw5498step1 = -raw5498step0 := by apply Matrix.ext; change ∀ i j, raw5498step1 i j = -(raw5498step0 i j); unfold raw5498step1 raw5498step0; decide +kernel
      have hl : raw5498step1Labels = raw5498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5498step1 raw5498step1Labels = mixedMoment B raw5498step2 raw5498step2Labels := by
      have ha : raw5498step2 = raw5498step1 := by apply Matrix.ext; unfold raw5498step2 raw5498step1; decide +kernel
      have hl : raw5498step1Labels = labelEmbedding1 ∘ raw5498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5498step1 raw5498step1Labels raw5498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw5499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw5499step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5499step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5499 raw5499Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5499 raw5499Labels = mixedMoment B raw5499step0 raw5499step0Labels := by
      have ha : raw5499step0 = (fun i j => raw5499 (permutation244 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5499step0 raw5499; decide +kernel
      have hl : raw5499step0Labels = raw5499Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5499 raw5499Labels permutation244 permutation7
    mixedMoment B raw5499step0 raw5499step0Labels = mixedMoment B raw5499step1 raw5499step1Labels := by
      have ha : raw5499step1 = -raw5499step0 := by apply Matrix.ext; change ∀ i j, raw5499step1 i j = -(raw5499step0 i j); unfold raw5499step1 raw5499step0; decide +kernel
      have hl : raw5499step1Labels = raw5499step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5499step1 raw5499step1Labels = mixedMoment B raw5499step2 raw5499step2Labels := by
      have ha : raw5499step2 = raw5499step1 := by apply Matrix.ext; unfold raw5499step2 raw5499step1; decide +kernel
      have hl : raw5499step1Labels = labelEmbedding1 ∘ raw5499step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5499step1 raw5499step1Labels raw5499step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw5500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5500step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5500step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5500step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5500 raw5500Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5500 raw5500Labels = mixedMoment B raw5500step0 raw5500step0Labels := by
      have hz : ∀ j, raw5500 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5500step0 = (fun i j => raw5500 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5500step0 raw5500; decide +kernel
      have hl : raw5500step0Labels = raw5500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5500 raw5500Labels permutation520 hz
    mixedMoment B raw5500step0 raw5500step0Labels = mixedMoment B raw5500step1 raw5500step1Labels := by
      have ha : raw5500step1 = (fun i j => raw5500step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5500step1 raw5500step0; decide +kernel
      have hl : raw5500step1Labels = raw5500step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5500step0 raw5500step0Labels permutation51 permutation7
    mixedMoment B raw5500step1 raw5500step1Labels = mixedMoment B raw5500step2 raw5500step2Labels := by
      have ha : raw5500step2 = -raw5500step1 := by apply Matrix.ext; change ∀ i j, raw5500step2 i j = -(raw5500step1 i j); unfold raw5500step2 raw5500step1; decide +kernel
      have hl : raw5500step2Labels = raw5500step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5500step2 raw5500step2Labels = mixedMoment B raw5500step3 raw5500step3Labels := by
      have ha : raw5500step3 = raw5500step2 := by apply Matrix.ext; unfold raw5500step3 raw5500step2; decide +kernel
      have hl : raw5500step2Labels = labelEmbedding1 ∘ raw5500step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5500step2 raw5500step2Labels raw5500step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw5501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5501 raw5501Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5501 raw5501Labels = mixedMoment B raw5501step0 raw5501step0Labels := by
      have ha : raw5501step0 = (fun i j => raw5501 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5501step0 raw5501; decide +kernel
      have hl : raw5501step0Labels = raw5501Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5501 raw5501Labels permutation241 permutation7
    mixedMoment B raw5501step0 raw5501step0Labels = mixedMoment B raw5501step1 raw5501step1Labels := by
      have ha : raw5501step1 = -raw5501step0 := by apply Matrix.ext; change ∀ i j, raw5501step1 i j = -(raw5501step0 i j); unfold raw5501step1 raw5501step0; decide +kernel
      have hl : raw5501step1Labels = raw5501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5501step1 raw5501step1Labels = mixedMoment B raw5501step2 raw5501step2Labels := by
      have ha : raw5501step2 = raw5501step1 := by apply Matrix.ext; unfold raw5501step2 raw5501step1; decide +kernel
      have hl : raw5501step1Labels = labelEmbedding1 ∘ raw5501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5501step1 raw5501step1Labels raw5501step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw5502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5502step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5502 raw5502Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw5502 raw5502Labels = mixedMoment B raw5502step0 raw5502step0Labels := by
      have ha : raw5502step0 = (fun i j => raw5502 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5502step0 raw5502; decide +kernel
      have hl : raw5502step0Labels = raw5502Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5502 raw5502Labels permutation240 permutation7
    mixedMoment B raw5502step0 raw5502step0Labels = mixedMoment B raw5502step1 raw5502step1Labels := by
      have ha : raw5502step1 = -raw5502step0 := by apply Matrix.ext; change ∀ i j, raw5502step1 i j = -(raw5502step0 i j); unfold raw5502step1 raw5502step0; decide +kernel
      have hl : raw5502step1Labels = raw5502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5502step1 raw5502step1Labels = mixedMoment B raw5502step2 raw5502step2Labels := by
      have ha : raw5502step2 = raw5502step1 := by apply Matrix.ext; unfold raw5502step2 raw5502step1; decide +kernel
      have hl : raw5502step1Labels = labelEmbedding1 ∘ raw5502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5502step1 raw5502step1Labels raw5502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw5503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw5503step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5503step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5503 raw5503Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5503 raw5503Labels = mixedMoment B raw5503step0 raw5503step0Labels := by
      have ha : raw5503step0 = (fun i j => raw5503 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5503step0 raw5503; decide +kernel
      have hl : raw5503step0Labels = raw5503Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5503 raw5503Labels permutation240 permutation7
    mixedMoment B raw5503step0 raw5503step0Labels = mixedMoment B raw5503step1 raw5503step1Labels := by
      have ha : raw5503step1 = -raw5503step0 := by apply Matrix.ext; change ∀ i j, raw5503step1 i j = -(raw5503step0 i j); unfold raw5503step1 raw5503step0; decide +kernel
      have hl : raw5503step1Labels = raw5503step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5503step1 raw5503step1Labels = mixedMoment B raw5503step2 raw5503step2Labels := by
      have ha : raw5503step2 = raw5503step1 := by apply Matrix.ext; unfold raw5503step2 raw5503step1; decide +kernel
      have hl : raw5503step1Labels = labelEmbedding1 ∘ raw5503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5503step1 raw5503step1Labels raw5503step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
