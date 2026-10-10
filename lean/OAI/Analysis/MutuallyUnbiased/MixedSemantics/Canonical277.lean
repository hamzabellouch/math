import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw35456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35456step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35456 raw35456Labels = mixedMoment B node5324 node5324Labels := by
  calc
    mixedMoment B raw35456 raw35456Labels = mixedMoment B raw35456step0 raw35456step0Labels := by
      have ha : raw35456step0 = (fun i j => raw35456 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35456step0 raw35456; decide +kernel
      have hl : raw35456step0Labels = raw35456Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35456 raw35456Labels permutation589 permutation2
    mixedMoment B raw35456step0 raw35456step0Labels = mixedMoment B raw35456step1 raw35456step1Labels := by
      have ha : raw35456step1 = -raw35456step0 := by apply Matrix.ext; change ∀ i j, raw35456step1 i j = -(raw35456step0 i j); unfold raw35456step1 raw35456step0; decide +kernel
      have hl : raw35456step1Labels = raw35456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5324 node5324Labels := by rfl

def raw35457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35457step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35457 raw35457Labels = mixedMoment B node5331 node5331Labels := by
  calc
    mixedMoment B raw35457 raw35457Labels = mixedMoment B raw35457step0 raw35457step0Labels := by
      have hz : ∀ j, raw35457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35457step0 = (fun i j => raw35457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35457step0 raw35457; decide +kernel
      have hl : raw35457step0Labels = raw35457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35457 raw35457Labels permutation346 hz
    mixedMoment B raw35457step0 raw35457step0Labels = mixedMoment B raw35457step1 raw35457step1Labels := by
      have ha : raw35457step1 = (fun i j => raw35457step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35457step1 raw35457step0; decide +kernel
      have hl : raw35457step1Labels = raw35457step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35457step0 raw35457step0Labels permutation127 permutation2
    mixedMoment B raw35457step1 raw35457step1Labels = mixedMoment B raw35457step2 raw35457step2Labels := by
      have ha : raw35457step2 = -raw35457step1 := by apply Matrix.ext; change ∀ i j, raw35457step2 i j = -(raw35457step1 i j); unfold raw35457step2 raw35457step1; decide +kernel
      have hl : raw35457step2Labels = raw35457step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5331 node5331Labels := by rfl

def raw35458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35458step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35458 raw35458Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw35458 raw35458Labels = mixedMoment B raw35458step0 raw35458step0Labels := by
      have hz : ∀ j, raw35458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35458step0 = (fun i j => raw35458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35458step0 raw35458; decide +kernel
      have hl : raw35458step0Labels = raw35458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35458 raw35458Labels permutation346 hz
    mixedMoment B raw35458step0 raw35458step0Labels = mixedMoment B raw35458step1 raw35458step1Labels := by
      have ha : raw35458step1 = (fun i j => raw35458step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35458step1 raw35458step0; decide +kernel
      have hl : raw35458step1Labels = raw35458step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35458step0 raw35458step0Labels permutation150 permutation7
    mixedMoment B raw35458step1 raw35458step1Labels = mixedMoment B raw35458step2 raw35458step2Labels := by
      have ha : raw35458step2 = raw35458step1 := by apply Matrix.ext; unfold raw35458step2 raw35458step1; decide +kernel
      have hl : raw35458step1Labels = labelEmbedding10 ∘ raw35458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35458step1 raw35458step1Labels raw35458step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw35459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35459step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35459step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35459step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35459 raw35459Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw35459 raw35459Labels = mixedMoment B raw35459step0 raw35459step0Labels := by
      have hz : ∀ j, raw35459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35459step0 = (fun i j => raw35459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35459step0 raw35459; decide +kernel
      have hl : raw35459step0Labels = raw35459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35459 raw35459Labels permutation346 hz
    mixedMoment B raw35459step0 raw35459step0Labels = mixedMoment B raw35459step1 raw35459step1Labels := by
      have ha : raw35459step1 = (fun i j => raw35459step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35459step1 raw35459step0; decide +kernel
      have hl : raw35459step1Labels = raw35459step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35459step0 raw35459step0Labels permutation126 permutation7
    mixedMoment B raw35459step1 raw35459step1Labels = mixedMoment B raw35459step2 raw35459step2Labels := by
      have ha : raw35459step2 = raw35459step1 := by apply Matrix.ext; unfold raw35459step2 raw35459step1; decide +kernel
      have hl : raw35459step1Labels = labelEmbedding10 ∘ raw35459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35459step1 raw35459step1Labels raw35459step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw35460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw35460step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw35460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35460 raw35460Labels = mixedMoment B node4962 node4962Labels := by
  calc
    mixedMoment B raw35460 raw35460Labels = mixedMoment B raw35460step0 raw35460step0Labels := by
      have ha : raw35460step0 = (fun i j => raw35460 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35460step0 raw35460; decide +kernel
      have hl : raw35460step0Labels = raw35460Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35460 raw35460Labels permutation158 permutation3
    mixedMoment B raw35460step0 raw35460step0Labels = mixedMoment B raw35460step1 raw35460step1Labels := by
      have ha : raw35460step1 = raw35460step0 := by apply Matrix.ext; unfold raw35460step1 raw35460step0; decide +kernel
      have hl : raw35460step0Labels = labelEmbedding6 ∘ raw35460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35460step0 raw35460step0Labels raw35460step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4962 node4962Labels := by rfl

def raw35461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35461 raw35461Labels = mixedMoment B node4926 node4926Labels := by
  calc
    mixedMoment B raw35461 raw35461Labels = mixedMoment B raw35461step0 raw35461step0Labels := by
      have ha : raw35461step0 = (fun i j => raw35461 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35461step0 raw35461; decide +kernel
      have hl : raw35461step0Labels = raw35461Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35461 raw35461Labels permutation271 permutation2
    _ = mixedMoment B node4926 node4926Labels := by rfl

def raw35462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35462 raw35462Labels = mixedMoment B node5314 node5314Labels := by
  calc
    mixedMoment B raw35462 raw35462Labels = mixedMoment B raw35462step0 raw35462step0Labels := by
      have ha : raw35462step0 = (fun i j => raw35462 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35462step0 raw35462; decide +kernel
      have hl : raw35462step0Labels = raw35462Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35462 raw35462Labels permutation583 permutation2
    mixedMoment B raw35462step0 raw35462step0Labels = mixedMoment B raw35462step1 raw35462step1Labels := by
      have ha : raw35462step1 = -raw35462step0 := by apply Matrix.ext; change ∀ i j, raw35462step1 i j = -(raw35462step0 i j); unfold raw35462step1 raw35462step0; decide +kernel
      have hl : raw35462step1Labels = raw35462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5314 node5314Labels := by rfl

def raw35463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35463 raw35463Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw35463 raw35463Labels = mixedMoment B raw35463step0 raw35463step0Labels := by
      have ha : raw35463step0 = (fun i j => raw35463 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35463step0 raw35463; decide +kernel
      have hl : raw35463step0Labels = raw35463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35463 raw35463Labels permutation271 permutation2
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw35464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35464 raw35464Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw35464 raw35464Labels = mixedMoment B raw35464step0 raw35464step0Labels := by
      have ha : raw35464step0 = (fun i j => raw35464 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35464step0 raw35464; decide +kernel
      have hl : raw35464step0Labels = raw35464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35464 raw35464Labels permutation272 permutation2
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw35465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw35465step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw35465step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35465 raw35465Labels = mixedMoment B node4978 node4978Labels := by
  calc
    mixedMoment B raw35465 raw35465Labels = mixedMoment B raw35465step0 raw35465step0Labels := by
      have hz : ∀ j, raw35465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35465step0 = (fun i j => raw35465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35465step0 raw35465; decide +kernel
      have hl : raw35465step0Labels = raw35465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35465 raw35465Labels permutation346 hz
    mixedMoment B raw35465step0 raw35465step0Labels = mixedMoment B raw35465step1 raw35465step1Labels := by
      have ha : raw35465step1 = (fun i j => raw35465step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35465step1 raw35465step0; decide +kernel
      have hl : raw35465step1Labels = raw35465step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35465step0 raw35465step0Labels permutation32 permutation3
    mixedMoment B raw35465step1 raw35465step1Labels = mixedMoment B raw35465step2 raw35465step2Labels := by
      have ha : raw35465step2 = raw35465step1 := by apply Matrix.ext; unfold raw35465step2 raw35465step1; decide +kernel
      have hl : raw35465step1Labels = labelEmbedding6 ∘ raw35465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35465step1 raw35465step1Labels raw35465step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4978 node4978Labels := by rfl

def raw35466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35466 raw35466Labels = mixedMoment B node4937 node4937Labels := by
  calc
    mixedMoment B raw35466 raw35466Labels = mixedMoment B raw35466step0 raw35466step0Labels := by
      have hz : ∀ j, raw35466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35466step0 = (fun i j => raw35466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35466step0 raw35466; decide +kernel
      have hl : raw35466step0Labels = raw35466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35466 raw35466Labels permutation346 hz
    mixedMoment B raw35466step0 raw35466step0Labels = mixedMoment B raw35466step1 raw35466step1Labels := by
      have ha : raw35466step1 = (fun i j => raw35466step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35466step1 raw35466step0; decide +kernel
      have hl : raw35466step1Labels = raw35466step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35466step0 raw35466step0Labels permutation56 permutation2
    _ = mixedMoment B node4937 node4937Labels := by rfl

def raw35467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw35467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35467 raw35467Labels = mixedMoment B node5317 node5317Labels := by
  calc
    mixedMoment B raw35467 raw35467Labels = mixedMoment B raw35467step0 raw35467step0Labels := by
      have ha : raw35467step0 = (fun i j => raw35467 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35467step0 raw35467; decide +kernel
      have hl : raw35467step0Labels = raw35467Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35467 raw35467Labels permutation588 permutation2
    mixedMoment B raw35467step0 raw35467step0Labels = mixedMoment B raw35467step1 raw35467step1Labels := by
      have ha : raw35467step1 = -raw35467step0 := by apply Matrix.ext; change ∀ i j, raw35467step1 i j = -(raw35467step0 i j); unfold raw35467step1 raw35467step0; decide +kernel
      have hl : raw35467step1Labels = raw35467step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5317 node5317Labels := by rfl

def raw35468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35468 raw35468Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw35468 raw35468Labels = mixedMoment B raw35468step0 raw35468step0Labels := by
      have hz : ∀ j, raw35468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35468step0 = (fun i j => raw35468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35468step0 raw35468; decide +kernel
      have hl : raw35468step0Labels = raw35468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35468 raw35468Labels permutation346 hz
    mixedMoment B raw35468step0 raw35468step0Labels = mixedMoment B raw35468step1 raw35468step1Labels := by
      have ha : raw35468step1 = (fun i j => raw35468step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35468step1 raw35468step0; decide +kernel
      have hl : raw35468step1Labels = raw35468step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35468step0 raw35468step0Labels permutation56 permutation2
    _ = mixedMoment B node5364 node5364Labels := by rfl

def raw35469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35469 raw35469Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw35469 raw35469Labels = mixedMoment B raw35469step0 raw35469step0Labels := by
      have hz : ∀ j, raw35469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35469step0 = (fun i j => raw35469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35469step0 raw35469; decide +kernel
      have hl : raw35469step0Labels = raw35469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35469 raw35469Labels permutation346 hz
    mixedMoment B raw35469step0 raw35469step0Labels = mixedMoment B raw35469step1 raw35469step1Labels := by
      have ha : raw35469step1 = (fun i j => raw35469step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35469step1 raw35469step0; decide +kernel
      have hl : raw35469step1Labels = raw35469step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35469step0 raw35469step0Labels permutation57 permutation2
    _ = mixedMoment B node5364 node5364Labels := by rfl

def raw35470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw35470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw35470step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35470 raw35470Labels = mixedMoment B node4908 node4908Labels := by
  calc
    mixedMoment B raw35470 raw35470Labels = mixedMoment B raw35470step0 raw35470step0Labels := by
      have hz : ∀ j, raw35470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35470step0 = (fun i j => raw35470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35470step0 raw35470; decide +kernel
      have hl : raw35470step0Labels = raw35470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35470 raw35470Labels permutation346 hz
    mixedMoment B raw35470step0 raw35470step0Labels = mixedMoment B raw35470step1 raw35470step1Labels := by
      have ha : raw35470step1 = (fun i j => raw35470step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35470step1 raw35470step0; decide +kernel
      have hl : raw35470step1Labels = raw35470step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35470step0 raw35470step0Labels permutation127 permutation2
    mixedMoment B raw35470step1 raw35470step1Labels = mixedMoment B raw35470step2 raw35470step2Labels := by
      have ha : raw35470step2 = -raw35470step1 := by apply Matrix.ext; change ∀ i j, raw35470step2 i j = -(raw35470step1 i j); unfold raw35470step2 raw35470step1; decide +kernel
      have hl : raw35470step2Labels = raw35470step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4908 node4908Labels := by rfl

def raw35471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw35471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw35471step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35471 raw35471Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw35471 raw35471Labels = mixedMoment B raw35471step0 raw35471step0Labels := by
      have hz : ∀ j, raw35471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35471step0 = (fun i j => raw35471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35471step0 raw35471; decide +kernel
      have hl : raw35471step0Labels = raw35471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35471 raw35471Labels permutation346 hz
    mixedMoment B raw35471step0 raw35471step0Labels = mixedMoment B raw35471step1 raw35471step1Labels := by
      have ha : raw35471step1 = (fun i j => raw35471step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35471step1 raw35471step0; decide +kernel
      have hl : raw35471step1Labels = raw35471step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35471step0 raw35471step0Labels permutation126 permutation2
    mixedMoment B raw35471step1 raw35471step1Labels = mixedMoment B raw35471step2 raw35471step2Labels := by
      have ha : raw35471step2 = -raw35471step1 := by apply Matrix.ext; change ∀ i j, raw35471step2 i j = -(raw35471step1 i j); unfold raw35471step2 raw35471step1; decide +kernel
      have hl : raw35471step2Labels = raw35471step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4907 node4907Labels := by rfl

def raw35472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw35472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35472 raw35472Labels = mixedMoment B node4903 node4903Labels := by
  calc
    mixedMoment B raw35472 raw35472Labels = mixedMoment B raw35472step0 raw35472step0Labels := by
      have ha : raw35472step0 = (fun i j => raw35472 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35472step0 raw35472; decide +kernel
      have hl : raw35472step0Labels = raw35472Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35472 raw35472Labels permutation588 permutation2
    mixedMoment B raw35472step0 raw35472step0Labels = mixedMoment B raw35472step1 raw35472step1Labels := by
      have ha : raw35472step1 = -raw35472step0 := by apply Matrix.ext; change ∀ i j, raw35472step1 i j = -(raw35472step0 i j); unfold raw35472step1 raw35472step0; decide +kernel
      have hl : raw35472step1Labels = raw35472step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4903 node4903Labels := by rfl

def raw35473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35473 raw35473Labels = mixedMoment B node4921 node4921Labels := by
  calc
    mixedMoment B raw35473 raw35473Labels = mixedMoment B raw35473step0 raw35473step0Labels := by
      have hz : ∀ j, raw35473 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35473step0 = (fun i j => raw35473 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35473step0 raw35473; decide +kernel
      have hl : raw35473step0Labels = raw35473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35473 raw35473Labels permutation346 hz
    mixedMoment B raw35473step0 raw35473step0Labels = mixedMoment B raw35473step1 raw35473step1Labels := by
      have ha : raw35473step1 = (fun i j => raw35473step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35473step1 raw35473step0; decide +kernel
      have hl : raw35473step1Labels = raw35473step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35473step0 raw35473step0Labels permutation126 permutation2
    mixedMoment B raw35473step1 raw35473step1Labels = mixedMoment B raw35473step2 raw35473step2Labels := by
      have ha : raw35473step2 = -raw35473step1 := by apply Matrix.ext; change ∀ i j, raw35473step2 i j = -(raw35473step1 i j); unfold raw35473step2 raw35473step1; decide +kernel
      have hl : raw35473step2Labels = raw35473step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4921 node4921Labels := by rfl

def raw35474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw35474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw35474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35474 raw35474Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw35474 raw35474Labels = mixedMoment B raw35474step0 raw35474step0Labels := by
      have hz : ∀ j, raw35474 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35474step0 = (fun i j => raw35474 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35474step0 raw35474; decide +kernel
      have hl : raw35474step0Labels = raw35474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35474 raw35474Labels permutation346 hz
    mixedMoment B raw35474step0 raw35474step0Labels = mixedMoment B raw35474step1 raw35474step1Labels := by
      have ha : raw35474step1 = (fun i j => raw35474step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35474step1 raw35474step0; decide +kernel
      have hl : raw35474step1Labels = raw35474step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35474step0 raw35474step0Labels permutation126 permutation2
    mixedMoment B raw35474step1 raw35474step1Labels = mixedMoment B raw35474step2 raw35474step2Labels := by
      have ha : raw35474step2 = -raw35474step1 := by apply Matrix.ext; change ∀ i j, raw35474step2 i j = -(raw35474step1 i j); unfold raw35474step2 raw35474step1; decide +kernel
      have hl : raw35474step2Labels = raw35474step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw35475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw35475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw35475step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35475 raw35475Labels = mixedMoment B node4908 node4908Labels := by
  calc
    mixedMoment B raw35475 raw35475Labels = mixedMoment B raw35475step0 raw35475step0Labels := by
      have hz : ∀ j, raw35475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35475step0 = (fun i j => raw35475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35475step0 raw35475; decide +kernel
      have hl : raw35475step0Labels = raw35475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35475 raw35475Labels permutation346 hz
    mixedMoment B raw35475step0 raw35475step0Labels = mixedMoment B raw35475step1 raw35475step1Labels := by
      have ha : raw35475step1 = (fun i j => raw35475step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35475step1 raw35475step0; decide +kernel
      have hl : raw35475step1Labels = raw35475step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35475step0 raw35475step0Labels permutation151 permutation2
    mixedMoment B raw35475step1 raw35475step1Labels = mixedMoment B raw35475step2 raw35475step2Labels := by
      have ha : raw35475step2 = -raw35475step1 := by apply Matrix.ext; change ∀ i j, raw35475step2 i j = -(raw35475step1 i j); unfold raw35475step2 raw35475step1; decide +kernel
      have hl : raw35475step2Labels = raw35475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4908 node4908Labels := by rfl

def raw35476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw35476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw35476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35476 raw35476Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw35476 raw35476Labels = mixedMoment B raw35476step0 raw35476step0Labels := by
      have hz : ∀ j, raw35476 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35476step0 = (fun i j => raw35476 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35476step0 raw35476; decide +kernel
      have hl : raw35476step0Labels = raw35476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35476 raw35476Labels permutation346 hz
    mixedMoment B raw35476step0 raw35476step0Labels = mixedMoment B raw35476step1 raw35476step1Labels := by
      have ha : raw35476step1 = (fun i j => raw35476step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35476step1 raw35476step0; decide +kernel
      have hl : raw35476step1Labels = raw35476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35476step0 raw35476step0Labels permutation150 permutation2
    mixedMoment B raw35476step1 raw35476step1Labels = mixedMoment B raw35476step2 raw35476step2Labels := by
      have ha : raw35476step2 = -raw35476step1 := by apply Matrix.ext; change ∀ i j, raw35476step2 i j = -(raw35476step1 i j); unfold raw35476step2 raw35476step1; decide +kernel
      have hl : raw35476step2Labels = raw35476step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4907 node4907Labels := by rfl

def raw35477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw35477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35477 raw35477Labels = mixedMoment B node4903 node4903Labels := by
  calc
    mixedMoment B raw35477 raw35477Labels = mixedMoment B raw35477step0 raw35477step0Labels := by
      have ha : raw35477step0 = (fun i j => raw35477 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35477step0 raw35477; decide +kernel
      have hl : raw35477step0Labels = raw35477Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35477 raw35477Labels permutation687 permutation2
    mixedMoment B raw35477step0 raw35477step0Labels = mixedMoment B raw35477step1 raw35477step1Labels := by
      have ha : raw35477step1 = -raw35477step0 := by apply Matrix.ext; change ∀ i j, raw35477step1 i j = -(raw35477step0 i j); unfold raw35477step1 raw35477step0; decide +kernel
      have hl : raw35477step1Labels = raw35477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4903 node4903Labels := by rfl

def raw35478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35478step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35478step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35478 raw35478Labels = mixedMoment B node4921 node4921Labels := by
  calc
    mixedMoment B raw35478 raw35478Labels = mixedMoment B raw35478step0 raw35478step0Labels := by
      have hz : ∀ j, raw35478 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35478step0 = (fun i j => raw35478 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35478step0 raw35478; decide +kernel
      have hl : raw35478step0Labels = raw35478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35478 raw35478Labels permutation346 hz
    mixedMoment B raw35478step0 raw35478step0Labels = mixedMoment B raw35478step1 raw35478step1Labels := by
      have ha : raw35478step1 = (fun i j => raw35478step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35478step1 raw35478step0; decide +kernel
      have hl : raw35478step1Labels = raw35478step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35478step0 raw35478step0Labels permutation150 permutation2
    mixedMoment B raw35478step1 raw35478step1Labels = mixedMoment B raw35478step2 raw35478step2Labels := by
      have ha : raw35478step2 = -raw35478step1 := by apply Matrix.ext; change ∀ i j, raw35478step2 i j = -(raw35478step1 i j); unfold raw35478step2 raw35478step1; decide +kernel
      have hl : raw35478step2Labels = raw35478step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4921 node4921Labels := by rfl

def raw35479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw35479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw35479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35479step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35479 raw35479Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw35479 raw35479Labels = mixedMoment B raw35479step0 raw35479step0Labels := by
      have hz : ∀ j, raw35479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35479step0 = (fun i j => raw35479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35479step0 raw35479; decide +kernel
      have hl : raw35479step0Labels = raw35479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35479 raw35479Labels permutation346 hz
    mixedMoment B raw35479step0 raw35479step0Labels = mixedMoment B raw35479step1 raw35479step1Labels := by
      have ha : raw35479step1 = (fun i j => raw35479step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35479step1 raw35479step0; decide +kernel
      have hl : raw35479step1Labels = raw35479step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35479step0 raw35479step0Labels permutation150 permutation2
    mixedMoment B raw35479step1 raw35479step1Labels = mixedMoment B raw35479step2 raw35479step2Labels := by
      have ha : raw35479step2 = -raw35479step1 := by apply Matrix.ext; change ∀ i j, raw35479step2 i j = -(raw35479step1 i j); unfold raw35479step2 raw35479step1; decide +kernel
      have hl : raw35479step2Labels = raw35479step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw35480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35480Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35480step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35480step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35480step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35480step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35480step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35480 raw35480Labels = mixedMoment B node3439 node3439Labels := by
  calc
    mixedMoment B raw35480 raw35480Labels = mixedMoment B raw35480step0 raw35480step0Labels := by
      have hz : ∀ j, raw35480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35480step0 = (fun i j => raw35480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35480step0 raw35480; decide +kernel
      have hl : raw35480step0Labels = raw35480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35480 raw35480Labels permutation346 hz
    mixedMoment B raw35480step0 raw35480step0Labels = mixedMoment B raw35480step1 raw35480step1Labels := by
      have ha : raw35480step1 = (fun i j => raw35480step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35480step1 raw35480step0; decide +kernel
      have hl : raw35480step1Labels = raw35480step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35480step0 raw35480step0Labels permutation56 permutation7
    mixedMoment B raw35480step1 raw35480step1Labels = mixedMoment B raw35480step2 raw35480step2Labels := by
      have ha : raw35480step2 = -raw35480step1 := by apply Matrix.ext; change ∀ i j, raw35480step2 i j = -(raw35480step1 i j); unfold raw35480step2 raw35480step1; decide +kernel
      have hl : raw35480step2Labels = raw35480step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35480step2 raw35480step2Labels = mixedMoment B raw35480step3 raw35480step3Labels := by
      have ha : raw35480step3 = raw35480step2 := by apply Matrix.ext; unfold raw35480step3 raw35480step2; decide +kernel
      have hl : raw35480step2Labels = labelEmbedding1 ∘ raw35480step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35480step2 raw35480step2Labels raw35480step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3439 node3439Labels := by rfl

def raw35481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35481Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35481step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35481 raw35481Labels = mixedMoment B node3650 node3650Labels := by
  calc
    mixedMoment B raw35481 raw35481Labels = mixedMoment B raw35481step0 raw35481step0Labels := by
      have ha : raw35481step0 = (fun i j => raw35481 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35481step0 raw35481; decide +kernel
      have hl : raw35481step0Labels = raw35481Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35481 raw35481Labels permutation583 permutation7
    mixedMoment B raw35481step0 raw35481step0Labels = mixedMoment B raw35481step1 raw35481step1Labels := by
      have ha : raw35481step1 = raw35481step0 := by apply Matrix.ext; unfold raw35481step1 raw35481step0; decide +kernel
      have hl : raw35481step0Labels = labelEmbedding1 ∘ raw35481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35481step0 raw35481step0Labels raw35481step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3650 node3650Labels := by rfl

def raw35482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35482Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35482step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35482step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![2, -2]]
def raw35482step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35482step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw35482step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35482step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw35482step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35482 raw35482Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw35482 raw35482Labels = mixedMoment B raw35482step0 raw35482step0Labels := by
      have hz : ∀ j, raw35482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35482step0 = (fun i j => raw35482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35482step0 raw35482; decide +kernel
      have hl : raw35482step0Labels = raw35482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35482 raw35482Labels permutation346 hz
    mixedMoment B raw35482step0 raw35482step0Labels = mixedMoment B raw35482step1 raw35482step1Labels := by
      have hz : ∀ i, raw35482step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw35482step1 = (fun i j => raw35482step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw35482step1 raw35482step0; decide +kernel
      have hl : raw35482step1Labels = (fun j => raw35482step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35482step0 raw35482step0Labels permutation4 hz
    mixedMoment B raw35482step1 raw35482step1Labels = mixedMoment B raw35482step2 raw35482step2Labels := by
      have ha : raw35482step2 = (fun i j => raw35482step1 (permutation123 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35482step2 raw35482step1; decide +kernel
      have hl : raw35482step2Labels = raw35482step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35482step1 raw35482step1Labels permutation123 permutation0
    mixedMoment B raw35482step2 raw35482step2Labels = mixedMoment B raw35482step3 raw35482step3Labels := by
      have ha : raw35482step3 = -raw35482step2 := by apply Matrix.ext; change ∀ i j, raw35482step3 i j = -(raw35482step2 i j); unfold raw35482step3 raw35482step2; decide +kernel
      have hl : raw35482step3Labels = raw35482step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw35483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35483Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35483step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35483step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35483 raw35483Labels = mixedMoment B node3704 node3704Labels := by
  calc
    mixedMoment B raw35483 raw35483Labels = mixedMoment B raw35483step0 raw35483step0Labels := by
      have hz : ∀ j, raw35483 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35483step0 = (fun i j => raw35483 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35483step0 raw35483; decide +kernel
      have hl : raw35483step0Labels = raw35483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35483 raw35483Labels permutation346 hz
    mixedMoment B raw35483step0 raw35483step0Labels = mixedMoment B raw35483step1 raw35483step1Labels := by
      have ha : raw35483step1 = (fun i j => raw35483step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35483step1 raw35483step0; decide +kernel
      have hl : raw35483step1Labels = raw35483step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35483step0 raw35483step0Labels permutation150 permutation7
    mixedMoment B raw35483step1 raw35483step1Labels = mixedMoment B raw35483step2 raw35483step2Labels := by
      have ha : raw35483step2 = raw35483step1 := by apply Matrix.ext; unfold raw35483step2 raw35483step1; decide +kernel
      have hl : raw35483step1Labels = labelEmbedding1 ∘ raw35483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35483step1 raw35483step1Labels raw35483step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3704 node3704Labels := by rfl

def raw35484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35484Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35484step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35484step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35484 raw35484Labels = mixedMoment B node3704 node3704Labels := by
  calc
    mixedMoment B raw35484 raw35484Labels = mixedMoment B raw35484step0 raw35484step0Labels := by
      have hz : ∀ j, raw35484 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35484step0 = (fun i j => raw35484 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35484step0 raw35484; decide +kernel
      have hl : raw35484step0Labels = raw35484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35484 raw35484Labels permutation346 hz
    mixedMoment B raw35484step0 raw35484step0Labels = mixedMoment B raw35484step1 raw35484step1Labels := by
      have ha : raw35484step1 = (fun i j => raw35484step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35484step1 raw35484step0; decide +kernel
      have hl : raw35484step1Labels = raw35484step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35484step0 raw35484step0Labels permutation126 permutation7
    mixedMoment B raw35484step1 raw35484step1Labels = mixedMoment B raw35484step2 raw35484step2Labels := by
      have ha : raw35484step2 = raw35484step1 := by apply Matrix.ext; unfold raw35484step2 raw35484step1; decide +kernel
      have hl : raw35484step1Labels = labelEmbedding1 ∘ raw35484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35484step1 raw35484step1Labels raw35484step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3704 node3704Labels := by rfl

def raw35485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35485Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35485step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw35485step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw35485step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35485step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw35485step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35485 raw35485Labels = mixedMoment B node3630 node3630Labels := by
  calc
    mixedMoment B raw35485 raw35485Labels = mixedMoment B raw35485step0 raw35485step0Labels := by
      have hz : ∀ j, raw35485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35485step0 = (fun i j => raw35485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35485step0 raw35485; decide +kernel
      have hl : raw35485step0Labels = raw35485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35485 raw35485Labels permutation346 hz
    mixedMoment B raw35485step0 raw35485step0Labels = mixedMoment B raw35485step1 raw35485step1Labels := by
      have ha : raw35485step1 = (fun i j => raw35485step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35485step1 raw35485step0; decide +kernel
      have hl : raw35485step1Labels = raw35485step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35485step0 raw35485step0Labels permutation48 permutation5
    mixedMoment B raw35485step1 raw35485step1Labels = mixedMoment B raw35485step2 raw35485step2Labels := by
      have ha : raw35485step2 = -raw35485step1 := by apply Matrix.ext; change ∀ i j, raw35485step2 i j = -(raw35485step1 i j); unfold raw35485step2 raw35485step1; decide +kernel
      have hl : raw35485step2Labels = raw35485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35485step2 raw35485step2Labels = mixedMoment B raw35485step3 raw35485step3Labels := by
      have ha : raw35485step3 = raw35485step2 := by apply Matrix.ext; unfold raw35485step3 raw35485step2; decide +kernel
      have hl : raw35485step2Labels = labelEmbedding1 ∘ raw35485step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35485step2 raw35485step2Labels raw35485step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3630 node3630Labels := by rfl

def raw35486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35486Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35486step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35486 raw35486Labels = mixedMoment B node3651 node3651Labels := by
  calc
    mixedMoment B raw35486 raw35486Labels = mixedMoment B raw35486step0 raw35486step0Labels := by
      have ha : raw35486step0 = (fun i j => raw35486 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35486step0 raw35486; decide +kernel
      have hl : raw35486step0Labels = raw35486Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35486 raw35486Labels permutation583 permutation7
    mixedMoment B raw35486step0 raw35486step0Labels = mixedMoment B raw35486step1 raw35486step1Labels := by
      have ha : raw35486step1 = raw35486step0 := by apply Matrix.ext; unfold raw35486step1 raw35486step0; decide +kernel
      have hl : raw35486step0Labels = labelEmbedding1 ∘ raw35486step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35486step0 raw35486step0Labels raw35486step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3651 node3651Labels := by rfl

def raw35487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35487Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35487step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35487step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35487 raw35487Labels = mixedMoment B node3665 node3665Labels := by
  calc
    mixedMoment B raw35487 raw35487Labels = mixedMoment B raw35487step0 raw35487step0Labels := by
      have hz : ∀ j, raw35487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35487step0 = (fun i j => raw35487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35487step0 raw35487; decide +kernel
      have hl : raw35487step0Labels = raw35487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35487 raw35487Labels permutation346 hz
    mixedMoment B raw35487step0 raw35487step0Labels = mixedMoment B raw35487step1 raw35487step1Labels := by
      have ha : raw35487step1 = (fun i j => raw35487step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35487step1 raw35487step0; decide +kernel
      have hl : raw35487step1Labels = raw35487step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35487step0 raw35487step0Labels permutation126 permutation7
    mixedMoment B raw35487step1 raw35487step1Labels = mixedMoment B raw35487step2 raw35487step2Labels := by
      have ha : raw35487step2 = raw35487step1 := by apply Matrix.ext; unfold raw35487step2 raw35487step1; decide +kernel
      have hl : raw35487step1Labels = labelEmbedding1 ∘ raw35487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35487step1 raw35487step1Labels raw35487step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3665 node3665Labels := by rfl

def raw35488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35488Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35488step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35488step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35488 raw35488Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw35488 raw35488Labels = mixedMoment B raw35488step0 raw35488step0Labels := by
      have hz : ∀ j, raw35488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35488step0 = (fun i j => raw35488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35488step0 raw35488; decide +kernel
      have hl : raw35488step0Labels = raw35488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35488 raw35488Labels permutation346 hz
    mixedMoment B raw35488step0 raw35488step0Labels = mixedMoment B raw35488step1 raw35488step1Labels := by
      have ha : raw35488step1 = (fun i j => raw35488step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35488step1 raw35488step0; decide +kernel
      have hl : raw35488step1Labels = raw35488step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35488step0 raw35488step0Labels permutation150 permutation7
    mixedMoment B raw35488step1 raw35488step1Labels = mixedMoment B raw35488step2 raw35488step2Labels := by
      have ha : raw35488step2 = raw35488step1 := by apply Matrix.ext; unfold raw35488step2 raw35488step1; decide +kernel
      have hl : raw35488step1Labels = labelEmbedding1 ∘ raw35488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35488step1 raw35488step1Labels raw35488step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw35489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35489Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35489step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35489 raw35489Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw35489 raw35489Labels = mixedMoment B raw35489step0 raw35489step0Labels := by
      have hz : ∀ j, raw35489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35489step0 = (fun i j => raw35489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35489step0 raw35489; decide +kernel
      have hl : raw35489step0Labels = raw35489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35489 raw35489Labels permutation346 hz
    mixedMoment B raw35489step0 raw35489step0Labels = mixedMoment B raw35489step1 raw35489step1Labels := by
      have ha : raw35489step1 = (fun i j => raw35489step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35489step1 raw35489step0; decide +kernel
      have hl : raw35489step1Labels = raw35489step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35489step0 raw35489step0Labels permutation126 permutation7
    mixedMoment B raw35489step1 raw35489step1Labels = mixedMoment B raw35489step2 raw35489step2Labels := by
      have ha : raw35489step2 = raw35489step1 := by apply Matrix.ext; unfold raw35489step2 raw35489step1; decide +kernel
      have hl : raw35489step1Labels = labelEmbedding1 ∘ raw35489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35489step1 raw35489step1Labels raw35489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw35490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw35490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw35490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw35490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35490 raw35490Labels = mixedMoment B node3593 node3593Labels := by
  calc
    mixedMoment B raw35490 raw35490Labels = mixedMoment B raw35490step0 raw35490step0Labels := by
      have ha : raw35490step0 = (fun i j => raw35490 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35490step0 raw35490; decide +kernel
      have hl : raw35490step0Labels = raw35490Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35490 raw35490Labels permutation169 permutation5
    mixedMoment B raw35490step0 raw35490step0Labels = mixedMoment B raw35490step1 raw35490step1Labels := by
      have ha : raw35490step1 = -raw35490step0 := by apply Matrix.ext; change ∀ i j, raw35490step1 i j = -(raw35490step0 i j); unfold raw35490step1 raw35490step0; decide +kernel
      have hl : raw35490step1Labels = raw35490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35490step1 raw35490step1Labels = mixedMoment B raw35490step2 raw35490step2Labels := by
      have ha : raw35490step2 = raw35490step1 := by apply Matrix.ext; unfold raw35490step2 raw35490step1; decide +kernel
      have hl : raw35490step1Labels = labelEmbedding1 ∘ raw35490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35490step1 raw35490step1Labels raw35490step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3593 node3593Labels := by rfl

def raw35491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw35491step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw35491step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35491step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw35491step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35491 raw35491Labels = mixedMoment B node3398 node3398Labels := by
  calc
    mixedMoment B raw35491 raw35491Labels = mixedMoment B raw35491step0 raw35491step0Labels := by
      have ha : raw35491step0 = (fun i j => raw35491 (permutation271 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35491step0 raw35491; decide +kernel
      have hl : raw35491step0Labels = raw35491Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35491 raw35491Labels permutation271 permutation7
    mixedMoment B raw35491step0 raw35491step0Labels = mixedMoment B raw35491step1 raw35491step1Labels := by
      have ha : raw35491step1 = -raw35491step0 := by apply Matrix.ext; change ∀ i j, raw35491step1 i j = -(raw35491step0 i j); unfold raw35491step1 raw35491step0; decide +kernel
      have hl : raw35491step1Labels = raw35491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35491step1 raw35491step1Labels = mixedMoment B raw35491step2 raw35491step2Labels := by
      have ha : raw35491step2 = raw35491step1 := by apply Matrix.ext; unfold raw35491step2 raw35491step1; decide +kernel
      have hl : raw35491step1Labels = labelEmbedding1 ∘ raw35491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35491step1 raw35491step1Labels raw35491step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3398 node3398Labels := by rfl

def raw35492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35492 raw35492Labels = mixedMoment B node3644 node3644Labels := by
  calc
    mixedMoment B raw35492 raw35492Labels = mixedMoment B raw35492step0 raw35492step0Labels := by
      have ha : raw35492step0 = (fun i j => raw35492 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35492step0 raw35492; decide +kernel
      have hl : raw35492step0Labels = raw35492Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35492 raw35492Labels permutation583 permutation7
    mixedMoment B raw35492step0 raw35492step0Labels = mixedMoment B raw35492step1 raw35492step1Labels := by
      have ha : raw35492step1 = raw35492step0 := by apply Matrix.ext; unfold raw35492step1 raw35492step0; decide +kernel
      have hl : raw35492step0Labels = labelEmbedding1 ∘ raw35492step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35492step0 raw35492step0Labels raw35492step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3644 node3644Labels := by rfl

def raw35493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35493step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35493 raw35493Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw35493 raw35493Labels = mixedMoment B raw35493step0 raw35493step0Labels := by
      have ha : raw35493step0 = (fun i j => raw35493 (permutation681 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35493step0 raw35493; decide +kernel
      have hl : raw35493step0Labels = raw35493Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35493 raw35493Labels permutation681 permutation7
    mixedMoment B raw35493step0 raw35493step0Labels = mixedMoment B raw35493step1 raw35493step1Labels := by
      have ha : raw35493step1 = raw35493step0 := by apply Matrix.ext; unfold raw35493step1 raw35493step0; decide +kernel
      have hl : raw35493step0Labels = labelEmbedding1 ∘ raw35493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35493step0 raw35493step0Labels raw35493step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw35494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35494step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35494 raw35494Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw35494 raw35494Labels = mixedMoment B raw35494step0 raw35494step0Labels := by
      have ha : raw35494step0 = (fun i j => raw35494 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35494step0 raw35494; decide +kernel
      have hl : raw35494step0Labels = raw35494Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35494 raw35494Labels permutation583 permutation7
    mixedMoment B raw35494step0 raw35494step0Labels = mixedMoment B raw35494step1 raw35494step1Labels := by
      have ha : raw35494step1 = raw35494step0 := by apply Matrix.ext; unfold raw35494step1 raw35494step0; decide +kernel
      have hl : raw35494step0Labels = labelEmbedding1 ∘ raw35494step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35494step0 raw35494step0Labels raw35494step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw35495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35495step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![0, -2, 2], ![-2, 1, 1]]
def raw35495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw35495step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35495step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw35495step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35495 raw35495Labels = mixedMoment B node3594 node3594Labels := by
  calc
    mixedMoment B raw35495 raw35495Labels = mixedMoment B raw35495step0 raw35495step0Labels := by
      have hz : ∀ j, raw35495 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35495step0 = (fun i j => raw35495 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35495step0 raw35495; decide +kernel
      have hl : raw35495step0Labels = raw35495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35495 raw35495Labels permutation346 hz
    mixedMoment B raw35495step0 raw35495step0Labels = mixedMoment B raw35495step1 raw35495step1Labels := by
      have ha : raw35495step1 = (fun i j => raw35495step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35495step1 raw35495step0; decide +kernel
      have hl : raw35495step1Labels = raw35495step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35495step0 raw35495step0Labels permutation35 permutation5
    mixedMoment B raw35495step1 raw35495step1Labels = mixedMoment B raw35495step2 raw35495step2Labels := by
      have ha : raw35495step2 = -raw35495step1 := by apply Matrix.ext; change ∀ i j, raw35495step2 i j = -(raw35495step1 i j); unfold raw35495step2 raw35495step1; decide +kernel
      have hl : raw35495step2Labels = raw35495step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35495step2 raw35495step2Labels = mixedMoment B raw35495step3 raw35495step3Labels := by
      have ha : raw35495step3 = raw35495step2 := by apply Matrix.ext; unfold raw35495step3 raw35495step2; decide +kernel
      have hl : raw35495step2Labels = labelEmbedding1 ∘ raw35495step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35495step2 raw35495step2Labels raw35495step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3594 node3594Labels := by rfl

def raw35496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35496step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw35496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw35496step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35496step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw35496step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35496 raw35496Labels = mixedMoment B node3402 node3402Labels := by
  calc
    mixedMoment B raw35496 raw35496Labels = mixedMoment B raw35496step0 raw35496step0Labels := by
      have hz : ∀ j, raw35496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35496step0 = (fun i j => raw35496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35496step0 raw35496; decide +kernel
      have hl : raw35496step0Labels = raw35496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35496 raw35496Labels permutation346 hz
    mixedMoment B raw35496step0 raw35496step0Labels = mixedMoment B raw35496step1 raw35496step1Labels := by
      have ha : raw35496step1 = (fun i j => raw35496step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35496step1 raw35496step0; decide +kernel
      have hl : raw35496step1Labels = raw35496step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35496step0 raw35496step0Labels permutation56 permutation7
    mixedMoment B raw35496step1 raw35496step1Labels = mixedMoment B raw35496step2 raw35496step2Labels := by
      have ha : raw35496step2 = -raw35496step1 := by apply Matrix.ext; change ∀ i j, raw35496step2 i j = -(raw35496step1 i j); unfold raw35496step2 raw35496step1; decide +kernel
      have hl : raw35496step2Labels = raw35496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35496step2 raw35496step2Labels = mixedMoment B raw35496step3 raw35496step3Labels := by
      have ha : raw35496step3 = raw35496step2 := by apply Matrix.ext; unfold raw35496step3 raw35496step2; decide +kernel
      have hl : raw35496step2Labels = labelEmbedding1 ∘ raw35496step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35496step2 raw35496step2Labels raw35496step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3402 node3402Labels := by rfl

def raw35497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35497step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35497 raw35497Labels = mixedMoment B node3649 node3649Labels := by
  calc
    mixedMoment B raw35497 raw35497Labels = mixedMoment B raw35497step0 raw35497step0Labels := by
      have ha : raw35497step0 = (fun i j => raw35497 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35497step0 raw35497; decide +kernel
      have hl : raw35497step0Labels = raw35497Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35497 raw35497Labels permutation583 permutation7
    mixedMoment B raw35497step0 raw35497step0Labels = mixedMoment B raw35497step1 raw35497step1Labels := by
      have ha : raw35497step1 = raw35497step0 := by apply Matrix.ext; unfold raw35497step1 raw35497step0; decide +kernel
      have hl : raw35497step0Labels = labelEmbedding1 ∘ raw35497step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35497step0 raw35497step0Labels raw35497step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3649 node3649Labels := by rfl

def raw35498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35498step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35498 raw35498Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw35498 raw35498Labels = mixedMoment B raw35498step0 raw35498step0Labels := by
      have hz : ∀ j, raw35498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35498step0 = (fun i j => raw35498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35498step0 raw35498; decide +kernel
      have hl : raw35498step0Labels = raw35498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35498 raw35498Labels permutation346 hz
    mixedMoment B raw35498step0 raw35498step0Labels = mixedMoment B raw35498step1 raw35498step1Labels := by
      have ha : raw35498step1 = (fun i j => raw35498step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35498step1 raw35498step0; decide +kernel
      have hl : raw35498step1Labels = raw35498step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35498step0 raw35498step0Labels permutation150 permutation7
    mixedMoment B raw35498step1 raw35498step1Labels = mixedMoment B raw35498step2 raw35498step2Labels := by
      have ha : raw35498step2 = raw35498step1 := by apply Matrix.ext; unfold raw35498step2 raw35498step1; decide +kernel
      have hl : raw35498step1Labels = labelEmbedding1 ∘ raw35498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35498step1 raw35498step1Labels raw35498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3702 node3702Labels := by rfl

def raw35499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35499 raw35499Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw35499 raw35499Labels = mixedMoment B raw35499step0 raw35499step0Labels := by
      have hz : ∀ j, raw35499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35499step0 = (fun i j => raw35499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35499step0 raw35499; decide +kernel
      have hl : raw35499step0Labels = raw35499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35499 raw35499Labels permutation346 hz
    mixedMoment B raw35499step0 raw35499step0Labels = mixedMoment B raw35499step1 raw35499step1Labels := by
      have ha : raw35499step1 = (fun i j => raw35499step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35499step1 raw35499step0; decide +kernel
      have hl : raw35499step1Labels = raw35499step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35499step0 raw35499step0Labels permutation126 permutation7
    mixedMoment B raw35499step1 raw35499step1Labels = mixedMoment B raw35499step2 raw35499step2Labels := by
      have ha : raw35499step2 = raw35499step1 := by apply Matrix.ext; unfold raw35499step2 raw35499step1; decide +kernel
      have hl : raw35499step1Labels = labelEmbedding1 ∘ raw35499step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35499step1 raw35499step1Labels raw35499step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3702 node3702Labels := by rfl

def raw35500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw35500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw35500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35500 raw35500Labels = mixedMoment B node3326 node3326Labels := by
  calc
    mixedMoment B raw35500 raw35500Labels = mixedMoment B raw35500step0 raw35500step0Labels := by
      have hz : ∀ j, raw35500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35500step0 = (fun i j => raw35500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35500step0 raw35500; decide +kernel
      have hl : raw35500step0Labels = raw35500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35500 raw35500Labels permutation346 hz
    mixedMoment B raw35500step0 raw35500step0Labels = mixedMoment B raw35500step1 raw35500step1Labels := by
      have ha : raw35500step1 = (fun i j => raw35500step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35500step1 raw35500step0; decide +kernel
      have hl : raw35500step1Labels = raw35500step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35500step0 raw35500step0Labels permutation126 permutation7
    mixedMoment B raw35500step1 raw35500step1Labels = mixedMoment B raw35500step2 raw35500step2Labels := by
      have ha : raw35500step2 = raw35500step1 := by apply Matrix.ext; unfold raw35500step2 raw35500step1; decide +kernel
      have hl : raw35500step1Labels = labelEmbedding1 ∘ raw35500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35500step1 raw35500step1Labels raw35500step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3326 node3326Labels := by rfl

def raw35501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35501step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw35501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw35501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35501 raw35501Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw35501 raw35501Labels = mixedMoment B raw35501step0 raw35501step0Labels := by
      have hz : ∀ j, raw35501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35501step0 = (fun i j => raw35501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35501step0 raw35501; decide +kernel
      have hl : raw35501step0Labels = raw35501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35501 raw35501Labels permutation346 hz
    mixedMoment B raw35501step0 raw35501step0Labels = mixedMoment B raw35501step1 raw35501step1Labels := by
      have ha : raw35501step1 = (fun i j => raw35501step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35501step1 raw35501step0; decide +kernel
      have hl : raw35501step1Labels = raw35501step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35501step0 raw35501step0Labels permutation126 permutation7
    mixedMoment B raw35501step1 raw35501step1Labels = mixedMoment B raw35501step2 raw35501step2Labels := by
      have ha : raw35501step2 = raw35501step1 := by apply Matrix.ext; unfold raw35501step2 raw35501step1; decide +kernel
      have hl : raw35501step1Labels = labelEmbedding1 ∘ raw35501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35501step1 raw35501step1Labels raw35501step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3325 node3325Labels := by rfl

def raw35502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35502 raw35502Labels = mixedMoment B node3316 node3316Labels := by
  calc
    mixedMoment B raw35502 raw35502Labels = mixedMoment B raw35502step0 raw35502step0Labels := by
      have ha : raw35502step0 = (fun i j => raw35502 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35502step0 raw35502; decide +kernel
      have hl : raw35502step0Labels = raw35502Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35502 raw35502Labels permutation583 permutation7
    mixedMoment B raw35502step0 raw35502step0Labels = mixedMoment B raw35502step1 raw35502step1Labels := by
      have ha : raw35502step1 = raw35502step0 := by apply Matrix.ext; unfold raw35502step1 raw35502step0; decide +kernel
      have hl : raw35502step0Labels = labelEmbedding1 ∘ raw35502step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35502step0 raw35502step0Labels raw35502step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3316 node3316Labels := by rfl

def raw35503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35503 raw35503Labels = mixedMoment B node3328 node3328Labels := by
  calc
    mixedMoment B raw35503 raw35503Labels = mixedMoment B raw35503step0 raw35503step0Labels := by
      have hz : ∀ j, raw35503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35503step0 = (fun i j => raw35503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35503step0 raw35503; decide +kernel
      have hl : raw35503step0Labels = raw35503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35503 raw35503Labels permutation346 hz
    mixedMoment B raw35503step0 raw35503step0Labels = mixedMoment B raw35503step1 raw35503step1Labels := by
      have ha : raw35503step1 = (fun i j => raw35503step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35503step1 raw35503step0; decide +kernel
      have hl : raw35503step1Labels = raw35503step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35503step0 raw35503step0Labels permutation126 permutation7
    mixedMoment B raw35503step1 raw35503step1Labels = mixedMoment B raw35503step2 raw35503step2Labels := by
      have ha : raw35503step2 = raw35503step1 := by apply Matrix.ext; unfold raw35503step2 raw35503step1; decide +kernel
      have hl : raw35503step1Labels = labelEmbedding1 ∘ raw35503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35503step1 raw35503step1Labels raw35503step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3328 node3328Labels := by rfl

def raw35504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw35504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw35504step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35504 raw35504Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw35504 raw35504Labels = mixedMoment B raw35504step0 raw35504step0Labels := by
      have hz : ∀ j, raw35504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35504step0 = (fun i j => raw35504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35504step0 raw35504; decide +kernel
      have hl : raw35504step0Labels = raw35504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35504 raw35504Labels permutation346 hz
    mixedMoment B raw35504step0 raw35504step0Labels = mixedMoment B raw35504step1 raw35504step1Labels := by
      have ha : raw35504step1 = (fun i j => raw35504step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35504step1 raw35504step0; decide +kernel
      have hl : raw35504step1Labels = raw35504step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35504step0 raw35504step0Labels permutation126 permutation7
    mixedMoment B raw35504step1 raw35504step1Labels = mixedMoment B raw35504step2 raw35504step2Labels := by
      have ha : raw35504step2 = raw35504step1 := by apply Matrix.ext; unfold raw35504step2 raw35504step1; decide +kernel
      have hl : raw35504step1Labels = labelEmbedding1 ∘ raw35504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35504step1 raw35504step1Labels raw35504step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3354 node3354Labels := by rfl

def raw35505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw35505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw35505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35505 raw35505Labels = mixedMoment B node3326 node3326Labels := by
  calc
    mixedMoment B raw35505 raw35505Labels = mixedMoment B raw35505step0 raw35505step0Labels := by
      have hz : ∀ j, raw35505 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35505step0 = (fun i j => raw35505 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35505step0 raw35505; decide +kernel
      have hl : raw35505step0Labels = raw35505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35505 raw35505Labels permutation346 hz
    mixedMoment B raw35505step0 raw35505step0Labels = mixedMoment B raw35505step1 raw35505step1Labels := by
      have ha : raw35505step1 = (fun i j => raw35505step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35505step1 raw35505step0; decide +kernel
      have hl : raw35505step1Labels = raw35505step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35505step0 raw35505step0Labels permutation150 permutation7
    mixedMoment B raw35505step1 raw35505step1Labels = mixedMoment B raw35505step2 raw35505step2Labels := by
      have ha : raw35505step2 = raw35505step1 := by apply Matrix.ext; unfold raw35505step2 raw35505step1; decide +kernel
      have hl : raw35505step1Labels = labelEmbedding1 ∘ raw35505step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35505step1 raw35505step1Labels raw35505step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3326 node3326Labels := by rfl

def raw35506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35506step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw35506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw35506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35506 raw35506Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw35506 raw35506Labels = mixedMoment B raw35506step0 raw35506step0Labels := by
      have hz : ∀ j, raw35506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35506step0 = (fun i j => raw35506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35506step0 raw35506; decide +kernel
      have hl : raw35506step0Labels = raw35506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35506 raw35506Labels permutation346 hz
    mixedMoment B raw35506step0 raw35506step0Labels = mixedMoment B raw35506step1 raw35506step1Labels := by
      have ha : raw35506step1 = (fun i j => raw35506step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35506step1 raw35506step0; decide +kernel
      have hl : raw35506step1Labels = raw35506step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35506step0 raw35506step0Labels permutation150 permutation7
    mixedMoment B raw35506step1 raw35506step1Labels = mixedMoment B raw35506step2 raw35506step2Labels := by
      have ha : raw35506step2 = raw35506step1 := by apply Matrix.ext; unfold raw35506step2 raw35506step1; decide +kernel
      have hl : raw35506step1Labels = labelEmbedding1 ∘ raw35506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35506step1 raw35506step1Labels raw35506step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3325 node3325Labels := by rfl

def raw35507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35507step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35507 raw35507Labels = mixedMoment B node3316 node3316Labels := by
  calc
    mixedMoment B raw35507 raw35507Labels = mixedMoment B raw35507step0 raw35507step0Labels := by
      have ha : raw35507step0 = (fun i j => raw35507 (permutation681 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35507step0 raw35507; decide +kernel
      have hl : raw35507step0Labels = raw35507Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35507 raw35507Labels permutation681 permutation7
    mixedMoment B raw35507step0 raw35507step0Labels = mixedMoment B raw35507step1 raw35507step1Labels := by
      have ha : raw35507step1 = raw35507step0 := by apply Matrix.ext; unfold raw35507step1 raw35507step0; decide +kernel
      have hl : raw35507step0Labels = labelEmbedding1 ∘ raw35507step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35507step0 raw35507step0Labels raw35507step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3316 node3316Labels := by rfl

def raw35508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35508step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35508 raw35508Labels = mixedMoment B node3328 node3328Labels := by
  calc
    mixedMoment B raw35508 raw35508Labels = mixedMoment B raw35508step0 raw35508step0Labels := by
      have hz : ∀ j, raw35508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35508step0 = (fun i j => raw35508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35508step0 raw35508; decide +kernel
      have hl : raw35508step0Labels = raw35508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35508 raw35508Labels permutation346 hz
    mixedMoment B raw35508step0 raw35508step0Labels = mixedMoment B raw35508step1 raw35508step1Labels := by
      have ha : raw35508step1 = (fun i j => raw35508step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35508step1 raw35508step0; decide +kernel
      have hl : raw35508step1Labels = raw35508step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35508step0 raw35508step0Labels permutation150 permutation7
    mixedMoment B raw35508step1 raw35508step1Labels = mixedMoment B raw35508step2 raw35508step2Labels := by
      have ha : raw35508step2 = raw35508step1 := by apply Matrix.ext; unfold raw35508step2 raw35508step1; decide +kernel
      have hl : raw35508step1Labels = labelEmbedding1 ∘ raw35508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35508step1 raw35508step1Labels raw35508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3328 node3328Labels := by rfl

def raw35509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw35509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw35509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35509 raw35509Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw35509 raw35509Labels = mixedMoment B raw35509step0 raw35509step0Labels := by
      have hz : ∀ j, raw35509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35509step0 = (fun i j => raw35509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35509step0 raw35509; decide +kernel
      have hl : raw35509step0Labels = raw35509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35509 raw35509Labels permutation346 hz
    mixedMoment B raw35509step0 raw35509step0Labels = mixedMoment B raw35509step1 raw35509step1Labels := by
      have ha : raw35509step1 = (fun i j => raw35509step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35509step1 raw35509step0; decide +kernel
      have hl : raw35509step1Labels = raw35509step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35509step0 raw35509step0Labels permutation150 permutation7
    mixedMoment B raw35509step1 raw35509step1Labels = mixedMoment B raw35509step2 raw35509step2Labels := by
      have ha : raw35509step2 = raw35509step1 := by apply Matrix.ext; unfold raw35509step2 raw35509step1; decide +kernel
      have hl : raw35509step1Labels = labelEmbedding1 ∘ raw35509step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35509step1 raw35509step1Labels raw35509step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3354 node3354Labels := by rfl

def raw35510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35510 raw35510Labels = mixedMoment B node2316 node2316Labels := by
  calc
    mixedMoment B raw35510 raw35510Labels = mixedMoment B raw35510step0 raw35510step0Labels := by
      have ha : raw35510step0 = (fun i j => raw35510 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35510step0 raw35510; decide +kernel
      have hl : raw35510step0Labels = raw35510Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35510 raw35510Labels permutation271 permutation2
    _ = mixedMoment B node2316 node2316Labels := by rfl

def raw35511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35511 raw35511Labels = mixedMoment B node3637 node3637Labels := by
  calc
    mixedMoment B raw35511 raw35511Labels = mixedMoment B raw35511step0 raw35511step0Labels := by
      have ha : raw35511step0 = (fun i j => raw35511 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35511step0 raw35511; decide +kernel
      have hl : raw35511step0Labels = raw35511Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35511 raw35511Labels permutation583 permutation2
    mixedMoment B raw35511step0 raw35511step0Labels = mixedMoment B raw35511step1 raw35511step1Labels := by
      have ha : raw35511step1 = -raw35511step0 := by apply Matrix.ext; change ∀ i j, raw35511step1 i j = -(raw35511step0 i j); unfold raw35511step1 raw35511step0; decide +kernel
      have hl : raw35511step1Labels = raw35511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3637 node3637Labels := by rfl

def raw35512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35512 raw35512Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw35512 raw35512Labels = mixedMoment B raw35512step0 raw35512step0Labels := by
      have ha : raw35512step0 = (fun i j => raw35512 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35512step0 raw35512; decide +kernel
      have hl : raw35512step0Labels = raw35512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35512 raw35512Labels permutation271 permutation2
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw35513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35513 raw35513Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw35513 raw35513Labels = mixedMoment B raw35513step0 raw35513step0Labels := by
      have ha : raw35513step0 = (fun i j => raw35513 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35513step0 raw35513; decide +kernel
      have hl : raw35513step0Labels = raw35513Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35513 raw35513Labels permutation272 permutation2
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw35514 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 3, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 3, -2], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw35514step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35514step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35514step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35514step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35514 raw35514Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw35514 raw35514Labels = mixedMoment B raw35514step0 raw35514step0Labels := by
      have hz : ∀ j, raw35514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35514step0 = (fun i j => raw35514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35514step0 raw35514; decide +kernel
      have hl : raw35514step0Labels = raw35514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35514 raw35514Labels permutation346 hz
    mixedMoment B raw35514step0 raw35514step0Labels = mixedMoment B raw35514step1 raw35514step1Labels := by
      have ha : raw35514step1 = (fun i j => raw35514step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35514step1 raw35514step0; decide +kernel
      have hl : raw35514step1Labels = raw35514step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35514step0 raw35514step0Labels permutation62 permutation4
    mixedMoment B raw35514step1 raw35514step1Labels = mixedMoment B raw35514step2 raw35514step2Labels := by
      have ha : raw35514step2 = -raw35514step1 := by apply Matrix.ext; change ∀ i j, raw35514step2 i j = -(raw35514step1 i j); unfold raw35514step2 raw35514step1; decide +kernel
      have hl : raw35514step2Labels = raw35514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35514step2 raw35514step2Labels = mixedMoment B raw35514step3 raw35514step3Labels := by
      have ha : raw35514step3 = raw35514step2 := by apply Matrix.ext; unfold raw35514step3 raw35514step2; decide +kernel
      have hl : raw35514step2Labels = labelEmbedding7 ∘ raw35514step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35514step2 raw35514step2Labels raw35514step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw35515 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35515step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35515step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35515step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35515step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35515 raw35515Labels = mixedMoment B node5320 node5320Labels := by
  calc
    mixedMoment B raw35515 raw35515Labels = mixedMoment B raw35515step0 raw35515step0Labels := by
      have ha : raw35515step0 = (fun i j => raw35515 (permutation583 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35515step0 raw35515; decide +kernel
      have hl : raw35515step0Labels = raw35515Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35515 raw35515Labels permutation583 permutation6
    mixedMoment B raw35515step0 raw35515step0Labels = mixedMoment B raw35515step1 raw35515step1Labels := by
      have ha : raw35515step1 = -raw35515step0 := by apply Matrix.ext; change ∀ i j, raw35515step1 i j = -(raw35515step0 i j); unfold raw35515step1 raw35515step0; decide +kernel
      have hl : raw35515step1Labels = raw35515step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35515step1 raw35515step1Labels = mixedMoment B raw35515step2 raw35515step2Labels := by
      have ha : raw35515step2 = raw35515step1 := by apply Matrix.ext; unfold raw35515step2 raw35515step1; decide +kernel
      have hl : raw35515step1Labels = labelEmbedding9 ∘ raw35515step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35515step1 raw35515step1Labels raw35515step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5320 node5320Labels := by rfl

def raw35516 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35516step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35516step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35516 raw35516Labels = mixedMoment B node5329 node5329Labels := by
  calc
    mixedMoment B raw35516 raw35516Labels = mixedMoment B raw35516step0 raw35516step0Labels := by
      have hz : ∀ j, raw35516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35516step0 = (fun i j => raw35516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35516step0 raw35516; decide +kernel
      have hl : raw35516step0Labels = raw35516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35516 raw35516Labels permutation346 hz
    mixedMoment B raw35516step0 raw35516step0Labels = mixedMoment B raw35516step1 raw35516step1Labels := by
      have ha : raw35516step1 = (fun i j => raw35516step0 (permutation123 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35516step1 raw35516step0; decide +kernel
      have hl : raw35516step1Labels = raw35516step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35516step0 raw35516step0Labels permutation123 permutation4
    mixedMoment B raw35516step1 raw35516step1Labels = mixedMoment B raw35516step2 raw35516step2Labels := by
      have ha : raw35516step2 = raw35516step1 := by apply Matrix.ext; unfold raw35516step2 raw35516step1; decide +kernel
      have hl : raw35516step1Labels = labelEmbedding7 ∘ raw35516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35516step1 raw35516step1Labels raw35516step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5329 node5329Labels := by rfl

def raw35517 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35517step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35517step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35517step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35517 raw35517Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35517 raw35517Labels = mixedMoment B raw35517step0 raw35517step0Labels := by
      have hz : ∀ j, raw35517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35517step0 = (fun i j => raw35517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35517step0 raw35517; decide +kernel
      have hl : raw35517step0Labels = raw35517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35517 raw35517Labels permutation346 hz
    mixedMoment B raw35517step0 raw35517step0Labels = mixedMoment B raw35517step1 raw35517step1Labels := by
      have ha : raw35517step1 = (fun i j => raw35517step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35517step1 raw35517step0; decide +kernel
      have hl : raw35517step1Labels = raw35517step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35517step0 raw35517step0Labels permutation150 permutation6
    mixedMoment B raw35517step1 raw35517step1Labels = mixedMoment B raw35517step2 raw35517step2Labels := by
      have ha : raw35517step2 = -raw35517step1 := by apply Matrix.ext; change ∀ i j, raw35517step2 i j = -(raw35517step1 i j); unfold raw35517step2 raw35517step1; decide +kernel
      have hl : raw35517step2Labels = raw35517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35517step2 raw35517step2Labels = mixedMoment B raw35517step3 raw35517step3Labels := by
      have ha : raw35517step3 = raw35517step2 := by apply Matrix.ext; unfold raw35517step3 raw35517step2; decide +kernel
      have hl : raw35517step2Labels = labelEmbedding9 ∘ raw35517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35517step2 raw35517step2Labels raw35517step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35518 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35518step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35518 raw35518Labels = mixedMoment B node5313 node5313Labels := by
  calc
    mixedMoment B raw35518 raw35518Labels = mixedMoment B raw35518step0 raw35518step0Labels := by
      have ha : raw35518step0 = (fun i j => raw35518 (permutation583 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35518step0 raw35518; decide +kernel
      have hl : raw35518step0Labels = raw35518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35518 raw35518Labels permutation583 permutation4
    mixedMoment B raw35518step0 raw35518step0Labels = mixedMoment B raw35518step1 raw35518step1Labels := by
      have ha : raw35518step1 = raw35518step0 := by apply Matrix.ext; unfold raw35518step1 raw35518step0; decide +kernel
      have hl : raw35518step0Labels = labelEmbedding7 ∘ raw35518step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35518step0 raw35518step0Labels raw35518step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5313 node5313Labels := by rfl

def raw35519 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35519step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35519step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35519step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35519step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35519 raw35519Labels = mixedMoment B node4985 node4985Labels := by
  calc
    mixedMoment B raw35519 raw35519Labels = mixedMoment B raw35519step0 raw35519step0Labels := by
      have ha : raw35519step0 = (fun i j => raw35519 (permutation271 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35519step0 raw35519; decide +kernel
      have hl : raw35519step0Labels = raw35519Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35519 raw35519Labels permutation271 permutation4
    mixedMoment B raw35519step0 raw35519step0Labels = mixedMoment B raw35519step1 raw35519step1Labels := by
      have ha : raw35519step1 = -raw35519step0 := by apply Matrix.ext; change ∀ i j, raw35519step1 i j = -(raw35519step0 i j); unfold raw35519step1 raw35519step0; decide +kernel
      have hl : raw35519step1Labels = raw35519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35519step1 raw35519step1Labels = mixedMoment B raw35519step2 raw35519step2Labels := by
      have ha : raw35519step2 = raw35519step1 := by apply Matrix.ext; unfold raw35519step2 raw35519step1; decide +kernel
      have hl : raw35519step1Labels = labelEmbedding7 ∘ raw35519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35519step1 raw35519step1Labels raw35519step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4985 node4985Labels := by rfl

def raw35520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35520step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35520 raw35520Labels = mixedMoment B node5315 node5315Labels := by
  calc
    mixedMoment B raw35520 raw35520Labels = mixedMoment B raw35520step0 raw35520step0Labels := by
      have ha : raw35520step0 = (fun i j => raw35520 (permutation581 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35520step0 raw35520; decide +kernel
      have hl : raw35520step0Labels = raw35520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35520 raw35520Labels permutation581 permutation4
    mixedMoment B raw35520step0 raw35520step0Labels = mixedMoment B raw35520step1 raw35520step1Labels := by
      have ha : raw35520step1 = raw35520step0 := by apply Matrix.ext; unfold raw35520step1 raw35520step0; decide +kernel
      have hl : raw35520step0Labels = labelEmbedding7 ∘ raw35520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35520step0 raw35520step0Labels raw35520step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5315 node5315Labels := by rfl

def raw35521 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw35521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35521step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35521 raw35521Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw35521 raw35521Labels = mixedMoment B raw35521step0 raw35521step0Labels := by
      have ha : raw35521step0 = (fun i j => raw35521 (permutation271 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35521step0 raw35521; decide +kernel
      have hl : raw35521step0Labels = raw35521Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35521 raw35521Labels permutation271 permutation6
    mixedMoment B raw35521step0 raw35521step0Labels = mixedMoment B raw35521step1 raw35521step1Labels := by
      have ha : raw35521step1 = raw35521step0 := by apply Matrix.ext; unfold raw35521step1 raw35521step0; decide +kernel
      have hl : raw35521step0Labels = labelEmbedding9 ∘ raw35521step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35521step0 raw35521step0Labels raw35521step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw35522 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, -2, 2], ![0, -2, 2]]
def raw35522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35522step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-2, 2], ![-2, 2]]
def raw35522step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw35522step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw35522step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw35522step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw35522step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35522 raw35522Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw35522 raw35522Labels = mixedMoment B raw35522step0 raw35522step0Labels := by
      have hz : ∀ j, raw35522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35522step0 = (fun i j => raw35522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35522step0 raw35522; decide +kernel
      have hl : raw35522step0Labels = raw35522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35522 raw35522Labels permutation434 hz
    mixedMoment B raw35522step0 raw35522step0Labels = mixedMoment B raw35522step1 raw35522step1Labels := by
      have hz : ∀ j, raw35522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35522step1 = (fun i j => raw35522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35522step1 raw35522step0; decide +kernel
      have hl : raw35522step1Labels = raw35522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35522step0 raw35522step0Labels permutation80 hz
    mixedMoment B raw35522step1 raw35522step1Labels = mixedMoment B raw35522step2 raw35522step2Labels := by
      have hz : ∀ i, raw35522step1 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw35522step2 = (fun i j => raw35522step1 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw35522step2 raw35522step1; decide +kernel
      have hl : raw35522step2Labels = (fun j => raw35522step1Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35522step1 raw35522step1Labels permutation2 hz
    mixedMoment B raw35522step2 raw35522step2Labels = mixedMoment B raw35522step3 raw35522step3Labels := by
      have ha : raw35522step3 = (fun i j => raw35522step2 (permutation24 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35522step3 raw35522step2; decide +kernel
      have hl : raw35522step3Labels = raw35522step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35522step2 raw35522step2Labels permutation24 permutation0
    mixedMoment B raw35522step3 raw35522step3Labels = mixedMoment B raw35522step4 raw35522step4Labels := by
      have ha : raw35522step4 = raw35522step3 := by apply Matrix.ext; unfold raw35522step4 raw35522step3; decide +kernel
      have hl : raw35522step3Labels = labelEmbedding3 ∘ raw35522step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35522step3 raw35522step3Labels raw35522step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4089 node4089Labels := by rfl

def raw35523 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, -2, 2], ![0, -2, 2]]
def raw35523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw35523step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35523step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35523step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35523step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35523 raw35523Labels = mixedMoment B node5024 node5024Labels := by
  calc
    mixedMoment B raw35523 raw35523Labels = mixedMoment B raw35523step0 raw35523step0Labels := by
      have hz : ∀ j, raw35523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35523step0 = (fun i j => raw35523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35523step0 raw35523; decide +kernel
      have hl : raw35523step0Labels = raw35523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35523 raw35523Labels permutation434 hz
    mixedMoment B raw35523step0 raw35523step0Labels = mixedMoment B raw35523step1 raw35523step1Labels := by
      have hz : ∀ j, raw35523step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35523step1 = (fun i j => raw35523step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35523step1 raw35523step0; decide +kernel
      have hl : raw35523step1Labels = raw35523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35523step0 raw35523step0Labels permutation80 hz
    mixedMoment B raw35523step1 raw35523step1Labels = mixedMoment B raw35523step2 raw35523step2Labels := by
      have ha : raw35523step2 = (fun i j => raw35523step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35523step2 raw35523step1; decide +kernel
      have hl : raw35523step2Labels = raw35523step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35523step1 raw35523step1Labels permutation14 permutation4
    mixedMoment B raw35523step2 raw35523step2Labels = mixedMoment B raw35523step3 raw35523step3Labels := by
      have ha : raw35523step3 = -raw35523step2 := by apply Matrix.ext; change ∀ i j, raw35523step3 i j = -(raw35523step2 i j); unfold raw35523step3 raw35523step2; decide +kernel
      have hl : raw35523step3Labels = raw35523step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35523step3 raw35523step3Labels = mixedMoment B raw35523step4 raw35523step4Labels := by
      have ha : raw35523step4 = raw35523step3 := by apply Matrix.ext; unfold raw35523step4 raw35523step3; decide +kernel
      have hl : raw35523step3Labels = labelEmbedding7 ∘ raw35523step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35523step3 raw35523step3Labels raw35523step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5024 node5024Labels := by rfl

def raw35524 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35524step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35524step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35524step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35524step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35524 raw35524Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw35524 raw35524Labels = mixedMoment B raw35524step0 raw35524step0Labels := by
      have hz : ∀ j, raw35524 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35524step0 = (fun i j => raw35524 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35524step0 raw35524; decide +kernel
      have hl : raw35524step0Labels = raw35524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35524 raw35524Labels permutation434 hz
    mixedMoment B raw35524step0 raw35524step0Labels = mixedMoment B raw35524step1 raw35524step1Labels := by
      have ha : raw35524step1 = (fun i j => raw35524step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35524step1 raw35524step0; decide +kernel
      have hl : raw35524step1Labels = raw35524step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35524step0 raw35524step0Labels permutation126 permutation6
    mixedMoment B raw35524step1 raw35524step1Labels = mixedMoment B raw35524step2 raw35524step2Labels := by
      have ha : raw35524step2 = -raw35524step1 := by apply Matrix.ext; change ∀ i j, raw35524step2 i j = -(raw35524step1 i j); unfold raw35524step2 raw35524step1; decide +kernel
      have hl : raw35524step2Labels = raw35524step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35524step2 raw35524step2Labels = mixedMoment B raw35524step3 raw35524step3Labels := by
      have ha : raw35524step3 = raw35524step2 := by apply Matrix.ext; unfold raw35524step3 raw35524step2; decide +kernel
      have hl : raw35524step2Labels = labelEmbedding9 ∘ raw35524step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35524step2 raw35524step2Labels raw35524step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5327 node5327Labels := by rfl

def raw35525 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw35525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw35525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35525step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35525 raw35525Labels = mixedMoment B node4915 node4915Labels := by
  calc
    mixedMoment B raw35525 raw35525Labels = mixedMoment B raw35525step0 raw35525step0Labels := by
      have hz : ∀ j, raw35525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35525step0 = (fun i j => raw35525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35525step0 raw35525; decide +kernel
      have hl : raw35525step0Labels = raw35525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35525 raw35525Labels permutation346 hz
    mixedMoment B raw35525step0 raw35525step0Labels = mixedMoment B raw35525step1 raw35525step1Labels := by
      have ha : raw35525step1 = (fun i j => raw35525step0 (permutation126 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35525step1 raw35525step0; decide +kernel
      have hl : raw35525step1Labels = raw35525step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35525step0 raw35525step0Labels permutation126 permutation4
    mixedMoment B raw35525step1 raw35525step1Labels = mixedMoment B raw35525step2 raw35525step2Labels := by
      have ha : raw35525step2 = raw35525step1 := by apply Matrix.ext; unfold raw35525step2 raw35525step1; decide +kernel
      have hl : raw35525step1Labels = labelEmbedding7 ∘ raw35525step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35525step1 raw35525step1Labels raw35525step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4915 node4915Labels := by rfl

def raw35526 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw35526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw35526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw35526step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw35526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35526 raw35526Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw35526 raw35526Labels = mixedMoment B raw35526step0 raw35526step0Labels := by
      have hz : ∀ j, raw35526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35526step0 = (fun i j => raw35526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35526step0 raw35526; decide +kernel
      have hl : raw35526step0Labels = raw35526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35526 raw35526Labels permutation346 hz
    mixedMoment B raw35526step0 raw35526step0Labels = mixedMoment B raw35526step1 raw35526step1Labels := by
      have ha : raw35526step1 = (fun i j => raw35526step0 (permutation126 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35526step1 raw35526step0; decide +kernel
      have hl : raw35526step1Labels = raw35526step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35526step0 raw35526step0Labels permutation126 permutation4
    mixedMoment B raw35526step1 raw35526step1Labels = mixedMoment B raw35526step2 raw35526step2Labels := by
      have ha : raw35526step2 = raw35526step1 := by apply Matrix.ext; unfold raw35526step2 raw35526step1; decide +kernel
      have hl : raw35526step1Labels = labelEmbedding7 ∘ raw35526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35526step1 raw35526step1Labels raw35526step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4913 node4913Labels := by rfl

def raw35527 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw35527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35527step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35527 raw35527Labels = mixedMoment B node4910 node4910Labels := by
  calc
    mixedMoment B raw35527 raw35527Labels = mixedMoment B raw35527step0 raw35527step0Labels := by
      have ha : raw35527step0 = (fun i j => raw35527 (permutation583 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35527step0 raw35527; decide +kernel
      have hl : raw35527step0Labels = raw35527Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35527 raw35527Labels permutation583 permutation4
    mixedMoment B raw35527step0 raw35527step0Labels = mixedMoment B raw35527step1 raw35527step1Labels := by
      have ha : raw35527step1 = raw35527step0 := by apply Matrix.ext; unfold raw35527step1 raw35527step0; decide +kernel
      have hl : raw35527step0Labels = labelEmbedding7 ∘ raw35527step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35527step0 raw35527step0Labels raw35527step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4910 node4910Labels := by rfl

def raw35528 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw35528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw35528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35528step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35528step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35528 raw35528Labels = mixedMoment B node4922 node4922Labels := by
  calc
    mixedMoment B raw35528 raw35528Labels = mixedMoment B raw35528step0 raw35528step0Labels := by
      have hz : ∀ j, raw35528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35528step0 = (fun i j => raw35528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35528step0 raw35528; decide +kernel
      have hl : raw35528step0Labels = raw35528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35528 raw35528Labels permutation346 hz
    mixedMoment B raw35528step0 raw35528step0Labels = mixedMoment B raw35528step1 raw35528step1Labels := by
      have ha : raw35528step1 = (fun i j => raw35528step0 (permutation123 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35528step1 raw35528step0; decide +kernel
      have hl : raw35528step1Labels = raw35528step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35528step0 raw35528step0Labels permutation123 permutation4
    mixedMoment B raw35528step1 raw35528step1Labels = mixedMoment B raw35528step2 raw35528step2Labels := by
      have ha : raw35528step2 = raw35528step1 := by apply Matrix.ext; unfold raw35528step2 raw35528step1; decide +kernel
      have hl : raw35528step1Labels = labelEmbedding7 ∘ raw35528step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35528step1 raw35528step1Labels raw35528step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4922 node4922Labels := by rfl

def raw35529 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw35529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw35529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35529step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35529 raw35529Labels = mixedMoment B node4915 node4915Labels := by
  calc
    mixedMoment B raw35529 raw35529Labels = mixedMoment B raw35529step0 raw35529step0Labels := by
      have hz : ∀ j, raw35529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35529step0 = (fun i j => raw35529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35529step0 raw35529; decide +kernel
      have hl : raw35529step0Labels = raw35529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35529 raw35529Labels permutation346 hz
    mixedMoment B raw35529step0 raw35529step0Labels = mixedMoment B raw35529step1 raw35529step1Labels := by
      have ha : raw35529step1 = (fun i j => raw35529step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35529step1 raw35529step0; decide +kernel
      have hl : raw35529step1Labels = raw35529step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35529step0 raw35529step0Labels permutation150 permutation4
    mixedMoment B raw35529step1 raw35529step1Labels = mixedMoment B raw35529step2 raw35529step2Labels := by
      have ha : raw35529step2 = raw35529step1 := by apply Matrix.ext; unfold raw35529step2 raw35529step1; decide +kernel
      have hl : raw35529step1Labels = labelEmbedding7 ∘ raw35529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35529step1 raw35529step1Labels raw35529step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4915 node4915Labels := by rfl

def raw35530 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw35530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw35530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw35530step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw35530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35530 raw35530Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw35530 raw35530Labels = mixedMoment B raw35530step0 raw35530step0Labels := by
      have hz : ∀ j, raw35530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35530step0 = (fun i j => raw35530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35530step0 raw35530; decide +kernel
      have hl : raw35530step0Labels = raw35530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35530 raw35530Labels permutation346 hz
    mixedMoment B raw35530step0 raw35530step0Labels = mixedMoment B raw35530step1 raw35530step1Labels := by
      have ha : raw35530step1 = (fun i j => raw35530step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35530step1 raw35530step0; decide +kernel
      have hl : raw35530step1Labels = raw35530step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35530step0 raw35530step0Labels permutation150 permutation4
    mixedMoment B raw35530step1 raw35530step1Labels = mixedMoment B raw35530step2 raw35530step2Labels := by
      have ha : raw35530step2 = raw35530step1 := by apply Matrix.ext; unfold raw35530step2 raw35530step1; decide +kernel
      have hl : raw35530step1Labels = labelEmbedding7 ∘ raw35530step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35530step1 raw35530step1Labels raw35530step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4913 node4913Labels := by rfl

def raw35531 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw35531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35531step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35531 raw35531Labels = mixedMoment B node4910 node4910Labels := by
  calc
    mixedMoment B raw35531 raw35531Labels = mixedMoment B raw35531step0 raw35531step0Labels := by
      have ha : raw35531step0 = (fun i j => raw35531 (permutation681 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35531step0 raw35531; decide +kernel
      have hl : raw35531step0Labels = raw35531Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35531 raw35531Labels permutation681 permutation4
    mixedMoment B raw35531step0 raw35531step0Labels = mixedMoment B raw35531step1 raw35531step1Labels := by
      have ha : raw35531step1 = raw35531step0 := by apply Matrix.ext; unfold raw35531step1 raw35531step0; decide +kernel
      have hl : raw35531step0Labels = labelEmbedding7 ∘ raw35531step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35531step0 raw35531step0Labels raw35531step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4910 node4910Labels := by rfl

def raw35532 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw35532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw35532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35532step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35532step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35532 raw35532Labels = mixedMoment B node4922 node4922Labels := by
  calc
    mixedMoment B raw35532 raw35532Labels = mixedMoment B raw35532step0 raw35532step0Labels := by
      have hz : ∀ j, raw35532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35532step0 = (fun i j => raw35532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35532step0 raw35532; decide +kernel
      have hl : raw35532step0Labels = raw35532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35532 raw35532Labels permutation346 hz
    mixedMoment B raw35532step0 raw35532step0Labels = mixedMoment B raw35532step1 raw35532step1Labels := by
      have ha : raw35532step1 = (fun i j => raw35532step0 (permutation147 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35532step1 raw35532step0; decide +kernel
      have hl : raw35532step1Labels = raw35532step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35532step0 raw35532step0Labels permutation147 permutation4
    mixedMoment B raw35532step1 raw35532step1Labels = mixedMoment B raw35532step2 raw35532step2Labels := by
      have ha : raw35532step2 = raw35532step1 := by apply Matrix.ext; unfold raw35532step2 raw35532step1; decide +kernel
      have hl : raw35532step1Labels = labelEmbedding7 ∘ raw35532step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35532step1 raw35532step1Labels raw35532step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4922 node4922Labels := by rfl

def raw35533 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw35533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw35533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35533step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35533step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35533 raw35533Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw35533 raw35533Labels = mixedMoment B raw35533step0 raw35533step0Labels := by
      have hz : ∀ j, raw35533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35533step0 = (fun i j => raw35533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35533step0 raw35533; decide +kernel
      have hl : raw35533step0Labels = raw35533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35533 raw35533Labels permutation346 hz
    mixedMoment B raw35533step0 raw35533step0Labels = mixedMoment B raw35533step1 raw35533step1Labels := by
      have ha : raw35533step1 = (fun i j => raw35533step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35533step1 raw35533step0; decide +kernel
      have hl : raw35533step1Labels = raw35533step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35533step0 raw35533step0Labels permutation150 permutation4
    mixedMoment B raw35533step1 raw35533step1Labels = mixedMoment B raw35533step2 raw35533step2Labels := by
      have ha : raw35533step2 = raw35533step1 := by apply Matrix.ext; unfold raw35533step2 raw35533step1; decide +kernel
      have hl : raw35533step1Labels = labelEmbedding7 ∘ raw35533step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35533step1 raw35533step1Labels raw35533step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw35534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35534step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![2, -2], ![2, -2]]
def raw35534step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35534step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw35534step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35534 raw35534Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw35534 raw35534Labels = mixedMoment B raw35534step0 raw35534step0Labels := by
      have hz : ∀ j, raw35534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35534step0 = (fun i j => raw35534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35534step0 raw35534; decide +kernel
      have hl : raw35534step0Labels = raw35534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35534 raw35534Labels permutation434 hz
    mixedMoment B raw35534step0 raw35534step0Labels = mixedMoment B raw35534step1 raw35534step1Labels := by
      have hz : ∀ j, raw35534step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35534step1 = (fun i j => raw35534step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35534step1 raw35534step0; decide +kernel
      have hl : raw35534step1Labels = raw35534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35534step0 raw35534step0Labels permutation80 hz
    mixedMoment B raw35534step1 raw35534step1Labels = mixedMoment B raw35534step2 raw35534step2Labels := by
      have hz : ∀ i, raw35534step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35534step2 = (fun i j => raw35534step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35534step2 raw35534step1; decide +kernel
      have hl : raw35534step2Labels = (fun j => raw35534step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35534step1 raw35534step1Labels permutation6 hz
    mixedMoment B raw35534step2 raw35534step2Labels = mixedMoment B raw35534step3 raw35534step3Labels := by
      have ha : raw35534step3 = (fun i j => raw35534step2 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35534step3 raw35534step2; decide +kernel
      have hl : raw35534step3Labels = raw35534step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35534step2 raw35534step2Labels permutation14 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw35535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35535step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![2, -2]]
def raw35535step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35535step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw35535step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35535step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw35535step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35535 raw35535Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw35535 raw35535Labels = mixedMoment B raw35535step0 raw35535step0Labels := by
      have hz : ∀ j, raw35535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35535step0 = (fun i j => raw35535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35535step0 raw35535; decide +kernel
      have hl : raw35535step0Labels = raw35535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35535 raw35535Labels permutation434 hz
    mixedMoment B raw35535step0 raw35535step0Labels = mixedMoment B raw35535step1 raw35535step1Labels := by
      have hz : ∀ i, raw35535step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35535step1 = (fun i j => raw35535step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35535step1 raw35535step0; decide +kernel
      have hl : raw35535step1Labels = (fun j => raw35535step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35535step0 raw35535step0Labels permutation6 hz
    mixedMoment B raw35535step1 raw35535step1Labels = mixedMoment B raw35535step2 raw35535step2Labels := by
      have ha : raw35535step2 = (fun i j => raw35535step1 (permutation123 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35535step2 raw35535step1; decide +kernel
      have hl : raw35535step2Labels = raw35535step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35535step1 raw35535step1Labels permutation123 permutation0
    mixedMoment B raw35535step2 raw35535step2Labels = mixedMoment B raw35535step3 raw35535step3Labels := by
      have ha : raw35535step3 = -raw35535step2 := by apply Matrix.ext; change ∀ i j, raw35535step3 i j = -(raw35535step2 i j); unfold raw35535step3 raw35535step2; decide +kernel
      have hl : raw35535step3Labels = raw35535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw35536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35536step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![2, -2]]
def raw35536step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35536step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw35536step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35536step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw35536step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35536 raw35536Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw35536 raw35536Labels = mixedMoment B raw35536step0 raw35536step0Labels := by
      have hz : ∀ j, raw35536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35536step0 = (fun i j => raw35536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35536step0 raw35536; decide +kernel
      have hl : raw35536step0Labels = raw35536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35536 raw35536Labels permutation346 hz
    mixedMoment B raw35536step0 raw35536step0Labels = mixedMoment B raw35536step1 raw35536step1Labels := by
      have hz : ∀ i, raw35536step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35536step1 = (fun i j => raw35536step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35536step1 raw35536step0; decide +kernel
      have hl : raw35536step1Labels = (fun j => raw35536step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35536step0 raw35536step0Labels permutation6 hz
    mixedMoment B raw35536step1 raw35536step1Labels = mixedMoment B raw35536step2 raw35536step2Labels := by
      have ha : raw35536step2 = (fun i j => raw35536step1 (permutation123 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35536step2 raw35536step1; decide +kernel
      have hl : raw35536step2Labels = raw35536step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35536step1 raw35536step1Labels permutation123 permutation0
    mixedMoment B raw35536step2 raw35536step2Labels = mixedMoment B raw35536step3 raw35536step3Labels := by
      have ha : raw35536step3 = -raw35536step2 := by apply Matrix.ext; change ∀ i j, raw35536step3 i j = -(raw35536step2 i j); unfold raw35536step3 raw35536step2; decide +kernel
      have hl : raw35536step3Labels = raw35536step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw35537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35537step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![2, -2], ![2, -2]]
def raw35537step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35537step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35537step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35537 raw35537Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35537 raw35537Labels = mixedMoment B raw35537step0 raw35537step0Labels := by
      have hz : ∀ j, raw35537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35537step0 = (fun i j => raw35537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35537step0 raw35537; decide +kernel
      have hl : raw35537step0Labels = raw35537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35537 raw35537Labels permutation434 hz
    mixedMoment B raw35537step0 raw35537step0Labels = mixedMoment B raw35537step1 raw35537step1Labels := by
      have hz : ∀ i, raw35537step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35537step1 = (fun i j => raw35537step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35537step1 raw35537step0; decide +kernel
      have hl : raw35537step1Labels = (fun j => raw35537step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35537step0 raw35537step0Labels permutation6 hz
    mixedMoment B raw35537step1 raw35537step1Labels = mixedMoment B raw35537step2 raw35537step2Labels := by
      have ha : raw35537step2 = (fun i j => raw35537step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35537step2 raw35537step1; decide +kernel
      have hl : raw35537step2Labels = raw35537step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35537step1 raw35537step1Labels permutation56 permutation0
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw35538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35538step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw35538step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35538step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw35538step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35538 raw35538Labels = mixedMoment B node4086 node4086Labels := by
  calc
    mixedMoment B raw35538 raw35538Labels = mixedMoment B raw35538step0 raw35538step0Labels := by
      have hz : ∀ i, raw35538 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35538step0 = (fun i j => raw35538 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35538step0 raw35538; decide +kernel
      have hl : raw35538step0Labels = (fun j => raw35538Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35538 raw35538Labels permutation6 hz
    mixedMoment B raw35538step0 raw35538step0Labels = mixedMoment B raw35538step1 raw35538step1Labels := by
      have ha : raw35538step1 = (fun i j => raw35538step0 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35538step1 raw35538step0; decide +kernel
      have hl : raw35538step1Labels = raw35538step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35538step0 raw35538step0Labels permutation158 permutation0
    _ = mixedMoment B node4086 node4086Labels := by rfl

def raw35539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw35539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw35539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35539step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw35539step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35539step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw35539step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35539 raw35539Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw35539 raw35539Labels = mixedMoment B raw35539step0 raw35539step0Labels := by
      have hz : ∀ j, raw35539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35539step0 = (fun i j => raw35539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35539step0 raw35539; decide +kernel
      have hl : raw35539step0Labels = raw35539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35539 raw35539Labels permutation434 hz
    mixedMoment B raw35539step0 raw35539step0Labels = mixedMoment B raw35539step1 raw35539step1Labels := by
      have hz : ∀ i, raw35539step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35539step1 = (fun i j => raw35539step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35539step1 raw35539step0; decide +kernel
      have hl : raw35539step1Labels = (fun j => raw35539step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35539step0 raw35539step0Labels permutation6 hz
    mixedMoment B raw35539step1 raw35539step1Labels = mixedMoment B raw35539step2 raw35539step2Labels := by
      have ha : raw35539step2 = (fun i j => raw35539step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35539step2 raw35539step1; decide +kernel
      have hl : raw35539step2Labels = raw35539step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35539step1 raw35539step1Labels permutation33 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw35540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35540step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![2, -2], ![2, -2]]
def raw35540step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35540step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35540step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35540 raw35540Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35540 raw35540Labels = mixedMoment B raw35540step0 raw35540step0Labels := by
      have hz : ∀ j, raw35540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35540step0 = (fun i j => raw35540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35540step0 raw35540; decide +kernel
      have hl : raw35540step0Labels = raw35540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35540 raw35540Labels permutation346 hz
    mixedMoment B raw35540step0 raw35540step0Labels = mixedMoment B raw35540step1 raw35540step1Labels := by
      have hz : ∀ i, raw35540step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35540step1 = (fun i j => raw35540step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35540step1 raw35540step0; decide +kernel
      have hl : raw35540step1Labels = (fun j => raw35540step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35540step0 raw35540step0Labels permutation6 hz
    mixedMoment B raw35540step1 raw35540step1Labels = mixedMoment B raw35540step2 raw35540step2Labels := by
      have ha : raw35540step2 = (fun i j => raw35540step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35540step2 raw35540step1; decide +kernel
      have hl : raw35540step2Labels = raw35540step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35540step1 raw35540step1Labels permutation56 permutation0
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw35541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw35541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35541step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw35541step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35541 raw35541Labels = mixedMoment B node4086 node4086Labels := by
  calc
    mixedMoment B raw35541 raw35541Labels = mixedMoment B raw35541step0 raw35541step0Labels := by
      have hz : ∀ i, raw35541 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35541step0 = (fun i j => raw35541 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35541step0 raw35541; decide +kernel
      have hl : raw35541step0Labels = (fun j => raw35541Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35541 raw35541Labels permutation6 hz
    _ = mixedMoment B node4086 node4086Labels := by rfl

def raw35542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35542step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35542step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![3, -3], ![2, -2]]
def raw35542step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35542step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw35542step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35542 raw35542Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw35542 raw35542Labels = mixedMoment B raw35542step0 raw35542step0Labels := by
      have hz : ∀ j, raw35542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35542step0 = (fun i j => raw35542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35542step0 raw35542; decide +kernel
      have hl : raw35542step0Labels = raw35542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35542 raw35542Labels permutation434 hz
    mixedMoment B raw35542step0 raw35542step0Labels = mixedMoment B raw35542step1 raw35542step1Labels := by
      have hz : ∀ j, raw35542step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35542step1 = (fun i j => raw35542step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35542step1 raw35542step0; decide +kernel
      have hl : raw35542step1Labels = raw35542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35542step0 raw35542step0Labels permutation80 hz
    mixedMoment B raw35542step1 raw35542step1Labels = mixedMoment B raw35542step2 raw35542step2Labels := by
      have hz : ∀ i, raw35542step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35542step2 = (fun i j => raw35542step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35542step2 raw35542step1; decide +kernel
      have hl : raw35542step2Labels = (fun j => raw35542step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35542step1 raw35542step1Labels permutation6 hz
    mixedMoment B raw35542step2 raw35542step2Labels = mixedMoment B raw35542step3 raw35542step3Labels := by
      have ha : raw35542step3 = (fun i j => raw35542step2 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35542step3 raw35542step2; decide +kernel
      have hl : raw35542step3Labels = raw35542step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35542step2 raw35542step2Labels permutation15 permutation0
    _ = mixedMoment B node4076 node4076Labels := by rfl

def raw35543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35543step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![3, -3], ![2, -2]]
def raw35543step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35543step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw35543step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35543step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35543step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35543 raw35543Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35543 raw35543Labels = mixedMoment B raw35543step0 raw35543step0Labels := by
      have hz : ∀ j, raw35543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35543step0 = (fun i j => raw35543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35543step0 raw35543; decide +kernel
      have hl : raw35543step0Labels = raw35543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35543 raw35543Labels permutation434 hz
    mixedMoment B raw35543step0 raw35543step0Labels = mixedMoment B raw35543step1 raw35543step1Labels := by
      have hz : ∀ i, raw35543step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35543step1 = (fun i j => raw35543step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35543step1 raw35543step0; decide +kernel
      have hl : raw35543step1Labels = (fun j => raw35543step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35543step0 raw35543step0Labels permutation6 hz
    mixedMoment B raw35543step1 raw35543step1Labels = mixedMoment B raw35543step2 raw35543step2Labels := by
      have ha : raw35543step2 = (fun i j => raw35543step1 (permutation126 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35543step2 raw35543step1; decide +kernel
      have hl : raw35543step2Labels = raw35543step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35543step1 raw35543step1Labels permutation126 permutation0
    mixedMoment B raw35543step2 raw35543step2Labels = mixedMoment B raw35543step3 raw35543step3Labels := by
      have ha : raw35543step3 = -raw35543step2 := by apply Matrix.ext; change ∀ i j, raw35543step3 i j = -(raw35543step2 i j); unfold raw35543step3 raw35543step2; decide +kernel
      have hl : raw35543step3Labels = raw35543step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw35544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw35544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35544step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![3, -3], ![2, -2]]
def raw35544step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35544step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw35544step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35544step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35544step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35544 raw35544Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35544 raw35544Labels = mixedMoment B raw35544step0 raw35544step0Labels := by
      have hz : ∀ j, raw35544 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35544step0 = (fun i j => raw35544 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35544step0 raw35544; decide +kernel
      have hl : raw35544step0Labels = raw35544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35544 raw35544Labels permutation346 hz
    mixedMoment B raw35544step0 raw35544step0Labels = mixedMoment B raw35544step1 raw35544step1Labels := by
      have hz : ∀ i, raw35544step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35544step1 = (fun i j => raw35544step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35544step1 raw35544step0; decide +kernel
      have hl : raw35544step1Labels = (fun j => raw35544step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35544step0 raw35544step0Labels permutation6 hz
    mixedMoment B raw35544step1 raw35544step1Labels = mixedMoment B raw35544step2 raw35544step2Labels := by
      have ha : raw35544step2 = (fun i j => raw35544step1 (permutation126 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35544step2 raw35544step1; decide +kernel
      have hl : raw35544step2Labels = raw35544step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35544step1 raw35544step1Labels permutation126 permutation0
    mixedMoment B raw35544step2 raw35544step2Labels = mixedMoment B raw35544step3 raw35544step3Labels := by
      have ha : raw35544step3 = -raw35544step2 := by apply Matrix.ext; change ∀ i j, raw35544step3 i j = -(raw35544step2 i j); unfold raw35544step3 raw35544step2; decide +kernel
      have hl : raw35544step3Labels = raw35544step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw35545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw35545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw35545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![3, -3, 0], ![1, -1, 0]]
def raw35545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35545step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![3, -3], ![1, -1]]
def raw35545step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35545step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw35545step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35545step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw35545step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35545 raw35545Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw35545 raw35545Labels = mixedMoment B raw35545step0 raw35545step0Labels := by
      have hz : ∀ j, raw35545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35545step0 = (fun i j => raw35545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35545step0 raw35545; decide +kernel
      have hl : raw35545step0Labels = raw35545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35545 raw35545Labels permutation434 hz
    mixedMoment B raw35545step0 raw35545step0Labels = mixedMoment B raw35545step1 raw35545step1Labels := by
      have hz : ∀ j, raw35545step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35545step1 = (fun i j => raw35545step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35545step1 raw35545step0; decide +kernel
      have hl : raw35545step1Labels = raw35545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35545step0 raw35545step0Labels permutation80 hz
    mixedMoment B raw35545step1 raw35545step1Labels = mixedMoment B raw35545step2 raw35545step2Labels := by
      have hz : ∀ i, raw35545step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35545step2 = (fun i j => raw35545step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35545step2 raw35545step1; decide +kernel
      have hl : raw35545step2Labels = (fun j => raw35545step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35545step1 raw35545step1Labels permutation6 hz
    mixedMoment B raw35545step2 raw35545step2Labels = mixedMoment B raw35545step3 raw35545step3Labels := by
      have ha : raw35545step3 = (fun i j => raw35545step2 (permutation24 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35545step3 raw35545step2; decide +kernel
      have hl : raw35545step3Labels = raw35545step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35545step2 raw35545step2Labels permutation24 permutation0
    mixedMoment B raw35545step3 raw35545step3Labels = mixedMoment B raw35545step4 raw35545step4Labels := by
      have ha : raw35545step4 = -raw35545step3 := by apply Matrix.ext; change ∀ i j, raw35545step4 i j = -(raw35545step3 i j); unfold raw35545step4 raw35545step3; decide +kernel
      have hl : raw35545step4Labels = raw35545step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw35546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35546step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35546step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![2, -2], ![3, -3]]
def raw35546step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35546step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw35546step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35546 raw35546Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw35546 raw35546Labels = mixedMoment B raw35546step0 raw35546step0Labels := by
      have hz : ∀ j, raw35546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35546step0 = (fun i j => raw35546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35546step0 raw35546; decide +kernel
      have hl : raw35546step0Labels = raw35546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35546 raw35546Labels permutation434 hz
    mixedMoment B raw35546step0 raw35546step0Labels = mixedMoment B raw35546step1 raw35546step1Labels := by
      have hz : ∀ j, raw35546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35546step1 = (fun i j => raw35546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35546step1 raw35546step0; decide +kernel
      have hl : raw35546step1Labels = raw35546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35546step0 raw35546step0Labels permutation80 hz
    mixedMoment B raw35546step1 raw35546step1Labels = mixedMoment B raw35546step2 raw35546step2Labels := by
      have hz : ∀ i, raw35546step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35546step2 = (fun i j => raw35546step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35546step2 raw35546step1; decide +kernel
      have hl : raw35546step2Labels = (fun j => raw35546step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35546step1 raw35546step1Labels permutation6 hz
    mixedMoment B raw35546step2 raw35546step2Labels = mixedMoment B raw35546step3 raw35546step3Labels := by
      have ha : raw35546step3 = (fun i j => raw35546step2 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35546step3 raw35546step2; decide +kernel
      have hl : raw35546step3Labels = raw35546step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35546step2 raw35546step2Labels permutation14 permutation0
    _ = mixedMoment B node4076 node4076Labels := by rfl

def raw35547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35547step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![2, -2], ![3, -3]]
def raw35547step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35547step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw35547step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35547step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35547step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35547 raw35547Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35547 raw35547Labels = mixedMoment B raw35547step0 raw35547step0Labels := by
      have hz : ∀ j, raw35547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35547step0 = (fun i j => raw35547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35547step0 raw35547; decide +kernel
      have hl : raw35547step0Labels = raw35547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35547 raw35547Labels permutation434 hz
    mixedMoment B raw35547step0 raw35547step0Labels = mixedMoment B raw35547step1 raw35547step1Labels := by
      have hz : ∀ i, raw35547step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35547step1 = (fun i j => raw35547step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35547step1 raw35547step0; decide +kernel
      have hl : raw35547step1Labels = (fun j => raw35547step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35547step0 raw35547step0Labels permutation6 hz
    mixedMoment B raw35547step1 raw35547step1Labels = mixedMoment B raw35547step2 raw35547step2Labels := by
      have ha : raw35547step2 = (fun i j => raw35547step1 (permutation150 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35547step2 raw35547step1; decide +kernel
      have hl : raw35547step2Labels = raw35547step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35547step1 raw35547step1Labels permutation150 permutation0
    mixedMoment B raw35547step2 raw35547step2Labels = mixedMoment B raw35547step3 raw35547step3Labels := by
      have ha : raw35547step3 = -raw35547step2 := by apply Matrix.ext; change ∀ i j, raw35547step3 i j = -(raw35547step2 i j); unfold raw35547step3 raw35547step2; decide +kernel
      have hl : raw35547step3Labels = raw35547step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw35548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw35548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35548step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![2, -2], ![3, -3]]
def raw35548step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35548step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw35548step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35548step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw35548step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35548 raw35548Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw35548 raw35548Labels = mixedMoment B raw35548step0 raw35548step0Labels := by
      have hz : ∀ j, raw35548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35548step0 = (fun i j => raw35548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35548step0 raw35548; decide +kernel
      have hl : raw35548step0Labels = raw35548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35548 raw35548Labels permutation346 hz
    mixedMoment B raw35548step0 raw35548step0Labels = mixedMoment B raw35548step1 raw35548step1Labels := by
      have hz : ∀ i, raw35548step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw35548step1 = (fun i j => raw35548step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw35548step1 raw35548step0; decide +kernel
      have hl : raw35548step1Labels = (fun j => raw35548step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35548step0 raw35548step0Labels permutation6 hz
    mixedMoment B raw35548step1 raw35548step1Labels = mixedMoment B raw35548step2 raw35548step2Labels := by
      have ha : raw35548step2 = (fun i j => raw35548step1 (permutation150 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35548step2 raw35548step1; decide +kernel
      have hl : raw35548step2Labels = raw35548step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35548step1 raw35548step1Labels permutation150 permutation0
    mixedMoment B raw35548step2 raw35548step2Labels = mixedMoment B raw35548step3 raw35548step3Labels := by
      have ha : raw35548step3 = -raw35548step2 := by apply Matrix.ext; change ∀ i j, raw35548step3 i j = -(raw35548step2 i j); unfold raw35548step3 raw35548step2; decide +kernel
      have hl : raw35548step3Labels = raw35548step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw35549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35549step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35549step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35549 raw35549Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw35549 raw35549Labels = mixedMoment B raw35549step0 raw35549step0Labels := by
      have hz : ∀ j, raw35549 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35549step0 = (fun i j => raw35549 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35549step0 raw35549; decide +kernel
      have hl : raw35549step0Labels = raw35549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35549 raw35549Labels permutation346 hz
    mixedMoment B raw35549step0 raw35549step0Labels = mixedMoment B raw35549step1 raw35549step1Labels := by
      have ha : raw35549step1 = (fun i j => raw35549step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35549step1 raw35549step0; decide +kernel
      have hl : raw35549step1Labels = raw35549step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35549step0 raw35549step0Labels permutation56 permutation3
    mixedMoment B raw35549step1 raw35549step1Labels = mixedMoment B raw35549step2 raw35549step2Labels := by
      have ha : raw35549step2 = raw35549step1 := by apply Matrix.ext; unfold raw35549step2 raw35549step1; decide +kernel
      have hl : raw35549step1Labels = labelEmbedding6 ∘ raw35549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35549step1 raw35549step1Labels raw35549step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw35550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw35550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw35550step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35550step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35550 raw35550Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw35550 raw35550Labels = mixedMoment B raw35550step0 raw35550step0Labels := by
      have hz : ∀ j, raw35550 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35550step0 = (fun i j => raw35550 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35550step0 raw35550; decide +kernel
      have hl : raw35550step0Labels = raw35550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35550 raw35550Labels permutation520 hz
    mixedMoment B raw35550step0 raw35550step0Labels = mixedMoment B raw35550step1 raw35550step1Labels := by
      have hz : ∀ j, raw35550step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35550step1 = (fun i j => raw35550step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35550step1 raw35550step0; decide +kernel
      have hl : raw35550step1Labels = raw35550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35550step0 raw35550step0Labels permutation80 hz
    mixedMoment B raw35550step1 raw35550step1Labels = mixedMoment B raw35550step2 raw35550step2Labels := by
      have ha : raw35550step2 = (fun i j => raw35550step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35550step2 raw35550step1; decide +kernel
      have hl : raw35550step2Labels = raw35550step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35550step1 raw35550step1Labels permutation30 permutation2
    mixedMoment B raw35550step2 raw35550step2Labels = mixedMoment B raw35550step3 raw35550step3Labels := by
      have ha : raw35550step3 = -raw35550step2 := by apply Matrix.ext; change ∀ i j, raw35550step3 i j = -(raw35550step2 i j); unfold raw35550step3 raw35550step2; decide +kernel
      have hl : raw35550step3Labels = raw35550step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw35551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35551step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35551 raw35551Labels = mixedMoment B node4685 node4685Labels := by
  calc
    mixedMoment B raw35551 raw35551Labels = mixedMoment B raw35551step0 raw35551step0Labels := by
      have ha : raw35551step0 = (fun i j => raw35551 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35551step0 raw35551; decide +kernel
      have hl : raw35551step0Labels = raw35551Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35551 raw35551Labels permutation265 permutation3
    mixedMoment B raw35551step0 raw35551step0Labels = mixedMoment B raw35551step1 raw35551step1Labels := by
      have ha : raw35551step1 = raw35551step0 := by apply Matrix.ext; unfold raw35551step1 raw35551step0; decide +kernel
      have hl : raw35551step0Labels = labelEmbedding6 ∘ raw35551step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35551step0 raw35551step0Labels raw35551step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4685 node4685Labels := by rfl

def raw35552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw35552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35552 raw35552Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw35552 raw35552Labels = mixedMoment B raw35552step0 raw35552step0Labels := by
      have hz : ∀ j, raw35552 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35552step0 = (fun i j => raw35552 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35552step0 raw35552; decide +kernel
      have hl : raw35552step0Labels = raw35552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35552 raw35552Labels permutation520 hz
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw35553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35553step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35553step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35553 raw35553Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw35553 raw35553Labels = mixedMoment B raw35553step0 raw35553step0Labels := by
      have hz : ∀ j, raw35553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35553step0 = (fun i j => raw35553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35553step0 raw35553; decide +kernel
      have hl : raw35553step0Labels = raw35553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35553 raw35553Labels permutation346 hz
    mixedMoment B raw35553step0 raw35553step0Labels = mixedMoment B raw35553step1 raw35553step1Labels := by
      have ha : raw35553step1 = (fun i j => raw35553step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35553step1 raw35553step0; decide +kernel
      have hl : raw35553step1Labels = raw35553step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35553step0 raw35553step0Labels permutation59 permutation3
    mixedMoment B raw35553step1 raw35553step1Labels = mixedMoment B raw35553step2 raw35553step2Labels := by
      have ha : raw35553step2 = raw35553step1 := by apply Matrix.ext; unfold raw35553step2 raw35553step1; decide +kernel
      have hl : raw35553step1Labels = labelEmbedding6 ∘ raw35553step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35553step1 raw35553step1Labels raw35553step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw35554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35554step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35554 raw35554Labels = mixedMoment B node5372 node5372Labels := by
  calc
    mixedMoment B raw35554 raw35554Labels = mixedMoment B raw35554step0 raw35554step0Labels := by
      have ha : raw35554step0 = (fun i j => raw35554 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35554step0 raw35554; decide +kernel
      have hl : raw35554step0Labels = raw35554Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35554 raw35554Labels permutation268 permutation3
    mixedMoment B raw35554step0 raw35554step0Labels = mixedMoment B raw35554step1 raw35554step1Labels := by
      have ha : raw35554step1 = raw35554step0 := by apply Matrix.ext; unfold raw35554step1 raw35554step0; decide +kernel
      have hl : raw35554step0Labels = labelEmbedding6 ∘ raw35554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35554step0 raw35554step0Labels raw35554step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5372 node5372Labels := by rfl

def raw35555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw35555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35555 raw35555Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw35555 raw35555Labels = mixedMoment B raw35555step0 raw35555step0Labels := by
      have hz : ∀ j, raw35555 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35555step0 = (fun i j => raw35555 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35555step0 raw35555; decide +kernel
      have hl : raw35555step0Labels = raw35555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35555 raw35555Labels permutation520 hz
    mixedMoment B raw35555step0 raw35555step0Labels = mixedMoment B raw35555step1 raw35555step1Labels := by
      have hz : ∀ j, raw35555step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35555step1 = (fun i j => raw35555step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35555step1 raw35555step0; decide +kernel
      have hl : raw35555step1Labels = raw35555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35555step0 raw35555step0Labels permutation80 hz
    _ = mixedMoment B node5389 node5389Labels := by rfl

def raw35556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35556step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35556 raw35556Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw35556 raw35556Labels = mixedMoment B raw35556step0 raw35556step0Labels := by
      have hz : ∀ j, raw35556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35556step0 = (fun i j => raw35556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35556step0 raw35556; decide +kernel
      have hl : raw35556step0Labels = raw35556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35556 raw35556Labels permutation346 hz
    mixedMoment B raw35556step0 raw35556step0Labels = mixedMoment B raw35556step1 raw35556step1Labels := by
      have ha : raw35556step1 = (fun i j => raw35556step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35556step1 raw35556step0; decide +kernel
      have hl : raw35556step1Labels = raw35556step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35556step0 raw35556step0Labels permutation56 permutation3
    mixedMoment B raw35556step1 raw35556step1Labels = mixedMoment B raw35556step2 raw35556step2Labels := by
      have ha : raw35556step2 = raw35556step1 := by apply Matrix.ext; unfold raw35556step2 raw35556step1; decide +kernel
      have hl : raw35556step1Labels = labelEmbedding6 ∘ raw35556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35556step1 raw35556step1Labels raw35556step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4686 node4686Labels := by rfl

def raw35557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35557 raw35557Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw35557 raw35557Labels = mixedMoment B raw35557step0 raw35557step0Labels := by
      have ha : raw35557step0 = (fun i j => raw35557 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35557step0 raw35557; decide +kernel
      have hl : raw35557step0Labels = raw35557Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35557 raw35557Labels permutation664 permutation2
    mixedMoment B raw35557step0 raw35557step0Labels = mixedMoment B raw35557step1 raw35557step1Labels := by
      have ha : raw35557step1 = -raw35557step0 := by apply Matrix.ext; change ∀ i j, raw35557step1 i j = -(raw35557step0 i j); unfold raw35557step1 raw35557step0; decide +kernel
      have hl : raw35557step1Labels = raw35557step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5114 node5114Labels := by rfl

def raw35558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw35558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35558step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35558step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35558step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35558 raw35558Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw35558 raw35558Labels = mixedMoment B raw35558step0 raw35558step0Labels := by
      have hz : ∀ j, raw35558 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35558step0 = (fun i j => raw35558 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35558step0 raw35558; decide +kernel
      have hl : raw35558step0Labels = raw35558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35558 raw35558Labels permutation520 hz
    mixedMoment B raw35558step0 raw35558step0Labels = mixedMoment B raw35558step1 raw35558step1Labels := by
      have hz : ∀ j, raw35558step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35558step1 = (fun i j => raw35558step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35558step1 raw35558step0; decide +kernel
      have hl : raw35558step1Labels = raw35558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35558step0 raw35558step0Labels permutation80 hz
    mixedMoment B raw35558step1 raw35558step1Labels = mixedMoment B raw35558step2 raw35558step2Labels := by
      have ha : raw35558step2 = (fun i j => raw35558step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35558step2 raw35558step1; decide +kernel
      have hl : raw35558step2Labels = raw35558step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35558step1 raw35558step1Labels permutation31 permutation2
    mixedMoment B raw35558step2 raw35558step2Labels = mixedMoment B raw35558step3 raw35558step3Labels := by
      have ha : raw35558step3 = -raw35558step2 := by apply Matrix.ext; change ∀ i j, raw35558step3 i j = -(raw35558step2 i j); unfold raw35558step3 raw35558step2; decide +kernel
      have hl : raw35558step3Labels = raw35558step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw35559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35559 raw35559Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw35559 raw35559Labels = mixedMoment B raw35559step0 raw35559step0Labels := by
      have hz : ∀ j, raw35559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35559step0 = (fun i j => raw35559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35559step0 raw35559; decide +kernel
      have hl : raw35559step0Labels = raw35559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35559 raw35559Labels permutation346 hz
    mixedMoment B raw35559step0 raw35559step0Labels = mixedMoment B raw35559step1 raw35559step1Labels := by
      have ha : raw35559step1 = (fun i j => raw35559step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35559step1 raw35559step0; decide +kernel
      have hl : raw35559step1Labels = raw35559step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35559step0 raw35559step0Labels permutation56 permutation2
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw35560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35560 raw35560Labels = mixedMoment B node5417 node5417Labels := by
  calc
    mixedMoment B raw35560 raw35560Labels = mixedMoment B raw35560step0 raw35560step0Labels := by
      have ha : raw35560step0 = (fun i j => raw35560 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35560step0 raw35560; decide +kernel
      have hl : raw35560step0Labels = raw35560Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35560 raw35560Labels permutation265 permutation2
    _ = mixedMoment B node5417 node5417Labels := by rfl

def raw35561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw35561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw35561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35561 raw35561Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw35561 raw35561Labels = mixedMoment B raw35561step0 raw35561step0Labels := by
      have hz : ∀ j, raw35561 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35561step0 = (fun i j => raw35561 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35561step0 raw35561; decide +kernel
      have hl : raw35561step0Labels = raw35561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35561 raw35561Labels permutation346 hz
    mixedMoment B raw35561step0 raw35561step0Labels = mixedMoment B raw35561step1 raw35561step1Labels := by
      have ha : raw35561step1 = (fun i j => raw35561step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35561step1 raw35561step0; decide +kernel
      have hl : raw35561step1Labels = raw35561step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35561step0 raw35561step0Labels permutation58 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw35562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35562 raw35562Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw35562 raw35562Labels = mixedMoment B raw35562step0 raw35562step0Labels := by
      have ha : raw35562step0 = (fun i j => raw35562 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35562step0 raw35562; decide +kernel
      have hl : raw35562step0Labels = raw35562Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35562 raw35562Labels permutation265 permutation2
    _ = mixedMoment B node4971 node4971Labels := by rfl

def raw35563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw35563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35563step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35563 raw35563Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35563 raw35563Labels = mixedMoment B raw35563step0 raw35563step0Labels := by
      have ha : raw35563step0 = (fun i j => raw35563 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35563step0 raw35563; decide +kernel
      have hl : raw35563step0Labels = raw35563Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35563 raw35563Labels permutation166 permutation3
    mixedMoment B raw35563step0 raw35563step0Labels = mixedMoment B raw35563step1 raw35563step1Labels := by
      have ha : raw35563step1 = raw35563step0 := by apply Matrix.ext; unfold raw35563step1 raw35563step0; decide +kernel
      have hl : raw35563step0Labels = labelEmbedding6 ∘ raw35563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35563step0 raw35563step0Labels raw35563step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw35564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35564 raw35564Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw35564 raw35564Labels = mixedMoment B raw35564step0 raw35564step0Labels := by
      have hz : ∀ j, raw35564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35564step0 = (fun i j => raw35564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35564step0 raw35564; decide +kernel
      have hl : raw35564step0Labels = raw35564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35564 raw35564Labels permutation346 hz
    mixedMoment B raw35564step0 raw35564step0Labels = mixedMoment B raw35564step1 raw35564step1Labels := by
      have ha : raw35564step1 = (fun i j => raw35564step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35564step1 raw35564step0; decide +kernel
      have hl : raw35564step1Labels = raw35564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35564step0 raw35564step0Labels permutation59 permutation2
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw35565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35565step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35565step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35565step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35565 raw35565Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw35565 raw35565Labels = mixedMoment B raw35565step0 raw35565step0Labels := by
      have ha : raw35565step0 = (fun i j => raw35565 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35565step0 raw35565; decide +kernel
      have hl : raw35565step0Labels = raw35565Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35565 raw35565Labels permutation664 permutation3
    mixedMoment B raw35565step0 raw35565step0Labels = mixedMoment B raw35565step1 raw35565step1Labels := by
      have ha : raw35565step1 = -raw35565step0 := by apply Matrix.ext; change ∀ i j, raw35565step1 i j = -(raw35565step0 i j); unfold raw35565step1 raw35565step0; decide +kernel
      have hl : raw35565step1Labels = raw35565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35565step1 raw35565step1Labels = mixedMoment B raw35565step2 raw35565step2Labels := by
      have ha : raw35565step2 = raw35565step1 := by apply Matrix.ext; unfold raw35565step2 raw35565step1; decide +kernel
      have hl : raw35565step1Labels = labelEmbedding6 ∘ raw35565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35565step1 raw35565step1Labels raw35565step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw35566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw35566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw35566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35566step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35566step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35566step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35566 raw35566Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35566 raw35566Labels = mixedMoment B raw35566step0 raw35566step0Labels := by
      have hz : ∀ j, raw35566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35566step0 = (fun i j => raw35566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35566step0 raw35566; decide +kernel
      have hl : raw35566step0Labels = raw35566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35566 raw35566Labels permutation346 hz
    mixedMoment B raw35566step0 raw35566step0Labels = mixedMoment B raw35566step1 raw35566step1Labels := by
      have ha : raw35566step1 = (fun i j => raw35566step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35566step1 raw35566step0; decide +kernel
      have hl : raw35566step1Labels = raw35566step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35566step0 raw35566step0Labels permutation145 permutation3
    mixedMoment B raw35566step1 raw35566step1Labels = mixedMoment B raw35566step2 raw35566step2Labels := by
      have ha : raw35566step2 = -raw35566step1 := by apply Matrix.ext; change ∀ i j, raw35566step2 i j = -(raw35566step1 i j); unfold raw35566step2 raw35566step1; decide +kernel
      have hl : raw35566step2Labels = raw35566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35566step2 raw35566step2Labels = mixedMoment B raw35566step3 raw35566step3Labels := by
      have ha : raw35566step3 = raw35566step2 := by apply Matrix.ext; unfold raw35566step3 raw35566step2; decide +kernel
      have hl : raw35566step2Labels = labelEmbedding6 ∘ raw35566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35566step2 raw35566step2Labels raw35566step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw35567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw35567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35567 raw35567Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw35567 raw35567Labels = mixedMoment B raw35567step0 raw35567step0Labels := by
      have hz : ∀ j, raw35567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35567step0 = (fun i j => raw35567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35567step0 raw35567; decide +kernel
      have hl : raw35567step0Labels = raw35567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35567 raw35567Labels permutation346 hz
    mixedMoment B raw35567step0 raw35567step0Labels = mixedMoment B raw35567step1 raw35567step1Labels := by
      have ha : raw35567step1 = (fun i j => raw35567step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35567step1 raw35567step0; decide +kernel
      have hl : raw35567step1Labels = raw35567step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35567step0 raw35567step0Labels permutation57 permutation2
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw35568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw35568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35568step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35568step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35568step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35568 raw35568Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw35568 raw35568Labels = mixedMoment B raw35568step0 raw35568step0Labels := by
      have ha : raw35568step0 = (fun i j => raw35568 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35568step0 raw35568; decide +kernel
      have hl : raw35568step0Labels = raw35568Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35568 raw35568Labels permutation688 permutation3
    mixedMoment B raw35568step0 raw35568step0Labels = mixedMoment B raw35568step1 raw35568step1Labels := by
      have ha : raw35568step1 = -raw35568step0 := by apply Matrix.ext; change ∀ i j, raw35568step1 i j = -(raw35568step0 i j); unfold raw35568step1 raw35568step0; decide +kernel
      have hl : raw35568step1Labels = raw35568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35568step1 raw35568step1Labels = mixedMoment B raw35568step2 raw35568step2Labels := by
      have ha : raw35568step2 = raw35568step1 := by apply Matrix.ext; unfold raw35568step2 raw35568step1; decide +kernel
      have hl : raw35568step1Labels = labelEmbedding6 ∘ raw35568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35568step1 raw35568step1Labels raw35568step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw35569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw35569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw35569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw35569step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35569step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35569step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35569 raw35569Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw35569 raw35569Labels = mixedMoment B raw35569step0 raw35569step0Labels := by
      have hz : ∀ j, raw35569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35569step0 = (fun i j => raw35569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35569step0 raw35569; decide +kernel
      have hl : raw35569step0Labels = raw35569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35569 raw35569Labels permutation346 hz
    mixedMoment B raw35569step0 raw35569step0Labels = mixedMoment B raw35569step1 raw35569step1Labels := by
      have ha : raw35569step1 = (fun i j => raw35569step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35569step1 raw35569step0; decide +kernel
      have hl : raw35569step1Labels = raw35569step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35569step0 raw35569step0Labels permutation144 permutation3
    mixedMoment B raw35569step1 raw35569step1Labels = mixedMoment B raw35569step2 raw35569step2Labels := by
      have ha : raw35569step2 = -raw35569step1 := by apply Matrix.ext; change ∀ i j, raw35569step2 i j = -(raw35569step1 i j); unfold raw35569step2 raw35569step1; decide +kernel
      have hl : raw35569step2Labels = raw35569step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35569step2 raw35569step2Labels = mixedMoment B raw35569step3 raw35569step3Labels := by
      have ha : raw35569step3 = raw35569step2 := by apply Matrix.ext; unfold raw35569step3 raw35569step2; decide +kernel
      have hl : raw35569step2Labels = labelEmbedding6 ∘ raw35569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35569step2 raw35569step2Labels raw35569step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

def raw35570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw35570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35570step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35570step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35570 raw35570Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw35570 raw35570Labels = mixedMoment B raw35570step0 raw35570step0Labels := by
      have ha : raw35570step0 = (fun i j => raw35570 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35570step0 raw35570; decide +kernel
      have hl : raw35570step0Labels = raw35570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35570 raw35570Labels permutation664 permutation3
    mixedMoment B raw35570step0 raw35570step0Labels = mixedMoment B raw35570step1 raw35570step1Labels := by
      have ha : raw35570step1 = -raw35570step0 := by apply Matrix.ext; change ∀ i j, raw35570step1 i j = -(raw35570step0 i j); unfold raw35570step1 raw35570step0; decide +kernel
      have hl : raw35570step1Labels = raw35570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35570step1 raw35570step1Labels = mixedMoment B raw35570step2 raw35570step2Labels := by
      have ha : raw35570step2 = raw35570step1 := by apply Matrix.ext; unfold raw35570step2 raw35570step1; decide +kernel
      have hl : raw35570step1Labels = labelEmbedding6 ∘ raw35570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35570step1 raw35570step1Labels raw35570step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

def raw35571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw35571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw35571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35571step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35571step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35571step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35571 raw35571Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw35571 raw35571Labels = mixedMoment B raw35571step0 raw35571step0Labels := by
      have hz : ∀ j, raw35571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35571step0 = (fun i j => raw35571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35571step0 raw35571; decide +kernel
      have hl : raw35571step0Labels = raw35571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35571 raw35571Labels permutation346 hz
    mixedMoment B raw35571step0 raw35571step0Labels = mixedMoment B raw35571step1 raw35571step1Labels := by
      have ha : raw35571step1 = (fun i j => raw35571step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35571step1 raw35571step0; decide +kernel
      have hl : raw35571step1Labels = raw35571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35571step0 raw35571step0Labels permutation145 permutation3
    mixedMoment B raw35571step1 raw35571step1Labels = mixedMoment B raw35571step2 raw35571step2Labels := by
      have ha : raw35571step2 = -raw35571step1 := by apply Matrix.ext; change ∀ i j, raw35571step2 i j = -(raw35571step1 i j); unfold raw35571step2 raw35571step1; decide +kernel
      have hl : raw35571step2Labels = raw35571step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35571step2 raw35571step2Labels = mixedMoment B raw35571step3 raw35571step3Labels := by
      have ha : raw35571step3 = raw35571step2 := by apply Matrix.ext; unfold raw35571step3 raw35571step2; decide +kernel
      have hl : raw35571step2Labels = labelEmbedding6 ∘ raw35571step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35571step2 raw35571step2Labels raw35571step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw35572 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35572step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35572step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35572step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35572step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35572 raw35572Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw35572 raw35572Labels = mixedMoment B raw35572step0 raw35572step0Labels := by
      have hz : ∀ j, raw35572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35572step0 = (fun i j => raw35572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35572step0 raw35572; decide +kernel
      have hl : raw35572step0Labels = raw35572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35572 raw35572Labels permutation346 hz
    mixedMoment B raw35572step0 raw35572step0Labels = mixedMoment B raw35572step1 raw35572step1Labels := by
      have ha : raw35572step1 = (fun i j => raw35572step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35572step1 raw35572step0; decide +kernel
      have hl : raw35572step1Labels = raw35572step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35572step0 raw35572step0Labels permutation144 permutation6
    mixedMoment B raw35572step1 raw35572step1Labels = mixedMoment B raw35572step2 raw35572step2Labels := by
      have ha : raw35572step2 = -raw35572step1 := by apply Matrix.ext; change ∀ i j, raw35572step2 i j = -(raw35572step1 i j); unfold raw35572step2 raw35572step1; decide +kernel
      have hl : raw35572step2Labels = raw35572step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35572step2 raw35572step2Labels = mixedMoment B raw35572step3 raw35572step3Labels := by
      have ha : raw35572step3 = raw35572step2 := by apply Matrix.ext; unfold raw35572step3 raw35572step2; decide +kernel
      have hl : raw35572step2Labels = labelEmbedding9 ∘ raw35572step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35572step2 raw35572step2Labels raw35572step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw35573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35573step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35573 raw35573Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw35573 raw35573Labels = mixedMoment B raw35573step0 raw35573step0Labels := by
      have ha : raw35573step0 = (fun i j => raw35573 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35573step0 raw35573; decide +kernel
      have hl : raw35573step0Labels = raw35573Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35573 raw35573Labels permutation265 permutation7
    mixedMoment B raw35573step0 raw35573step0Labels = mixedMoment B raw35573step1 raw35573step1Labels := by
      have ha : raw35573step1 = raw35573step0 := by apply Matrix.ext; unfold raw35573step1 raw35573step0; decide +kernel
      have hl : raw35573step0Labels = labelEmbedding10 ∘ raw35573step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35573step0 raw35573step0Labels raw35573step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw35574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35574step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35574 raw35574Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw35574 raw35574Labels = mixedMoment B raw35574step0 raw35574step0Labels := by
      have hz : ∀ j, raw35574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35574step0 = (fun i j => raw35574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35574step0 raw35574; decide +kernel
      have hl : raw35574step0Labels = raw35574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35574 raw35574Labels permutation346 hz
    mixedMoment B raw35574step0 raw35574step0Labels = mixedMoment B raw35574step1 raw35574step1Labels := by
      have ha : raw35574step1 = (fun i j => raw35574step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35574step1 raw35574step0; decide +kernel
      have hl : raw35574step1Labels = raw35574step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35574step0 raw35574step0Labels permutation58 permutation7
    mixedMoment B raw35574step1 raw35574step1Labels = mixedMoment B raw35574step2 raw35574step2Labels := by
      have ha : raw35574step2 = raw35574step1 := by apply Matrix.ext; unfold raw35574step2 raw35574step1; decide +kernel
      have hl : raw35574step1Labels = labelEmbedding10 ∘ raw35574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35574step1 raw35574step1Labels raw35574step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw35575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35575step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35575 raw35575Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw35575 raw35575Labels = mixedMoment B raw35575step0 raw35575step0Labels := by
      have hz : ∀ j, raw35575 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35575step0 = (fun i j => raw35575 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35575step0 raw35575; decide +kernel
      have hl : raw35575step0Labels = raw35575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35575 raw35575Labels permutation346 hz
    mixedMoment B raw35575step0 raw35575step0Labels = mixedMoment B raw35575step1 raw35575step1Labels := by
      have ha : raw35575step1 = (fun i j => raw35575step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35575step1 raw35575step0; decide +kernel
      have hl : raw35575step1Labels = raw35575step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35575step0 raw35575step0Labels permutation56 permutation7
    mixedMoment B raw35575step1 raw35575step1Labels = mixedMoment B raw35575step2 raw35575step2Labels := by
      have ha : raw35575step2 = raw35575step1 := by apply Matrix.ext; unfold raw35575step2 raw35575step1; decide +kernel
      have hl : raw35575step1Labels = labelEmbedding10 ∘ raw35575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35575step1 raw35575step1Labels raw35575step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw35576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35576step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35576 raw35576Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw35576 raw35576Labels = mixedMoment B raw35576step0 raw35576step0Labels := by
      have hz : ∀ j, raw35576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35576step0 = (fun i j => raw35576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35576step0 raw35576; decide +kernel
      have hl : raw35576step0Labels = raw35576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35576 raw35576Labels permutation346 hz
    mixedMoment B raw35576step0 raw35576step0Labels = mixedMoment B raw35576step1 raw35576step1Labels := by
      have ha : raw35576step1 = (fun i j => raw35576step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35576step1 raw35576step0; decide +kernel
      have hl : raw35576step1Labels = raw35576step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35576step0 raw35576step0Labels permutation56 permutation7
    mixedMoment B raw35576step1 raw35576step1Labels = mixedMoment B raw35576step2 raw35576step2Labels := by
      have ha : raw35576step2 = raw35576step1 := by apply Matrix.ext; unfold raw35576step2 raw35576step1; decide +kernel
      have hl : raw35576step1Labels = labelEmbedding10 ∘ raw35576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35576step1 raw35576step1Labels raw35576step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw35577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw35577step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw35577step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35577step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw35577step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35577 raw35577Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw35577 raw35577Labels = mixedMoment B raw35577step0 raw35577step0Labels := by
      have hz : ∀ j, raw35577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35577step0 = (fun i j => raw35577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35577step0 raw35577; decide +kernel
      have hl : raw35577step0Labels = raw35577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35577 raw35577Labels permutation346 hz
    mixedMoment B raw35577step0 raw35577step0Labels = mixedMoment B raw35577step1 raw35577step1Labels := by
      have ha : raw35577step1 = (fun i j => raw35577step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35577step1 raw35577step0; decide +kernel
      have hl : raw35577step1Labels = raw35577step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35577step0 raw35577step0Labels permutation40 permutation4
    mixedMoment B raw35577step1 raw35577step1Labels = mixedMoment B raw35577step2 raw35577step2Labels := by
      have ha : raw35577step2 = -raw35577step1 := by apply Matrix.ext; change ∀ i j, raw35577step2 i j = -(raw35577step1 i j); unfold raw35577step2 raw35577step1; decide +kernel
      have hl : raw35577step2Labels = raw35577step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35577step2 raw35577step2Labels = mixedMoment B raw35577step3 raw35577step3Labels := by
      have ha : raw35577step3 = raw35577step2 := by apply Matrix.ext; unfold raw35577step3 raw35577step2; decide +kernel
      have hl : raw35577step2Labels = labelEmbedding7 ∘ raw35577step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35577step2 raw35577step2Labels raw35577step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw35578 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw35578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35578 raw35578Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw35578 raw35578Labels = mixedMoment B raw35578step0 raw35578step0Labels := by
      have ha : raw35578step0 = (fun i j => raw35578 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35578step0 raw35578; decide +kernel
      have hl : raw35578step0Labels = raw35578Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35578 raw35578Labels permutation283 permutation2
    mixedMoment B raw35578step0 raw35578step0Labels = mixedMoment B raw35578step1 raw35578step1Labels := by
      have ha : raw35578step1 = -raw35578step0 := by apply Matrix.ext; change ∀ i j, raw35578step1 i j = -(raw35578step0 i j); unfold raw35578step1 raw35578step0; decide +kernel
      have hl : raw35578step1Labels = raw35578step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw35579 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35579step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35579 raw35579Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw35579 raw35579Labels = mixedMoment B raw35579step0 raw35579step0Labels := by
      have hz : ∀ j, raw35579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35579step0 = (fun i j => raw35579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35579step0 raw35579; decide +kernel
      have hl : raw35579step0Labels = raw35579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35579 raw35579Labels permutation346 hz
    mixedMoment B raw35579step0 raw35579step0Labels = mixedMoment B raw35579step1 raw35579step1Labels := by
      have ha : raw35579step1 = (fun i j => raw35579step0 (permutation61 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35579step1 raw35579step0; decide +kernel
      have hl : raw35579step1Labels = raw35579step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35579step0 raw35579step0Labels permutation61 permutation2
    mixedMoment B raw35579step1 raw35579step1Labels = mixedMoment B raw35579step2 raw35579step2Labels := by
      have ha : raw35579step2 = -raw35579step1 := by apply Matrix.ext; change ∀ i j, raw35579step2 i j = -(raw35579step1 i j); unfold raw35579step2 raw35579step1; decide +kernel
      have hl : raw35579step2Labels = raw35579step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw35580 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35580 raw35580Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw35580 raw35580Labels = mixedMoment B raw35580step0 raw35580step0Labels := by
      have hz : ∀ j, raw35580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35580step0 = (fun i j => raw35580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35580step0 raw35580; decide +kernel
      have hl : raw35580step0Labels = raw35580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35580 raw35580Labels permutation346 hz
    mixedMoment B raw35580step0 raw35580step0Labels = mixedMoment B raw35580step1 raw35580step1Labels := by
      have ha : raw35580step1 = (fun i j => raw35580step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35580step1 raw35580step0; decide +kernel
      have hl : raw35580step1Labels = raw35580step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35580step0 raw35580step0Labels permutation60 permutation2
    mixedMoment B raw35580step1 raw35580step1Labels = mixedMoment B raw35580step2 raw35580step2Labels := by
      have ha : raw35580step2 = -raw35580step1 := by apply Matrix.ext; change ∀ i j, raw35580step2 i j = -(raw35580step1 i j); unfold raw35580step2 raw35580step1; decide +kernel
      have hl : raw35580step2Labels = raw35580step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw35581 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35581 raw35581Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw35581 raw35581Labels = mixedMoment B raw35581step0 raw35581step0Labels := by
      have hz : ∀ j, raw35581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35581step0 = (fun i j => raw35581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35581step0 raw35581; decide +kernel
      have hl : raw35581step0Labels = raw35581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35581 raw35581Labels permutation346 hz
    mixedMoment B raw35581step0 raw35581step0Labels = mixedMoment B raw35581step1 raw35581step1Labels := by
      have ha : raw35581step1 = (fun i j => raw35581step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35581step1 raw35581step0; decide +kernel
      have hl : raw35581step1Labels = raw35581step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35581step0 raw35581step0Labels permutation56 permutation2
    mixedMoment B raw35581step1 raw35581step1Labels = mixedMoment B raw35581step2 raw35581step2Labels := by
      have ha : raw35581step2 = -raw35581step1 := by apply Matrix.ext; change ∀ i j, raw35581step2 i j = -(raw35581step1 i j); unfold raw35581step2 raw35581step1; decide +kernel
      have hl : raw35581step2Labels = raw35581step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw35582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw35582step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35582step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35582step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35582 raw35582Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw35582 raw35582Labels = mixedMoment B raw35582step0 raw35582step0Labels := by
      have ha : raw35582step0 = (fun i j => raw35582 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35582step0 raw35582; decide +kernel
      have hl : raw35582step0Labels = raw35582Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35582 raw35582Labels permutation160 permutation4
    mixedMoment B raw35582step0 raw35582step0Labels = mixedMoment B raw35582step1 raw35582step1Labels := by
      have ha : raw35582step1 = -raw35582step0 := by apply Matrix.ext; change ∀ i j, raw35582step1 i j = -(raw35582step0 i j); unfold raw35582step1 raw35582step0; decide +kernel
      have hl : raw35582step1Labels = raw35582step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35582step1 raw35582step1Labels = mixedMoment B raw35582step2 raw35582step2Labels := by
      have ha : raw35582step2 = raw35582step1 := by apply Matrix.ext; unfold raw35582step2 raw35582step1; decide +kernel
      have hl : raw35582step1Labels = labelEmbedding7 ∘ raw35582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35582step1 raw35582step1Labels raw35582step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw35583 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35583step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35583 raw35583Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw35583 raw35583Labels = mixedMoment B raw35583step0 raw35583step0Labels := by
      have ha : raw35583step0 = (fun i j => raw35583 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35583step0 raw35583; decide +kernel
      have hl : raw35583step0Labels = raw35583Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35583 raw35583Labels permutation152 permutation6
    mixedMoment B raw35583step0 raw35583step0Labels = mixedMoment B raw35583step1 raw35583step1Labels := by
      have ha : raw35583step1 = raw35583step0 := by apply Matrix.ext; unfold raw35583step1 raw35583step0; decide +kernel
      have hl : raw35583step0Labels = labelEmbedding9 ∘ raw35583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35583step0 raw35583step0Labels raw35583step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
