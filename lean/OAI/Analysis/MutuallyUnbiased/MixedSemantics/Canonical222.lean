import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![3, 0, -3]]
def raw28416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28416step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28416step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28416 raw28416Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw28416 raw28416Labels = mixedMoment B raw28416step0 raw28416step0Labels := by
      have hz : ∀ j, raw28416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28416step0 = (fun i j => raw28416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28416step0 raw28416; decide +kernel
      have hl : raw28416step0Labels = raw28416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28416 raw28416Labels permutation434 hz
    mixedMoment B raw28416step0 raw28416step0Labels = mixedMoment B raw28416step1 raw28416step1Labels := by
      have hz : ∀ j, raw28416step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28416step1 = (fun i j => raw28416step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28416step1 raw28416step0; decide +kernel
      have hl : raw28416step1Labels = raw28416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28416step0 raw28416step0Labels permutation80 hz
    mixedMoment B raw28416step1 raw28416step1Labels = mixedMoment B raw28416step2 raw28416step2Labels := by
      have ha : raw28416step2 = (fun i j => raw28416step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28416step2 raw28416step1; decide +kernel
      have hl : raw28416step2Labels = raw28416step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28416step1 raw28416step1Labels permutation31 permutation2
    mixedMoment B raw28416step2 raw28416step2Labels = mixedMoment B raw28416step3 raw28416step3Labels := by
      have ha : raw28416step3 = -raw28416step2 := by apply Matrix.ext; change ∀ i j, raw28416step3 i j = -(raw28416step2 i j); unfold raw28416step3 raw28416step2; decide +kernel
      have hl : raw28416step3Labels = raw28416step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4693 node4693Labels := by rfl

def raw28417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28417 raw28417Labels = mixedMoment B node4682 node4682Labels := by
  calc
    mixedMoment B raw28417 raw28417Labels = mixedMoment B raw28417step0 raw28417step0Labels := by
      have hz : ∀ j, raw28417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28417step0 = (fun i j => raw28417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28417step0 raw28417; decide +kernel
      have hl : raw28417step0Labels = raw28417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28417 raw28417Labels permutation434 hz
    mixedMoment B raw28417step0 raw28417step0Labels = mixedMoment B raw28417step1 raw28417step1Labels := by
      have ha : raw28417step1 = (fun i j => raw28417step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28417step1 raw28417step0; decide +kernel
      have hl : raw28417step1Labels = raw28417step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28417step0 raw28417step0Labels permutation151 permutation2
    mixedMoment B raw28417step1 raw28417step1Labels = mixedMoment B raw28417step2 raw28417step2Labels := by
      have ha : raw28417step2 = -raw28417step1 := by apply Matrix.ext; change ∀ i j, raw28417step2 i j = -(raw28417step1 i j); unfold raw28417step2 raw28417step1; decide +kernel
      have hl : raw28417step2Labels = raw28417step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4682 node4682Labels := by rfl

def raw28418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28418 raw28418Labels = mixedMoment B node4682 node4682Labels := by
  calc
    mixedMoment B raw28418 raw28418Labels = mixedMoment B raw28418step0 raw28418step0Labels := by
      have hz : ∀ j, raw28418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28418step0 = (fun i j => raw28418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28418step0 raw28418; decide +kernel
      have hl : raw28418step0Labels = raw28418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28418 raw28418Labels permutation346 hz
    mixedMoment B raw28418step0 raw28418step0Labels = mixedMoment B raw28418step1 raw28418step1Labels := by
      have ha : raw28418step1 = (fun i j => raw28418step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28418step1 raw28418step0; decide +kernel
      have hl : raw28418step1Labels = raw28418step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28418step0 raw28418step0Labels permutation151 permutation2
    mixedMoment B raw28418step1 raw28418step1Labels = mixedMoment B raw28418step2 raw28418step2Labels := by
      have ha : raw28418step2 = -raw28418step1 := by apply Matrix.ext; change ∀ i j, raw28418step2 i j = -(raw28418step1 i j); unfold raw28418step2 raw28418step1; decide +kernel
      have hl : raw28418step2Labels = raw28418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4682 node4682Labels := by rfl

def raw28419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw28419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28419step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28419step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28419step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28419 raw28419Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw28419 raw28419Labels = mixedMoment B raw28419step0 raw28419step0Labels := by
      have hz : ∀ j, raw28419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28419step0 = (fun i j => raw28419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28419step0 raw28419; decide +kernel
      have hl : raw28419step0Labels = raw28419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28419 raw28419Labels permutation434 hz
    mixedMoment B raw28419step0 raw28419step0Labels = mixedMoment B raw28419step1 raw28419step1Labels := by
      have hz : ∀ j, raw28419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28419step1 = (fun i j => raw28419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28419step1 raw28419step0; decide +kernel
      have hl : raw28419step1Labels = raw28419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28419step0 raw28419step0Labels permutation80 hz
    mixedMoment B raw28419step1 raw28419step1Labels = mixedMoment B raw28419step2 raw28419step2Labels := by
      have ha : raw28419step2 = (fun i j => raw28419step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28419step2 raw28419step1; decide +kernel
      have hl : raw28419step2Labels = raw28419step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28419step1 raw28419step1Labels permutation9 permutation3
    mixedMoment B raw28419step2 raw28419step2Labels = mixedMoment B raw28419step3 raw28419step3Labels := by
      have ha : raw28419step3 = raw28419step2 := by apply Matrix.ext; unfold raw28419step3 raw28419step2; decide +kernel
      have hl : raw28419step2Labels = labelEmbedding6 ∘ raw28419step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28419step2 raw28419step2Labels raw28419step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw28420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![4, -1, -3]]
def raw28420step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, -1, 2], ![-4, 3, 1]]
def raw28420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28420step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw28420step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28420 raw28420Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw28420 raw28420Labels = mixedMoment B raw28420step0 raw28420step0Labels := by
      have hz : ∀ j, raw28420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28420step0 = (fun i j => raw28420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28420step0 raw28420; decide +kernel
      have hl : raw28420step0Labels = raw28420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28420 raw28420Labels permutation434 hz
    mixedMoment B raw28420step0 raw28420step0Labels = mixedMoment B raw28420step1 raw28420step1Labels := by
      have hz : ∀ j, raw28420step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28420step1 = (fun i j => raw28420step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28420step1 raw28420step0; decide +kernel
      have hl : raw28420step1Labels = raw28420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28420step0 raw28420step0Labels permutation80 hz
    mixedMoment B raw28420step1 raw28420step1Labels = mixedMoment B raw28420step2 raw28420step2Labels := by
      have ha : raw28420step2 = (fun i j => raw28420step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28420step2 raw28420step1; decide +kernel
      have hl : raw28420step2Labels = raw28420step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28420step1 raw28420step1Labels permutation31 permutation2
    mixedMoment B raw28420step2 raw28420step2Labels = mixedMoment B raw28420step3 raw28420step3Labels := by
      have ha : raw28420step3 = -raw28420step2 := by apply Matrix.ext; change ∀ i j, raw28420step3 i j = -(raw28420step2 i j); unfold raw28420step3 raw28420step2; decide +kernel
      have hl : raw28420step3Labels = raw28420step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4358 node4358Labels := by rfl

def raw28421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![4, -1, -3]]
def raw28421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28421step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28421step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28421 raw28421Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw28421 raw28421Labels = mixedMoment B raw28421step0 raw28421step0Labels := by
      have hz : ∀ j, raw28421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28421step0 = (fun i j => raw28421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28421step0 raw28421; decide +kernel
      have hl : raw28421step0Labels = raw28421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28421 raw28421Labels permutation434 hz
    mixedMoment B raw28421step0 raw28421step0Labels = mixedMoment B raw28421step1 raw28421step1Labels := by
      have hz : ∀ j, raw28421step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28421step1 = (fun i j => raw28421step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28421step1 raw28421step0; decide +kernel
      have hl : raw28421step1Labels = raw28421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28421step0 raw28421step0Labels permutation80 hz
    mixedMoment B raw28421step1 raw28421step1Labels = mixedMoment B raw28421step2 raw28421step2Labels := by
      have ha : raw28421step2 = (fun i j => raw28421step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28421step2 raw28421step1; decide +kernel
      have hl : raw28421step2Labels = raw28421step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28421step1 raw28421step1Labels permutation31 permutation2
    mixedMoment B raw28421step2 raw28421step2Labels = mixedMoment B raw28421step3 raw28421step3Labels := by
      have ha : raw28421step3 = -raw28421step2 := by apply Matrix.ext; change ∀ i j, raw28421step3 i j = -(raw28421step2 i j); unfold raw28421step3 raw28421step2; decide +kernel
      have hl : raw28421step3Labels = raw28421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4361 node4361Labels := by rfl

def raw28422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28422step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28422 raw28422Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw28422 raw28422Labels = mixedMoment B raw28422step0 raw28422step0Labels := by
      have hz : ∀ j, raw28422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28422step0 = (fun i j => raw28422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28422step0 raw28422; decide +kernel
      have hl : raw28422step0Labels = raw28422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28422 raw28422Labels permutation434 hz
    mixedMoment B raw28422step0 raw28422step0Labels = mixedMoment B raw28422step1 raw28422step1Labels := by
      have ha : raw28422step1 = (fun i j => raw28422step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28422step1 raw28422step0; decide +kernel
      have hl : raw28422step1Labels = raw28422step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28422step0 raw28422step0Labels permutation151 permutation2
    mixedMoment B raw28422step1 raw28422step1Labels = mixedMoment B raw28422step2 raw28422step2Labels := by
      have ha : raw28422step2 = -raw28422step1 := by apply Matrix.ext; change ∀ i j, raw28422step2 i j = -(raw28422step1 i j); unfold raw28422step2 raw28422step1; decide +kernel
      have hl : raw28422step2Labels = raw28422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw28423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28423step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28423 raw28423Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw28423 raw28423Labels = mixedMoment B raw28423step0 raw28423step0Labels := by
      have hz : ∀ j, raw28423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28423step0 = (fun i j => raw28423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28423step0 raw28423; decide +kernel
      have hl : raw28423step0Labels = raw28423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28423 raw28423Labels permutation346 hz
    mixedMoment B raw28423step0 raw28423step0Labels = mixedMoment B raw28423step1 raw28423step1Labels := by
      have ha : raw28423step1 = (fun i j => raw28423step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28423step1 raw28423step0; decide +kernel
      have hl : raw28423step1Labels = raw28423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28423step0 raw28423step0Labels permutation151 permutation2
    mixedMoment B raw28423step1 raw28423step1Labels = mixedMoment B raw28423step2 raw28423step2Labels := by
      have ha : raw28423step2 = -raw28423step1 := by apply Matrix.ext; change ∀ i j, raw28423step2 i j = -(raw28423step1 i j); unfold raw28423step2 raw28423step1; decide +kernel
      have hl : raw28423step2Labels = raw28423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw28424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw28424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw28424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![4, -1, -3]]
def raw28424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw28424step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw28424step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw28424step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28424 raw28424Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw28424 raw28424Labels = mixedMoment B raw28424step0 raw28424step0Labels := by
      have hz : ∀ j, raw28424 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28424step0 = (fun i j => raw28424 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28424step0 raw28424; decide +kernel
      have hl : raw28424step0Labels = raw28424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28424 raw28424Labels permutation520 hz
    mixedMoment B raw28424step0 raw28424step0Labels = mixedMoment B raw28424step1 raw28424step1Labels := by
      have hz : ∀ j, raw28424step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28424step1 = (fun i j => raw28424step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28424step1 raw28424step0; decide +kernel
      have hl : raw28424step1Labels = raw28424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28424step0 raw28424step0Labels permutation104 hz
    mixedMoment B raw28424step1 raw28424step1Labels = mixedMoment B raw28424step2 raw28424step2Labels := by
      have hz : ∀ j, raw28424step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28424step2 = (fun i j => raw28424step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28424step2 raw28424step1; decide +kernel
      have hl : raw28424step2Labels = raw28424step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28424step1 raw28424step1Labels permutation20 hz
    mixedMoment B raw28424step2 raw28424step2Labels = mixedMoment B raw28424step3 raw28424step3Labels := by
      have ha : raw28424step3 = (fun i j => raw28424step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28424step3 raw28424step2; decide +kernel
      have hl : raw28424step3Labels = raw28424step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28424step2 raw28424step2Labels permutation7 permutation2
    mixedMoment B raw28424step3 raw28424step3Labels = mixedMoment B raw28424step4 raw28424step4Labels := by
      have ha : raw28424step4 = -raw28424step3 := by apply Matrix.ext; change ∀ i j, raw28424step4 i j = -(raw28424step3 i j); unfold raw28424step4 raw28424step3; decide +kernel
      have hl : raw28424step4Labels = raw28424step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw28425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28425step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28425step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28425 raw28425Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw28425 raw28425Labels = mixedMoment B raw28425step0 raw28425step0Labels := by
      have hz : ∀ j, raw28425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28425step0 = (fun i j => raw28425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28425step0 raw28425; decide +kernel
      have hl : raw28425step0Labels = raw28425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28425 raw28425Labels permutation434 hz
    mixedMoment B raw28425step0 raw28425step0Labels = mixedMoment B raw28425step1 raw28425step1Labels := by
      have hz : ∀ j, raw28425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28425step1 = (fun i j => raw28425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28425step1 raw28425step0; decide +kernel
      have hl : raw28425step1Labels = raw28425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28425step0 raw28425step0Labels permutation80 hz
    mixedMoment B raw28425step1 raw28425step1Labels = mixedMoment B raw28425step2 raw28425step2Labels := by
      have ha : raw28425step2 = (fun i j => raw28425step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28425step2 raw28425step1; decide +kernel
      have hl : raw28425step2Labels = raw28425step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28425step1 raw28425step1Labels permutation30 permutation7
    mixedMoment B raw28425step2 raw28425step2Labels = mixedMoment B raw28425step3 raw28425step3Labels := by
      have ha : raw28425step3 = raw28425step2 := by apply Matrix.ext; unfold raw28425step3 raw28425step2; decide +kernel
      have hl : raw28425step2Labels = labelEmbedding1 ∘ raw28425step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28425step2 raw28425step2Labels raw28425step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw28426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28426 raw28426Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw28426 raw28426Labels = mixedMoment B raw28426step0 raw28426step0Labels := by
      have hz : ∀ j, raw28426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28426step0 = (fun i j => raw28426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28426step0 raw28426; decide +kernel
      have hl : raw28426step0Labels = raw28426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28426 raw28426Labels permutation434 hz
    mixedMoment B raw28426step0 raw28426step0Labels = mixedMoment B raw28426step1 raw28426step1Labels := by
      have ha : raw28426step1 = (fun i j => raw28426step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28426step1 raw28426step0; decide +kernel
      have hl : raw28426step1Labels = raw28426step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28426step0 raw28426step0Labels permutation150 permutation7
    mixedMoment B raw28426step1 raw28426step1Labels = mixedMoment B raw28426step2 raw28426step2Labels := by
      have ha : raw28426step2 = raw28426step1 := by apply Matrix.ext; unfold raw28426step2 raw28426step1; decide +kernel
      have hl : raw28426step1Labels = labelEmbedding1 ∘ raw28426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28426step1 raw28426step1Labels raw28426step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw28427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28427step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28427step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28427 raw28427Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw28427 raw28427Labels = mixedMoment B raw28427step0 raw28427step0Labels := by
      have hz : ∀ j, raw28427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28427step0 = (fun i j => raw28427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28427step0 raw28427; decide +kernel
      have hl : raw28427step0Labels = raw28427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28427 raw28427Labels permutation346 hz
    mixedMoment B raw28427step0 raw28427step0Labels = mixedMoment B raw28427step1 raw28427step1Labels := by
      have ha : raw28427step1 = (fun i j => raw28427step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28427step1 raw28427step0; decide +kernel
      have hl : raw28427step1Labels = raw28427step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28427step0 raw28427step0Labels permutation150 permutation7
    mixedMoment B raw28427step1 raw28427step1Labels = mixedMoment B raw28427step2 raw28427step2Labels := by
      have ha : raw28427step2 = raw28427step1 := by apply Matrix.ext; unfold raw28427step2 raw28427step1; decide +kernel
      have hl : raw28427step1Labels = labelEmbedding1 ∘ raw28427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28427step1 raw28427step1Labels raw28427step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw28428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28428step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28428step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw28428step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28428step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw28428step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28428step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw28428step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28428 raw28428Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw28428 raw28428Labels = mixedMoment B raw28428step0 raw28428step0Labels := by
      have hz : ∀ j, raw28428 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28428step0 = (fun i j => raw28428 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28428step0 raw28428; decide +kernel
      have hl : raw28428step0Labels = raw28428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28428 raw28428Labels permutation520 hz
    mixedMoment B raw28428step0 raw28428step0Labels = mixedMoment B raw28428step1 raw28428step1Labels := by
      have hz : ∀ j, raw28428step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28428step1 = (fun i j => raw28428step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28428step1 raw28428step0; decide +kernel
      have hl : raw28428step1Labels = raw28428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28428step0 raw28428step0Labels permutation104 hz
    mixedMoment B raw28428step1 raw28428step1Labels = mixedMoment B raw28428step2 raw28428step2Labels := by
      have hz : ∀ j, raw28428step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28428step2 = (fun i j => raw28428step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28428step2 raw28428step1; decide +kernel
      have hl : raw28428step2Labels = raw28428step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28428step1 raw28428step1Labels permutation20 hz
    mixedMoment B raw28428step2 raw28428step2Labels = mixedMoment B raw28428step3 raw28428step3Labels := by
      have ha : raw28428step3 = (fun i j => raw28428step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28428step3 raw28428step2; decide +kernel
      have hl : raw28428step3Labels = raw28428step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28428step2 raw28428step2Labels permutation6 permutation7
    mixedMoment B raw28428step3 raw28428step3Labels = mixedMoment B raw28428step4 raw28428step4Labels := by
      have ha : raw28428step4 = raw28428step3 := by apply Matrix.ext; unfold raw28428step4 raw28428step3; decide +kernel
      have hl : raw28428step3Labels = labelEmbedding1 ∘ raw28428step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28428step3 raw28428step3Labels raw28428step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw28429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28429step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28429step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28429 raw28429Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw28429 raw28429Labels = mixedMoment B raw28429step0 raw28429step0Labels := by
      have hz : ∀ j, raw28429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28429step0 = (fun i j => raw28429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28429step0 raw28429; decide +kernel
      have hl : raw28429step0Labels = raw28429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28429 raw28429Labels permutation434 hz
    mixedMoment B raw28429step0 raw28429step0Labels = mixedMoment B raw28429step1 raw28429step1Labels := by
      have hz : ∀ j, raw28429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28429step1 = (fun i j => raw28429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28429step1 raw28429step0; decide +kernel
      have hl : raw28429step1Labels = raw28429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28429step0 raw28429step0Labels permutation80 hz
    mixedMoment B raw28429step1 raw28429step1Labels = mixedMoment B raw28429step2 raw28429step2Labels := by
      have ha : raw28429step2 = (fun i j => raw28429step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28429step2 raw28429step1; decide +kernel
      have hl : raw28429step2Labels = raw28429step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28429step1 raw28429step1Labels permutation30 permutation7
    mixedMoment B raw28429step2 raw28429step2Labels = mixedMoment B raw28429step3 raw28429step3Labels := by
      have ha : raw28429step3 = raw28429step2 := by apply Matrix.ext; unfold raw28429step3 raw28429step2; decide +kernel
      have hl : raw28429step2Labels = labelEmbedding1 ∘ raw28429step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28429step2 raw28429step2Labels raw28429step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw28430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28430step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw28430step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw28430step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28430step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw28430step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28430 raw28430Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw28430 raw28430Labels = mixedMoment B raw28430step0 raw28430step0Labels := by
      have hz : ∀ j, raw28430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28430step0 = (fun i j => raw28430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28430step0 raw28430; decide +kernel
      have hl : raw28430step0Labels = raw28430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28430 raw28430Labels permutation434 hz
    mixedMoment B raw28430step0 raw28430step0Labels = mixedMoment B raw28430step1 raw28430step1Labels := by
      have hz : ∀ j, raw28430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28430step1 = (fun i j => raw28430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28430step1 raw28430step0; decide +kernel
      have hl : raw28430step1Labels = raw28430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28430step0 raw28430step0Labels permutation80 hz
    mixedMoment B raw28430step1 raw28430step1Labels = mixedMoment B raw28430step2 raw28430step2Labels := by
      have ha : raw28430step2 = (fun i j => raw28430step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28430step2 raw28430step1; decide +kernel
      have hl : raw28430step2Labels = raw28430step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28430step1 raw28430step1Labels permutation13 permutation5
    mixedMoment B raw28430step2 raw28430step2Labels = mixedMoment B raw28430step3 raw28430step3Labels := by
      have ha : raw28430step3 = -raw28430step2 := by apply Matrix.ext; change ∀ i j, raw28430step3 i j = -(raw28430step2 i j); unfold raw28430step3 raw28430step2; decide +kernel
      have hl : raw28430step3Labels = raw28430step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28430step3 raw28430step3Labels = mixedMoment B raw28430step4 raw28430step4Labels := by
      have ha : raw28430step4 = raw28430step3 := by apply Matrix.ext; unfold raw28430step4 raw28430step3; decide +kernel
      have hl : raw28430step3Labels = labelEmbedding1 ∘ raw28430step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28430step3 raw28430step3Labels raw28430step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw28431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28431 raw28431Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw28431 raw28431Labels = mixedMoment B raw28431step0 raw28431step0Labels := by
      have hz : ∀ j, raw28431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28431step0 = (fun i j => raw28431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28431step0 raw28431; decide +kernel
      have hl : raw28431step0Labels = raw28431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28431 raw28431Labels permutation434 hz
    mixedMoment B raw28431step0 raw28431step0Labels = mixedMoment B raw28431step1 raw28431step1Labels := by
      have ha : raw28431step1 = (fun i j => raw28431step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28431step1 raw28431step0; decide +kernel
      have hl : raw28431step1Labels = raw28431step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28431step0 raw28431step0Labels permutation150 permutation7
    mixedMoment B raw28431step1 raw28431step1Labels = mixedMoment B raw28431step2 raw28431step2Labels := by
      have ha : raw28431step2 = raw28431step1 := by apply Matrix.ext; unfold raw28431step2 raw28431step1; decide +kernel
      have hl : raw28431step1Labels = labelEmbedding1 ∘ raw28431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28431step1 raw28431step1Labels raw28431step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw28432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28432step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28432 raw28432Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw28432 raw28432Labels = mixedMoment B raw28432step0 raw28432step0Labels := by
      have hz : ∀ j, raw28432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28432step0 = (fun i j => raw28432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28432step0 raw28432; decide +kernel
      have hl : raw28432step0Labels = raw28432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28432 raw28432Labels permutation346 hz
    mixedMoment B raw28432step0 raw28432step0Labels = mixedMoment B raw28432step1 raw28432step1Labels := by
      have ha : raw28432step1 = (fun i j => raw28432step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28432step1 raw28432step0; decide +kernel
      have hl : raw28432step1Labels = raw28432step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28432step0 raw28432step0Labels permutation150 permutation7
    mixedMoment B raw28432step1 raw28432step1Labels = mixedMoment B raw28432step2 raw28432step2Labels := by
      have ha : raw28432step2 = raw28432step1 := by apply Matrix.ext; unfold raw28432step2 raw28432step1; decide +kernel
      have hl : raw28432step1Labels = labelEmbedding1 ∘ raw28432step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28432step1 raw28432step1Labels raw28432step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw28433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28433step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28433step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28433step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![3, 0, -3]]
def raw28433step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28433step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw28433step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28433step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw28433step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28433 raw28433Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw28433 raw28433Labels = mixedMoment B raw28433step0 raw28433step0Labels := by
      have hz : ∀ j, raw28433 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28433step0 = (fun i j => raw28433 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28433step0 raw28433; decide +kernel
      have hl : raw28433step0Labels = raw28433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28433 raw28433Labels permutation520 hz
    mixedMoment B raw28433step0 raw28433step0Labels = mixedMoment B raw28433step1 raw28433step1Labels := by
      have hz : ∀ j, raw28433step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28433step1 = (fun i j => raw28433step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28433step1 raw28433step0; decide +kernel
      have hl : raw28433step1Labels = raw28433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28433step0 raw28433step0Labels permutation104 hz
    mixedMoment B raw28433step1 raw28433step1Labels = mixedMoment B raw28433step2 raw28433step2Labels := by
      have hz : ∀ j, raw28433step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28433step2 = (fun i j => raw28433step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28433step2 raw28433step1; decide +kernel
      have hl : raw28433step2Labels = raw28433step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28433step1 raw28433step1Labels permutation20 hz
    mixedMoment B raw28433step2 raw28433step2Labels = mixedMoment B raw28433step3 raw28433step3Labels := by
      have ha : raw28433step3 = (fun i j => raw28433step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28433step3 raw28433step2; decide +kernel
      have hl : raw28433step3Labels = raw28433step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28433step2 raw28433step2Labels permutation6 permutation7
    mixedMoment B raw28433step3 raw28433step3Labels = mixedMoment B raw28433step4 raw28433step4Labels := by
      have ha : raw28433step4 = raw28433step3 := by apply Matrix.ext; unfold raw28433step4 raw28433step3; decide +kernel
      have hl : raw28433step3Labels = labelEmbedding1 ∘ raw28433step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28433step3 raw28433step3Labels raw28433step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw28434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28434step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw28434step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28434step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw28434step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28434 raw28434Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw28434 raw28434Labels = mixedMoment B raw28434step0 raw28434step0Labels := by
      have hz : ∀ j, raw28434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28434step0 = (fun i j => raw28434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28434step0 raw28434; decide +kernel
      have hl : raw28434step0Labels = raw28434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28434 raw28434Labels permutation434 hz
    mixedMoment B raw28434step0 raw28434step0Labels = mixedMoment B raw28434step1 raw28434step1Labels := by
      have hz : ∀ j, raw28434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28434step1 = (fun i j => raw28434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28434step1 raw28434step0; decide +kernel
      have hl : raw28434step1Labels = raw28434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28434step0 raw28434step0Labels permutation80 hz
    mixedMoment B raw28434step1 raw28434step1Labels = mixedMoment B raw28434step2 raw28434step2Labels := by
      have ha : raw28434step2 = (fun i j => raw28434step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28434step2 raw28434step1; decide +kernel
      have hl : raw28434step2Labels = raw28434step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28434step1 raw28434step1Labels permutation30 permutation7
    mixedMoment B raw28434step2 raw28434step2Labels = mixedMoment B raw28434step3 raw28434step3Labels := by
      have ha : raw28434step3 = raw28434step2 := by apply Matrix.ext; unfold raw28434step3 raw28434step2; decide +kernel
      have hl : raw28434step2Labels = labelEmbedding1 ∘ raw28434step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28434step2 raw28434step2Labels raw28434step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw28435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw28435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw28435step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28435step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw28435step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28435 raw28435Labels = mixedMoment B node1742 node1742Labels := by
  calc
    mixedMoment B raw28435 raw28435Labels = mixedMoment B raw28435step0 raw28435step0Labels := by
      have hz : ∀ j, raw28435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28435step0 = (fun i j => raw28435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28435step0 raw28435; decide +kernel
      have hl : raw28435step0Labels = raw28435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28435 raw28435Labels permutation434 hz
    mixedMoment B raw28435step0 raw28435step0Labels = mixedMoment B raw28435step1 raw28435step1Labels := by
      have ha : raw28435step1 = (fun i j => raw28435step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28435step1 raw28435step0; decide +kernel
      have hl : raw28435step1Labels = raw28435step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28435step0 raw28435step0Labels permutation50 permutation5
    mixedMoment B raw28435step1 raw28435step1Labels = mixedMoment B raw28435step2 raw28435step2Labels := by
      have ha : raw28435step2 = -raw28435step1 := by apply Matrix.ext; change ∀ i j, raw28435step2 i j = -(raw28435step1 i j); unfold raw28435step2 raw28435step1; decide +kernel
      have hl : raw28435step2Labels = raw28435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28435step2 raw28435step2Labels = mixedMoment B raw28435step3 raw28435step3Labels := by
      have ha : raw28435step3 = raw28435step2 := by apply Matrix.ext; unfold raw28435step3 raw28435step2; decide +kernel
      have hl : raw28435step2Labels = labelEmbedding1 ∘ raw28435step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28435step2 raw28435step2Labels raw28435step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1742 node1742Labels := by rfl

def raw28436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28436step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28436 raw28436Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw28436 raw28436Labels = mixedMoment B raw28436step0 raw28436step0Labels := by
      have hz : ∀ j, raw28436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28436step0 = (fun i j => raw28436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28436step0 raw28436; decide +kernel
      have hl : raw28436step0Labels = raw28436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28436 raw28436Labels permutation434 hz
    mixedMoment B raw28436step0 raw28436step0Labels = mixedMoment B raw28436step1 raw28436step1Labels := by
      have ha : raw28436step1 = (fun i j => raw28436step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28436step1 raw28436step0; decide +kernel
      have hl : raw28436step1Labels = raw28436step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28436step0 raw28436step0Labels permutation144 permutation7
    mixedMoment B raw28436step1 raw28436step1Labels = mixedMoment B raw28436step2 raw28436step2Labels := by
      have ha : raw28436step2 = raw28436step1 := by apply Matrix.ext; unfold raw28436step2 raw28436step1; decide +kernel
      have hl : raw28436step1Labels = labelEmbedding1 ∘ raw28436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28436step1 raw28436step1Labels raw28436step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

def raw28437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28437step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28437 raw28437Labels = mixedMoment B node2175 node2175Labels := by
  calc
    mixedMoment B raw28437 raw28437Labels = mixedMoment B raw28437step0 raw28437step0Labels := by
      have ha : raw28437step0 = (fun i j => raw28437 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28437step0 raw28437; decide +kernel
      have hl : raw28437step0Labels = raw28437Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28437 raw28437Labels permutation645 permutation7
    mixedMoment B raw28437step0 raw28437step0Labels = mixedMoment B raw28437step1 raw28437step1Labels := by
      have ha : raw28437step1 = raw28437step0 := by apply Matrix.ext; unfold raw28437step1 raw28437step0; decide +kernel
      have hl : raw28437step0Labels = labelEmbedding1 ∘ raw28437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28437step0 raw28437step0Labels raw28437step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2175 node2175Labels := by rfl

def raw28438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28438step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28438step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28438step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28438step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28438step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28438 raw28438Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw28438 raw28438Labels = mixedMoment B raw28438step0 raw28438step0Labels := by
      have hz : ∀ j, raw28438 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28438step0 = (fun i j => raw28438 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28438step0 raw28438; decide +kernel
      have hl : raw28438step0Labels = raw28438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28438 raw28438Labels permutation520 hz
    mixedMoment B raw28438step0 raw28438step0Labels = mixedMoment B raw28438step1 raw28438step1Labels := by
      have hz : ∀ j, raw28438step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28438step1 = (fun i j => raw28438step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28438step1 raw28438step0; decide +kernel
      have hl : raw28438step1Labels = raw28438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28438step0 raw28438step0Labels permutation104 hz
    mixedMoment B raw28438step1 raw28438step1Labels = mixedMoment B raw28438step2 raw28438step2Labels := by
      have ha : raw28438step2 = (fun i j => raw28438step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28438step2 raw28438step1; decide +kernel
      have hl : raw28438step2Labels = raw28438step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28438step1 raw28438step1Labels permutation30 permutation7
    mixedMoment B raw28438step2 raw28438step2Labels = mixedMoment B raw28438step3 raw28438step3Labels := by
      have ha : raw28438step3 = raw28438step2 := by apply Matrix.ext; unfold raw28438step3 raw28438step2; decide +kernel
      have hl : raw28438step2Labels = labelEmbedding1 ∘ raw28438step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28438step2 raw28438step2Labels raw28438step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw28439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28439 raw28439Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw28439 raw28439Labels = mixedMoment B raw28439step0 raw28439step0Labels := by
      have hz : ∀ j, raw28439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28439step0 = (fun i j => raw28439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28439step0 raw28439; decide +kernel
      have hl : raw28439step0Labels = raw28439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28439 raw28439Labels permutation434 hz
    mixedMoment B raw28439step0 raw28439step0Labels = mixedMoment B raw28439step1 raw28439step1Labels := by
      have ha : raw28439step1 = (fun i j => raw28439step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28439step1 raw28439step0; decide +kernel
      have hl : raw28439step1Labels = raw28439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28439step0 raw28439step0Labels permutation144 permutation7
    mixedMoment B raw28439step1 raw28439step1Labels = mixedMoment B raw28439step2 raw28439step2Labels := by
      have ha : raw28439step2 = raw28439step1 := by apply Matrix.ext; unfold raw28439step2 raw28439step1; decide +kernel
      have hl : raw28439step1Labels = labelEmbedding1 ∘ raw28439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28439step1 raw28439step1Labels raw28439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw28440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw28440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw28440step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28440step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw28440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28440 raw28440Labels = mixedMoment B node1742 node1742Labels := by
  calc
    mixedMoment B raw28440 raw28440Labels = mixedMoment B raw28440step0 raw28440step0Labels := by
      have hz : ∀ j, raw28440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28440step0 = (fun i j => raw28440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28440step0 raw28440; decide +kernel
      have hl : raw28440step0Labels = raw28440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28440 raw28440Labels permutation346 hz
    mixedMoment B raw28440step0 raw28440step0Labels = mixedMoment B raw28440step1 raw28440step1Labels := by
      have ha : raw28440step1 = (fun i j => raw28440step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28440step1 raw28440step0; decide +kernel
      have hl : raw28440step1Labels = raw28440step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28440step0 raw28440step0Labels permutation50 permutation5
    mixedMoment B raw28440step1 raw28440step1Labels = mixedMoment B raw28440step2 raw28440step2Labels := by
      have ha : raw28440step2 = -raw28440step1 := by apply Matrix.ext; change ∀ i j, raw28440step2 i j = -(raw28440step1 i j); unfold raw28440step2 raw28440step1; decide +kernel
      have hl : raw28440step2Labels = raw28440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28440step2 raw28440step2Labels = mixedMoment B raw28440step3 raw28440step3Labels := by
      have ha : raw28440step3 = raw28440step2 := by apply Matrix.ext; unfold raw28440step3 raw28440step2; decide +kernel
      have hl : raw28440step2Labels = labelEmbedding1 ∘ raw28440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28440step2 raw28440step2Labels raw28440step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1742 node1742Labels := by rfl

def raw28441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28441step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28441 raw28441Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw28441 raw28441Labels = mixedMoment B raw28441step0 raw28441step0Labels := by
      have hz : ∀ j, raw28441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28441step0 = (fun i j => raw28441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28441step0 raw28441; decide +kernel
      have hl : raw28441step0Labels = raw28441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28441 raw28441Labels permutation346 hz
    mixedMoment B raw28441step0 raw28441step0Labels = mixedMoment B raw28441step1 raw28441step1Labels := by
      have ha : raw28441step1 = (fun i j => raw28441step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28441step1 raw28441step0; decide +kernel
      have hl : raw28441step1Labels = raw28441step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28441step0 raw28441step0Labels permutation144 permutation7
    mixedMoment B raw28441step1 raw28441step1Labels = mixedMoment B raw28441step2 raw28441step2Labels := by
      have ha : raw28441step2 = raw28441step1 := by apply Matrix.ext; unfold raw28441step2 raw28441step1; decide +kernel
      have hl : raw28441step1Labels = labelEmbedding1 ∘ raw28441step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28441step1 raw28441step1Labels raw28441step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

def raw28442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28442 raw28442Labels = mixedMoment B node2175 node2175Labels := by
  calc
    mixedMoment B raw28442 raw28442Labels = mixedMoment B raw28442step0 raw28442step0Labels := by
      have ha : raw28442step0 = (fun i j => raw28442 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28442step0 raw28442; decide +kernel
      have hl : raw28442step0Labels = raw28442Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28442 raw28442Labels permutation663 permutation7
    mixedMoment B raw28442step0 raw28442step0Labels = mixedMoment B raw28442step1 raw28442step1Labels := by
      have ha : raw28442step1 = raw28442step0 := by apply Matrix.ext; unfold raw28442step1 raw28442step0; decide +kernel
      have hl : raw28442step0Labels = labelEmbedding1 ∘ raw28442step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28442step0 raw28442step0Labels raw28442step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2175 node2175Labels := by rfl

def raw28443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28443step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28443step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28443step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28443step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28443 raw28443Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw28443 raw28443Labels = mixedMoment B raw28443step0 raw28443step0Labels := by
      have hz : ∀ j, raw28443 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28443step0 = (fun i j => raw28443 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28443step0 raw28443; decide +kernel
      have hl : raw28443step0Labels = raw28443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28443 raw28443Labels permutation520 hz
    mixedMoment B raw28443step0 raw28443step0Labels = mixedMoment B raw28443step1 raw28443step1Labels := by
      have hz : ∀ j, raw28443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28443step1 = (fun i j => raw28443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28443step1 raw28443step0; decide +kernel
      have hl : raw28443step1Labels = raw28443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28443step0 raw28443step0Labels permutation80 hz
    mixedMoment B raw28443step1 raw28443step1Labels = mixedMoment B raw28443step2 raw28443step2Labels := by
      have ha : raw28443step2 = (fun i j => raw28443step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28443step2 raw28443step1; decide +kernel
      have hl : raw28443step2Labels = raw28443step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28443step1 raw28443step1Labels permutation30 permutation7
    mixedMoment B raw28443step2 raw28443step2Labels = mixedMoment B raw28443step3 raw28443step3Labels := by
      have ha : raw28443step3 = raw28443step2 := by apply Matrix.ext; unfold raw28443step3 raw28443step2; decide +kernel
      have hl : raw28443step2Labels = labelEmbedding1 ∘ raw28443step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28443step2 raw28443step2Labels raw28443step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw28444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28444 raw28444Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw28444 raw28444Labels = mixedMoment B raw28444step0 raw28444step0Labels := by
      have hz : ∀ j, raw28444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28444step0 = (fun i j => raw28444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28444step0 raw28444; decide +kernel
      have hl : raw28444step0Labels = raw28444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28444 raw28444Labels permutation346 hz
    mixedMoment B raw28444step0 raw28444step0Labels = mixedMoment B raw28444step1 raw28444step1Labels := by
      have ha : raw28444step1 = (fun i j => raw28444step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28444step1 raw28444step0; decide +kernel
      have hl : raw28444step1Labels = raw28444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28444step0 raw28444step0Labels permutation144 permutation7
    mixedMoment B raw28444step1 raw28444step1Labels = mixedMoment B raw28444step2 raw28444step2Labels := by
      have ha : raw28444step2 = raw28444step1 := by apply Matrix.ext; unfold raw28444step2 raw28444step1; decide +kernel
      have hl : raw28444step1Labels = labelEmbedding1 ∘ raw28444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28444step1 raw28444step1Labels raw28444step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw28445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw28445step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-2, 0, 2]]
def raw28445step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw28445step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28445step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw28445step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28445 raw28445Labels = mixedMoment B node1743 node1743Labels := by
  calc
    mixedMoment B raw28445 raw28445Labels = mixedMoment B raw28445step0 raw28445step0Labels := by
      have hz : ∀ j, raw28445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28445step0 = (fun i j => raw28445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28445step0 raw28445; decide +kernel
      have hl : raw28445step0Labels = raw28445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28445 raw28445Labels permutation434 hz
    mixedMoment B raw28445step0 raw28445step0Labels = mixedMoment B raw28445step1 raw28445step1Labels := by
      have hz : ∀ j, raw28445step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28445step1 = (fun i j => raw28445step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28445step1 raw28445step0; decide +kernel
      have hl : raw28445step1Labels = raw28445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28445step0 raw28445step0Labels permutation80 hz
    mixedMoment B raw28445step1 raw28445step1Labels = mixedMoment B raw28445step2 raw28445step2Labels := by
      have ha : raw28445step2 = (fun i j => raw28445step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28445step2 raw28445step1; decide +kernel
      have hl : raw28445step2Labels = raw28445step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28445step1 raw28445step1Labels permutation12 permutation5
    mixedMoment B raw28445step2 raw28445step2Labels = mixedMoment B raw28445step3 raw28445step3Labels := by
      have ha : raw28445step3 = -raw28445step2 := by apply Matrix.ext; change ∀ i j, raw28445step3 i j = -(raw28445step2 i j); unfold raw28445step3 raw28445step2; decide +kernel
      have hl : raw28445step3Labels = raw28445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28445step3 raw28445step3Labels = mixedMoment B raw28445step4 raw28445step4Labels := by
      have ha : raw28445step4 = raw28445step3 := by apply Matrix.ext; unfold raw28445step4 raw28445step3; decide +kernel
      have hl : raw28445step3Labels = labelEmbedding1 ∘ raw28445step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28445step3 raw28445step3Labels raw28445step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1743 node1743Labels := by rfl

def raw28446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![3, 0, -3]]
def raw28446step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw28446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw28446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28446 raw28446Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw28446 raw28446Labels = mixedMoment B raw28446step0 raw28446step0Labels := by
      have hz : ∀ j, raw28446 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28446step0 = (fun i j => raw28446 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28446step0 raw28446; decide +kernel
      have hl : raw28446step0Labels = raw28446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28446 raw28446Labels permutation434 hz
    mixedMoment B raw28446step0 raw28446step0Labels = mixedMoment B raw28446step1 raw28446step1Labels := by
      have hz : ∀ j, raw28446step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28446step1 = (fun i j => raw28446step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28446step1 raw28446step0; decide +kernel
      have hl : raw28446step1Labels = raw28446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28446step0 raw28446step0Labels permutation80 hz
    mixedMoment B raw28446step1 raw28446step1Labels = mixedMoment B raw28446step2 raw28446step2Labels := by
      have ha : raw28446step2 = (fun i j => raw28446step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28446step2 raw28446step1; decide +kernel
      have hl : raw28446step2Labels = raw28446step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28446step1 raw28446step1Labels permutation30 permutation7
    mixedMoment B raw28446step2 raw28446step2Labels = mixedMoment B raw28446step3 raw28446step3Labels := by
      have ha : raw28446step3 = raw28446step2 := by apply Matrix.ext; unfold raw28446step3 raw28446step2; decide +kernel
      have hl : raw28446step2Labels = labelEmbedding1 ∘ raw28446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28446step2 raw28446step2Labels raw28446step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

def raw28447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28447 raw28447Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw28447 raw28447Labels = mixedMoment B raw28447step0 raw28447step0Labels := by
      have hz : ∀ j, raw28447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28447step0 = (fun i j => raw28447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28447step0 raw28447; decide +kernel
      have hl : raw28447step0Labels = raw28447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28447 raw28447Labels permutation434 hz
    mixedMoment B raw28447step0 raw28447step0Labels = mixedMoment B raw28447step1 raw28447step1Labels := by
      have ha : raw28447step1 = (fun i j => raw28447step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28447step1 raw28447step0; decide +kernel
      have hl : raw28447step1Labels = raw28447step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28447step0 raw28447step0Labels permutation150 permutation7
    mixedMoment B raw28447step1 raw28447step1Labels = mixedMoment B raw28447step2 raw28447step2Labels := by
      have ha : raw28447step2 = raw28447step1 := by apply Matrix.ext; unfold raw28447step2 raw28447step1; decide +kernel
      have hl : raw28447step1Labels = labelEmbedding1 ∘ raw28447step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28447step1 raw28447step1Labels raw28447step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

def raw28448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28448 raw28448Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw28448 raw28448Labels = mixedMoment B raw28448step0 raw28448step0Labels := by
      have hz : ∀ j, raw28448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28448step0 = (fun i j => raw28448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28448step0 raw28448; decide +kernel
      have hl : raw28448step0Labels = raw28448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28448 raw28448Labels permutation346 hz
    mixedMoment B raw28448step0 raw28448step0Labels = mixedMoment B raw28448step1 raw28448step1Labels := by
      have ha : raw28448step1 = (fun i j => raw28448step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28448step1 raw28448step0; decide +kernel
      have hl : raw28448step1Labels = raw28448step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28448step0 raw28448step0Labels permutation150 permutation7
    mixedMoment B raw28448step1 raw28448step1Labels = mixedMoment B raw28448step2 raw28448step2Labels := by
      have ha : raw28448step2 = raw28448step1 := by apply Matrix.ext; unfold raw28448step2 raw28448step1; decide +kernel
      have hl : raw28448step1Labels = labelEmbedding1 ∘ raw28448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28448step1 raw28448step1Labels raw28448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

def raw28449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw28449step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw28449step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28449step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw28449step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28449 raw28449Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw28449 raw28449Labels = mixedMoment B raw28449step0 raw28449step0Labels := by
      have hz : ∀ j, raw28449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28449step0 = (fun i j => raw28449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28449step0 raw28449; decide +kernel
      have hl : raw28449step0Labels = raw28449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28449 raw28449Labels permutation434 hz
    mixedMoment B raw28449step0 raw28449step0Labels = mixedMoment B raw28449step1 raw28449step1Labels := by
      have hz : ∀ j, raw28449step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28449step1 = (fun i j => raw28449step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28449step1 raw28449step0; decide +kernel
      have hl : raw28449step1Labels = raw28449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28449step0 raw28449step0Labels permutation80 hz
    mixedMoment B raw28449step1 raw28449step1Labels = mixedMoment B raw28449step2 raw28449step2Labels := by
      have ha : raw28449step2 = (fun i j => raw28449step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28449step2 raw28449step1; decide +kernel
      have hl : raw28449step2Labels = raw28449step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28449step1 raw28449step1Labels permutation30 permutation7
    mixedMoment B raw28449step2 raw28449step2Labels = mixedMoment B raw28449step3 raw28449step3Labels := by
      have ha : raw28449step3 = raw28449step2 := by apply Matrix.ext; unfold raw28449step3 raw28449step2; decide +kernel
      have hl : raw28449step2Labels = labelEmbedding1 ∘ raw28449step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28449step2 raw28449step2Labels raw28449step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw28450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![4, -1, -3]]
def raw28450step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw28450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw28450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28450 raw28450Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw28450 raw28450Labels = mixedMoment B raw28450step0 raw28450step0Labels := by
      have hz : ∀ j, raw28450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28450step0 = (fun i j => raw28450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28450step0 raw28450; decide +kernel
      have hl : raw28450step0Labels = raw28450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28450 raw28450Labels permutation434 hz
    mixedMoment B raw28450step0 raw28450step0Labels = mixedMoment B raw28450step1 raw28450step1Labels := by
      have hz : ∀ j, raw28450step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28450step1 = (fun i j => raw28450step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28450step1 raw28450step0; decide +kernel
      have hl : raw28450step1Labels = raw28450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28450step0 raw28450step0Labels permutation80 hz
    mixedMoment B raw28450step1 raw28450step1Labels = mixedMoment B raw28450step2 raw28450step2Labels := by
      have ha : raw28450step2 = (fun i j => raw28450step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28450step2 raw28450step1; decide +kernel
      have hl : raw28450step2Labels = raw28450step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28450step1 raw28450step1Labels permutation30 permutation7
    mixedMoment B raw28450step2 raw28450step2Labels = mixedMoment B raw28450step3 raw28450step3Labels := by
      have ha : raw28450step3 = raw28450step2 := by apply Matrix.ext; unfold raw28450step3 raw28450step2; decide +kernel
      have hl : raw28450step2Labels = labelEmbedding1 ∘ raw28450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28450step2 raw28450step2Labels raw28450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

def raw28451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![4, -1, -3]]
def raw28451step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28451step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28451step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28451step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28451 raw28451Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw28451 raw28451Labels = mixedMoment B raw28451step0 raw28451step0Labels := by
      have hz : ∀ j, raw28451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28451step0 = (fun i j => raw28451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28451step0 raw28451; decide +kernel
      have hl : raw28451step0Labels = raw28451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28451 raw28451Labels permutation434 hz
    mixedMoment B raw28451step0 raw28451step0Labels = mixedMoment B raw28451step1 raw28451step1Labels := by
      have hz : ∀ j, raw28451step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28451step1 = (fun i j => raw28451step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28451step1 raw28451step0; decide +kernel
      have hl : raw28451step1Labels = raw28451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28451step0 raw28451step0Labels permutation80 hz
    mixedMoment B raw28451step1 raw28451step1Labels = mixedMoment B raw28451step2 raw28451step2Labels := by
      have ha : raw28451step2 = (fun i j => raw28451step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28451step2 raw28451step1; decide +kernel
      have hl : raw28451step2Labels = raw28451step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28451step1 raw28451step1Labels permutation30 permutation7
    mixedMoment B raw28451step2 raw28451step2Labels = mixedMoment B raw28451step3 raw28451step3Labels := by
      have ha : raw28451step3 = raw28451step2 := by apply Matrix.ext; unfold raw28451step3 raw28451step2; decide +kernel
      have hl : raw28451step2Labels = labelEmbedding1 ∘ raw28451step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28451step2 raw28451step2Labels raw28451step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

def raw28452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28452 raw28452Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw28452 raw28452Labels = mixedMoment B raw28452step0 raw28452step0Labels := by
      have hz : ∀ j, raw28452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28452step0 = (fun i j => raw28452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28452step0 raw28452; decide +kernel
      have hl : raw28452step0Labels = raw28452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28452 raw28452Labels permutation434 hz
    mixedMoment B raw28452step0 raw28452step0Labels = mixedMoment B raw28452step1 raw28452step1Labels := by
      have ha : raw28452step1 = (fun i j => raw28452step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28452step1 raw28452step0; decide +kernel
      have hl : raw28452step1Labels = raw28452step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28452step0 raw28452step0Labels permutation150 permutation7
    mixedMoment B raw28452step1 raw28452step1Labels = mixedMoment B raw28452step2 raw28452step2Labels := by
      have ha : raw28452step2 = raw28452step1 := by apply Matrix.ext; unfold raw28452step2 raw28452step1; decide +kernel
      have hl : raw28452step1Labels = labelEmbedding1 ∘ raw28452step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28452step1 raw28452step1Labels raw28452step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw28453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28453 raw28453Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw28453 raw28453Labels = mixedMoment B raw28453step0 raw28453step0Labels := by
      have hz : ∀ j, raw28453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28453step0 = (fun i j => raw28453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28453step0 raw28453; decide +kernel
      have hl : raw28453step0Labels = raw28453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28453 raw28453Labels permutation346 hz
    mixedMoment B raw28453step0 raw28453step0Labels = mixedMoment B raw28453step1 raw28453step1Labels := by
      have ha : raw28453step1 = (fun i j => raw28453step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28453step1 raw28453step0; decide +kernel
      have hl : raw28453step1Labels = raw28453step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28453step0 raw28453step0Labels permutation150 permutation7
    mixedMoment B raw28453step1 raw28453step1Labels = mixedMoment B raw28453step2 raw28453step2Labels := by
      have ha : raw28453step2 = raw28453step1 := by apply Matrix.ext; unfold raw28453step2 raw28453step1; decide +kernel
      have hl : raw28453step1Labels = labelEmbedding1 ∘ raw28453step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28453step1 raw28453step1Labels raw28453step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw28454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw28454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw28454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![4, -1, -3]]
def raw28454step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28454step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw28454step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28454step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw28454step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28454step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw28454step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28454 raw28454Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw28454 raw28454Labels = mixedMoment B raw28454step0 raw28454step0Labels := by
      have hz : ∀ j, raw28454 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28454step0 = (fun i j => raw28454 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28454step0 raw28454; decide +kernel
      have hl : raw28454step0Labels = raw28454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28454 raw28454Labels permutation520 hz
    mixedMoment B raw28454step0 raw28454step0Labels = mixedMoment B raw28454step1 raw28454step1Labels := by
      have hz : ∀ j, raw28454step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28454step1 = (fun i j => raw28454step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28454step1 raw28454step0; decide +kernel
      have hl : raw28454step1Labels = raw28454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28454step0 raw28454step0Labels permutation104 hz
    mixedMoment B raw28454step1 raw28454step1Labels = mixedMoment B raw28454step2 raw28454step2Labels := by
      have hz : ∀ j, raw28454step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28454step2 = (fun i j => raw28454step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28454step2 raw28454step1; decide +kernel
      have hl : raw28454step2Labels = raw28454step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28454step1 raw28454step1Labels permutation20 hz
    mixedMoment B raw28454step2 raw28454step2Labels = mixedMoment B raw28454step3 raw28454step3Labels := by
      have ha : raw28454step3 = (fun i j => raw28454step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28454step3 raw28454step2; decide +kernel
      have hl : raw28454step3Labels = raw28454step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28454step2 raw28454step2Labels permutation6 permutation7
    mixedMoment B raw28454step3 raw28454step3Labels = mixedMoment B raw28454step4 raw28454step4Labels := by
      have ha : raw28454step4 = raw28454step3 := by apply Matrix.ext; unfold raw28454step4 raw28454step3; decide +kernel
      have hl : raw28454step3Labels = labelEmbedding1 ∘ raw28454step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28454step3 raw28454step3Labels raw28454step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

def raw28455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw28455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28455step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28455 raw28455Labels = mixedMoment B node2066 node2066Labels := by
  calc
    mixedMoment B raw28455 raw28455Labels = mixedMoment B raw28455step0 raw28455step0Labels := by
      have hz : ∀ j, raw28455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28455step0 = (fun i j => raw28455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28455step0 raw28455; decide +kernel
      have hl : raw28455step0Labels = raw28455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28455 raw28455Labels permutation434 hz
    mixedMoment B raw28455step0 raw28455step0Labels = mixedMoment B raw28455step1 raw28455step1Labels := by
      have hz : ∀ j, raw28455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28455step1 = (fun i j => raw28455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28455step1 raw28455step0; decide +kernel
      have hl : raw28455step1Labels = raw28455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28455step0 raw28455step0Labels permutation80 hz
    mixedMoment B raw28455step1 raw28455step1Labels = mixedMoment B raw28455step2 raw28455step2Labels := by
      have ha : raw28455step2 = (fun i j => raw28455step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28455step2 raw28455step1; decide +kernel
      have hl : raw28455step2Labels = raw28455step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28455step1 raw28455step1Labels permutation30 permutation2
    mixedMoment B raw28455step2 raw28455step2Labels = mixedMoment B raw28455step3 raw28455step3Labels := by
      have ha : raw28455step3 = -raw28455step2 := by apply Matrix.ext; change ∀ i j, raw28455step3 i j = -(raw28455step2 i j); unfold raw28455step3 raw28455step2; decide +kernel
      have hl : raw28455step3Labels = raw28455step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2066 node2066Labels := by rfl

def raw28456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28456step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28456 raw28456Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw28456 raw28456Labels = mixedMoment B raw28456step0 raw28456step0Labels := by
      have hz : ∀ j, raw28456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28456step0 = (fun i j => raw28456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28456step0 raw28456; decide +kernel
      have hl : raw28456step0Labels = raw28456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28456 raw28456Labels permutation434 hz
    mixedMoment B raw28456step0 raw28456step0Labels = mixedMoment B raw28456step1 raw28456step1Labels := by
      have hz : ∀ j, raw28456step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28456step1 = (fun i j => raw28456step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28456step1 raw28456step0; decide +kernel
      have hl : raw28456step1Labels = raw28456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28456step0 raw28456step0Labels permutation80 hz
    mixedMoment B raw28456step1 raw28456step1Labels = mixedMoment B raw28456step2 raw28456step2Labels := by
      have ha : raw28456step2 = (fun i j => raw28456step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28456step2 raw28456step1; decide +kernel
      have hl : raw28456step2Labels = raw28456step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28456step1 raw28456step1Labels permutation31 permutation2
    mixedMoment B raw28456step2 raw28456step2Labels = mixedMoment B raw28456step3 raw28456step3Labels := by
      have ha : raw28456step3 = -raw28456step2 := by apply Matrix.ext; change ∀ i j, raw28456step3 i j = -(raw28456step2 i j); unfold raw28456step3 raw28456step2; decide +kernel
      have hl : raw28456step3Labels = raw28456step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw28457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28457 raw28457Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw28457 raw28457Labels = mixedMoment B raw28457step0 raw28457step0Labels := by
      have hz : ∀ j, raw28457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28457step0 = (fun i j => raw28457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28457step0 raw28457; decide +kernel
      have hl : raw28457step0Labels = raw28457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28457 raw28457Labels permutation434 hz
    mixedMoment B raw28457step0 raw28457step0Labels = mixedMoment B raw28457step1 raw28457step1Labels := by
      have ha : raw28457step1 = (fun i j => raw28457step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28457step1 raw28457step0; decide +kernel
      have hl : raw28457step1Labels = raw28457step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28457step0 raw28457step0Labels permutation145 permutation2
    mixedMoment B raw28457step1 raw28457step1Labels = mixedMoment B raw28457step2 raw28457step2Labels := by
      have ha : raw28457step2 = -raw28457step1 := by apply Matrix.ext; change ∀ i j, raw28457step2 i j = -(raw28457step1 i j); unfold raw28457step2 raw28457step1; decide +kernel
      have hl : raw28457step2Labels = raw28457step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1970 node1970Labels := by rfl

def raw28458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28458 raw28458Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw28458 raw28458Labels = mixedMoment B raw28458step0 raw28458step0Labels := by
      have hz : ∀ j, raw28458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28458step0 = (fun i j => raw28458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28458step0 raw28458; decide +kernel
      have hl : raw28458step0Labels = raw28458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28458 raw28458Labels permutation346 hz
    mixedMoment B raw28458step0 raw28458step0Labels = mixedMoment B raw28458step1 raw28458step1Labels := by
      have ha : raw28458step1 = (fun i j => raw28458step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28458step1 raw28458step0; decide +kernel
      have hl : raw28458step1Labels = raw28458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28458step0 raw28458step0Labels permutation145 permutation2
    mixedMoment B raw28458step1 raw28458step1Labels = mixedMoment B raw28458step2 raw28458step2Labels := by
      have ha : raw28458step2 = -raw28458step1 := by apply Matrix.ext; change ∀ i j, raw28458step2 i j = -(raw28458step1 i j); unfold raw28458step2 raw28458step1; decide +kernel
      have hl : raw28458step2Labels = raw28458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1970 node1970Labels := by rfl

def raw28459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![3, 0, -3]]
def raw28459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28459step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28459step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28459step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28459 raw28459Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw28459 raw28459Labels = mixedMoment B raw28459step0 raw28459step0Labels := by
      have hz : ∀ j, raw28459 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28459step0 = (fun i j => raw28459 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28459step0 raw28459; decide +kernel
      have hl : raw28459step0Labels = raw28459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28459 raw28459Labels permutation434 hz
    mixedMoment B raw28459step0 raw28459step0Labels = mixedMoment B raw28459step1 raw28459step1Labels := by
      have hz : ∀ j, raw28459step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28459step1 = (fun i j => raw28459step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28459step1 raw28459step0; decide +kernel
      have hl : raw28459step1Labels = raw28459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28459step0 raw28459step0Labels permutation80 hz
    mixedMoment B raw28459step1 raw28459step1Labels = mixedMoment B raw28459step2 raw28459step2Labels := by
      have ha : raw28459step2 = (fun i j => raw28459step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28459step2 raw28459step1; decide +kernel
      have hl : raw28459step2Labels = raw28459step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28459step1 raw28459step1Labels permutation31 permutation2
    mixedMoment B raw28459step2 raw28459step2Labels = mixedMoment B raw28459step3 raw28459step3Labels := by
      have ha : raw28459step3 = -raw28459step2 := by apply Matrix.ext; change ∀ i j, raw28459step3 i j = -(raw28459step2 i j); unfold raw28459step3 raw28459step2; decide +kernel
      have hl : raw28459step3Labels = raw28459step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw28460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![4, -1, -3]]
def raw28460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28460step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28460step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28460 raw28460Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw28460 raw28460Labels = mixedMoment B raw28460step0 raw28460step0Labels := by
      have hz : ∀ j, raw28460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28460step0 = (fun i j => raw28460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28460step0 raw28460; decide +kernel
      have hl : raw28460step0Labels = raw28460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28460 raw28460Labels permutation434 hz
    mixedMoment B raw28460step0 raw28460step0Labels = mixedMoment B raw28460step1 raw28460step1Labels := by
      have hz : ∀ j, raw28460step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28460step1 = (fun i j => raw28460step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28460step1 raw28460step0; decide +kernel
      have hl : raw28460step1Labels = raw28460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28460step0 raw28460step0Labels permutation80 hz
    mixedMoment B raw28460step1 raw28460step1Labels = mixedMoment B raw28460step2 raw28460step2Labels := by
      have ha : raw28460step2 = (fun i j => raw28460step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28460step2 raw28460step1; decide +kernel
      have hl : raw28460step2Labels = raw28460step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28460step1 raw28460step1Labels permutation31 permutation2
    mixedMoment B raw28460step2 raw28460step2Labels = mixedMoment B raw28460step3 raw28460step3Labels := by
      have ha : raw28460step3 = -raw28460step2 := by apply Matrix.ext; change ∀ i j, raw28460step3 i j = -(raw28460step2 i j); unfold raw28460step3 raw28460step2; decide +kernel
      have hl : raw28460step3Labels = raw28460step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node939 node939Labels := by rfl

def raw28461 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw28461Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28461step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![3, -3]]
def raw28461step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28461step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]
def raw28461step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28461step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]
def raw28461step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28461step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw28461step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28461step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw28461step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28461 raw28461Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw28461 raw28461Labels = mixedMoment B raw28461step0 raw28461step0Labels := by
      have hz : ∀ j, raw28461 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28461step0 = (fun i j => raw28461 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28461step0 raw28461; decide +kernel
      have hl : raw28461step0Labels = raw28461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28461 raw28461Labels permutation520 hz
    mixedMoment B raw28461step0 raw28461step0Labels = mixedMoment B raw28461step1 raw28461step1Labels := by
      have hz : ∀ j, raw28461step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28461step1 = (fun i j => raw28461step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28461step1 raw28461step0; decide +kernel
      have hl : raw28461step1Labels = raw28461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28461step0 raw28461step0Labels permutation104 hz
    mixedMoment B raw28461step1 raw28461step1Labels = mixedMoment B raw28461step2 raw28461step2Labels := by
      have hz : ∀ j, raw28461step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28461step2 = (fun i j => raw28461step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28461step2 raw28461step1; decide +kernel
      have hl : raw28461step2Labels = raw28461step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28461step1 raw28461step1Labels permutation20 hz
    mixedMoment B raw28461step2 raw28461step2Labels = mixedMoment B raw28461step3 raw28461step3Labels := by
      have ha : raw28461step3 = (fun i j => raw28461step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28461step3 raw28461step2; decide +kernel
      have hl : raw28461step3Labels = raw28461step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28461step2 raw28461step2Labels permutation6 permutation0
    mixedMoment B raw28461step3 raw28461step3Labels = mixedMoment B raw28461step4 raw28461step4Labels := by
      have ha : raw28461step4 = -raw28461step3 := by apply Matrix.ext; change ∀ i j, raw28461step4 i j = -(raw28461step3 i j); unfold raw28461step4 raw28461step3; decide +kernel
      have hl : raw28461step4Labels = raw28461step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw28462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28462 raw28462Labels = mixedMoment B node1315 node1315Labels := by
  calc
    mixedMoment B raw28462 raw28462Labels = mixedMoment B raw28462step0 raw28462step0Labels := by
      have hz : ∀ j, raw28462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28462step0 = (fun i j => raw28462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28462step0 raw28462; decide +kernel
      have hl : raw28462step0Labels = raw28462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28462 raw28462Labels permutation434 hz
    _ = mixedMoment B node1315 node1315Labels := by rfl

def raw28463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28463 raw28463Labels = mixedMoment B node1961 node1961Labels := by
  calc
    mixedMoment B raw28463 raw28463Labels = mixedMoment B raw28463step0 raw28463step0Labels := by
      have ha : raw28463step0 = (fun i j => raw28463 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28463step0 raw28463; decide +kernel
      have hl : raw28463step0Labels = raw28463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28463 raw28463Labels permutation646 permutation2
    mixedMoment B raw28463step0 raw28463step0Labels = mixedMoment B raw28463step1 raw28463step1Labels := by
      have ha : raw28463step1 = -raw28463step0 := by apply Matrix.ext; change ∀ i j, raw28463step1 i j = -(raw28463step0 i j); unfold raw28463step1 raw28463step0; decide +kernel
      have hl : raw28463step1Labels = raw28463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1961 node1961Labels := by rfl

def raw28464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28464step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28464step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28464step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28464 raw28464Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw28464 raw28464Labels = mixedMoment B raw28464step0 raw28464step0Labels := by
      have hz : ∀ j, raw28464 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28464step0 = (fun i j => raw28464 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28464step0 raw28464; decide +kernel
      have hl : raw28464step0Labels = raw28464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28464 raw28464Labels permutation520 hz
    mixedMoment B raw28464step0 raw28464step0Labels = mixedMoment B raw28464step1 raw28464step1Labels := by
      have hz : ∀ j, raw28464step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28464step1 = (fun i j => raw28464step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28464step1 raw28464step0; decide +kernel
      have hl : raw28464step1Labels = raw28464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28464step0 raw28464step0Labels permutation104 hz
    mixedMoment B raw28464step1 raw28464step1Labels = mixedMoment B raw28464step2 raw28464step2Labels := by
      have ha : raw28464step2 = (fun i j => raw28464step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28464step2 raw28464step1; decide +kernel
      have hl : raw28464step2Labels = raw28464step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28464step1 raw28464step1Labels permutation31 permutation2
    mixedMoment B raw28464step2 raw28464step2Labels = mixedMoment B raw28464step3 raw28464step3Labels := by
      have ha : raw28464step3 = -raw28464step2 := by apply Matrix.ext; change ∀ i j, raw28464step3 i j = -(raw28464step2 i j); unfold raw28464step3 raw28464step2; decide +kernel
      have hl : raw28464step3Labels = raw28464step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw28465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28465 raw28465Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw28465 raw28465Labels = mixedMoment B raw28465step0 raw28465step0Labels := by
      have hz : ∀ j, raw28465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28465step0 = (fun i j => raw28465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28465step0 raw28465; decide +kernel
      have hl : raw28465step0Labels = raw28465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28465 raw28465Labels permutation434 hz
    _ = mixedMoment B node2879 node2879Labels := by rfl

def raw28466 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw28466step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28466step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28466step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28466step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28466 raw28466Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw28466 raw28466Labels = mixedMoment B raw28466step0 raw28466step0Labels := by
      have hz : ∀ j, raw28466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28466step0 = (fun i j => raw28466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28466step0 raw28466; decide +kernel
      have hl : raw28466step0Labels = raw28466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28466 raw28466Labels permutation434 hz
    mixedMoment B raw28466step0 raw28466step0Labels = mixedMoment B raw28466step1 raw28466step1Labels := by
      have ha : raw28466step1 = (fun i j => raw28466step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28466step1 raw28466step0; decide +kernel
      have hl : raw28466step1Labels = raw28466step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28466step0 raw28466step0Labels permutation151 permutation7
    mixedMoment B raw28466step1 raw28466step1Labels = mixedMoment B raw28466step2 raw28466step2Labels := by
      have ha : raw28466step2 = -raw28466step1 := by apply Matrix.ext; change ∀ i j, raw28466step2 i j = -(raw28466step1 i j); unfold raw28466step2 raw28466step1; decide +kernel
      have hl : raw28466step2Labels = raw28466step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28466step2 raw28466step2Labels = mixedMoment B raw28466step3 raw28466step3Labels := by
      have ha : raw28466step3 = raw28466step2 := by apply Matrix.ext; unfold raw28466step3 raw28466step2; decide +kernel
      have hl : raw28466step2Labels = labelEmbedding10 ∘ raw28466step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28466step2 raw28466step2Labels raw28466step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw28467 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw28467step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28467step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28467step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28467step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28467 raw28467Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw28467 raw28467Labels = mixedMoment B raw28467step0 raw28467step0Labels := by
      have hz : ∀ j, raw28467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28467step0 = (fun i j => raw28467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28467step0 raw28467; decide +kernel
      have hl : raw28467step0Labels = raw28467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28467 raw28467Labels permutation346 hz
    mixedMoment B raw28467step0 raw28467step0Labels = mixedMoment B raw28467step1 raw28467step1Labels := by
      have ha : raw28467step1 = (fun i j => raw28467step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28467step1 raw28467step0; decide +kernel
      have hl : raw28467step1Labels = raw28467step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28467step0 raw28467step0Labels permutation151 permutation7
    mixedMoment B raw28467step1 raw28467step1Labels = mixedMoment B raw28467step2 raw28467step2Labels := by
      have ha : raw28467step2 = -raw28467step1 := by apply Matrix.ext; change ∀ i j, raw28467step2 i j = -(raw28467step1 i j); unfold raw28467step2 raw28467step1; decide +kernel
      have hl : raw28467step2Labels = raw28467step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28467step2 raw28467step2Labels = mixedMoment B raw28467step3 raw28467step3Labels := by
      have ha : raw28467step3 = raw28467step2 := by apply Matrix.ext; unfold raw28467step3 raw28467step2; decide +kernel
      have hl : raw28467step2Labels = labelEmbedding10 ∘ raw28467step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28467step2 raw28467step2Labels raw28467step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw28468 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw28468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw28468step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28468step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28468step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28468step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28468step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28468 raw28468Labels = mixedMoment B node4753 node4753Labels := by
  calc
    mixedMoment B raw28468 raw28468Labels = mixedMoment B raw28468step0 raw28468step0Labels := by
      have hz : ∀ j, raw28468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28468step0 = (fun i j => raw28468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28468step0 raw28468; decide +kernel
      have hl : raw28468step0Labels = raw28468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28468 raw28468Labels permutation434 hz
    mixedMoment B raw28468step0 raw28468step0Labels = mixedMoment B raw28468step1 raw28468step1Labels := by
      have hz : ∀ j, raw28468step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28468step1 = (fun i j => raw28468step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28468step1 raw28468step0; decide +kernel
      have hl : raw28468step1Labels = raw28468step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28468step0 raw28468step0Labels permutation80 hz
    mixedMoment B raw28468step1 raw28468step1Labels = mixedMoment B raw28468step2 raw28468step2Labels := by
      have ha : raw28468step2 = (fun i j => raw28468step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28468step2 raw28468step1; decide +kernel
      have hl : raw28468step2Labels = raw28468step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28468step1 raw28468step1Labels permutation31 permutation7
    mixedMoment B raw28468step2 raw28468step2Labels = mixedMoment B raw28468step3 raw28468step3Labels := by
      have ha : raw28468step3 = -raw28468step2 := by apply Matrix.ext; change ∀ i j, raw28468step3 i j = -(raw28468step2 i j); unfold raw28468step3 raw28468step2; decide +kernel
      have hl : raw28468step3Labels = raw28468step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28468step3 raw28468step3Labels = mixedMoment B raw28468step4 raw28468step4Labels := by
      have ha : raw28468step4 = raw28468step3 := by apply Matrix.ext; unfold raw28468step4 raw28468step3; decide +kernel
      have hl : raw28468step3Labels = labelEmbedding10 ∘ raw28468step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28468step3 raw28468step3Labels raw28468step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4753 node4753Labels := by rfl

def raw28469 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-4, 1, 3]]
def raw28469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw28469step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28469 raw28469Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw28469 raw28469Labels = mixedMoment B raw28469step0 raw28469step0Labels := by
      have hz : ∀ j, raw28469 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28469step0 = (fun i j => raw28469 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28469step0 raw28469; decide +kernel
      have hl : raw28469step0Labels = raw28469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28469 raw28469Labels permutation434 hz
    mixedMoment B raw28469step0 raw28469step0Labels = mixedMoment B raw28469step1 raw28469step1Labels := by
      have hz : ∀ j, raw28469step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28469step1 = (fun i j => raw28469step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28469step1 raw28469step0; decide +kernel
      have hl : raw28469step1Labels = raw28469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28469step0 raw28469step0Labels permutation80 hz
    mixedMoment B raw28469step1 raw28469step1Labels = mixedMoment B raw28469step2 raw28469step2Labels := by
      have ha : raw28469step2 = (fun i j => raw28469step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28469step2 raw28469step1; decide +kernel
      have hl : raw28469step2Labels = raw28469step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28469step1 raw28469step1Labels permutation31 permutation2
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw28470 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw28470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28470step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw28470step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28470step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw28470step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28470step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw28470step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28470 raw28470Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw28470 raw28470Labels = mixedMoment B raw28470step0 raw28470step0Labels := by
      have hz : ∀ j, raw28470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28470step0 = (fun i j => raw28470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28470step0 raw28470; decide +kernel
      have hl : raw28470step0Labels = raw28470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28470 raw28470Labels permutation434 hz
    mixedMoment B raw28470step0 raw28470step0Labels = mixedMoment B raw28470step1 raw28470step1Labels := by
      have hz : ∀ j, raw28470step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28470step1 = (fun i j => raw28470step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28470step1 raw28470step0; decide +kernel
      have hl : raw28470step1Labels = raw28470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28470step0 raw28470step0Labels permutation80 hz
    mixedMoment B raw28470step1 raw28470step1Labels = mixedMoment B raw28470step2 raw28470step2Labels := by
      have ha : raw28470step2 = (fun i j => raw28470step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28470step2 raw28470step1; decide +kernel
      have hl : raw28470step2Labels = raw28470step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28470step1 raw28470step1Labels permutation31 permutation7
    mixedMoment B raw28470step2 raw28470step2Labels = mixedMoment B raw28470step3 raw28470step3Labels := by
      have ha : raw28470step3 = -raw28470step2 := by apply Matrix.ext; change ∀ i j, raw28470step3 i j = -(raw28470step2 i j); unfold raw28470step3 raw28470step2; decide +kernel
      have hl : raw28470step3Labels = raw28470step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28470step3 raw28470step3Labels = mixedMoment B raw28470step4 raw28470step4Labels := by
      have ha : raw28470step4 = raw28470step3 := by apply Matrix.ext; unfold raw28470step4 raw28470step3; decide +kernel
      have hl : raw28470step3Labels = labelEmbedding10 ∘ raw28470step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28470step3 raw28470step3Labels raw28470step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw28471 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw28471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28471 raw28471Labels = mixedMoment B node4789 node4789Labels := by
  calc
    mixedMoment B raw28471 raw28471Labels = mixedMoment B raw28471step0 raw28471step0Labels := by
      have hz : ∀ j, raw28471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28471step0 = (fun i j => raw28471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28471step0 raw28471; decide +kernel
      have hl : raw28471step0Labels = raw28471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28471 raw28471Labels permutation434 hz
    mixedMoment B raw28471step0 raw28471step0Labels = mixedMoment B raw28471step1 raw28471step1Labels := by
      have ha : raw28471step1 = (fun i j => raw28471step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28471step1 raw28471step0; decide +kernel
      have hl : raw28471step1Labels = raw28471step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28471step0 raw28471step0Labels permutation144 permutation2
    _ = mixedMoment B node4789 node4789Labels := by rfl

def raw28472 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw28472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28472 raw28472Labels = mixedMoment B node4789 node4789Labels := by
  calc
    mixedMoment B raw28472 raw28472Labels = mixedMoment B raw28472step0 raw28472step0Labels := by
      have hz : ∀ j, raw28472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28472step0 = (fun i j => raw28472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28472step0 raw28472; decide +kernel
      have hl : raw28472step0Labels = raw28472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28472 raw28472Labels permutation346 hz
    mixedMoment B raw28472step0 raw28472step0Labels = mixedMoment B raw28472step1 raw28472step1Labels := by
      have ha : raw28472step1 = (fun i j => raw28472step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28472step1 raw28472step0; decide +kernel
      have hl : raw28472step1Labels = raw28472step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28472step0 raw28472step0Labels permutation144 permutation2
    _ = mixedMoment B node4789 node4789Labels := by rfl

def raw28473 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw28473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28473step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw28473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28473 raw28473Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw28473 raw28473Labels = mixedMoment B raw28473step0 raw28473step0Labels := by
      have hz : ∀ j, raw28473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28473step0 = (fun i j => raw28473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28473step0 raw28473; decide +kernel
      have hl : raw28473step0Labels = raw28473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28473 raw28473Labels permutation434 hz
    mixedMoment B raw28473step0 raw28473step0Labels = mixedMoment B raw28473step1 raw28473step1Labels := by
      have hz : ∀ j, raw28473step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28473step1 = (fun i j => raw28473step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28473step1 raw28473step0; decide +kernel
      have hl : raw28473step1Labels = raw28473step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28473step0 raw28473step0Labels permutation80 hz
    mixedMoment B raw28473step1 raw28473step1Labels = mixedMoment B raw28473step2 raw28473step2Labels := by
      have ha : raw28473step2 = (fun i j => raw28473step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28473step2 raw28473step1; decide +kernel
      have hl : raw28473step2Labels = raw28473step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28473step1 raw28473step1Labels permutation30 permutation2
    _ = mixedMoment B node4754 node4754Labels := by rfl

def raw28474 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, -1, 1], ![-4, 1, 3]]
def raw28474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw28474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28474 raw28474Labels = mixedMoment B node4429 node4429Labels := by
  calc
    mixedMoment B raw28474 raw28474Labels = mixedMoment B raw28474step0 raw28474step0Labels := by
      have hz : ∀ j, raw28474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28474step0 = (fun i j => raw28474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28474step0 raw28474; decide +kernel
      have hl : raw28474step0Labels = raw28474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28474 raw28474Labels permutation434 hz
    mixedMoment B raw28474step0 raw28474step0Labels = mixedMoment B raw28474step1 raw28474step1Labels := by
      have hz : ∀ j, raw28474step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28474step1 = (fun i j => raw28474step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28474step1 raw28474step0; decide +kernel
      have hl : raw28474step1Labels = raw28474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28474step0 raw28474step0Labels permutation80 hz
    mixedMoment B raw28474step1 raw28474step1Labels = mixedMoment B raw28474step2 raw28474step2Labels := by
      have ha : raw28474step2 = (fun i j => raw28474step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28474step2 raw28474step1; decide +kernel
      have hl : raw28474step2Labels = raw28474step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28474step1 raw28474step1Labels permutation30 permutation2
    _ = mixedMoment B node4429 node4429Labels := by rfl

def raw28475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw28475step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28475step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28475step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28475 raw28475Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw28475 raw28475Labels = mixedMoment B raw28475step0 raw28475step0Labels := by
      have hz : ∀ j, raw28475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28475step0 = (fun i j => raw28475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28475step0 raw28475; decide +kernel
      have hl : raw28475step0Labels = raw28475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28475 raw28475Labels permutation434 hz
    mixedMoment B raw28475step0 raw28475step0Labels = mixedMoment B raw28475step1 raw28475step1Labels := by
      have ha : raw28475step1 = (fun i j => raw28475step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28475step1 raw28475step0; decide +kernel
      have hl : raw28475step1Labels = raw28475step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28475step0 raw28475step0Labels permutation151 permutation7
    mixedMoment B raw28475step1 raw28475step1Labels = mixedMoment B raw28475step2 raw28475step2Labels := by
      have ha : raw28475step2 = -raw28475step1 := by apply Matrix.ext; change ∀ i j, raw28475step2 i j = -(raw28475step1 i j); unfold raw28475step2 raw28475step1; decide +kernel
      have hl : raw28475step2Labels = raw28475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28475step2 raw28475step2Labels = mixedMoment B raw28475step3 raw28475step3Labels := by
      have ha : raw28475step3 = raw28475step2 := by apply Matrix.ext; unfold raw28475step3 raw28475step2; decide +kernel
      have hl : raw28475step2Labels = labelEmbedding10 ∘ raw28475step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28475step2 raw28475step2Labels raw28475step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw28476 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28476step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28476step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28476step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28476 raw28476Labels = mixedMoment B node4780 node4780Labels := by
  calc
    mixedMoment B raw28476 raw28476Labels = mixedMoment B raw28476step0 raw28476step0Labels := by
      have ha : raw28476step0 = (fun i j => raw28476 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28476step0 raw28476; decide +kernel
      have hl : raw28476step0Labels = raw28476Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28476 raw28476Labels permutation688 permutation7
    mixedMoment B raw28476step0 raw28476step0Labels = mixedMoment B raw28476step1 raw28476step1Labels := by
      have ha : raw28476step1 = -raw28476step0 := by apply Matrix.ext; change ∀ i j, raw28476step1 i j = -(raw28476step0 i j); unfold raw28476step1 raw28476step0; decide +kernel
      have hl : raw28476step1Labels = raw28476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28476step1 raw28476step1Labels = mixedMoment B raw28476step2 raw28476step2Labels := by
      have ha : raw28476step2 = raw28476step1 := by apply Matrix.ext; unfold raw28476step2 raw28476step1; decide +kernel
      have hl : raw28476step1Labels = labelEmbedding10 ∘ raw28476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28476step1 raw28476step1Labels raw28476step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4780 node4780Labels := by rfl

def raw28477 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28477step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28477step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28477step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28477step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28477 raw28477Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw28477 raw28477Labels = mixedMoment B raw28477step0 raw28477step0Labels := by
      have hz : ∀ j, raw28477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28477step0 = (fun i j => raw28477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28477step0 raw28477; decide +kernel
      have hl : raw28477step0Labels = raw28477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28477 raw28477Labels permutation434 hz
    mixedMoment B raw28477step0 raw28477step0Labels = mixedMoment B raw28477step1 raw28477step1Labels := by
      have ha : raw28477step1 = (fun i j => raw28477step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28477step1 raw28477step0; decide +kernel
      have hl : raw28477step1Labels = raw28477step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28477step0 raw28477step0Labels permutation151 permutation7
    mixedMoment B raw28477step1 raw28477step1Labels = mixedMoment B raw28477step2 raw28477step2Labels := by
      have ha : raw28477step2 = -raw28477step1 := by apply Matrix.ext; change ∀ i j, raw28477step2 i j = -(raw28477step1 i j); unfold raw28477step2 raw28477step1; decide +kernel
      have hl : raw28477step2Labels = raw28477step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28477step2 raw28477step2Labels = mixedMoment B raw28477step3 raw28477step3Labels := by
      have ha : raw28477step3 = raw28477step2 := by apply Matrix.ext; unfold raw28477step3 raw28477step2; decide +kernel
      have hl : raw28477step2Labels = labelEmbedding10 ∘ raw28477step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28477step2 raw28477step2Labels raw28477step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw28478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw28478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28478 raw28478Labels = mixedMoment B node4420 node4420Labels := by
  calc
    mixedMoment B raw28478 raw28478Labels = mixedMoment B raw28478step0 raw28478step0Labels := by
      have hz : ∀ j, raw28478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28478step0 = (fun i j => raw28478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28478step0 raw28478; decide +kernel
      have hl : raw28478step0Labels = raw28478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28478 raw28478Labels permutation434 hz
    mixedMoment B raw28478step0 raw28478step0Labels = mixedMoment B raw28478step1 raw28478step1Labels := by
      have ha : raw28478step1 = (fun i j => raw28478step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28478step1 raw28478step0; decide +kernel
      have hl : raw28478step1Labels = raw28478step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28478step0 raw28478step0Labels permutation150 permutation2
    _ = mixedMoment B node4420 node4420Labels := by rfl

def raw28479 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw28479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28479 raw28479Labels = mixedMoment B node1864 node1864Labels := by
  calc
    mixedMoment B raw28479 raw28479Labels = mixedMoment B raw28479step0 raw28479step0Labels := by
      have ha : raw28479step0 = (fun i j => raw28479 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28479step0 raw28479; decide +kernel
      have hl : raw28479step0Labels = raw28479Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28479 raw28479Labels permutation682 permutation2
    _ = mixedMoment B node1864 node1864Labels := by rfl

def raw28480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw28480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -1, -1], ![2, 1, -3]]
def raw28480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28480 raw28480Labels = mixedMoment B node1953 node1953Labels := by
  calc
    mixedMoment B raw28480 raw28480Labels = mixedMoment B raw28480step0 raw28480step0Labels := by
      have hz : ∀ j, raw28480 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28480step0 = (fun i j => raw28480 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28480step0 raw28480; decide +kernel
      have hl : raw28480step0Labels = raw28480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28480 raw28480Labels permutation434 hz
    mixedMoment B raw28480step0 raw28480step0Labels = mixedMoment B raw28480step1 raw28480step1Labels := by
      have hz : ∀ j, raw28480step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28480step1 = (fun i j => raw28480step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28480step1 raw28480step0; decide +kernel
      have hl : raw28480step1Labels = raw28480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28480step0 raw28480step0Labels permutation80 hz
    mixedMoment B raw28480step1 raw28480step1Labels = mixedMoment B raw28480step2 raw28480step2Labels := by
      have ha : raw28480step2 = (fun i j => raw28480step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28480step2 raw28480step1; decide +kernel
      have hl : raw28480step2Labels = raw28480step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28480step1 raw28480step1Labels permutation31 permutation2
    _ = mixedMoment B node1953 node1953Labels := by rfl

def raw28481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw28481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw28481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw28481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28481 raw28481Labels = mixedMoment B node1774 node1774Labels := by
  calc
    mixedMoment B raw28481 raw28481Labels = mixedMoment B raw28481step0 raw28481step0Labels := by
      have hz : ∀ j, raw28481 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28481step0 = (fun i j => raw28481 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28481step0 raw28481; decide +kernel
      have hl : raw28481step0Labels = raw28481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28481 raw28481Labels permutation346 hz
    mixedMoment B raw28481step0 raw28481step0Labels = mixedMoment B raw28481step1 raw28481step1Labels := by
      have ha : raw28481step1 = (fun i j => raw28481step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28481step1 raw28481step0; decide +kernel
      have hl : raw28481step1Labels = raw28481step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28481step0 raw28481step0Labels permutation151 permutation2
    _ = mixedMoment B node1774 node1774Labels := by rfl

def raw28482 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw28482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw28482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw28482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28482 raw28482Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw28482 raw28482Labels = mixedMoment B raw28482step0 raw28482step0Labels := by
      have hz : ∀ j, raw28482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28482step0 = (fun i j => raw28482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28482step0 raw28482; decide +kernel
      have hl : raw28482step0Labels = raw28482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28482 raw28482Labels permutation346 hz
    mixedMoment B raw28482step0 raw28482step0Labels = mixedMoment B raw28482step1 raw28482step1Labels := by
      have ha : raw28482step1 = (fun i j => raw28482step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28482step1 raw28482step0; decide +kernel
      have hl : raw28482step1Labels = raw28482step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28482step0 raw28482step0Labels permutation151 permutation2
    _ = mixedMoment B node882 node882Labels := by rfl

def raw28483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw28483step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw28483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28483 raw28483Labels = mixedMoment B node2465 node2465Labels := by
  calc
    mixedMoment B raw28483 raw28483Labels = mixedMoment B raw28483step0 raw28483step0Labels := by
      have hz : ∀ j, raw28483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28483step0 = (fun i j => raw28483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28483step0 raw28483; decide +kernel
      have hl : raw28483step0Labels = raw28483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28483 raw28483Labels permutation434 hz
    mixedMoment B raw28483step0 raw28483step0Labels = mixedMoment B raw28483step1 raw28483step1Labels := by
      have ha : raw28483step1 = (fun i j => raw28483step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28483step1 raw28483step0; decide +kernel
      have hl : raw28483step1Labels = raw28483step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28483step0 raw28483step0Labels permutation151 permutation2
    mixedMoment B raw28483step1 raw28483step1Labels = mixedMoment B raw28483step2 raw28483step2Labels := by
      have ha : raw28483step2 = -raw28483step1 := by apply Matrix.ext; change ∀ i j, raw28483step2 i j = -(raw28483step1 i j); unfold raw28483step2 raw28483step1; decide +kernel
      have hl : raw28483step2Labels = raw28483step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2465 node2465Labels := by rfl

def raw28484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw28484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw28484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28484 raw28484Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw28484 raw28484Labels = mixedMoment B raw28484step0 raw28484step0Labels := by
      have hz : ∀ j, raw28484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28484step0 = (fun i j => raw28484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28484step0 raw28484; decide +kernel
      have hl : raw28484step0Labels = raw28484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28484 raw28484Labels permutation434 hz
    mixedMoment B raw28484step0 raw28484step0Labels = mixedMoment B raw28484step1 raw28484step1Labels := by
      have ha : raw28484step1 = (fun i j => raw28484step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28484step1 raw28484step0; decide +kernel
      have hl : raw28484step1Labels = raw28484step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28484step0 raw28484step0Labels permutation150 permutation2
    mixedMoment B raw28484step1 raw28484step1Labels = mixedMoment B raw28484step2 raw28484step2Labels := by
      have ha : raw28484step2 = -raw28484step1 := by apply Matrix.ext; change ∀ i j, raw28484step2 i j = -(raw28484step1 i j); unfold raw28484step2 raw28484step1; decide +kernel
      have hl : raw28484step2Labels = raw28484step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw28485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw28485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28485 raw28485Labels = mixedMoment B node2506 node2506Labels := by
  calc
    mixedMoment B raw28485 raw28485Labels = mixedMoment B raw28485step0 raw28485step0Labels := by
      have hz : ∀ j, raw28485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28485step0 = (fun i j => raw28485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28485step0 raw28485; decide +kernel
      have hl : raw28485step0Labels = raw28485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28485 raw28485Labels permutation434 hz
    mixedMoment B raw28485step0 raw28485step0Labels = mixedMoment B raw28485step1 raw28485step1Labels := by
      have ha : raw28485step1 = (fun i j => raw28485step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28485step1 raw28485step0; decide +kernel
      have hl : raw28485step1Labels = raw28485step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28485step0 raw28485step0Labels permutation151 permutation2
    mixedMoment B raw28485step1 raw28485step1Labels = mixedMoment B raw28485step2 raw28485step2Labels := by
      have ha : raw28485step2 = -raw28485step1 := by apply Matrix.ext; change ∀ i j, raw28485step2 i j = -(raw28485step1 i j); unfold raw28485step2 raw28485step1; decide +kernel
      have hl : raw28485step2Labels = raw28485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2506 node2506Labels := by rfl

def raw28486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw28486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw28486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28486 raw28486Labels = mixedMoment B node2460 node2460Labels := by
  calc
    mixedMoment B raw28486 raw28486Labels = mixedMoment B raw28486step0 raw28486step0Labels := by
      have ha : raw28486step0 = (fun i j => raw28486 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28486step0 raw28486; decide +kernel
      have hl : raw28486step0Labels = raw28486Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28486 raw28486Labels permutation682 permutation2
    mixedMoment B raw28486step0 raw28486step0Labels = mixedMoment B raw28486step1 raw28486step1Labels := by
      have ha : raw28486step1 = -raw28486step0 := by apply Matrix.ext; change ∀ i j, raw28486step1 i j = -(raw28486step0 i j); unfold raw28486step1 raw28486step0; decide +kernel
      have hl : raw28486step1Labels = raw28486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2460 node2460Labels := by rfl

def raw28487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw28487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw28487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28487 raw28487Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw28487 raw28487Labels = mixedMoment B raw28487step0 raw28487step0Labels := by
      have hz : ∀ j, raw28487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28487step0 = (fun i j => raw28487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28487step0 raw28487; decide +kernel
      have hl : raw28487step0Labels = raw28487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28487 raw28487Labels permutation434 hz
    mixedMoment B raw28487step0 raw28487step0Labels = mixedMoment B raw28487step1 raw28487step1Labels := by
      have ha : raw28487step1 = (fun i j => raw28487step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28487step1 raw28487step0; decide +kernel
      have hl : raw28487step1Labels = raw28487step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28487step0 raw28487step0Labels permutation145 permutation2
    mixedMoment B raw28487step1 raw28487step1Labels = mixedMoment B raw28487step2 raw28487step2Labels := by
      have ha : raw28487step2 = -raw28487step1 := by apply Matrix.ext; change ∀ i j, raw28487step2 i j = -(raw28487step1 i j); unfold raw28487step2 raw28487step1; decide +kernel
      have hl : raw28487step2Labels = raw28487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw28488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw28488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28488 raw28488Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw28488 raw28488Labels = mixedMoment B raw28488step0 raw28488step0Labels := by
      have hz : ∀ j, raw28488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28488step0 = (fun i j => raw28488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28488step0 raw28488; decide +kernel
      have hl : raw28488step0Labels = raw28488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28488 raw28488Labels permutation434 hz
    mixedMoment B raw28488step0 raw28488step0Labels = mixedMoment B raw28488step1 raw28488step1Labels := by
      have ha : raw28488step1 = (fun i j => raw28488step0 (permutation72 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28488step1 raw28488step0; decide +kernel
      have hl : raw28488step1Labels = raw28488step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28488step0 raw28488step0Labels permutation72 permutation4
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw28489 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]
def raw28489Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28489step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![2, -2]]
def raw28489step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28489step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw28489step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28489 raw28489Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw28489 raw28489Labels = mixedMoment B raw28489step0 raw28489step0Labels := by
      have hz : ∀ j, raw28489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28489step0 = (fun i j => raw28489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28489step0 raw28489; decide +kernel
      have hl : raw28489step0Labels = raw28489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28489 raw28489Labels permutation434 hz
    mixedMoment B raw28489step0 raw28489step0Labels = mixedMoment B raw28489step1 raw28489step1Labels := by
      have ha : raw28489step1 = (fun i j => raw28489step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28489step1 raw28489step0; decide +kernel
      have hl : raw28489step1Labels = raw28489step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28489step0 raw28489step0Labels permutation56 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw28490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw28490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28490 raw28490Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw28490 raw28490Labels = mixedMoment B raw28490step0 raw28490step0Labels := by
      have hz : ∀ j, raw28490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28490step0 = (fun i j => raw28490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28490step0 raw28490; decide +kernel
      have hl : raw28490step0Labels = raw28490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28490 raw28490Labels permutation434 hz
    mixedMoment B raw28490step0 raw28490step0Labels = mixedMoment B raw28490step1 raw28490step1Labels := by
      have ha : raw28490step1 = (fun i j => raw28490step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28490step1 raw28490step0; decide +kernel
      have hl : raw28490step1Labels = raw28490step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28490step0 raw28490step0Labels permutation73 permutation4
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw28491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28491 raw28491Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw28491 raw28491Labels = mixedMoment B raw28491step0 raw28491step0Labels := by
      have hz : ∀ j, raw28491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28491step0 = (fun i j => raw28491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28491step0 raw28491; decide +kernel
      have hl : raw28491step0Labels = raw28491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28491 raw28491Labels permutation434 hz
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw28492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28492 raw28492Labels = mixedMoment B node2833 node2833Labels := by
  calc
    _ = mixedMoment B node2833 node2833Labels := by rfl

def raw28493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw28493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28493 raw28493Labels = mixedMoment B node2835 node2835Labels := by
  calc
    mixedMoment B raw28493 raw28493Labels = mixedMoment B raw28493step0 raw28493step0Labels := by
      have hz : ∀ j, raw28493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28493step0 = (fun i j => raw28493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28493step0 raw28493; decide +kernel
      have hl : raw28493step0Labels = raw28493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28493 raw28493Labels permutation434 hz
    _ = mixedMoment B node2835 node2835Labels := by rfl

def raw28494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -3, 2], ![3, 0, -3]]
def raw28494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw28494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28494step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw28494step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28494 raw28494Labels = mixedMoment B node2137 node2137Labels := by
  calc
    mixedMoment B raw28494 raw28494Labels = mixedMoment B raw28494step0 raw28494step0Labels := by
      have hz : ∀ j, raw28494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28494step0 = (fun i j => raw28494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28494step0 raw28494; decide +kernel
      have hl : raw28494step0Labels = raw28494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28494 raw28494Labels permutation434 hz
    mixedMoment B raw28494step0 raw28494step0Labels = mixedMoment B raw28494step1 raw28494step1Labels := by
      have hz : ∀ j, raw28494step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28494step1 = (fun i j => raw28494step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28494step1 raw28494step0; decide +kernel
      have hl : raw28494step1Labels = raw28494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28494step0 raw28494step0Labels permutation80 hz
    mixedMoment B raw28494step1 raw28494step1Labels = mixedMoment B raw28494step2 raw28494step2Labels := by
      have ha : raw28494step2 = (fun i j => raw28494step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28494step2 raw28494step1; decide +kernel
      have hl : raw28494step2Labels = raw28494step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28494step1 raw28494step1Labels permutation31 permutation2
    mixedMoment B raw28494step2 raw28494step2Labels = mixedMoment B raw28494step3 raw28494step3Labels := by
      have ha : raw28494step3 = -raw28494step2 := by apply Matrix.ext; change ∀ i j, raw28494step3 i j = -(raw28494step2 i j); unfold raw28494step3 raw28494step2; decide +kernel
      have hl : raw28494step3Labels = raw28494step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2137 node2137Labels := by rfl

def raw28495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28495 raw28495Labels = mixedMoment B node2128 node2128Labels := by
  calc
    mixedMoment B raw28495 raw28495Labels = mixedMoment B raw28495step0 raw28495step0Labels := by
      have hz : ∀ j, raw28495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28495step0 = (fun i j => raw28495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28495step0 raw28495; decide +kernel
      have hl : raw28495step0Labels = raw28495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28495 raw28495Labels permutation434 hz
    mixedMoment B raw28495step0 raw28495step0Labels = mixedMoment B raw28495step1 raw28495step1Labels := by
      have ha : raw28495step1 = (fun i j => raw28495step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28495step1 raw28495step0; decide +kernel
      have hl : raw28495step1Labels = raw28495step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28495step0 raw28495step0Labels permutation149 permutation2
    mixedMoment B raw28495step1 raw28495step1Labels = mixedMoment B raw28495step2 raw28495step2Labels := by
      have ha : raw28495step2 = -raw28495step1 := by apply Matrix.ext; change ∀ i j, raw28495step2 i j = -(raw28495step1 i j); unfold raw28495step2 raw28495step1; decide +kernel
      have hl : raw28495step2Labels = raw28495step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2128 node2128Labels := by rfl

def raw28496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28496 raw28496Labels = mixedMoment B node2128 node2128Labels := by
  calc
    mixedMoment B raw28496 raw28496Labels = mixedMoment B raw28496step0 raw28496step0Labels := by
      have hz : ∀ j, raw28496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28496step0 = (fun i j => raw28496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28496step0 raw28496; decide +kernel
      have hl : raw28496step0Labels = raw28496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28496 raw28496Labels permutation346 hz
    mixedMoment B raw28496step0 raw28496step0Labels = mixedMoment B raw28496step1 raw28496step1Labels := by
      have ha : raw28496step1 = (fun i j => raw28496step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28496step1 raw28496step0; decide +kernel
      have hl : raw28496step1Labels = raw28496step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28496step0 raw28496step0Labels permutation149 permutation2
    mixedMoment B raw28496step1 raw28496step1Labels = mixedMoment B raw28496step2 raw28496step2Labels := by
      have ha : raw28496step2 = -raw28496step1 := by apply Matrix.ext; change ∀ i j, raw28496step2 i j = -(raw28496step1 i j); unfold raw28496step2 raw28496step1; decide +kernel
      have hl : raw28496step2Labels = raw28496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2128 node2128Labels := by rfl

def raw28497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw28497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw28497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![3, 0, -3]]
def raw28497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw28497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28497step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28497step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28497 raw28497Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw28497 raw28497Labels = mixedMoment B raw28497step0 raw28497step0Labels := by
      have hz : ∀ j, raw28497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28497step0 = (fun i j => raw28497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28497step0 raw28497; decide +kernel
      have hl : raw28497step0Labels = raw28497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28497 raw28497Labels permutation434 hz
    mixedMoment B raw28497step0 raw28497step0Labels = mixedMoment B raw28497step1 raw28497step1Labels := by
      have hz : ∀ j, raw28497step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28497step1 = (fun i j => raw28497step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28497step1 raw28497step0; decide +kernel
      have hl : raw28497step1Labels = raw28497step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28497step0 raw28497step0Labels permutation80 hz
    mixedMoment B raw28497step1 raw28497step1Labels = mixedMoment B raw28497step2 raw28497step2Labels := by
      have ha : raw28497step2 = (fun i j => raw28497step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28497step2 raw28497step1; decide +kernel
      have hl : raw28497step2Labels = raw28497step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28497step1 raw28497step1Labels permutation31 permutation2
    mixedMoment B raw28497step2 raw28497step2Labels = mixedMoment B raw28497step3 raw28497step3Labels := by
      have ha : raw28497step3 = -raw28497step2 := by apply Matrix.ext; change ∀ i j, raw28497step3 i j = -(raw28497step2 i j); unfold raw28497step3 raw28497step2; decide +kernel
      have hl : raw28497step3Labels = raw28497step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw28498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw28498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw28498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28498step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw28498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28498 raw28498Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw28498 raw28498Labels = mixedMoment B raw28498step0 raw28498step0Labels := by
      have hz : ∀ j, raw28498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28498step0 = (fun i j => raw28498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28498step0 raw28498; decide +kernel
      have hl : raw28498step0Labels = raw28498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28498 raw28498Labels permutation434 hz
    mixedMoment B raw28498step0 raw28498step0Labels = mixedMoment B raw28498step1 raw28498step1Labels := by
      have hz : ∀ j, raw28498step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28498step1 = (fun i j => raw28498step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28498step1 raw28498step0; decide +kernel
      have hl : raw28498step1Labels = raw28498step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28498step0 raw28498step0Labels permutation80 hz
    mixedMoment B raw28498step1 raw28498step1Labels = mixedMoment B raw28498step2 raw28498step2Labels := by
      have ha : raw28498step2 = (fun i j => raw28498step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28498step2 raw28498step1; decide +kernel
      have hl : raw28498step2Labels = raw28498step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28498step1 raw28498step1Labels permutation21 permutation4
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw28499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw28499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28499 raw28499Labels = mixedMoment B node2093 node2093Labels := by
  calc
    mixedMoment B raw28499 raw28499Labels = mixedMoment B raw28499step0 raw28499step0Labels := by
      have hz : ∀ j, raw28499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28499step0 = (fun i j => raw28499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28499step0 raw28499; decide +kernel
      have hl : raw28499step0Labels = raw28499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28499 raw28499Labels permutation346 hz
    mixedMoment B raw28499step0 raw28499step0Labels = mixedMoment B raw28499step1 raw28499step1Labels := by
      have ha : raw28499step1 = (fun i j => raw28499step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28499step1 raw28499step0; decide +kernel
      have hl : raw28499step1Labels = raw28499step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28499step0 raw28499step0Labels permutation151 permutation2
    mixedMoment B raw28499step1 raw28499step1Labels = mixedMoment B raw28499step2 raw28499step2Labels := by
      have ha : raw28499step2 = -raw28499step1 := by apply Matrix.ext; change ∀ i j, raw28499step2 i j = -(raw28499step1 i j); unfold raw28499step2 raw28499step1; decide +kernel
      have hl : raw28499step2Labels = raw28499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2093 node2093Labels := by rfl

def raw28500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28500 raw28500Labels = mixedMoment B node2085 node2085Labels := by
  calc
    mixedMoment B raw28500 raw28500Labels = mixedMoment B raw28500step0 raw28500step0Labels := by
      have ha : raw28500step0 = (fun i j => raw28500 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28500step0 raw28500; decide +kernel
      have hl : raw28500step0Labels = raw28500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28500 raw28500Labels permutation686 permutation2
    mixedMoment B raw28500step0 raw28500step0Labels = mixedMoment B raw28500step1 raw28500step1Labels := by
      have ha : raw28500step1 = -raw28500step0 := by apply Matrix.ext; change ∀ i j, raw28500step1 i j = -(raw28500step0 i j); unfold raw28500step1 raw28500step0; decide +kernel
      have hl : raw28500step1Labels = raw28500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2085 node2085Labels := by rfl

def raw28501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28501 raw28501Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw28501 raw28501Labels = mixedMoment B raw28501step0 raw28501step0Labels := by
      have hz : ∀ j, raw28501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28501step0 = (fun i j => raw28501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28501step0 raw28501; decide +kernel
      have hl : raw28501step0Labels = raw28501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28501 raw28501Labels permutation346 hz
    mixedMoment B raw28501step0 raw28501step0Labels = mixedMoment B raw28501step1 raw28501step1Labels := by
      have ha : raw28501step1 = (fun i j => raw28501step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28501step1 raw28501step0; decide +kernel
      have hl : raw28501step1Labels = raw28501step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28501step0 raw28501step0Labels permutation149 permutation2
    mixedMoment B raw28501step1 raw28501step1Labels = mixedMoment B raw28501step2 raw28501step2Labels := by
      have ha : raw28501step2 = -raw28501step1 := by apply Matrix.ext; change ∀ i j, raw28501step2 i j = -(raw28501step1 i j); unfold raw28501step2 raw28501step1; decide +kernel
      have hl : raw28501step2Labels = raw28501step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw28502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28502 raw28502Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw28502 raw28502Labels = mixedMoment B raw28502step0 raw28502step0Labels := by
      have hz : ∀ j, raw28502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28502step0 = (fun i j => raw28502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28502step0 raw28502; decide +kernel
      have hl : raw28502step0Labels = raw28502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28502 raw28502Labels permutation346 hz
    mixedMoment B raw28502step0 raw28502step0Labels = mixedMoment B raw28502step1 raw28502step1Labels := by
      have ha : raw28502step1 = (fun i j => raw28502step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28502step1 raw28502step0; decide +kernel
      have hl : raw28502step1Labels = raw28502step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28502step0 raw28502step0Labels permutation145 permutation2
    mixedMoment B raw28502step1 raw28502step1Labels = mixedMoment B raw28502step2 raw28502step2Labels := by
      have ha : raw28502step2 = -raw28502step1 := by apply Matrix.ext; change ∀ i j, raw28502step2 i j = -(raw28502step1 i j); unfold raw28502step2 raw28502step1; decide +kernel
      have hl : raw28502step2Labels = raw28502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw28503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw28503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw28503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28503 raw28503Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw28503 raw28503Labels = mixedMoment B raw28503step0 raw28503step0Labels := by
      have hz : ∀ j, raw28503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28503step0 = (fun i j => raw28503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28503step0 raw28503; decide +kernel
      have hl : raw28503step0Labels = raw28503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28503 raw28503Labels permutation346 hz
    mixedMoment B raw28503step0 raw28503step0Labels = mixedMoment B raw28503step1 raw28503step1Labels := by
      have ha : raw28503step1 = (fun i j => raw28503step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28503step1 raw28503step0; decide +kernel
      have hl : raw28503step1Labels = raw28503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28503step0 raw28503step0Labels permutation151 permutation2
    mixedMoment B raw28503step1 raw28503step1Labels = mixedMoment B raw28503step2 raw28503step2Labels := by
      have ha : raw28503step2 = -raw28503step1 := by apply Matrix.ext; change ∀ i j, raw28503step2 i j = -(raw28503step1 i j); unfold raw28503step2 raw28503step1; decide +kernel
      have hl : raw28503step2Labels = raw28503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw28504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw28504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw28504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28504 raw28504Labels = mixedMoment B node2498 node2498Labels := by
  calc
    mixedMoment B raw28504 raw28504Labels = mixedMoment B raw28504step0 raw28504step0Labels := by
      have hz : ∀ j, raw28504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28504step0 = (fun i j => raw28504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28504step0 raw28504; decide +kernel
      have hl : raw28504step0Labels = raw28504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28504 raw28504Labels permutation346 hz
    mixedMoment B raw28504step0 raw28504step0Labels = mixedMoment B raw28504step1 raw28504step1Labels := by
      have ha : raw28504step1 = (fun i j => raw28504step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28504step1 raw28504step0; decide +kernel
      have hl : raw28504step1Labels = raw28504step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28504step0 raw28504step0Labels permutation151 permutation2
    mixedMoment B raw28504step1 raw28504step1Labels = mixedMoment B raw28504step2 raw28504step2Labels := by
      have ha : raw28504step2 = -raw28504step1 := by apply Matrix.ext; change ∀ i j, raw28504step2 i j = -(raw28504step1 i j); unfold raw28504step2 raw28504step1; decide +kernel
      have hl : raw28504step2Labels = raw28504step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2498 node2498Labels := by rfl

def raw28505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28505 raw28505Labels = mixedMoment B node2490 node2490Labels := by
  calc
    mixedMoment B raw28505 raw28505Labels = mixedMoment B raw28505step0 raw28505step0Labels := by
      have ha : raw28505step0 = (fun i j => raw28505 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28505step0 raw28505; decide +kernel
      have hl : raw28505step0Labels = raw28505Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28505 raw28505Labels permutation686 permutation2
    mixedMoment B raw28505step0 raw28505step0Labels = mixedMoment B raw28505step1 raw28505step1Labels := by
      have ha : raw28505step1 = -raw28505step0 := by apply Matrix.ext; change ∀ i j, raw28505step1 i j = -(raw28505step0 i j); unfold raw28505step1 raw28505step0; decide +kernel
      have hl : raw28505step1Labels = raw28505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2490 node2490Labels := by rfl

def raw28506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw28506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28506 raw28506Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw28506 raw28506Labels = mixedMoment B raw28506step0 raw28506step0Labels := by
      have hz : ∀ j, raw28506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28506step0 = (fun i j => raw28506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28506step0 raw28506; decide +kernel
      have hl : raw28506step0Labels = raw28506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28506 raw28506Labels permutation346 hz
    mixedMoment B raw28506step0 raw28506step0Labels = mixedMoment B raw28506step1 raw28506step1Labels := by
      have ha : raw28506step1 = (fun i j => raw28506step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28506step1 raw28506step0; decide +kernel
      have hl : raw28506step1Labels = raw28506step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28506step0 raw28506step0Labels permutation149 permutation2
    mixedMoment B raw28506step1 raw28506step1Labels = mixedMoment B raw28506step2 raw28506step2Labels := by
      have ha : raw28506step2 = -raw28506step1 := by apply Matrix.ext; change ∀ i j, raw28506step2 i j = -(raw28506step1 i j); unfold raw28506step2 raw28506step1; decide +kernel
      have hl : raw28506step2Labels = raw28506step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw28507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw28507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28507 raw28507Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw28507 raw28507Labels = mixedMoment B raw28507step0 raw28507step0Labels := by
      have hz : ∀ j, raw28507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28507step0 = (fun i j => raw28507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28507step0 raw28507; decide +kernel
      have hl : raw28507step0Labels = raw28507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28507 raw28507Labels permutation346 hz
    mixedMoment B raw28507step0 raw28507step0Labels = mixedMoment B raw28507step1 raw28507step1Labels := by
      have ha : raw28507step1 = (fun i j => raw28507step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28507step1 raw28507step0; decide +kernel
      have hl : raw28507step1Labels = raw28507step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28507step0 raw28507step0Labels permutation151 permutation2
    mixedMoment B raw28507step1 raw28507step1Labels = mixedMoment B raw28507step2 raw28507step2Labels := by
      have ha : raw28507step2 = -raw28507step1 := by apply Matrix.ext; change ∀ i j, raw28507step2 i j = -(raw28507step1 i j); unfold raw28507step2 raw28507step1; decide +kernel
      have hl : raw28507step2Labels = raw28507step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw28508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw28508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28508 raw28508Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw28508 raw28508Labels = mixedMoment B raw28508step0 raw28508step0Labels := by
      have hz : ∀ j, raw28508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28508step0 = (fun i j => raw28508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28508step0 raw28508; decide +kernel
      have hl : raw28508step0Labels = raw28508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28508 raw28508Labels permutation346 hz
    mixedMoment B raw28508step0 raw28508step0Labels = mixedMoment B raw28508step1 raw28508step1Labels := by
      have ha : raw28508step1 = (fun i j => raw28508step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28508step1 raw28508step0; decide +kernel
      have hl : raw28508step1Labels = raw28508step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28508step0 raw28508step0Labels permutation151 permutation2
    mixedMoment B raw28508step1 raw28508step1Labels = mixedMoment B raw28508step2 raw28508step2Labels := by
      have ha : raw28508step2 = -raw28508step1 := by apply Matrix.ext; change ∀ i j, raw28508step2 i j = -(raw28508step1 i j); unfold raw28508step2 raw28508step1; decide +kernel
      have hl : raw28508step2Labels = raw28508step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw28509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28509 raw28509Labels = mixedMoment B node2606 node2606Labels := by
  calc
    mixedMoment B raw28509 raw28509Labels = mixedMoment B raw28509step0 raw28509step0Labels := by
      have ha : raw28509step0 = (fun i j => raw28509 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28509step0 raw28509; decide +kernel
      have hl : raw28509step0Labels = raw28509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28509 raw28509Labels permutation158 permutation2
    _ = mixedMoment B node2606 node2606Labels := by rfl

def raw28510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28510 raw28510Labels = mixedMoment B node2629 node2629Labels := by
  calc
    mixedMoment B raw28510 raw28510Labels = mixedMoment B raw28510step0 raw28510step0Labels := by
      have hz : ∀ j, raw28510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28510step0 = (fun i j => raw28510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28510step0 raw28510; decide +kernel
      have hl : raw28510step0Labels = raw28510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28510 raw28510Labels permutation346 hz
    _ = mixedMoment B node2629 node2629Labels := by rfl

def raw28511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28511 raw28511Labels = mixedMoment B node2608 node2608Labels := by
  calc
    mixedMoment B raw28511 raw28511Labels = mixedMoment B raw28511step0 raw28511step0Labels := by
      have hz : ∀ j, raw28511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28511step0 = (fun i j => raw28511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28511step0 raw28511; decide +kernel
      have hl : raw28511step0Labels = raw28511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28511 raw28511Labels permutation346 hz
    _ = mixedMoment B node2608 node2608Labels := by rfl

def raw28512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw28512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw28512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28512 raw28512Labels = mixedMoment B node2038 node2038Labels := by
  calc
    mixedMoment B raw28512 raw28512Labels = mixedMoment B raw28512step0 raw28512step0Labels := by
      have hz : ∀ j, raw28512 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28512step0 = (fun i j => raw28512 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28512step0 raw28512; decide +kernel
      have hl : raw28512step0Labels = raw28512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28512 raw28512Labels permutation346 hz
    mixedMoment B raw28512step0 raw28512step0Labels = mixedMoment B raw28512step1 raw28512step1Labels := by
      have ha : raw28512step1 = (fun i j => raw28512step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28512step1 raw28512step0; decide +kernel
      have hl : raw28512step1Labels = raw28512step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28512step0 raw28512step0Labels permutation151 permutation2
    mixedMoment B raw28512step1 raw28512step1Labels = mixedMoment B raw28512step2 raw28512step2Labels := by
      have ha : raw28512step2 = -raw28512step1 := by apply Matrix.ext; change ∀ i j, raw28512step2 i j = -(raw28512step1 i j); unfold raw28512step2 raw28512step1; decide +kernel
      have hl : raw28512step2Labels = raw28512step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2038 node2038Labels := by rfl

def raw28513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28513 raw28513Labels = mixedMoment B node2030 node2030Labels := by
  calc
    mixedMoment B raw28513 raw28513Labels = mixedMoment B raw28513step0 raw28513step0Labels := by
      have ha : raw28513step0 = (fun i j => raw28513 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28513step0 raw28513; decide +kernel
      have hl : raw28513step0Labels = raw28513Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28513 raw28513Labels permutation686 permutation2
    mixedMoment B raw28513step0 raw28513step0Labels = mixedMoment B raw28513step1 raw28513step1Labels := by
      have ha : raw28513step1 = -raw28513step0 := by apply Matrix.ext; change ∀ i j, raw28513step1 i j = -(raw28513step0 i j); unfold raw28513step1 raw28513step0; decide +kernel
      have hl : raw28513step1Labels = raw28513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2030 node2030Labels := by rfl

def raw28514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw28514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28514 raw28514Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw28514 raw28514Labels = mixedMoment B raw28514step0 raw28514step0Labels := by
      have hz : ∀ j, raw28514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28514step0 = (fun i j => raw28514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28514step0 raw28514; decide +kernel
      have hl : raw28514step0Labels = raw28514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28514 raw28514Labels permutation346 hz
    mixedMoment B raw28514step0 raw28514step0Labels = mixedMoment B raw28514step1 raw28514step1Labels := by
      have ha : raw28514step1 = (fun i j => raw28514step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28514step1 raw28514step0; decide +kernel
      have hl : raw28514step1Labels = raw28514step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28514step0 raw28514step0Labels permutation149 permutation2
    mixedMoment B raw28514step1 raw28514step1Labels = mixedMoment B raw28514step2 raw28514step2Labels := by
      have ha : raw28514step2 = -raw28514step1 := by apply Matrix.ext; change ∀ i j, raw28514step2 i j = -(raw28514step1 i j); unfold raw28514step2 raw28514step1; decide +kernel
      have hl : raw28514step2Labels = raw28514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2048 node2048Labels := by rfl

def raw28515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw28515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![3, 0, -3]]
def raw28515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw28515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28515step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28515step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28515 raw28515Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw28515 raw28515Labels = mixedMoment B raw28515step0 raw28515step0Labels := by
      have hz : ∀ j, raw28515 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28515step0 = (fun i j => raw28515 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28515step0 raw28515; decide +kernel
      have hl : raw28515step0Labels = raw28515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28515 raw28515Labels permutation520 hz
    mixedMoment B raw28515step0 raw28515step0Labels = mixedMoment B raw28515step1 raw28515step1Labels := by
      have hz : ∀ j, raw28515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28515step1 = (fun i j => raw28515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28515step1 raw28515step0; decide +kernel
      have hl : raw28515step1Labels = raw28515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28515step0 raw28515step0Labels permutation80 hz
    mixedMoment B raw28515step1 raw28515step1Labels = mixedMoment B raw28515step2 raw28515step2Labels := by
      have ha : raw28515step2 = (fun i j => raw28515step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28515step2 raw28515step1; decide +kernel
      have hl : raw28515step2Labels = raw28515step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28515step1 raw28515step1Labels permutation31 permutation2
    mixedMoment B raw28515step2 raw28515step2Labels = mixedMoment B raw28515step3 raw28515step3Labels := by
      have ha : raw28515step3 = -raw28515step2 := by apply Matrix.ext; change ∀ i j, raw28515step3 i j = -(raw28515step2 i j); unfold raw28515step3 raw28515step2; decide +kernel
      have hl : raw28515step3Labels = raw28515step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw28516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw28516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28516 raw28516Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw28516 raw28516Labels = mixedMoment B raw28516step0 raw28516step0Labels := by
      have hz : ∀ j, raw28516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28516step0 = (fun i j => raw28516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28516step0 raw28516; decide +kernel
      have hl : raw28516step0Labels = raw28516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28516 raw28516Labels permutation346 hz
    mixedMoment B raw28516step0 raw28516step0Labels = mixedMoment B raw28516step1 raw28516step1Labels := by
      have ha : raw28516step1 = (fun i j => raw28516step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28516step1 raw28516step0; decide +kernel
      have hl : raw28516step1Labels = raw28516step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28516step0 raw28516step0Labels permutation151 permutation2
    mixedMoment B raw28516step1 raw28516step1Labels = mixedMoment B raw28516step2 raw28516step2Labels := by
      have ha : raw28516step2 = -raw28516step1 := by apply Matrix.ext; change ∀ i j, raw28516step2 i j = -(raw28516step1 i j); unfold raw28516step2 raw28516step1; decide +kernel
      have hl : raw28516step2Labels = raw28516step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw28517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw28517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28517 raw28517Labels = mixedMoment B node2472 node2472Labels := by
  calc
    mixedMoment B raw28517 raw28517Labels = mixedMoment B raw28517step0 raw28517step0Labels := by
      have ha : raw28517step0 = (fun i j => raw28517 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28517step0 raw28517; decide +kernel
      have hl : raw28517step0Labels = raw28517Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28517 raw28517Labels permutation682 permutation2
    mixedMoment B raw28517step0 raw28517step0Labels = mixedMoment B raw28517step1 raw28517step1Labels := by
      have ha : raw28517step1 = -raw28517step0 := by apply Matrix.ext; change ∀ i j, raw28517step1 i j = -(raw28517step0 i j); unfold raw28517step1 raw28517step0; decide +kernel
      have hl : raw28517step1Labels = raw28517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2472 node2472Labels := by rfl

def raw28518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28518 raw28518Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw28518 raw28518Labels = mixedMoment B raw28518step0 raw28518step0Labels := by
      have ha : raw28518step0 = (fun i j => raw28518 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28518step0 raw28518; decide +kernel
      have hl : raw28518step0Labels = raw28518Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28518 raw28518Labels permutation686 permutation2
    mixedMoment B raw28518step0 raw28518step0Labels = mixedMoment B raw28518step1 raw28518step1Labels := by
      have ha : raw28518step1 = -raw28518step0 := by apply Matrix.ext; change ∀ i j, raw28518step1 i j = -(raw28518step0 i j); unfold raw28518step1 raw28518step0; decide +kernel
      have hl : raw28518step1Labels = raw28518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw28519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28519 raw28519Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw28519 raw28519Labels = mixedMoment B raw28519step0 raw28519step0Labels := by
      have ha : raw28519step0 = (fun i j => raw28519 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28519step0 raw28519; decide +kernel
      have hl : raw28519step0Labels = raw28519Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28519 raw28519Labels permutation680 permutation2
    mixedMoment B raw28519step0 raw28519step0Labels = mixedMoment B raw28519step1 raw28519step1Labels := by
      have ha : raw28519step1 = -raw28519step0 := by apply Matrix.ext; change ∀ i j, raw28519step1 i j = -(raw28519step0 i j); unfold raw28519step1 raw28519step0; decide +kernel
      have hl : raw28519step1Labels = raw28519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw28520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28520 raw28520Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw28520 raw28520Labels = mixedMoment B raw28520step0 raw28520step0Labels := by
      have ha : raw28520step0 = (fun i j => raw28520 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28520step0 raw28520; decide +kernel
      have hl : raw28520step0Labels = raw28520Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28520 raw28520Labels permutation682 permutation2
    mixedMoment B raw28520step0 raw28520step0Labels = mixedMoment B raw28520step1 raw28520step1Labels := by
      have ha : raw28520step1 = -raw28520step0 := by apply Matrix.ext; change ∀ i j, raw28520step1 i j = -(raw28520step0 i j); unfold raw28520step1 raw28520step0; decide +kernel
      have hl : raw28520step1Labels = raw28520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw28521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28521 raw28521Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw28521 raw28521Labels = mixedMoment B raw28521step0 raw28521step0Labels := by
      have ha : raw28521step0 = (fun i j => raw28521 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28521step0 raw28521; decide +kernel
      have hl : raw28521step0Labels = raw28521Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28521 raw28521Labels permutation682 permutation2
    mixedMoment B raw28521step0 raw28521step0Labels = mixedMoment B raw28521step1 raw28521step1Labels := by
      have ha : raw28521step1 = -raw28521step0 := by apply Matrix.ext; change ∀ i j, raw28521step1 i j = -(raw28521step0 i j); unfold raw28521step1 raw28521step0; decide +kernel
      have hl : raw28521step1Labels = raw28521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw28522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28522 raw28522Labels = mixedMoment B node2613 node2613Labels := by
  calc
    mixedMoment B raw28522 raw28522Labels = mixedMoment B raw28522step0 raw28522step0Labels := by
      have ha : raw28522step0 = (fun i j => raw28522 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28522step0 raw28522; decide +kernel
      have hl : raw28522step0Labels = raw28522Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28522 raw28522Labels permutation158 permutation2
    _ = mixedMoment B node2613 node2613Labels := by rfl

def raw28523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28523 raw28523Labels = mixedMoment B node2613 node2613Labels := by
  calc
    _ = mixedMoment B node2613 node2613Labels := by rfl

def raw28524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28524 raw28524Labels = mixedMoment B node2609 node2609Labels := by
  calc
    _ = mixedMoment B node2609 node2609Labels := by rfl

def raw28525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw28525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28525 raw28525Labels = mixedMoment B node2011 node2011Labels := by
  calc
    mixedMoment B raw28525 raw28525Labels = mixedMoment B raw28525step0 raw28525step0Labels := by
      have ha : raw28525step0 = (fun i j => raw28525 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28525step0 raw28525; decide +kernel
      have hl : raw28525step0Labels = raw28525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28525 raw28525Labels permutation682 permutation2
    mixedMoment B raw28525step0 raw28525step0Labels = mixedMoment B raw28525step1 raw28525step1Labels := by
      have ha : raw28525step1 = -raw28525step0 := by apply Matrix.ext; change ∀ i j, raw28525step1 i j = -(raw28525step0 i j); unfold raw28525step1 raw28525step0; decide +kernel
      have hl : raw28525step1Labels = raw28525step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2011 node2011Labels := by rfl

def raw28526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28526 raw28526Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw28526 raw28526Labels = mixedMoment B raw28526step0 raw28526step0Labels := by
      have ha : raw28526step0 = (fun i j => raw28526 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28526step0 raw28526; decide +kernel
      have hl : raw28526step0Labels = raw28526Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28526 raw28526Labels permutation686 permutation2
    mixedMoment B raw28526step0 raw28526step0Labels = mixedMoment B raw28526step1 raw28526step1Labels := by
      have ha : raw28526step1 = -raw28526step0 := by apply Matrix.ext; change ∀ i j, raw28526step1 i j = -(raw28526step0 i j); unfold raw28526step1 raw28526step0; decide +kernel
      have hl : raw28526step1Labels = raw28526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2016 node2016Labels := by rfl

def raw28527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28527 raw28527Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw28527 raw28527Labels = mixedMoment B raw28527step0 raw28527step0Labels := by
      have ha : raw28527step0 = (fun i j => raw28527 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28527step0 raw28527; decide +kernel
      have hl : raw28527step0Labels = raw28527Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28527 raw28527Labels permutation680 permutation2
    mixedMoment B raw28527step0 raw28527step0Labels = mixedMoment B raw28527step1 raw28527step1Labels := by
      have ha : raw28527step1 = -raw28527step0 := by apply Matrix.ext; change ∀ i j, raw28527step1 i j = -(raw28527step0 i j); unfold raw28527step1 raw28527step0; decide +kernel
      have hl : raw28527step1Labels = raw28527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2016 node2016Labels := by rfl

def raw28528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28528 raw28528Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw28528 raw28528Labels = mixedMoment B raw28528step0 raw28528step0Labels := by
      have hz : ∀ j, raw28528 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28528step0 = (fun i j => raw28528 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28528step0 raw28528; decide +kernel
      have hl : raw28528step0Labels = raw28528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28528 raw28528Labels permutation520 hz
    mixedMoment B raw28528step0 raw28528step0Labels = mixedMoment B raw28528step1 raw28528step1Labels := by
      have ha : raw28528step1 = (fun i j => raw28528step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28528step1 raw28528step0; decide +kernel
      have hl : raw28528step1Labels = raw28528step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28528step0 raw28528step0Labels permutation145 permutation2
    mixedMoment B raw28528step1 raw28528step1Labels = mixedMoment B raw28528step2 raw28528step2Labels := by
      have ha : raw28528step2 = -raw28528step1 := by apply Matrix.ext; change ∀ i j, raw28528step2 i j = -(raw28528step1 i j); unfold raw28528step2 raw28528step1; decide +kernel
      have hl : raw28528step2Labels = raw28528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw28529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28529 raw28529Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw28529 raw28529Labels = mixedMoment B raw28529step0 raw28529step0Labels := by
      have ha : raw28529step0 = (fun i j => raw28529 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28529step0 raw28529; decide +kernel
      have hl : raw28529step0Labels = raw28529Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28529 raw28529Labels permutation682 permutation2
    mixedMoment B raw28529step0 raw28529step0Labels = mixedMoment B raw28529step1 raw28529step1Labels := by
      have ha : raw28529step1 = -raw28529step0 := by apply Matrix.ext; change ∀ i j, raw28529step1 i j = -(raw28529step0 i j); unfold raw28529step1 raw28529step0; decide +kernel
      have hl : raw28529step1Labels = raw28529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw28530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw28530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw28530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28530 raw28530Labels = mixedMoment B node2119 node2119Labels := by
  calc
    mixedMoment B raw28530 raw28530Labels = mixedMoment B raw28530step0 raw28530step0Labels := by
      have hz : ∀ j, raw28530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28530step0 = (fun i j => raw28530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28530step0 raw28530; decide +kernel
      have hl : raw28530step0Labels = raw28530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28530 raw28530Labels permutation434 hz
    mixedMoment B raw28530step0 raw28530step0Labels = mixedMoment B raw28530step1 raw28530step1Labels := by
      have ha : raw28530step1 = (fun i j => raw28530step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28530step1 raw28530step0; decide +kernel
      have hl : raw28530step1Labels = raw28530step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28530step0 raw28530step0Labels permutation151 permutation2
    mixedMoment B raw28530step1 raw28530step1Labels = mixedMoment B raw28530step2 raw28530step2Labels := by
      have ha : raw28530step2 = -raw28530step1 := by apply Matrix.ext; change ∀ i j, raw28530step2 i j = -(raw28530step1 i j); unfold raw28530step2 raw28530step1; decide +kernel
      have hl : raw28530step2Labels = raw28530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2119 node2119Labels := by rfl

def raw28531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw28531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw28531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28531 raw28531Labels = mixedMoment B node2122 node2122Labels := by
  calc
    mixedMoment B raw28531 raw28531Labels = mixedMoment B raw28531step0 raw28531step0Labels := by
      have hz : ∀ j, raw28531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28531step0 = (fun i j => raw28531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28531step0 raw28531; decide +kernel
      have hl : raw28531step0Labels = raw28531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28531 raw28531Labels permutation434 hz
    mixedMoment B raw28531step0 raw28531step0Labels = mixedMoment B raw28531step1 raw28531step1Labels := by
      have ha : raw28531step1 = (fun i j => raw28531step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28531step1 raw28531step0; decide +kernel
      have hl : raw28531step1Labels = raw28531step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28531step0 raw28531step0Labels permutation151 permutation2
    mixedMoment B raw28531step1 raw28531step1Labels = mixedMoment B raw28531step2 raw28531step2Labels := by
      have ha : raw28531step2 = -raw28531step1 := by apply Matrix.ext; change ∀ i j, raw28531step2 i j = -(raw28531step1 i j); unfold raw28531step2 raw28531step1; decide +kernel
      have hl : raw28531step2Labels = raw28531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2122 node2122Labels := by rfl

def raw28532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -3, 2], ![3, 0, -3]]
def raw28532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28532 raw28532Labels = mixedMoment B node2128 node2128Labels := by
  calc
    mixedMoment B raw28532 raw28532Labels = mixedMoment B raw28532step0 raw28532step0Labels := by
      have hz : ∀ j, raw28532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28532step0 = (fun i j => raw28532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28532step0 raw28532; decide +kernel
      have hl : raw28532step0Labels = raw28532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28532 raw28532Labels permutation434 hz
    mixedMoment B raw28532step0 raw28532step0Labels = mixedMoment B raw28532step1 raw28532step1Labels := by
      have ha : raw28532step1 = (fun i j => raw28532step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28532step1 raw28532step0; decide +kernel
      have hl : raw28532step1Labels = raw28532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28532step0 raw28532step0Labels permutation151 permutation2
    mixedMoment B raw28532step1 raw28532step1Labels = mixedMoment B raw28532step2 raw28532step2Labels := by
      have ha : raw28532step2 = -raw28532step1 := by apply Matrix.ext; change ∀ i j, raw28532step2 i j = -(raw28532step1 i j); unfold raw28532step2 raw28532step1; decide +kernel
      have hl : raw28532step2Labels = raw28532step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2128 node2128Labels := by rfl

def raw28533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28533 raw28533Labels = mixedMoment B node2117 node2117Labels := by
  calc
    mixedMoment B raw28533 raw28533Labels = mixedMoment B raw28533step0 raw28533step0Labels := by
      have ha : raw28533step0 = (fun i j => raw28533 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28533step0 raw28533; decide +kernel
      have hl : raw28533step0Labels = raw28533Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28533 raw28533Labels permutation680 permutation2
    mixedMoment B raw28533step0 raw28533step0Labels = mixedMoment B raw28533step1 raw28533step1Labels := by
      have ha : raw28533step1 = -raw28533step0 := by apply Matrix.ext; change ∀ i j, raw28533step1 i j = -(raw28533step0 i j); unfold raw28533step1 raw28533step0; decide +kernel
      have hl : raw28533step1Labels = raw28533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2117 node2117Labels := by rfl

def raw28534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw28534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw28534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28534 raw28534Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw28534 raw28534Labels = mixedMoment B raw28534step0 raw28534step0Labels := by
      have hz : ∀ j, raw28534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28534step0 = (fun i j => raw28534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28534step0 raw28534; decide +kernel
      have hl : raw28534step0Labels = raw28534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28534 raw28534Labels permutation434 hz
    mixedMoment B raw28534step0 raw28534step0Labels = mixedMoment B raw28534step1 raw28534step1Labels := by
      have ha : raw28534step1 = (fun i j => raw28534step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28534step1 raw28534step0; decide +kernel
      have hl : raw28534step1Labels = raw28534step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28534step0 raw28534step0Labels permutation145 permutation2
    mixedMoment B raw28534step1 raw28534step1Labels = mixedMoment B raw28534step2 raw28534step2Labels := by
      have ha : raw28534step2 = -raw28534step1 := by apply Matrix.ext; change ∀ i j, raw28534step2 i j = -(raw28534step1 i j); unfold raw28534step2 raw28534step1; decide +kernel
      have hl : raw28534step2Labels = raw28534step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw28535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw28535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28535 raw28535Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw28535 raw28535Labels = mixedMoment B raw28535step0 raw28535step0Labels := by
      have hz : ∀ j, raw28535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28535step0 = (fun i j => raw28535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28535step0 raw28535; decide +kernel
      have hl : raw28535step0Labels = raw28535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28535 raw28535Labels permutation434 hz
    mixedMoment B raw28535step0 raw28535step0Labels = mixedMoment B raw28535step1 raw28535step1Labels := by
      have ha : raw28535step1 = (fun i j => raw28535step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28535step1 raw28535step0; decide +kernel
      have hl : raw28535step1Labels = raw28535step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28535step0 raw28535step0Labels permutation104 permutation4
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw28536 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![-2, 2], ![3, -3]]
def raw28536Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28536step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![3, -3]]
def raw28536step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28536step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw28536step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28536step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw28536step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28536step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw28536step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28536 raw28536Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw28536 raw28536Labels = mixedMoment B raw28536step0 raw28536step0Labels := by
      have hz : ∀ j, raw28536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28536step0 = (fun i j => raw28536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28536step0 raw28536; decide +kernel
      have hl : raw28536step0Labels = raw28536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28536 raw28536Labels permutation434 hz
    mixedMoment B raw28536step0 raw28536step0Labels = mixedMoment B raw28536step1 raw28536step1Labels := by
      have hz : ∀ j, raw28536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw28536step1 = (fun i j => raw28536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw28536step1 raw28536step0; decide +kernel
      have hl : raw28536step1Labels = raw28536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28536step0 raw28536step0Labels permutation56 hz
    mixedMoment B raw28536step1 raw28536step1Labels = mixedMoment B raw28536step2 raw28536step2Labels := by
      have ha : raw28536step2 = (fun i j => raw28536step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28536step2 raw28536step1; decide +kernel
      have hl : raw28536step2Labels = raw28536step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28536step1 raw28536step1Labels permutation28 permutation0
    mixedMoment B raw28536step2 raw28536step2Labels = mixedMoment B raw28536step3 raw28536step3Labels := by
      have ha : raw28536step3 = -raw28536step2 := by apply Matrix.ext; change ∀ i j, raw28536step3 i j = -(raw28536step2 i j); unfold raw28536step3 raw28536step2; decide +kernel
      have hl : raw28536step3Labels = raw28536step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw28537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28537 raw28537Labels = mixedMoment B node2070 node2070Labels := by
  calc
    mixedMoment B raw28537 raw28537Labels = mixedMoment B raw28537step0 raw28537step0Labels := by
      have ha : raw28537step0 = (fun i j => raw28537 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28537step0 raw28537; decide +kernel
      have hl : raw28537step0Labels = raw28537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28537 raw28537Labels permutation682 permutation2
    mixedMoment B raw28537step0 raw28537step0Labels = mixedMoment B raw28537step1 raw28537step1Labels := by
      have ha : raw28537step1 = -raw28537step0 := by apply Matrix.ext; change ∀ i j, raw28537step1 i j = -(raw28537step0 i j); unfold raw28537step1 raw28537step0; decide +kernel
      have hl : raw28537step1Labels = raw28537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2070 node2070Labels := by rfl

def raw28538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28538 raw28538Labels = mixedMoment B node2072 node2072Labels := by
  calc
    mixedMoment B raw28538 raw28538Labels = mixedMoment B raw28538step0 raw28538step0Labels := by
      have ha : raw28538step0 = (fun i j => raw28538 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28538step0 raw28538; decide +kernel
      have hl : raw28538step0Labels = raw28538Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28538 raw28538Labels permutation682 permutation2
    mixedMoment B raw28538step0 raw28538step0Labels = mixedMoment B raw28538step1 raw28538step1Labels := by
      have ha : raw28538step1 = -raw28538step0 := by apply Matrix.ext; change ∀ i j, raw28538step1 i j = -(raw28538step0 i j); unfold raw28538step1 raw28538step0; decide +kernel
      have hl : raw28538step1Labels = raw28538step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2072 node2072Labels := by rfl

def raw28539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28539 raw28539Labels = mixedMoment B node2085 node2085Labels := by
  calc
    mixedMoment B raw28539 raw28539Labels = mixedMoment B raw28539step0 raw28539step0Labels := by
      have ha : raw28539step0 = (fun i j => raw28539 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28539step0 raw28539; decide +kernel
      have hl : raw28539step0Labels = raw28539Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28539 raw28539Labels permutation688 permutation2
    mixedMoment B raw28539step0 raw28539step0Labels = mixedMoment B raw28539step1 raw28539step1Labels := by
      have ha : raw28539step1 = -raw28539step0 := by apply Matrix.ext; change ∀ i j, raw28539step1 i j = -(raw28539step0 i j); unfold raw28539step1 raw28539step0; decide +kernel
      have hl : raw28539step1Labels = raw28539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2085 node2085Labels := by rfl

def raw28540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28540 raw28540Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw28540 raw28540Labels = mixedMoment B raw28540step0 raw28540step0Labels := by
      have ha : raw28540step0 = (fun i j => raw28540 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28540step0 raw28540; decide +kernel
      have hl : raw28540step0Labels = raw28540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28540 raw28540Labels permutation680 permutation2
    mixedMoment B raw28540step0 raw28540step0Labels = mixedMoment B raw28540step1 raw28540step1Labels := by
      have ha : raw28540step1 = -raw28540step0 := by apply Matrix.ext; change ∀ i j, raw28540step1 i j = -(raw28540step0 i j); unfold raw28540step1 raw28540step0; decide +kernel
      have hl : raw28540step1Labels = raw28540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2075 node2075Labels := by rfl

def raw28541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28541 raw28541Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw28541 raw28541Labels = mixedMoment B raw28541step0 raw28541step0Labels := by
      have ha : raw28541step0 = (fun i j => raw28541 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28541step0 raw28541; decide +kernel
      have hl : raw28541step0Labels = raw28541Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28541 raw28541Labels permutation640 permutation2
    mixedMoment B raw28541step0 raw28541step0Labels = mixedMoment B raw28541step1 raw28541step1Labels := by
      have ha : raw28541step1 = -raw28541step0 := by apply Matrix.ext; change ∀ i j, raw28541step1 i j = -(raw28541step0 i j); unfold raw28541step1 raw28541step0; decide +kernel
      have hl : raw28541step1Labels = raw28541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw28542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw28542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28542 raw28542Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw28542 raw28542Labels = mixedMoment B raw28542step0 raw28542step0Labels := by
      have ha : raw28542step0 = (fun i j => raw28542 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28542step0 raw28542; decide +kernel
      have hl : raw28542step0Labels = raw28542Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28542 raw28542Labels permutation682 permutation2
    mixedMoment B raw28542step0 raw28542step0Labels = mixedMoment B raw28542step1 raw28542step1Labels := by
      have ha : raw28542step1 = -raw28542step0 := by apply Matrix.ext; change ∀ i j, raw28542step1 i j = -(raw28542step0 i j); unfold raw28542step1 raw28542step0; decide +kernel
      have hl : raw28542step1Labels = raw28542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw28543 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw28543Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28543step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw28543step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28543step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw28543step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28543step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw28543step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28543 raw28543Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw28543 raw28543Labels = mixedMoment B raw28543step0 raw28543step0Labels := by
      have hz : ∀ j, raw28543 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw28543step0 = (fun i j => raw28543 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw28543step0 raw28543; decide +kernel
      have hl : raw28543step0Labels = raw28543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28543 raw28543Labels permutation265 hz
    mixedMoment B raw28543step0 raw28543step0Labels = mixedMoment B raw28543step1 raw28543step1Labels := by
      have ha : raw28543step1 = (fun i j => raw28543step0 (permutation137 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28543step1 raw28543step0; decide +kernel
      have hl : raw28543step1Labels = raw28543step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28543step0 raw28543step0Labels permutation137 permutation0
    mixedMoment B raw28543step1 raw28543step1Labels = mixedMoment B raw28543step2 raw28543step2Labels := by
      have ha : raw28543step2 = -raw28543step1 := by apply Matrix.ext; change ∀ i j, raw28543step2 i j = -(raw28543step1 i j); unfold raw28543step2 raw28543step1; decide +kernel
      have hl : raw28543step2Labels = raw28543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
