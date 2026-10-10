import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12416step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12416step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12416step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12416 raw12416Labels = mixedMoment B node3507 node3507Labels := by
  calc
    mixedMoment B raw12416 raw12416Labels = mixedMoment B raw12416step0 raw12416step0Labels := by
      have hz : ∀ j, raw12416 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12416step0 = (fun i j => raw12416 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12416step0 raw12416; decide +kernel
      have hl : raw12416step0Labels = raw12416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12416 raw12416Labels permutation265 hz
    mixedMoment B raw12416step0 raw12416step0Labels = mixedMoment B raw12416step1 raw12416step1Labels := by
      have ha : raw12416step1 = (fun i j => raw12416step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12416step1 raw12416step0; decide +kernel
      have hl : raw12416step1Labels = raw12416step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12416step0 raw12416step0Labels permutation46 permutation5
    mixedMoment B raw12416step1 raw12416step1Labels = mixedMoment B raw12416step2 raw12416step2Labels := by
      have ha : raw12416step2 = -raw12416step1 := by apply Matrix.ext; change ∀ i j, raw12416step2 i j = -(raw12416step1 i j); unfold raw12416step2 raw12416step1; decide +kernel
      have hl : raw12416step2Labels = raw12416step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12416step2 raw12416step2Labels = mixedMoment B raw12416step3 raw12416step3Labels := by
      have ha : raw12416step3 = raw12416step2 := by apply Matrix.ext; unfold raw12416step3 raw12416step2; decide +kernel
      have hl : raw12416step2Labels = labelEmbedding1 ∘ raw12416step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12416step2 raw12416step2Labels raw12416step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3507 node3507Labels := by rfl

def raw12417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12417step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12417step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12417step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12417step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12417 raw12417Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw12417 raw12417Labels = mixedMoment B raw12417step0 raw12417step0Labels := by
      have hz : ∀ j, raw12417 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12417step0 = (fun i j => raw12417 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12417step0 raw12417; decide +kernel
      have hl : raw12417step0Labels = raw12417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12417 raw12417Labels permutation265 hz
    mixedMoment B raw12417step0 raw12417step0Labels = mixedMoment B raw12417step1 raw12417step1Labels := by
      have ha : raw12417step1 = (fun i j => raw12417step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12417step1 raw12417step0; decide +kernel
      have hl : raw12417step1Labels = raw12417step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12417step0 raw12417step0Labels permutation41 permutation5
    mixedMoment B raw12417step1 raw12417step1Labels = mixedMoment B raw12417step2 raw12417step2Labels := by
      have ha : raw12417step2 = -raw12417step1 := by apply Matrix.ext; change ∀ i j, raw12417step2 i j = -(raw12417step1 i j); unfold raw12417step2 raw12417step1; decide +kernel
      have hl : raw12417step2Labels = raw12417step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12417step2 raw12417step2Labels = mixedMoment B raw12417step3 raw12417step3Labels := by
      have ha : raw12417step3 = raw12417step2 := by apply Matrix.ext; unfold raw12417step3 raw12417step2; decide +kernel
      have hl : raw12417step2Labels = labelEmbedding1 ∘ raw12417step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12417step2 raw12417step2Labels raw12417step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw12418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12418step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12418step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12418step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12418step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12418 raw12418Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw12418 raw12418Labels = mixedMoment B raw12418step0 raw12418step0Labels := by
      have hz : ∀ j, raw12418 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12418step0 = (fun i j => raw12418 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12418step0 raw12418; decide +kernel
      have hl : raw12418step0Labels = raw12418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12418 raw12418Labels permutation265 hz
    mixedMoment B raw12418step0 raw12418step0Labels = mixedMoment B raw12418step1 raw12418step1Labels := by
      have ha : raw12418step1 = (fun i j => raw12418step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12418step1 raw12418step0; decide +kernel
      have hl : raw12418step1Labels = raw12418step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12418step0 raw12418step0Labels permutation46 permutation5
    mixedMoment B raw12418step1 raw12418step1Labels = mixedMoment B raw12418step2 raw12418step2Labels := by
      have ha : raw12418step2 = -raw12418step1 := by apply Matrix.ext; change ∀ i j, raw12418step2 i j = -(raw12418step1 i j); unfold raw12418step2 raw12418step1; decide +kernel
      have hl : raw12418step2Labels = raw12418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12418step2 raw12418step2Labels = mixedMoment B raw12418step3 raw12418step3Labels := by
      have ha : raw12418step3 = raw12418step2 := by apply Matrix.ext; unfold raw12418step3 raw12418step2; decide +kernel
      have hl : raw12418step2Labels = labelEmbedding1 ∘ raw12418step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12418step2 raw12418step2Labels raw12418step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw12419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12419Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12419step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12419step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12419step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12419 raw12419Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw12419 raw12419Labels = mixedMoment B raw12419step0 raw12419step0Labels := by
      have ha : raw12419step0 = (fun i j => raw12419 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12419step0 raw12419; decide +kernel
      have hl : raw12419step0Labels = raw12419Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12419 raw12419Labels permutation166 permutation5
    mixedMoment B raw12419step0 raw12419step0Labels = mixedMoment B raw12419step1 raw12419step1Labels := by
      have ha : raw12419step1 = -raw12419step0 := by apply Matrix.ext; change ∀ i j, raw12419step1 i j = -(raw12419step0 i j); unfold raw12419step1 raw12419step0; decide +kernel
      have hl : raw12419step1Labels = raw12419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12419step1 raw12419step1Labels = mixedMoment B raw12419step2 raw12419step2Labels := by
      have ha : raw12419step2 = raw12419step1 := by apply Matrix.ext; unfold raw12419step2 raw12419step1; decide +kernel
      have hl : raw12419step1Labels = labelEmbedding1 ∘ raw12419step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12419step1 raw12419step1Labels raw12419step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw12420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12420step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw12420step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw12420step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12420step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw12420step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12420 raw12420Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw12420 raw12420Labels = mixedMoment B raw12420step0 raw12420step0Labels := by
      have hz : ∀ j, raw12420 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12420step0 = (fun i j => raw12420 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12420step0 raw12420; decide +kernel
      have hl : raw12420step0Labels = raw12420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12420 raw12420Labels permutation265 hz
    mixedMoment B raw12420step0 raw12420step0Labels = mixedMoment B raw12420step1 raw12420step1Labels := by
      have ha : raw12420step1 = (fun i j => raw12420step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12420step1 raw12420step0; decide +kernel
      have hl : raw12420step1Labels = raw12420step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12420step0 raw12420step0Labels permutation34 permutation5
    mixedMoment B raw12420step1 raw12420step1Labels = mixedMoment B raw12420step2 raw12420step2Labels := by
      have ha : raw12420step2 = -raw12420step1 := by apply Matrix.ext; change ∀ i j, raw12420step2 i j = -(raw12420step1 i j); unfold raw12420step2 raw12420step1; decide +kernel
      have hl : raw12420step2Labels = raw12420step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12420step2 raw12420step2Labels = mixedMoment B raw12420step3 raw12420step3Labels := by
      have ha : raw12420step3 = raw12420step2 := by apply Matrix.ext; unfold raw12420step3 raw12420step2; decide +kernel
      have hl : raw12420step2Labels = labelEmbedding1 ∘ raw12420step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12420step2 raw12420step2Labels raw12420step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw12421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12421step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12421step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12421step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12421step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12421 raw12421Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw12421 raw12421Labels = mixedMoment B raw12421step0 raw12421step0Labels := by
      have hz : ∀ j, raw12421 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12421step0 = (fun i j => raw12421 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12421step0 raw12421; decide +kernel
      have hl : raw12421step0Labels = raw12421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12421 raw12421Labels permutation265 hz
    mixedMoment B raw12421step0 raw12421step0Labels = mixedMoment B raw12421step1 raw12421step1Labels := by
      have ha : raw12421step1 = (fun i j => raw12421step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12421step1 raw12421step0; decide +kernel
      have hl : raw12421step1Labels = raw12421step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12421step0 raw12421step0Labels permutation46 permutation5
    mixedMoment B raw12421step1 raw12421step1Labels = mixedMoment B raw12421step2 raw12421step2Labels := by
      have ha : raw12421step2 = -raw12421step1 := by apply Matrix.ext; change ∀ i j, raw12421step2 i j = -(raw12421step1 i j); unfold raw12421step2 raw12421step1; decide +kernel
      have hl : raw12421step2Labels = raw12421step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12421step2 raw12421step2Labels = mixedMoment B raw12421step3 raw12421step3Labels := by
      have ha : raw12421step3 = raw12421step2 := by apply Matrix.ext; unfold raw12421step3 raw12421step2; decide +kernel
      have hl : raw12421step2Labels = labelEmbedding1 ∘ raw12421step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12421step2 raw12421step2Labels raw12421step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw12422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12422step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw12422step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12422step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12422step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12422step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12422 raw12422Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw12422 raw12422Labels = mixedMoment B raw12422step0 raw12422step0Labels := by
      have hz : ∀ j, raw12422 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12422step0 = (fun i j => raw12422 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12422step0 raw12422; decide +kernel
      have hl : raw12422step0Labels = raw12422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12422 raw12422Labels permutation265 hz
    mixedMoment B raw12422step0 raw12422step0Labels = mixedMoment B raw12422step1 raw12422step1Labels := by
      have ha : raw12422step1 = (fun i j => raw12422step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12422step1 raw12422step0; decide +kernel
      have hl : raw12422step1Labels = raw12422step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12422step0 raw12422step0Labels permutation46 permutation5
    mixedMoment B raw12422step1 raw12422step1Labels = mixedMoment B raw12422step2 raw12422step2Labels := by
      have ha : raw12422step2 = -raw12422step1 := by apply Matrix.ext; change ∀ i j, raw12422step2 i j = -(raw12422step1 i j); unfold raw12422step2 raw12422step1; decide +kernel
      have hl : raw12422step2Labels = raw12422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12422step2 raw12422step2Labels = mixedMoment B raw12422step3 raw12422step3Labels := by
      have ha : raw12422step3 = raw12422step2 := by apply Matrix.ext; unfold raw12422step3 raw12422step2; decide +kernel
      have hl : raw12422step2Labels = labelEmbedding1 ∘ raw12422step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12422step2 raw12422step2Labels raw12422step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw12423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12423step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw12423step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12423step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12423step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12423step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12423 raw12423Labels = mixedMoment B node1646 node1646Labels := by
  calc
    mixedMoment B raw12423 raw12423Labels = mixedMoment B raw12423step0 raw12423step0Labels := by
      have hz : ∀ j, raw12423 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12423step0 = (fun i j => raw12423 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12423step0 raw12423; decide +kernel
      have hl : raw12423step0Labels = raw12423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12423 raw12423Labels permutation265 hz
    mixedMoment B raw12423step0 raw12423step0Labels = mixedMoment B raw12423step1 raw12423step1Labels := by
      have ha : raw12423step1 = (fun i j => raw12423step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12423step1 raw12423step0; decide +kernel
      have hl : raw12423step1Labels = raw12423step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12423step0 raw12423step0Labels permutation38 permutation5
    mixedMoment B raw12423step1 raw12423step1Labels = mixedMoment B raw12423step2 raw12423step2Labels := by
      have ha : raw12423step2 = -raw12423step1 := by apply Matrix.ext; change ∀ i j, raw12423step2 i j = -(raw12423step1 i j); unfold raw12423step2 raw12423step1; decide +kernel
      have hl : raw12423step2Labels = raw12423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12423step2 raw12423step2Labels = mixedMoment B raw12423step3 raw12423step3Labels := by
      have ha : raw12423step3 = raw12423step2 := by apply Matrix.ext; unfold raw12423step3 raw12423step2; decide +kernel
      have hl : raw12423step2Labels = labelEmbedding1 ∘ raw12423step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12423step2 raw12423step2Labels raw12423step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1646 node1646Labels := by rfl

def raw12424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw12424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12424step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12424step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12424 raw12424Labels = mixedMoment B node3445 node3445Labels := by
  calc
    mixedMoment B raw12424 raw12424Labels = mixedMoment B raw12424step0 raw12424step0Labels := by
      have ha : raw12424step0 = (fun i j => raw12424 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12424step0 raw12424; decide +kernel
      have hl : raw12424step0Labels = raw12424Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12424 raw12424Labels permutation158 permutation5
    mixedMoment B raw12424step0 raw12424step0Labels = mixedMoment B raw12424step1 raw12424step1Labels := by
      have ha : raw12424step1 = -raw12424step0 := by apply Matrix.ext; change ∀ i j, raw12424step1 i j = -(raw12424step0 i j); unfold raw12424step1 raw12424step0; decide +kernel
      have hl : raw12424step1Labels = raw12424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12424step1 raw12424step1Labels = mixedMoment B raw12424step2 raw12424step2Labels := by
      have ha : raw12424step2 = raw12424step1 := by apply Matrix.ext; unfold raw12424step2 raw12424step1; decide +kernel
      have hl : raw12424step1Labels = labelEmbedding1 ∘ raw12424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12424step1 raw12424step1Labels raw12424step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3445 node3445Labels := by rfl

def raw12425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw12425step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12425step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12425 raw12425Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw12425 raw12425Labels = mixedMoment B raw12425step0 raw12425step0Labels := by
      have hz : ∀ j, raw12425 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12425step0 = (fun i j => raw12425 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12425step0 raw12425; decide +kernel
      have hl : raw12425step0Labels = raw12425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12425 raw12425Labels permutation265 hz
    mixedMoment B raw12425step0 raw12425step0Labels = mixedMoment B raw12425step1 raw12425step1Labels := by
      have ha : raw12425step1 = (fun i j => raw12425step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12425step1 raw12425step0; decide +kernel
      have hl : raw12425step1Labels = raw12425step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12425step0 raw12425step0Labels permutation38 permutation5
    mixedMoment B raw12425step1 raw12425step1Labels = mixedMoment B raw12425step2 raw12425step2Labels := by
      have ha : raw12425step2 = -raw12425step1 := by apply Matrix.ext; change ∀ i j, raw12425step2 i j = -(raw12425step1 i j); unfold raw12425step2 raw12425step1; decide +kernel
      have hl : raw12425step2Labels = raw12425step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12425step2 raw12425step2Labels = mixedMoment B raw12425step3 raw12425step3Labels := by
      have ha : raw12425step3 = raw12425step2 := by apply Matrix.ext; unfold raw12425step3 raw12425step2; decide +kernel
      have hl : raw12425step2Labels = labelEmbedding1 ∘ raw12425step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12425step2 raw12425step2Labels raw12425step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw12426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw12426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12426step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12426step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12426step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12426 raw12426Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw12426 raw12426Labels = mixedMoment B raw12426step0 raw12426step0Labels := by
      have hz : ∀ j, raw12426 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12426step0 = (fun i j => raw12426 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12426step0 raw12426; decide +kernel
      have hl : raw12426step0Labels = raw12426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12426 raw12426Labels permutation265 hz
    mixedMoment B raw12426step0 raw12426step0Labels = mixedMoment B raw12426step1 raw12426step1Labels := by
      have ha : raw12426step1 = (fun i j => raw12426step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12426step1 raw12426step0; decide +kernel
      have hl : raw12426step1Labels = raw12426step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12426step0 raw12426step0Labels permutation38 permutation5
    mixedMoment B raw12426step1 raw12426step1Labels = mixedMoment B raw12426step2 raw12426step2Labels := by
      have ha : raw12426step2 = -raw12426step1 := by apply Matrix.ext; change ∀ i j, raw12426step2 i j = -(raw12426step1 i j); unfold raw12426step2 raw12426step1; decide +kernel
      have hl : raw12426step2Labels = raw12426step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12426step2 raw12426step2Labels = mixedMoment B raw12426step3 raw12426step3Labels := by
      have ha : raw12426step3 = raw12426step2 := by apply Matrix.ext; unfold raw12426step3 raw12426step2; decide +kernel
      have hl : raw12426step2Labels = labelEmbedding1 ∘ raw12426step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12426step2 raw12426step2Labels raw12426step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3392 node3392Labels := by rfl

def raw12427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12427step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw12427step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12427step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12427step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12427step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12427 raw12427Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw12427 raw12427Labels = mixedMoment B raw12427step0 raw12427step0Labels := by
      have hz : ∀ j, raw12427 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12427step0 = (fun i j => raw12427 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12427step0 raw12427; decide +kernel
      have hl : raw12427step0Labels = raw12427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12427 raw12427Labels permutation265 hz
    mixedMoment B raw12427step0 raw12427step0Labels = mixedMoment B raw12427step1 raw12427step1Labels := by
      have ha : raw12427step1 = (fun i j => raw12427step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12427step1 raw12427step0; decide +kernel
      have hl : raw12427step1Labels = raw12427step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12427step0 raw12427step0Labels permutation39 permutation5
    mixedMoment B raw12427step1 raw12427step1Labels = mixedMoment B raw12427step2 raw12427step2Labels := by
      have ha : raw12427step2 = -raw12427step1 := by apply Matrix.ext; change ∀ i j, raw12427step2 i j = -(raw12427step1 i j); unfold raw12427step2 raw12427step1; decide +kernel
      have hl : raw12427step2Labels = raw12427step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12427step2 raw12427step2Labels = mixedMoment B raw12427step3 raw12427step3Labels := by
      have ha : raw12427step3 = raw12427step2 := by apply Matrix.ext; unfold raw12427step3 raw12427step2; decide +kernel
      have hl : raw12427step2Labels = labelEmbedding1 ∘ raw12427step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12427step2 raw12427step2Labels raw12427step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw12428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw12428step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw12428step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12428step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw12428step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12428 raw12428Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw12428 raw12428Labels = mixedMoment B raw12428step0 raw12428step0Labels := by
      have hz : ∀ j, raw12428 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12428step0 = (fun i j => raw12428 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12428step0 raw12428; decide +kernel
      have hl : raw12428step0Labels = raw12428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12428 raw12428Labels permutation265 hz
    mixedMoment B raw12428step0 raw12428step0Labels = mixedMoment B raw12428step1 raw12428step1Labels := by
      have ha : raw12428step1 = (fun i j => raw12428step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12428step1 raw12428step0; decide +kernel
      have hl : raw12428step1Labels = raw12428step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12428step0 raw12428step0Labels permutation40 permutation5
    mixedMoment B raw12428step1 raw12428step1Labels = mixedMoment B raw12428step2 raw12428step2Labels := by
      have ha : raw12428step2 = -raw12428step1 := by apply Matrix.ext; change ∀ i j, raw12428step2 i j = -(raw12428step1 i j); unfold raw12428step2 raw12428step1; decide +kernel
      have hl : raw12428step2Labels = raw12428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12428step2 raw12428step2Labels = mixedMoment B raw12428step3 raw12428step3Labels := by
      have ha : raw12428step3 = raw12428step2 := by apply Matrix.ext; unfold raw12428step3 raw12428step2; decide +kernel
      have hl : raw12428step2Labels = labelEmbedding1 ∘ raw12428step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12428step2 raw12428step2Labels raw12428step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1637 node1637Labels := by rfl

def raw12429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12429step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12429 raw12429Labels = mixedMoment B node2550 node2550Labels := by
  calc
    mixedMoment B raw12429 raw12429Labels = mixedMoment B raw12429step0 raw12429step0Labels := by
      have ha : raw12429step0 = (fun i j => raw12429 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12429step0 raw12429; decide +kernel
      have hl : raw12429step0Labels = raw12429Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12429 raw12429Labels permutation646 permutation5
    mixedMoment B raw12429step0 raw12429step0Labels = mixedMoment B raw12429step1 raw12429step1Labels := by
      have ha : raw12429step1 = raw12429step0 := by apply Matrix.ext; unfold raw12429step1 raw12429step0; decide +kernel
      have hl : raw12429step0Labels = labelEmbedding1 ∘ raw12429step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12429step0 raw12429step0Labels raw12429step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2550 node2550Labels := by rfl

def raw12430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw12430step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw12430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12430 raw12430Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw12430 raw12430Labels = mixedMoment B raw12430step0 raw12430step0Labels := by
      have hz : ∀ j, raw12430 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12430step0 = (fun i j => raw12430 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12430step0 raw12430; decide +kernel
      have hl : raw12430step0Labels = raw12430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12430 raw12430Labels permutation265 hz
    mixedMoment B raw12430step0 raw12430step0Labels = mixedMoment B raw12430step1 raw12430step1Labels := by
      have ha : raw12430step1 = (fun i j => raw12430step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12430step1 raw12430step0; decide +kernel
      have hl : raw12430step1Labels = raw12430step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12430step0 raw12430step0Labels permutation149 permutation5
    mixedMoment B raw12430step1 raw12430step1Labels = mixedMoment B raw12430step2 raw12430step2Labels := by
      have ha : raw12430step2 = raw12430step1 := by apply Matrix.ext; unfold raw12430step2 raw12430step1; decide +kernel
      have hl : raw12430step1Labels = labelEmbedding1 ∘ raw12430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12430step1 raw12430step1Labels raw12430step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw12431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12431 raw12431Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw12431 raw12431Labels = mixedMoment B raw12431step0 raw12431step0Labels := by
      have hz : ∀ j, raw12431 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12431step0 = (fun i j => raw12431 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12431step0 raw12431; decide +kernel
      have hl : raw12431step0Labels = raw12431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12431 raw12431Labels permutation265 hz
    mixedMoment B raw12431step0 raw12431step0Labels = mixedMoment B raw12431step1 raw12431step1Labels := by
      have ha : raw12431step1 = (fun i j => raw12431step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12431step1 raw12431step0; decide +kernel
      have hl : raw12431step1Labels = raw12431step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12431step0 raw12431step0Labels permutation139 permutation5
    mixedMoment B raw12431step1 raw12431step1Labels = mixedMoment B raw12431step2 raw12431step2Labels := by
      have ha : raw12431step2 = raw12431step1 := by apply Matrix.ext; unfold raw12431step2 raw12431step1; decide +kernel
      have hl : raw12431step1Labels = labelEmbedding1 ∘ raw12431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12431step1 raw12431step1Labels raw12431step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2560 node2560Labels := by rfl

def raw12432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12432step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12432 raw12432Labels = mixedMoment B node2588 node2588Labels := by
  calc
    mixedMoment B raw12432 raw12432Labels = mixedMoment B raw12432step0 raw12432step0Labels := by
      have hz : ∀ j, raw12432 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12432step0 = (fun i j => raw12432 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12432step0 raw12432; decide +kernel
      have hl : raw12432step0Labels = raw12432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12432 raw12432Labels permutation265 hz
    mixedMoment B raw12432step0 raw12432step0Labels = mixedMoment B raw12432step1 raw12432step1Labels := by
      have ha : raw12432step1 = (fun i j => raw12432step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12432step1 raw12432step0; decide +kernel
      have hl : raw12432step1Labels = raw12432step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12432step0 raw12432step0Labels permutation137 permutation5
    mixedMoment B raw12432step1 raw12432step1Labels = mixedMoment B raw12432step2 raw12432step2Labels := by
      have ha : raw12432step2 = raw12432step1 := by apply Matrix.ext; unfold raw12432step2 raw12432step1; decide +kernel
      have hl : raw12432step1Labels = labelEmbedding1 ∘ raw12432step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12432step1 raw12432step1Labels raw12432step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2588 node2588Labels := by rfl

def raw12433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12433 raw12433Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw12433 raw12433Labels = mixedMoment B raw12433step0 raw12433step0Labels := by
      have hz : ∀ j, raw12433 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12433step0 = (fun i j => raw12433 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12433step0 raw12433; decide +kernel
      have hl : raw12433step0Labels = raw12433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12433 raw12433Labels permutation265 hz
    mixedMoment B raw12433step0 raw12433step0Labels = mixedMoment B raw12433step1 raw12433step1Labels := by
      have ha : raw12433step1 = (fun i j => raw12433step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12433step1 raw12433step0; decide +kernel
      have hl : raw12433step1Labels = raw12433step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12433step0 raw12433step0Labels permutation37 permutation2
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw12434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12434 raw12434Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw12434 raw12434Labels = mixedMoment B raw12434step0 raw12434step0Labels := by
      have ha : raw12434step0 = (fun i j => raw12434 (permutation641 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12434step0 raw12434; decide +kernel
      have hl : raw12434step0Labels = raw12434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12434 raw12434Labels permutation641 permutation4
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw12435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12435 raw12435Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw12435 raw12435Labels = mixedMoment B raw12435step0 raw12435step0Labels := by
      have hz : ∀ j, raw12435 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12435step0 = (fun i j => raw12435 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12435step0 raw12435; decide +kernel
      have hl : raw12435step0Labels = raw12435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12435 raw12435Labels permutation265 hz
    mixedMoment B raw12435step0 raw12435step0Labels = mixedMoment B raw12435step1 raw12435step1Labels := by
      have ha : raw12435step1 = (fun i j => raw12435step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12435step1 raw12435step0; decide +kernel
      have hl : raw12435step1Labels = raw12435step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12435step0 raw12435step0Labels permutation37 permutation2
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw12436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12436 raw12436Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw12436 raw12436Labels = mixedMoment B raw12436step0 raw12436step0Labels := by
      have hz : ∀ j, raw12436 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12436step0 = (fun i j => raw12436 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12436step0 raw12436; decide +kernel
      have hl : raw12436step0Labels = raw12436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12436 raw12436Labels permutation265 hz
    mixedMoment B raw12436step0 raw12436step0Labels = mixedMoment B raw12436step1 raw12436step1Labels := by
      have ha : raw12436step1 = (fun i j => raw12436step0 (permutation82 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12436step1 raw12436step0; decide +kernel
      have hl : raw12436step1Labels = raw12436step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12436step0 raw12436step0Labels permutation82 permutation4
    mixedMoment B raw12436step1 raw12436step1Labels = mixedMoment B raw12436step2 raw12436step2Labels := by
      have ha : raw12436step2 = -raw12436step1 := by apply Matrix.ext; change ∀ i j, raw12436step2 i j = -(raw12436step1 i j); unfold raw12436step2 raw12436step1; decide +kernel
      have hl : raw12436step2Labels = raw12436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw12437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12437 raw12437Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw12437 raw12437Labels = mixedMoment B raw12437step0 raw12437step0Labels := by
      have hz : ∀ j, raw12437 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12437step0 = (fun i j => raw12437 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12437step0 raw12437; decide +kernel
      have hl : raw12437step0Labels = raw12437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12437 raw12437Labels permutation265 hz
    mixedMoment B raw12437step0 raw12437step0Labels = mixedMoment B raw12437step1 raw12437step1Labels := by
      have ha : raw12437step1 = (fun i j => raw12437step0 (permutation135 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12437step1 raw12437step0; decide +kernel
      have hl : raw12437step1Labels = raw12437step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12437step0 raw12437step0Labels permutation135 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw12438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12438 raw12438Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw12438 raw12438Labels = mixedMoment B raw12438step0 raw12438step0Labels := by
      have hz : ∀ j, raw12438 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12438step0 = (fun i j => raw12438 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12438step0 raw12438; decide +kernel
      have hl : raw12438step0Labels = raw12438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12438 raw12438Labels permutation265 hz
    mixedMoment B raw12438step0 raw12438step0Labels = mixedMoment B raw12438step1 raw12438step1Labels := by
      have ha : raw12438step1 = (fun i j => raw12438step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12438step1 raw12438step0; decide +kernel
      have hl : raw12438step1Labels = raw12438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12438step0 raw12438step0Labels permutation37 permutation2
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw12439 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]
def raw12439Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12439step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![-1, 1]]
def raw12439step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12439step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw12439step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12439step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw12439step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical12439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12439 raw12439Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw12439 raw12439Labels = mixedMoment B raw12439step0 raw12439step0Labels := by
      have hz : ∀ j, raw12439 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12439step0 = (fun i j => raw12439 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12439step0 raw12439; decide +kernel
      have hl : raw12439step0Labels = raw12439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12439 raw12439Labels permutation265 hz
    mixedMoment B raw12439step0 raw12439step0Labels = mixedMoment B raw12439step1 raw12439step1Labels := by
      have ha : raw12439step1 = (fun i j => raw12439step0 (permutation92 i) (permutation0 j)) := by apply Matrix.ext; unfold raw12439step1 raw12439step0; decide +kernel
      have hl : raw12439step1Labels = raw12439step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12439step0 raw12439step0Labels permutation92 permutation0
    mixedMoment B raw12439step1 raw12439step1Labels = mixedMoment B raw12439step2 raw12439step2Labels := by
      have ha : raw12439step2 = -raw12439step1 := by apply Matrix.ext; change ∀ i j, raw12439step2 i j = -(raw12439step1 i j); unfold raw12439step2 raw12439step1; decide +kernel
      have hl : raw12439step2Labels = raw12439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw12440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12440 raw12440Labels = mixedMoment B node1403 node1403Labels := by
  calc
    mixedMoment B raw12440 raw12440Labels = mixedMoment B raw12440step0 raw12440step0Labels := by
      have ha : raw12440step0 = (fun i j => raw12440 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12440step0 raw12440; decide +kernel
      have hl : raw12440step0Labels = raw12440Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12440 raw12440Labels permutation195 permutation2
    _ = mixedMoment B node1403 node1403Labels := by rfl

def raw12441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12441 raw12441Labels = mixedMoment B node1439 node1439Labels := by
  calc
    mixedMoment B raw12441 raw12441Labels = mixedMoment B raw12441step0 raw12441step0Labels := by
      have hz : ∀ j, raw12441 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12441step0 = (fun i j => raw12441 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12441step0 raw12441; decide +kernel
      have hl : raw12441step0Labels = raw12441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12441 raw12441Labels permutation265 hz
    mixedMoment B raw12441step0 raw12441step0Labels = mixedMoment B raw12441step1 raw12441step1Labels := by
      have ha : raw12441step1 = (fun i j => raw12441step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12441step1 raw12441step0; decide +kernel
      have hl : raw12441step1Labels = raw12441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12441step0 raw12441step0Labels permutation37 permutation2
    _ = mixedMoment B node1439 node1439Labels := by rfl

def raw12442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12442 raw12442Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw12442 raw12442Labels = mixedMoment B raw12442step0 raw12442step0Labels := by
      have hz : ∀ j, raw12442 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12442step0 = (fun i j => raw12442 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12442step0 raw12442; decide +kernel
      have hl : raw12442step0Labels = raw12442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12442 raw12442Labels permutation265 hz
    mixedMoment B raw12442step0 raw12442step0Labels = mixedMoment B raw12442step1 raw12442step1Labels := by
      have ha : raw12442step1 = (fun i j => raw12442step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12442step1 raw12442step0; decide +kernel
      have hl : raw12442step1Labels = raw12442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12442step0 raw12442step0Labels permutation37 permutation2
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw12443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12443 raw12443Labels = mixedMoment B node1407 node1407Labels := by
  calc
    mixedMoment B raw12443 raw12443Labels = mixedMoment B raw12443step0 raw12443step0Labels := by
      have hz : ∀ j, raw12443 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12443step0 = (fun i j => raw12443 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12443step0 raw12443; decide +kernel
      have hl : raw12443step0Labels = raw12443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12443 raw12443Labels permutation265 hz
    mixedMoment B raw12443step0 raw12443step0Labels = mixedMoment B raw12443step1 raw12443step1Labels := by
      have ha : raw12443step1 = (fun i j => raw12443step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12443step1 raw12443step0; decide +kernel
      have hl : raw12443step1Labels = raw12443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12443step0 raw12443step0Labels permutation36 permutation2
    _ = mixedMoment B node1407 node1407Labels := by rfl

def raw12444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12444 raw12444Labels = mixedMoment B node1415 node1415Labels := by
  calc
    mixedMoment B raw12444 raw12444Labels = mixedMoment B raw12444step0 raw12444step0Labels := by
      have hz : ∀ j, raw12444 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12444step0 = (fun i j => raw12444 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12444step0 raw12444; decide +kernel
      have hl : raw12444step0Labels = raw12444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12444 raw12444Labels permutation265 hz
    mixedMoment B raw12444step0 raw12444step0Labels = mixedMoment B raw12444step1 raw12444step1Labels := by
      have ha : raw12444step1 = (fun i j => raw12444step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12444step1 raw12444step0; decide +kernel
      have hl : raw12444step1Labels = raw12444step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12444step0 raw12444step0Labels permutation34 permutation2
    _ = mixedMoment B node1415 node1415Labels := by rfl

def raw12445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12445 raw12445Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw12445 raw12445Labels = mixedMoment B raw12445step0 raw12445step0Labels := by
      have ha : raw12445step0 = (fun i j => raw12445 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12445step0 raw12445; decide +kernel
      have hl : raw12445step0Labels = raw12445Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12445 raw12445Labels permutation195 permutation2
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw12446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12446 raw12446Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw12446 raw12446Labels = mixedMoment B raw12446step0 raw12446step0Labels := by
      have ha : raw12446step0 = (fun i j => raw12446 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12446step0 raw12446; decide +kernel
      have hl : raw12446step0Labels = raw12446Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12446 raw12446Labels permutation186 permutation2
    _ = mixedMoment B node3091 node3091Labels := by rfl

def raw12447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12447 raw12447Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw12447 raw12447Labels = mixedMoment B raw12447step0 raw12447step0Labels := by
      have ha : raw12447step0 = (fun i j => raw12447 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12447step0 raw12447; decide +kernel
      have hl : raw12447step0Labels = raw12447Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12447 raw12447Labels permutation192 permutation2
    _ = mixedMoment B node3084 node3084Labels := by rfl

def raw12448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12448 raw12448Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw12448 raw12448Labels = mixedMoment B raw12448step0 raw12448step0Labels := by
      have ha : raw12448step0 = (fun i j => raw12448 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12448step0 raw12448; decide +kernel
      have hl : raw12448step0Labels = raw12448Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12448 raw12448Labels permutation195 permutation2
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw12449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12449 raw12449Labels = mixedMoment B node2994 node2994Labels := by
  calc
    mixedMoment B raw12449 raw12449Labels = mixedMoment B raw12449step0 raw12449step0Labels := by
      have ha : raw12449step0 = (fun i j => raw12449 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12449step0 raw12449; decide +kernel
      have hl : raw12449step0Labels = raw12449Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12449 raw12449Labels permutation157 permutation2
    _ = mixedMoment B node2994 node2994Labels := by rfl

def raw12450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12450 raw12450Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw12450 raw12450Labels = mixedMoment B raw12450step0 raw12450step0Labels := by
      have ha : raw12450step0 = (fun i j => raw12450 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12450step0 raw12450; decide +kernel
      have hl : raw12450step0Labels = raw12450Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12450 raw12450Labels permutation157 permutation2
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw12451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12451 raw12451Labels = mixedMoment B node2985 node2985Labels := by
  calc
    mixedMoment B raw12451 raw12451Labels = mixedMoment B raw12451step0 raw12451step0Labels := by
      have ha : raw12451step0 = (fun i j => raw12451 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12451step0 raw12451; decide +kernel
      have hl : raw12451step0Labels = raw12451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12451 raw12451Labels permutation156 permutation2
    _ = mixedMoment B node2985 node2985Labels := by rfl

def raw12452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw12452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12452 raw12452Labels = mixedMoment B node2938 node2938Labels := by
  calc
    mixedMoment B raw12452 raw12452Labels = mixedMoment B raw12452step0 raw12452step0Labels := by
      have ha : raw12452step0 = (fun i j => raw12452 (permutation644 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12452step0 raw12452; decide +kernel
      have hl : raw12452step0Labels = raw12452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12452 raw12452Labels permutation644 permutation4
    _ = mixedMoment B node2938 node2938Labels := by rfl

def raw12453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw12453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12453 raw12453Labels = mixedMoment B node3115 node3115Labels := by
  calc
    mixedMoment B raw12453 raw12453Labels = mixedMoment B raw12453step0 raw12453step0Labels := by
      have hz : ∀ j, raw12453 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12453step0 = (fun i j => raw12453 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12453step0 raw12453; decide +kernel
      have hl : raw12453step0Labels = raw12453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12453 raw12453Labels permutation265 hz
    mixedMoment B raw12453step0 raw12453step0Labels = mixedMoment B raw12453step1 raw12453step1Labels := by
      have ha : raw12453step1 = (fun i j => raw12453step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12453step1 raw12453step0; decide +kernel
      have hl : raw12453step1Labels = raw12453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12453step0 raw12453step0Labels permutation39 permutation2
    _ = mixedMoment B node3115 node3115Labels := by rfl

def raw12454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12454 raw12454Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw12454 raw12454Labels = mixedMoment B raw12454step0 raw12454step0Labels := by
      have hz : ∀ j, raw12454 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12454step0 = (fun i j => raw12454 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12454step0 raw12454; decide +kernel
      have hl : raw12454step0Labels = raw12454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12454 raw12454Labels permutation265 hz
    mixedMoment B raw12454step0 raw12454step0Labels = mixedMoment B raw12454step1 raw12454step1Labels := by
      have ha : raw12454step1 = (fun i j => raw12454step0 (permutation45 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12454step1 raw12454step0; decide +kernel
      have hl : raw12454step1Labels = raw12454step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12454step0 raw12454step0Labels permutation45 permutation2
    _ = mixedMoment B node3108 node3108Labels := by rfl

def raw12455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12455 raw12455Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw12455 raw12455Labels = mixedMoment B raw12455step0 raw12455step0Labels := by
      have hz : ∀ j, raw12455 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12455step0 = (fun i j => raw12455 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12455step0 raw12455; decide +kernel
      have hl : raw12455step0Labels = raw12455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12455 raw12455Labels permutation265 hz
    mixedMoment B raw12455step0 raw12455step0Labels = mixedMoment B raw12455step1 raw12455step1Labels := by
      have ha : raw12455step1 = (fun i j => raw12455step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12455step1 raw12455step0; decide +kernel
      have hl : raw12455step1Labels = raw12455step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12455step0 raw12455step0Labels permutation51 permutation2
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw12456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12456 raw12456Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw12456 raw12456Labels = mixedMoment B raw12456step0 raw12456step0Labels := by
      have hz : ∀ j, raw12456 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12456step0 = (fun i j => raw12456 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12456step0 raw12456; decide +kernel
      have hl : raw12456step0Labels = raw12456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12456 raw12456Labels permutation265 hz
    mixedMoment B raw12456step0 raw12456step0Labels = mixedMoment B raw12456step1 raw12456step1Labels := by
      have ha : raw12456step1 = (fun i j => raw12456step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12456step1 raw12456step0; decide +kernel
      have hl : raw12456step1Labels = raw12456step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12456step0 raw12456step0Labels permutation37 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw12457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12457 raw12457Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw12457 raw12457Labels = mixedMoment B raw12457step0 raw12457step0Labels := by
      have hz : ∀ j, raw12457 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12457step0 = (fun i j => raw12457 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12457step0 raw12457; decide +kernel
      have hl : raw12457step0Labels = raw12457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12457 raw12457Labels permutation265 hz
    mixedMoment B raw12457step0 raw12457step0Labels = mixedMoment B raw12457step1 raw12457step1Labels := by
      have ha : raw12457step1 = (fun i j => raw12457step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12457step1 raw12457step0; decide +kernel
      have hl : raw12457step1Labels = raw12457step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12457step0 raw12457step0Labels permutation36 permutation2
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw12458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12458 raw12458Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw12458 raw12458Labels = mixedMoment B raw12458step0 raw12458step0Labels := by
      have hz : ∀ j, raw12458 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12458step0 = (fun i j => raw12458 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12458step0 raw12458; decide +kernel
      have hl : raw12458step0Labels = raw12458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12458 raw12458Labels permutation265 hz
    mixedMoment B raw12458step0 raw12458step0Labels = mixedMoment B raw12458step1 raw12458step1Labels := by
      have ha : raw12458step1 = (fun i j => raw12458step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12458step1 raw12458step0; decide +kernel
      have hl : raw12458step1Labels = raw12458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12458step0 raw12458step0Labels permutation34 permutation2
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw12459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12459 raw12459Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw12459 raw12459Labels = mixedMoment B raw12459step0 raw12459step0Labels := by
      have hz : ∀ j, raw12459 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12459step0 = (fun i j => raw12459 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12459step0 raw12459; decide +kernel
      have hl : raw12459step0Labels = raw12459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12459 raw12459Labels permutation265 hz
    mixedMoment B raw12459step0 raw12459step0Labels = mixedMoment B raw12459step1 raw12459step1Labels := by
      have ha : raw12459step1 = (fun i j => raw12459step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12459step1 raw12459step0; decide +kernel
      have hl : raw12459step1Labels = raw12459step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12459step0 raw12459step0Labels permutation33 permutation2
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw12460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12460 raw12460Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw12460 raw12460Labels = mixedMoment B raw12460step0 raw12460step0Labels := by
      have hz : ∀ j, raw12460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12460step0 = (fun i j => raw12460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12460step0 raw12460; decide +kernel
      have hl : raw12460step0Labels = raw12460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12460 raw12460Labels permutation265 hz
    mixedMoment B raw12460step0 raw12460step0Labels = mixedMoment B raw12460step1 raw12460step1Labels := by
      have ha : raw12460step1 = (fun i j => raw12460step0 (permutation138 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12460step1 raw12460step0; decide +kernel
      have hl : raw12460step1Labels = raw12460step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12460step0 raw12460step0Labels permutation138 permutation4
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw12461 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12461step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12461 raw12461Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw12461 raw12461Labels = mixedMoment B raw12461step0 raw12461step0Labels := by
      have hz : ∀ j, raw12461 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12461step0 = (fun i j => raw12461 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12461step0 raw12461; decide +kernel
      have hl : raw12461step0Labels = raw12461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12461 raw12461Labels permutation265 hz
    mixedMoment B raw12461step0 raw12461step0Labels = mixedMoment B raw12461step1 raw12461step1Labels := by
      have ha : raw12461step1 = (fun i j => raw12461step0 (permutation95 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12461step1 raw12461step0; decide +kernel
      have hl : raw12461step1Labels = raw12461step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12461step0 raw12461step0Labels permutation95 permutation3
    mixedMoment B raw12461step1 raw12461step1Labels = mixedMoment B raw12461step2 raw12461step2Labels := by
      have ha : raw12461step2 = raw12461step1 := by apply Matrix.ext; unfold raw12461step2 raw12461step1; decide +kernel
      have hl : raw12461step1Labels = labelEmbedding6 ∘ raw12461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12461step1 raw12461step1Labels raw12461step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw12462 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12462step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12462step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12462 raw12462Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw12462 raw12462Labels = mixedMoment B raw12462step0 raw12462step0Labels := by
      have hz : ∀ j, raw12462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12462step0 = (fun i j => raw12462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12462step0 raw12462; decide +kernel
      have hl : raw12462step0Labels = raw12462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12462 raw12462Labels permutation265 hz
    mixedMoment B raw12462step0 raw12462step0Labels = mixedMoment B raw12462step1 raw12462step1Labels := by
      have ha : raw12462step1 = (fun i j => raw12462step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12462step1 raw12462step0; decide +kernel
      have hl : raw12462step1Labels = raw12462step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12462step0 raw12462step0Labels permutation36 permutation7
    mixedMoment B raw12462step1 raw12462step1Labels = mixedMoment B raw12462step2 raw12462step2Labels := by
      have ha : raw12462step2 = raw12462step1 := by apply Matrix.ext; unfold raw12462step2 raw12462step1; decide +kernel
      have hl : raw12462step1Labels = labelEmbedding10 ∘ raw12462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12462step1 raw12462step1Labels raw12462step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw12463 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12463step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12463 raw12463Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12463 raw12463Labels = mixedMoment B raw12463step0 raw12463step0Labels := by
      have hz : ∀ j, raw12463 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12463step0 = (fun i j => raw12463 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12463step0 raw12463; decide +kernel
      have hl : raw12463step0Labels = raw12463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12463 raw12463Labels permutation265 hz
    mixedMoment B raw12463step0 raw12463step0Labels = mixedMoment B raw12463step1 raw12463step1Labels := by
      have ha : raw12463step1 = (fun i j => raw12463step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12463step1 raw12463step0; decide +kernel
      have hl : raw12463step1Labels = raw12463step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12463step0 raw12463step0Labels permutation37 permutation7
    mixedMoment B raw12463step1 raw12463step1Labels = mixedMoment B raw12463step2 raw12463step2Labels := by
      have ha : raw12463step2 = raw12463step1 := by apply Matrix.ext; unfold raw12463step2 raw12463step1; decide +kernel
      have hl : raw12463step1Labels = labelEmbedding10 ∘ raw12463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12463step1 raw12463step1Labels raw12463step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw12464 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw12464step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12464step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12464step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12464step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12464 raw12464Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw12464 raw12464Labels = mixedMoment B raw12464step0 raw12464step0Labels := by
      have ha : raw12464step0 = (fun i j => raw12464 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12464step0 raw12464; decide +kernel
      have hl : raw12464step0Labels = raw12464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12464 raw12464Labels permutation212 permutation4
    mixedMoment B raw12464step0 raw12464step0Labels = mixedMoment B raw12464step1 raw12464step1Labels := by
      have ha : raw12464step1 = -raw12464step0 := by apply Matrix.ext; change ∀ i j, raw12464step1 i j = -(raw12464step0 i j); unfold raw12464step1 raw12464step0; decide +kernel
      have hl : raw12464step1Labels = raw12464step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12464step1 raw12464step1Labels = mixedMoment B raw12464step2 raw12464step2Labels := by
      have ha : raw12464step2 = raw12464step1 := by apply Matrix.ext; unfold raw12464step2 raw12464step1; decide +kernel
      have hl : raw12464step1Labels = labelEmbedding7 ∘ raw12464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12464step1 raw12464step1Labels raw12464step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw12465 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12465step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12465 raw12465Labels = mixedMoment B node5157 node5157Labels := by
  calc
    mixedMoment B raw12465 raw12465Labels = mixedMoment B raw12465step0 raw12465step0Labels := by
      have ha : raw12465step0 = (fun i j => raw12465 (permutation484 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12465step0 raw12465; decide +kernel
      have hl : raw12465step0Labels = raw12465Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12465 raw12465Labels permutation484 permutation3
    mixedMoment B raw12465step0 raw12465step0Labels = mixedMoment B raw12465step1 raw12465step1Labels := by
      have ha : raw12465step1 = raw12465step0 := by apply Matrix.ext; unfold raw12465step1 raw12465step0; decide +kernel
      have hl : raw12465step0Labels = labelEmbedding6 ∘ raw12465step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12465step0 raw12465step0Labels raw12465step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5157 node5157Labels := by rfl

def raw12466 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12466step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12466 raw12466Labels = mixedMoment B node5280 node5280Labels := by
  calc
    mixedMoment B raw12466 raw12466Labels = mixedMoment B raw12466step0 raw12466step0Labels := by
      have ha : raw12466step0 = (fun i j => raw12466 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12466step0 raw12466; decide +kernel
      have hl : raw12466step0Labels = raw12466Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12466 raw12466Labels permutation152 permutation6
    mixedMoment B raw12466step0 raw12466step0Labels = mixedMoment B raw12466step1 raw12466step1Labels := by
      have ha : raw12466step1 = raw12466step0 := by apply Matrix.ext; unfold raw12466step1 raw12466step0; decide +kernel
      have hl : raw12466step0Labels = labelEmbedding9 ∘ raw12466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12466step0 raw12466step0Labels raw12466step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5280 node5280Labels := by rfl

def raw12467 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12467step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12467 raw12467Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw12467 raw12467Labels = mixedMoment B raw12467step0 raw12467step0Labels := by
      have ha : raw12467step0 = (fun i j => raw12467 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12467step0 raw12467; decide +kernel
      have hl : raw12467step0Labels = raw12467Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12467 raw12467Labels permutation152 permutation6
    mixedMoment B raw12467step0 raw12467step0Labels = mixedMoment B raw12467step1 raw12467step1Labels := by
      have ha : raw12467step1 = raw12467step0 := by apply Matrix.ext; unfold raw12467step1 raw12467step0; decide +kernel
      have hl : raw12467step0Labels = labelEmbedding9 ∘ raw12467step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12467step0 raw12467step0Labels raw12467step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw12468 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw12468step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw12468step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12468step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw12468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12468 raw12468Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw12468 raw12468Labels = mixedMoment B raw12468step0 raw12468step0Labels := by
      have hz : ∀ j, raw12468 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12468step0 = (fun i j => raw12468 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12468step0 raw12468; decide +kernel
      have hl : raw12468step0Labels = raw12468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12468 raw12468Labels permutation265 hz
    mixedMoment B raw12468step0 raw12468step0Labels = mixedMoment B raw12468step1 raw12468step1Labels := by
      have ha : raw12468step1 = (fun i j => raw12468step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12468step1 raw12468step0; decide +kernel
      have hl : raw12468step1Labels = raw12468step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12468step0 raw12468step0Labels permutation40 permutation4
    mixedMoment B raw12468step1 raw12468step1Labels = mixedMoment B raw12468step2 raw12468step2Labels := by
      have ha : raw12468step2 = -raw12468step1 := by apply Matrix.ext; change ∀ i j, raw12468step2 i j = -(raw12468step1 i j); unfold raw12468step2 raw12468step1; decide +kernel
      have hl : raw12468step2Labels = raw12468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12468step2 raw12468step2Labels = mixedMoment B raw12468step3 raw12468step3Labels := by
      have ha : raw12468step3 = raw12468step2 := by apply Matrix.ext; unfold raw12468step3 raw12468step2; decide +kernel
      have hl : raw12468step2Labels = labelEmbedding7 ∘ raw12468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12468step2 raw12468step2Labels raw12468step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw12469 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw12469step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw12469step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12469 raw12469Labels = mixedMoment B node5158 node5158Labels := by
  calc
    mixedMoment B raw12469 raw12469Labels = mixedMoment B raw12469step0 raw12469step0Labels := by
      have hz : ∀ j, raw12469 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12469step0 = (fun i j => raw12469 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12469step0 raw12469; decide +kernel
      have hl : raw12469step0Labels = raw12469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12469 raw12469Labels permutation265 hz
    mixedMoment B raw12469step0 raw12469step0Labels = mixedMoment B raw12469step1 raw12469step1Labels := by
      have ha : raw12469step1 = (fun i j => raw12469step0 (permutation93 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12469step1 raw12469step0; decide +kernel
      have hl : raw12469step1Labels = raw12469step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12469step0 raw12469step0Labels permutation93 permutation3
    mixedMoment B raw12469step1 raw12469step1Labels = mixedMoment B raw12469step2 raw12469step2Labels := by
      have ha : raw12469step2 = raw12469step1 := by apply Matrix.ext; unfold raw12469step2 raw12469step1; decide +kernel
      have hl : raw12469step1Labels = labelEmbedding6 ∘ raw12469step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12469step1 raw12469step1Labels raw12469step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5158 node5158Labels := by rfl

def raw12470 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12470step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12470step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12470 raw12470Labels = mixedMoment B node5298 node5298Labels := by
  calc
    mixedMoment B raw12470 raw12470Labels = mixedMoment B raw12470step0 raw12470step0Labels := by
      have hz : ∀ j, raw12470 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12470step0 = (fun i j => raw12470 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12470step0 raw12470; decide +kernel
      have hl : raw12470step0Labels = raw12470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12470 raw12470Labels permutation265 hz
    mixedMoment B raw12470step0 raw12470step0Labels = mixedMoment B raw12470step1 raw12470step1Labels := by
      have ha : raw12470step1 = (fun i j => raw12470step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12470step1 raw12470step0; decide +kernel
      have hl : raw12470step1Labels = raw12470step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12470step0 raw12470step0Labels permutation32 permutation6
    mixedMoment B raw12470step1 raw12470step1Labels = mixedMoment B raw12470step2 raw12470step2Labels := by
      have ha : raw12470step2 = raw12470step1 := by apply Matrix.ext; unfold raw12470step2 raw12470step1; decide +kernel
      have hl : raw12470step1Labels = labelEmbedding9 ∘ raw12470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12470step1 raw12470step1Labels raw12470step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5298 node5298Labels := by rfl

def raw12471 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12471step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12471step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12471step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12471step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12471 raw12471Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw12471 raw12471Labels = mixedMoment B raw12471step0 raw12471step0Labels := by
      have hz : ∀ j, raw12471 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12471step0 = (fun i j => raw12471 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12471step0 raw12471; decide +kernel
      have hl : raw12471step0Labels = raw12471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12471 raw12471Labels permutation265 hz
    mixedMoment B raw12471step0 raw12471step0Labels = mixedMoment B raw12471step1 raw12471step1Labels := by
      have ha : raw12471step1 = (fun i j => raw12471step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12471step1 raw12471step0; decide +kernel
      have hl : raw12471step1Labels = raw12471step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12471step0 raw12471step0Labels permutation38 permutation4
    mixedMoment B raw12471step1 raw12471step1Labels = mixedMoment B raw12471step2 raw12471step2Labels := by
      have ha : raw12471step2 = -raw12471step1 := by apply Matrix.ext; change ∀ i j, raw12471step2 i j = -(raw12471step1 i j); unfold raw12471step2 raw12471step1; decide +kernel
      have hl : raw12471step2Labels = raw12471step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12471step2 raw12471step2Labels = mixedMoment B raw12471step3 raw12471step3Labels := by
      have ha : raw12471step3 = raw12471step2 := by apply Matrix.ext; unfold raw12471step3 raw12471step2; decide +kernel
      have hl : raw12471step2Labels = labelEmbedding7 ∘ raw12471step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12471step2 raw12471step2Labels raw12471step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw12472 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw12472step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw12472step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12472 raw12472Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw12472 raw12472Labels = mixedMoment B raw12472step0 raw12472step0Labels := by
      have hz : ∀ j, raw12472 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12472step0 = (fun i j => raw12472 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12472step0 raw12472; decide +kernel
      have hl : raw12472step0Labels = raw12472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12472 raw12472Labels permutation265 hz
    mixedMoment B raw12472step0 raw12472step0Labels = mixedMoment B raw12472step1 raw12472step1Labels := by
      have ha : raw12472step1 = (fun i j => raw12472step0 (permutation92 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12472step1 raw12472step0; decide +kernel
      have hl : raw12472step1Labels = raw12472step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12472step0 raw12472step0Labels permutation92 permutation3
    mixedMoment B raw12472step1 raw12472step1Labels = mixedMoment B raw12472step2 raw12472step2Labels := by
      have ha : raw12472step2 = raw12472step1 := by apply Matrix.ext; unfold raw12472step2 raw12472step1; decide +kernel
      have hl : raw12472step1Labels = labelEmbedding6 ∘ raw12472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12472step1 raw12472step1Labels raw12472step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw12473 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12473step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12473 raw12473Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw12473 raw12473Labels = mixedMoment B raw12473step0 raw12473step0Labels := by
      have hz : ∀ j, raw12473 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12473step0 = (fun i j => raw12473 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12473step0 raw12473; decide +kernel
      have hl : raw12473step0Labels = raw12473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12473 raw12473Labels permutation265 hz
    mixedMoment B raw12473step0 raw12473step0Labels = mixedMoment B raw12473step1 raw12473step1Labels := by
      have ha : raw12473step1 = (fun i j => raw12473step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12473step1 raw12473step0; decide +kernel
      have hl : raw12473step1Labels = raw12473step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12473step0 raw12473step0Labels permutation32 permutation6
    mixedMoment B raw12473step1 raw12473step1Labels = mixedMoment B raw12473step2 raw12473step2Labels := by
      have ha : raw12473step2 = raw12473step1 := by apply Matrix.ext; unfold raw12473step2 raw12473step1; decide +kernel
      have hl : raw12473step1Labels = labelEmbedding9 ∘ raw12473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12473step1 raw12473step1Labels raw12473step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw12474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw12474step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw12474step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12474step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw12474step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12474 raw12474Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw12474 raw12474Labels = mixedMoment B raw12474step0 raw12474step0Labels := by
      have hz : ∀ j, raw12474 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12474step0 = (fun i j => raw12474 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12474step0 raw12474; decide +kernel
      have hl : raw12474step0Labels = raw12474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12474 raw12474Labels permutation265 hz
    mixedMoment B raw12474step0 raw12474step0Labels = mixedMoment B raw12474step1 raw12474step1Labels := by
      have ha : raw12474step1 = (fun i j => raw12474step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12474step1 raw12474step0; decide +kernel
      have hl : raw12474step1Labels = raw12474step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12474step0 raw12474step0Labels permutation40 permutation4
    mixedMoment B raw12474step1 raw12474step1Labels = mixedMoment B raw12474step2 raw12474step2Labels := by
      have ha : raw12474step2 = -raw12474step1 := by apply Matrix.ext; change ∀ i j, raw12474step2 i j = -(raw12474step1 i j); unfold raw12474step2 raw12474step1; decide +kernel
      have hl : raw12474step2Labels = raw12474step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12474step2 raw12474step2Labels = mixedMoment B raw12474step3 raw12474step3Labels := by
      have ha : raw12474step3 = raw12474step2 := by apply Matrix.ext; unfold raw12474step3 raw12474step2; decide +kernel
      have hl : raw12474step2Labels = labelEmbedding7 ∘ raw12474step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12474step2 raw12474step2Labels raw12474step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw12475 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw12475step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw12475step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12475 raw12475Labels = mixedMoment B node5079 node5079Labels := by
  calc
    mixedMoment B raw12475 raw12475Labels = mixedMoment B raw12475step0 raw12475step0Labels := by
      have hz : ∀ j, raw12475 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12475step0 = (fun i j => raw12475 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12475step0 raw12475; decide +kernel
      have hl : raw12475step0Labels = raw12475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12475 raw12475Labels permutation265 hz
    mixedMoment B raw12475step0 raw12475step0Labels = mixedMoment B raw12475step1 raw12475step1Labels := by
      have ha : raw12475step1 = (fun i j => raw12475step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12475step1 raw12475step0; decide +kernel
      have hl : raw12475step1Labels = raw12475step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12475step0 raw12475step0Labels permutation138 permutation5
    mixedMoment B raw12475step1 raw12475step1Labels = mixedMoment B raw12475step2 raw12475step2Labels := by
      have ha : raw12475step2 = raw12475step1 := by apply Matrix.ext; unfold raw12475step2 raw12475step1; decide +kernel
      have hl : raw12475step1Labels = labelEmbedding8 ∘ raw12475step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12475step1 raw12475step1Labels raw12475step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5079 node5079Labels := by rfl

def raw12476 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw12476step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw12476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12476 raw12476Labels = mixedMoment B node5108 node5108Labels := by
  calc
    mixedMoment B raw12476 raw12476Labels = mixedMoment B raw12476step0 raw12476step0Labels := by
      have hz : ∀ j, raw12476 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12476step0 = (fun i j => raw12476 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12476step0 raw12476; decide +kernel
      have hl : raw12476step0Labels = raw12476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12476 raw12476Labels permutation265 hz
    mixedMoment B raw12476step0 raw12476step0Labels = mixedMoment B raw12476step1 raw12476step1Labels := by
      have ha : raw12476step1 = (fun i j => raw12476step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12476step1 raw12476step0; decide +kernel
      have hl : raw12476step1Labels = raw12476step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12476step0 raw12476step0Labels permutation137 permutation5
    mixedMoment B raw12476step1 raw12476step1Labels = mixedMoment B raw12476step2 raw12476step2Labels := by
      have ha : raw12476step2 = raw12476step1 := by apply Matrix.ext; unfold raw12476step2 raw12476step1; decide +kernel
      have hl : raw12476step1Labels = labelEmbedding8 ∘ raw12476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12476step1 raw12476step1Labels raw12476step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5108 node5108Labels := by rfl

def raw12477 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12477step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12477step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12477 raw12477Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw12477 raw12477Labels = mixedMoment B raw12477step0 raw12477step0Labels := by
      have hz : ∀ j, raw12477 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12477step0 = (fun i j => raw12477 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12477step0 raw12477; decide +kernel
      have hl : raw12477step0Labels = raw12477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12477 raw12477Labels permutation346 hz
    mixedMoment B raw12477step0 raw12477step0Labels = mixedMoment B raw12477step1 raw12477step1Labels := by
      have hz : ∀ j, raw12477step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12477step1 = (fun i j => raw12477step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12477step1 raw12477step0; decide +kernel
      have hl : raw12477step1Labels = raw12477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12477step0 raw12477step0Labels permutation56 hz
    mixedMoment B raw12477step1 raw12477step1Labels = mixedMoment B raw12477step2 raw12477step2Labels := by
      have ha : raw12477step2 = (fun i j => raw12477step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12477step2 raw12477step1; decide +kernel
      have hl : raw12477step2Labels = raw12477step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12477step1 raw12477step1Labels permutation8 permutation6
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw12478 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12478 raw12478Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw12478 raw12478Labels = mixedMoment B raw12478step0 raw12478step0Labels := by
      have hz : ∀ j, raw12478 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12478step0 = (fun i j => raw12478 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12478step0 raw12478; decide +kernel
      have hl : raw12478step0Labels = raw12478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12478 raw12478Labels permutation265 hz
    mixedMoment B raw12478step0 raw12478step0Labels = mixedMoment B raw12478step1 raw12478step1Labels := by
      have ha : raw12478step1 = (fun i j => raw12478step0 (permutation95 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12478step1 raw12478step0; decide +kernel
      have hl : raw12478step1Labels = raw12478step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12478step0 raw12478step0Labels permutation95 permutation3
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw12479 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12479 raw12479Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw12479 raw12479Labels = mixedMoment B raw12479step0 raw12479step0Labels := by
      have hz : ∀ j, raw12479 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12479step0 = (fun i j => raw12479 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12479step0 raw12479; decide +kernel
      have hl : raw12479step0Labels = raw12479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12479 raw12479Labels permutation265 hz
    mixedMoment B raw12479step0 raw12479step0Labels = mixedMoment B raw12479step1 raw12479step1Labels := by
      have ha : raw12479step1 = (fun i j => raw12479step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12479step1 raw12479step0; decide +kernel
      have hl : raw12479step1Labels = raw12479step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12479step0 raw12479step0Labels permutation32 permutation6
    _ = mixedMoment B node3108 node3108Labels := by rfl

def raw12480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12480 raw12480Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw12480 raw12480Labels = mixedMoment B raw12480step0 raw12480step0Labels := by
      have hz : ∀ j, raw12480 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12480step0 = (fun i j => raw12480 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12480step0 raw12480; decide +kernel
      have hl : raw12480step0Labels = raw12480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12480 raw12480Labels permutation265 hz
    mixedMoment B raw12480step0 raw12480step0Labels = mixedMoment B raw12480step1 raw12480step1Labels := by
      have ha : raw12480step1 = (fun i j => raw12480step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12480step1 raw12480step0; decide +kernel
      have hl : raw12480step1Labels = raw12480step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12480step0 raw12480step0Labels permutation32 permutation6
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw12481 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12481 raw12481Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw12481 raw12481Labels = mixedMoment B raw12481step0 raw12481step0Labels := by
      have ha : raw12481step0 = (fun i j => raw12481 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12481step0 raw12481; decide +kernel
      have hl : raw12481step0Labels = raw12481Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12481 raw12481Labels permutation152 permutation6
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw12482 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12482 raw12482Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw12482 raw12482Labels = mixedMoment B raw12482step0 raw12482step0Labels := by
      have hz : ∀ j, raw12482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12482step0 = (fun i j => raw12482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12482step0 raw12482; decide +kernel
      have hl : raw12482step0Labels = raw12482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12482 raw12482Labels permutation346 hz
    mixedMoment B raw12482step0 raw12482step0Labels = mixedMoment B raw12482step1 raw12482step1Labels := by
      have ha : raw12482step1 = (fun i j => raw12482step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12482step1 raw12482step0; decide +kernel
      have hl : raw12482step1Labels = raw12482step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12482step0 raw12482step0Labels permutation32 permutation6
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw12483 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12483 raw12483Labels = mixedMoment B node2583 node2583Labels := by
  calc
    mixedMoment B raw12483 raw12483Labels = mixedMoment B raw12483step0 raw12483step0Labels := by
      have ha : raw12483step0 = (fun i j => raw12483 (permutation484 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12483step0 raw12483; decide +kernel
      have hl : raw12483step0Labels = raw12483Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12483 raw12483Labels permutation484 permutation3
    _ = mixedMoment B node2583 node2583Labels := by rfl

def raw12484 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12484 raw12484Labels = mixedMoment B node2749 node2749Labels := by
  calc
    mixedMoment B raw12484 raw12484Labels = mixedMoment B raw12484step0 raw12484step0Labels := by
      have ha : raw12484step0 = (fun i j => raw12484 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12484step0 raw12484; decide +kernel
      have hl : raw12484step0Labels = raw12484Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12484 raw12484Labels permutation152 permutation6
    _ = mixedMoment B node2749 node2749Labels := by rfl

def raw12485 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12485 raw12485Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw12485 raw12485Labels = mixedMoment B raw12485step0 raw12485step0Labels := by
      have ha : raw12485step0 = (fun i j => raw12485 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12485step0 raw12485; decide +kernel
      have hl : raw12485step0Labels = raw12485Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12485 raw12485Labels permutation152 permutation6
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw12486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12486 raw12486Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw12486 raw12486Labels = mixedMoment B raw12486step0 raw12486step0Labels := by
      have hz : ∀ j, raw12486 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12486step0 = (fun i j => raw12486 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12486step0 raw12486; decide +kernel
      have hl : raw12486step0Labels = raw12486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12486 raw12486Labels permutation265 hz
    mixedMoment B raw12486step0 raw12486step0Labels = mixedMoment B raw12486step1 raw12486step1Labels := by
      have ha : raw12486step1 = (fun i j => raw12486step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12486step1 raw12486step0; decide +kernel
      have hl : raw12486step1Labels = raw12486step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12486step0 raw12486step0Labels permutation32 permutation6
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw12487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw12487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12487 raw12487Labels = mixedMoment B node2585 node2585Labels := by
  calc
    mixedMoment B raw12487 raw12487Labels = mixedMoment B raw12487step0 raw12487step0Labels := by
      have hz : ∀ j, raw12487 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12487step0 = (fun i j => raw12487 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12487step0 raw12487; decide +kernel
      have hl : raw12487step0Labels = raw12487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12487 raw12487Labels permutation265 hz
    mixedMoment B raw12487step0 raw12487step0Labels = mixedMoment B raw12487step1 raw12487step1Labels := by
      have ha : raw12487step1 = (fun i j => raw12487step0 (permutation93 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12487step1 raw12487step0; decide +kernel
      have hl : raw12487step1Labels = raw12487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12487step0 raw12487step0Labels permutation93 permutation3
    _ = mixedMoment B node2585 node2585Labels := by rfl

def raw12488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw12488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12488 raw12488Labels = mixedMoment B node2772 node2772Labels := by
  calc
    mixedMoment B raw12488 raw12488Labels = mixedMoment B raw12488step0 raw12488step0Labels := by
      have hz : ∀ j, raw12488 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12488step0 = (fun i j => raw12488 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12488step0 raw12488; decide +kernel
      have hl : raw12488step0Labels = raw12488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12488 raw12488Labels permutation265 hz
    mixedMoment B raw12488step0 raw12488step0Labels = mixedMoment B raw12488step1 raw12488step1Labels := by
      have ha : raw12488step1 = (fun i j => raw12488step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12488step1 raw12488step0; decide +kernel
      have hl : raw12488step1Labels = raw12488step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12488step0 raw12488step0Labels permutation32 permutation6
    _ = mixedMoment B node2772 node2772Labels := by rfl

def raw12489 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12489 raw12489Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw12489 raw12489Labels = mixedMoment B raw12489step0 raw12489step0Labels := by
      have hz : ∀ j, raw12489 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12489step0 = (fun i j => raw12489 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12489step0 raw12489; decide +kernel
      have hl : raw12489step0Labels = raw12489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12489 raw12489Labels permutation265 hz
    mixedMoment B raw12489step0 raw12489step0Labels = mixedMoment B raw12489step1 raw12489step1Labels := by
      have ha : raw12489step1 = (fun i j => raw12489step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12489step1 raw12489step0; decide +kernel
      have hl : raw12489step1Labels = raw12489step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12489step0 raw12489step0Labels permutation32 permutation6
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw12490 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12490 raw12490Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw12490 raw12490Labels = mixedMoment B raw12490step0 raw12490step0Labels := by
      have hz : ∀ j, raw12490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12490step0 = (fun i j => raw12490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12490step0 raw12490; decide +kernel
      have hl : raw12490step0Labels = raw12490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12490 raw12490Labels permutation346 hz
    mixedMoment B raw12490step0 raw12490step0Labels = mixedMoment B raw12490step1 raw12490step1Labels := by
      have hz : ∀ j, raw12490step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12490step1 = (fun i j => raw12490step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12490step1 raw12490step0; decide +kernel
      have hl : raw12490step1Labels = raw12490step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12490step0 raw12490step0Labels permutation56 hz
    mixedMoment B raw12490step1 raw12490step1Labels = mixedMoment B raw12490step2 raw12490step2Labels := by
      have ha : raw12490step2 = (fun i j => raw12490step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12490step2 raw12490step1; decide +kernel
      have hl : raw12490step2Labels = raw12490step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12490step1 raw12490step1Labels permutation8 permutation6
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw12491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw12491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12491 raw12491Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw12491 raw12491Labels = mixedMoment B raw12491step0 raw12491step0Labels := by
      have hz : ∀ j, raw12491 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12491step0 = (fun i j => raw12491 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12491step0 raw12491; decide +kernel
      have hl : raw12491step0Labels = raw12491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12491 raw12491Labels permutation265 hz
    mixedMoment B raw12491step0 raw12491step0Labels = mixedMoment B raw12491step1 raw12491step1Labels := by
      have ha : raw12491step1 = (fun i j => raw12491step0 (permutation92 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12491step1 raw12491step0; decide +kernel
      have hl : raw12491step1Labels = raw12491step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12491step0 raw12491step0Labels permutation92 permutation3
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw12492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12492 raw12492Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw12492 raw12492Labels = mixedMoment B raw12492step0 raw12492step0Labels := by
      have hz : ∀ j, raw12492 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12492step0 = (fun i j => raw12492 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12492step0 raw12492; decide +kernel
      have hl : raw12492step0Labels = raw12492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12492 raw12492Labels permutation265 hz
    mixedMoment B raw12492step0 raw12492step0Labels = mixedMoment B raw12492step1 raw12492step1Labels := by
      have ha : raw12492step1 = (fun i j => raw12492step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12492step1 raw12492step0; decide +kernel
      have hl : raw12492step1Labels = raw12492step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12492step0 raw12492step0Labels permutation32 permutation6
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw12493 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12493 raw12493Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw12493 raw12493Labels = mixedMoment B raw12493step0 raw12493step0Labels := by
      have hz : ∀ j, raw12493 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12493step0 = (fun i j => raw12493 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12493step0 raw12493; decide +kernel
      have hl : raw12493step0Labels = raw12493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12493 raw12493Labels permutation265 hz
    mixedMoment B raw12493step0 raw12493step0Labels = mixedMoment B raw12493step1 raw12493step1Labels := by
      have ha : raw12493step1 = (fun i j => raw12493step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12493step1 raw12493step0; decide +kernel
      have hl : raw12493step1Labels = raw12493step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12493step0 raw12493step0Labels permutation32 permutation6
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw12494 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12494step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12494 raw12494Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw12494 raw12494Labels = mixedMoment B raw12494step0 raw12494step0Labels := by
      have hz : ∀ j, raw12494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12494step0 = (fun i j => raw12494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12494step0 raw12494; decide +kernel
      have hl : raw12494step0Labels = raw12494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12494 raw12494Labels permutation346 hz
    mixedMoment B raw12494step0 raw12494step0Labels = mixedMoment B raw12494step1 raw12494step1Labels := by
      have hz : ∀ j, raw12494step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12494step1 = (fun i j => raw12494step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12494step1 raw12494step0; decide +kernel
      have hl : raw12494step1Labels = raw12494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12494step0 raw12494step0Labels permutation56 hz
    mixedMoment B raw12494step1 raw12494step1Labels = mixedMoment B raw12494step2 raw12494step2Labels := by
      have ha : raw12494step2 = (fun i j => raw12494step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12494step2 raw12494step1; decide +kernel
      have hl : raw12494step2Labels = raw12494step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12494step1 raw12494step1Labels permutation8 permutation6
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw12495 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw12495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12495 raw12495Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw12495 raw12495Labels = mixedMoment B raw12495step0 raw12495step0Labels := by
      have hz : ∀ j, raw12495 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12495step0 = (fun i j => raw12495 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12495step0 raw12495; decide +kernel
      have hl : raw12495step0Labels = raw12495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12495 raw12495Labels permutation265 hz
    mixedMoment B raw12495step0 raw12495step0Labels = mixedMoment B raw12495step1 raw12495step1Labels := by
      have ha : raw12495step1 = (fun i j => raw12495step0 (permutation92 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12495step1 raw12495step0; decide +kernel
      have hl : raw12495step1Labels = raw12495step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12495step0 raw12495step0Labels permutation92 permutation3
    _ = mixedMoment B node2584 node2584Labels := by rfl

def raw12496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw12496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12496 raw12496Labels = mixedMoment B node2762 node2762Labels := by
  calc
    mixedMoment B raw12496 raw12496Labels = mixedMoment B raw12496step0 raw12496step0Labels := by
      have hz : ∀ j, raw12496 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12496step0 = (fun i j => raw12496 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12496step0 raw12496; decide +kernel
      have hl : raw12496step0Labels = raw12496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12496 raw12496Labels permutation265 hz
    mixedMoment B raw12496step0 raw12496step0Labels = mixedMoment B raw12496step1 raw12496step1Labels := by
      have ha : raw12496step1 = (fun i j => raw12496step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12496step1 raw12496step0; decide +kernel
      have hl : raw12496step1Labels = raw12496step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12496step0 raw12496step0Labels permutation32 permutation6
    _ = mixedMoment B node2762 node2762Labels := by rfl

def raw12497 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12497step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw12497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw12497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12497 raw12497Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw12497 raw12497Labels = mixedMoment B raw12497step0 raw12497step0Labels := by
      have hz : ∀ j, raw12497 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12497step0 = (fun i j => raw12497 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12497step0 raw12497; decide +kernel
      have hl : raw12497step0Labels = raw12497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12497 raw12497Labels permutation265 hz
    mixedMoment B raw12497step0 raw12497step0Labels = mixedMoment B raw12497step1 raw12497step1Labels := by
      have ha : raw12497step1 = (fun i j => raw12497step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12497step1 raw12497step0; decide +kernel
      have hl : raw12497step1Labels = raw12497step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12497step0 raw12497step0Labels permutation37 permutation7
    mixedMoment B raw12497step1 raw12497step1Labels = mixedMoment B raw12497step2 raw12497step2Labels := by
      have ha : raw12497step2 = raw12497step1 := by apply Matrix.ext; unfold raw12497step2 raw12497step1; decide +kernel
      have hl : raw12497step1Labels = labelEmbedding1 ∘ raw12497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12497step1 raw12497step1Labels raw12497step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw12498 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12498step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12498 raw12498Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw12498 raw12498Labels = mixedMoment B raw12498step0 raw12498step0Labels := by
      have hz : ∀ j, raw12498 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12498step0 = (fun i j => raw12498 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12498step0 raw12498; decide +kernel
      have hl : raw12498step0Labels = raw12498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12498 raw12498Labels permutation265 hz
    mixedMoment B raw12498step0 raw12498step0Labels = mixedMoment B raw12498step1 raw12498step1Labels := by
      have ha : raw12498step1 = (fun i j => raw12498step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12498step1 raw12498step0; decide +kernel
      have hl : raw12498step1Labels = raw12498step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12498step0 raw12498step0Labels permutation36 permutation7
    mixedMoment B raw12498step1 raw12498step1Labels = mixedMoment B raw12498step2 raw12498step2Labels := by
      have ha : raw12498step2 = raw12498step1 := by apply Matrix.ext; unfold raw12498step2 raw12498step1; decide +kernel
      have hl : raw12498step1Labels = labelEmbedding1 ∘ raw12498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12498step1 raw12498step1Labels raw12498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw12499 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12499 raw12499Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw12499 raw12499Labels = mixedMoment B raw12499step0 raw12499step0Labels := by
      have hz : ∀ j, raw12499 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12499step0 = (fun i j => raw12499 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12499step0 raw12499; decide +kernel
      have hl : raw12499step0Labels = raw12499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12499 raw12499Labels permutation265 hz
    mixedMoment B raw12499step0 raw12499step0Labels = mixedMoment B raw12499step1 raw12499step1Labels := by
      have ha : raw12499step1 = (fun i j => raw12499step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12499step1 raw12499step0; decide +kernel
      have hl : raw12499step1Labels = raw12499step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12499step0 raw12499step0Labels permutation37 permutation7
    mixedMoment B raw12499step1 raw12499step1Labels = mixedMoment B raw12499step2 raw12499step2Labels := by
      have ha : raw12499step2 = raw12499step1 := by apply Matrix.ext; unfold raw12499step2 raw12499step1; decide +kernel
      have hl : raw12499step1Labels = labelEmbedding1 ∘ raw12499step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12499step1 raw12499step1Labels raw12499step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw12500 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12500step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12500step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12500 raw12500Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw12500 raw12500Labels = mixedMoment B raw12500step0 raw12500step0Labels := by
      have ha : raw12500step0 = (fun i j => raw12500 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12500step0 raw12500; decide +kernel
      have hl : raw12500step0Labels = raw12500Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12500 raw12500Labels permutation212 permutation5
    mixedMoment B raw12500step0 raw12500step0Labels = mixedMoment B raw12500step1 raw12500step1Labels := by
      have ha : raw12500step1 = -raw12500step0 := by apply Matrix.ext; change ∀ i j, raw12500step1 i j = -(raw12500step0 i j); unfold raw12500step1 raw12500step0; decide +kernel
      have hl : raw12500step1Labels = raw12500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12500step1 raw12500step1Labels = mixedMoment B raw12500step2 raw12500step2Labels := by
      have ha : raw12500step2 = raw12500step1 := by apply Matrix.ext; unfold raw12500step2 raw12500step1; decide +kernel
      have hl : raw12500step1Labels = labelEmbedding1 ∘ raw12500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12500step1 raw12500step1Labels raw12500step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3172 node3172Labels := by rfl

def raw12501 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw12501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw12501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12501 raw12501Labels = mixedMoment B node3070 node3070Labels := by
  calc
    mixedMoment B raw12501 raw12501Labels = mixedMoment B raw12501step0 raw12501step0Labels := by
      have ha : raw12501step0 = (fun i j => raw12501 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12501step0 raw12501; decide +kernel
      have hl : raw12501step0Labels = raw12501Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12501 raw12501Labels permutation157 permutation7
    mixedMoment B raw12501step0 raw12501step0Labels = mixedMoment B raw12501step1 raw12501step1Labels := by
      have ha : raw12501step1 = raw12501step0 := by apply Matrix.ext; unfold raw12501step1 raw12501step0; decide +kernel
      have hl : raw12501step0Labels = labelEmbedding1 ∘ raw12501step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12501step0 raw12501step0Labels raw12501step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3070 node3070Labels := by rfl

def raw12502 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12502 raw12502Labels = mixedMoment B node3071 node3071Labels := by
  calc
    mixedMoment B raw12502 raw12502Labels = mixedMoment B raw12502step0 raw12502step0Labels := by
      have ha : raw12502step0 = (fun i j => raw12502 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12502step0 raw12502; decide +kernel
      have hl : raw12502step0Labels = raw12502Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12502 raw12502Labels permutation156 permutation7
    mixedMoment B raw12502step0 raw12502step0Labels = mixedMoment B raw12502step1 raw12502step1Labels := by
      have ha : raw12502step1 = raw12502step0 := by apply Matrix.ext; unfold raw12502step1 raw12502step0; decide +kernel
      have hl : raw12502step0Labels = labelEmbedding1 ∘ raw12502step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12502step0 raw12502step0Labels raw12502step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3071 node3071Labels := by rfl

def raw12503 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12503step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12503 raw12503Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw12503 raw12503Labels = mixedMoment B raw12503step0 raw12503step0Labels := by
      have ha : raw12503step0 = (fun i j => raw12503 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12503step0 raw12503; decide +kernel
      have hl : raw12503step0Labels = raw12503Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12503 raw12503Labels permutation157 permutation7
    mixedMoment B raw12503step0 raw12503step0Labels = mixedMoment B raw12503step1 raw12503step1Labels := by
      have ha : raw12503step1 = raw12503step0 := by apply Matrix.ext; unfold raw12503step1 raw12503step0; decide +kernel
      have hl : raw12503step0Labels = labelEmbedding1 ∘ raw12503step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12503step0 raw12503step0Labels raw12503step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw12504 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12504step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw12504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw12504step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12504step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw12504step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12504 raw12504Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw12504 raw12504Labels = mixedMoment B raw12504step0 raw12504step0Labels := by
      have hz : ∀ j, raw12504 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12504step0 = (fun i j => raw12504 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12504step0 raw12504; decide +kernel
      have hl : raw12504step0Labels = raw12504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12504 raw12504Labels permutation265 hz
    mixedMoment B raw12504step0 raw12504step0Labels = mixedMoment B raw12504step1 raw12504step1Labels := by
      have ha : raw12504step1 = (fun i j => raw12504step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12504step1 raw12504step0; decide +kernel
      have hl : raw12504step1Labels = raw12504step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12504step0 raw12504step0Labels permutation41 permutation5
    mixedMoment B raw12504step1 raw12504step1Labels = mixedMoment B raw12504step2 raw12504step2Labels := by
      have ha : raw12504step2 = -raw12504step1 := by apply Matrix.ext; change ∀ i j, raw12504step2 i j = -(raw12504step1 i j); unfold raw12504step2 raw12504step1; decide +kernel
      have hl : raw12504step2Labels = raw12504step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12504step2 raw12504step2Labels = mixedMoment B raw12504step3 raw12504step3Labels := by
      have ha : raw12504step3 = raw12504step2 := by apply Matrix.ext; unfold raw12504step3 raw12504step2; decide +kernel
      have hl : raw12504step2Labels = labelEmbedding1 ∘ raw12504step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12504step2 raw12504step2Labels raw12504step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3174 node3174Labels := by rfl

def raw12505 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw12505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw12505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12505 raw12505Labels = mixedMoment B node3047 node3047Labels := by
  calc
    mixedMoment B raw12505 raw12505Labels = mixedMoment B raw12505step0 raw12505step0Labels := by
      have hz : ∀ j, raw12505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12505step0 = (fun i j => raw12505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12505step0 raw12505; decide +kernel
      have hl : raw12505step0Labels = raw12505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12505 raw12505Labels permutation265 hz
    mixedMoment B raw12505step0 raw12505step0Labels = mixedMoment B raw12505step1 raw12505step1Labels := by
      have ha : raw12505step1 = (fun i j => raw12505step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12505step1 raw12505step0; decide +kernel
      have hl : raw12505step1Labels = raw12505step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12505step0 raw12505step0Labels permutation37 permutation7
    mixedMoment B raw12505step1 raw12505step1Labels = mixedMoment B raw12505step2 raw12505step2Labels := by
      have ha : raw12505step2 = raw12505step1 := by apply Matrix.ext; unfold raw12505step2 raw12505step1; decide +kernel
      have hl : raw12505step1Labels = labelEmbedding1 ∘ raw12505step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12505step1 raw12505step1Labels raw12505step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3047 node3047Labels := by rfl

def raw12506 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12506step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12506 raw12506Labels = mixedMoment B node3048 node3048Labels := by
  calc
    mixedMoment B raw12506 raw12506Labels = mixedMoment B raw12506step0 raw12506step0Labels := by
      have hz : ∀ j, raw12506 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12506step0 = (fun i j => raw12506 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12506step0 raw12506; decide +kernel
      have hl : raw12506step0Labels = raw12506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12506 raw12506Labels permutation265 hz
    mixedMoment B raw12506step0 raw12506step0Labels = mixedMoment B raw12506step1 raw12506step1Labels := by
      have ha : raw12506step1 = (fun i j => raw12506step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12506step1 raw12506step0; decide +kernel
      have hl : raw12506step1Labels = raw12506step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12506step0 raw12506step0Labels permutation36 permutation7
    mixedMoment B raw12506step1 raw12506step1Labels = mixedMoment B raw12506step2 raw12506step2Labels := by
      have ha : raw12506step2 = raw12506step1 := by apply Matrix.ext; unfold raw12506step2 raw12506step1; decide +kernel
      have hl : raw12506step1Labels = labelEmbedding1 ∘ raw12506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12506step1 raw12506step1Labels raw12506step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3048 node3048Labels := by rfl

def raw12507 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12507step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12507step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12507step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12507 raw12507Labels = mixedMoment B node3184 node3184Labels := by
  calc
    mixedMoment B raw12507 raw12507Labels = mixedMoment B raw12507step0 raw12507step0Labels := by
      have hz : ∀ j, raw12507 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12507step0 = (fun i j => raw12507 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12507step0 raw12507; decide +kernel
      have hl : raw12507step0Labels = raw12507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12507 raw12507Labels permutation265 hz
    mixedMoment B raw12507step0 raw12507step0Labels = mixedMoment B raw12507step1 raw12507step1Labels := by
      have ha : raw12507step1 = (fun i j => raw12507step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12507step1 raw12507step0; decide +kernel
      have hl : raw12507step1Labels = raw12507step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12507step0 raw12507step0Labels permutation40 permutation5
    mixedMoment B raw12507step1 raw12507step1Labels = mixedMoment B raw12507step2 raw12507step2Labels := by
      have ha : raw12507step2 = -raw12507step1 := by apply Matrix.ext; change ∀ i j, raw12507step2 i j = -(raw12507step1 i j); unfold raw12507step2 raw12507step1; decide +kernel
      have hl : raw12507step2Labels = raw12507step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12507step2 raw12507step2Labels = mixedMoment B raw12507step3 raw12507step3Labels := by
      have ha : raw12507step3 = raw12507step2 := by apply Matrix.ext; unfold raw12507step3 raw12507step2; decide +kernel
      have hl : raw12507step2Labels = labelEmbedding1 ∘ raw12507step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12507step2 raw12507step2Labels raw12507step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3184 node3184Labels := by rfl

def raw12508 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12508step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12508 raw12508Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw12508 raw12508Labels = mixedMoment B raw12508step0 raw12508step0Labels := by
      have hz : ∀ j, raw12508 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12508step0 = (fun i j => raw12508 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12508step0 raw12508; decide +kernel
      have hl : raw12508step0Labels = raw12508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12508 raw12508Labels permutation265 hz
    mixedMoment B raw12508step0 raw12508step0Labels = mixedMoment B raw12508step1 raw12508step1Labels := by
      have ha : raw12508step1 = (fun i j => raw12508step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12508step1 raw12508step0; decide +kernel
      have hl : raw12508step1Labels = raw12508step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12508step0 raw12508step0Labels permutation37 permutation7
    mixedMoment B raw12508step1 raw12508step1Labels = mixedMoment B raw12508step2 raw12508step2Labels := by
      have ha : raw12508step2 = raw12508step1 := by apply Matrix.ext; unfold raw12508step2 raw12508step1; decide +kernel
      have hl : raw12508step1Labels = labelEmbedding1 ∘ raw12508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12508step1 raw12508step1Labels raw12508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3096 node3096Labels := by rfl

def raw12509 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12509 raw12509Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw12509 raw12509Labels = mixedMoment B raw12509step0 raw12509step0Labels := by
      have hz : ∀ j, raw12509 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12509step0 = (fun i j => raw12509 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12509step0 raw12509; decide +kernel
      have hl : raw12509step0Labels = raw12509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12509 raw12509Labels permutation265 hz
    mixedMoment B raw12509step0 raw12509step0Labels = mixedMoment B raw12509step1 raw12509step1Labels := by
      have ha : raw12509step1 = (fun i j => raw12509step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12509step1 raw12509step0; decide +kernel
      have hl : raw12509step1Labels = raw12509step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12509step0 raw12509step0Labels permutation35 permutation7
    mixedMoment B raw12509step1 raw12509step1Labels = mixedMoment B raw12509step2 raw12509step2Labels := by
      have ha : raw12509step2 = raw12509step1 := by apply Matrix.ext; unfold raw12509step2 raw12509step1; decide +kernel
      have hl : raw12509step1Labels = labelEmbedding1 ∘ raw12509step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12509step1 raw12509step1Labels raw12509step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw12510 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw12510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw12510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12510 raw12510Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw12510 raw12510Labels = mixedMoment B raw12510step0 raw12510step0Labels := by
      have hz : ∀ j, raw12510 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12510step0 = (fun i j => raw12510 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12510step0 raw12510; decide +kernel
      have hl : raw12510step0Labels = raw12510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12510 raw12510Labels permutation265 hz
    mixedMoment B raw12510step0 raw12510step0Labels = mixedMoment B raw12510step1 raw12510step1Labels := by
      have ha : raw12510step1 = (fun i j => raw12510step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12510step1 raw12510step0; decide +kernel
      have hl : raw12510step1Labels = raw12510step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12510step0 raw12510step0Labels permutation139 permutation5
    mixedMoment B raw12510step1 raw12510step1Labels = mixedMoment B raw12510step2 raw12510step2Labels := by
      have ha : raw12510step2 = raw12510step1 := by apply Matrix.ext; unfold raw12510step2 raw12510step1; decide +kernel
      have hl : raw12510step1Labels = labelEmbedding1 ∘ raw12510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12510step1 raw12510step1Labels raw12510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw12511 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw12511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw12511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12511 raw12511Labels = mixedMoment B node2487 node2487Labels := by
  calc
    mixedMoment B raw12511 raw12511Labels = mixedMoment B raw12511step0 raw12511step0Labels := by
      have hz : ∀ j, raw12511 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12511step0 = (fun i j => raw12511 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12511step0 raw12511; decide +kernel
      have hl : raw12511step0Labels = raw12511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12511 raw12511Labels permutation265 hz
    mixedMoment B raw12511step0 raw12511step0Labels = mixedMoment B raw12511step1 raw12511step1Labels := by
      have ha : raw12511step1 = (fun i j => raw12511step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12511step1 raw12511step0; decide +kernel
      have hl : raw12511step1Labels = raw12511step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12511step0 raw12511step0Labels permutation138 permutation5
    mixedMoment B raw12511step1 raw12511step1Labels = mixedMoment B raw12511step2 raw12511step2Labels := by
      have ha : raw12511step2 = raw12511step1 := by apply Matrix.ext; unfold raw12511step2 raw12511step1; decide +kernel
      have hl : raw12511step1Labels = labelEmbedding1 ∘ raw12511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12511step1 raw12511step1Labels raw12511step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2487 node2487Labels := by rfl

def raw12512 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12512step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw12512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw12512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12512 raw12512Labels = mixedMoment B node2518 node2518Labels := by
  calc
    mixedMoment B raw12512 raw12512Labels = mixedMoment B raw12512step0 raw12512step0Labels := by
      have hz : ∀ j, raw12512 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12512step0 = (fun i j => raw12512 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12512step0 raw12512; decide +kernel
      have hl : raw12512step0Labels = raw12512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12512 raw12512Labels permutation265 hz
    mixedMoment B raw12512step0 raw12512step0Labels = mixedMoment B raw12512step1 raw12512step1Labels := by
      have ha : raw12512step1 = (fun i j => raw12512step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12512step1 raw12512step0; decide +kernel
      have hl : raw12512step1Labels = raw12512step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12512step0 raw12512step0Labels permutation137 permutation5
    mixedMoment B raw12512step1 raw12512step1Labels = mixedMoment B raw12512step2 raw12512step2Labels := by
      have ha : raw12512step2 = raw12512step1 := by apply Matrix.ext; unfold raw12512step2 raw12512step1; decide +kernel
      have hl : raw12512step1Labels = labelEmbedding1 ∘ raw12512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12512step1 raw12512step1Labels raw12512step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2518 node2518Labels := by rfl

def raw12513 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12513 raw12513Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw12513 raw12513Labels = mixedMoment B raw12513step0 raw12513step0Labels := by
      have hz : ∀ j, raw12513 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12513step0 = (fun i j => raw12513 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12513step0 raw12513; decide +kernel
      have hl : raw12513step0Labels = raw12513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12513 raw12513Labels permutation265 hz
    mixedMoment B raw12513step0 raw12513step0Labels = mixedMoment B raw12513step1 raw12513step1Labels := by
      have ha : raw12513step1 = (fun i j => raw12513step0 (permutation97 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12513step1 raw12513step0; decide +kernel
      have hl : raw12513step1Labels = raw12513step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12513step0 raw12513step0Labels permutation97 permutation2
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw12514 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12514 raw12514Labels = mixedMoment B node3507 node3507Labels := by
  calc
    mixedMoment B raw12514 raw12514Labels = mixedMoment B raw12514step0 raw12514step0Labels := by
      have hz : ∀ j, raw12514 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12514step0 = (fun i j => raw12514 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12514step0 raw12514; decide +kernel
      have hl : raw12514step0Labels = raw12514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12514 raw12514Labels permutation265 hz
    mixedMoment B raw12514step0 raw12514step0Labels = mixedMoment B raw12514step1 raw12514step1Labels := by
      have ha : raw12514step1 = (fun i j => raw12514step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12514step1 raw12514step0; decide +kernel
      have hl : raw12514step1Labels = raw12514step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12514step0 raw12514step0Labels permutation36 permutation2
    mixedMoment B raw12514step1 raw12514step1Labels = mixedMoment B raw12514step2 raw12514step2Labels := by
      have ha : raw12514step2 = -raw12514step1 := by apply Matrix.ext; change ∀ i j, raw12514step2 i j = -(raw12514step1 i j); unfold raw12514step2 raw12514step1; decide +kernel
      have hl : raw12514step2Labels = raw12514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3507 node3507Labels := by rfl

def raw12515 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12515 raw12515Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw12515 raw12515Labels = mixedMoment B raw12515step0 raw12515step0Labels := by
      have hz : ∀ j, raw12515 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12515step0 = (fun i j => raw12515 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12515step0 raw12515; decide +kernel
      have hl : raw12515step0Labels = raw12515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12515 raw12515Labels permutation265 hz
    mixedMoment B raw12515step0 raw12515step0Labels = mixedMoment B raw12515step1 raw12515step1Labels := by
      have ha : raw12515step1 = (fun i j => raw12515step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12515step1 raw12515step0; decide +kernel
      have hl : raw12515step1Labels = raw12515step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12515step0 raw12515step0Labels permutation37 permutation2
    mixedMoment B raw12515step1 raw12515step1Labels = mixedMoment B raw12515step2 raw12515step2Labels := by
      have ha : raw12515step2 = -raw12515step1 := by apply Matrix.ext; change ∀ i j, raw12515step2 i j = -(raw12515step1 i j); unfold raw12515step2 raw12515step1; decide +kernel
      have hl : raw12515step2Labels = raw12515step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw12516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw12516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12516 raw12516Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw12516 raw12516Labels = mixedMoment B raw12516step0 raw12516step0Labels := by
      have ha : raw12516step0 = (fun i j => raw12516 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12516step0 raw12516; decide +kernel
      have hl : raw12516step0Labels = raw12516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12516 raw12516Labels permutation212 permutation4
    mixedMoment B raw12516step0 raw12516step0Labels = mixedMoment B raw12516step1 raw12516step1Labels := by
      have ha : raw12516step1 = -raw12516step0 := by apply Matrix.ext; change ∀ i j, raw12516step1 i j = -(raw12516step0 i j); unfold raw12516step1 raw12516step0; decide +kernel
      have hl : raw12516step1Labels = raw12516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2088 node2088Labels := by rfl

def raw12517 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12517 raw12517Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw12517 raw12517Labels = mixedMoment B raw12517step0 raw12517step0Labels := by
      have hz : ∀ j, raw12517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12517step0 = (fun i j => raw12517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12517step0 raw12517; decide +kernel
      have hl : raw12517step0Labels = raw12517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12517 raw12517Labels permutation346 hz
    mixedMoment B raw12517step0 raw12517step0Labels = mixedMoment B raw12517step1 raw12517step1Labels := by
      have ha : raw12517step1 = (fun i j => raw12517step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12517step1 raw12517step0; decide +kernel
      have hl : raw12517step1Labels = raw12517step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12517step0 raw12517step0Labels permutation40 permutation4
    mixedMoment B raw12517step1 raw12517step1Labels = mixedMoment B raw12517step2 raw12517step2Labels := by
      have ha : raw12517step2 = -raw12517step1 := by apply Matrix.ext; change ∀ i j, raw12517step2 i j = -(raw12517step1 i j); unfold raw12517step2 raw12517step1; decide +kernel
      have hl : raw12517step2Labels = raw12517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw12518 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw12518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12518 raw12518Labels = mixedMoment B node2950 node2950Labels := by
  calc
    mixedMoment B raw12518 raw12518Labels = mixedMoment B raw12518step0 raw12518step0Labels := by
      have ha : raw12518step0 = (fun i j => raw12518 (permutation502 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12518step0 raw12518; decide +kernel
      have hl : raw12518step0Labels = raw12518Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12518 raw12518Labels permutation502 permutation2
    _ = mixedMoment B node2950 node2950Labels := by rfl

def raw12519 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw12519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12519 raw12519Labels = mixedMoment B node3550 node3550Labels := by
  calc
    mixedMoment B raw12519 raw12519Labels = mixedMoment B raw12519step0 raw12519step0Labels := by
      have ha : raw12519step0 = (fun i j => raw12519 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12519step0 raw12519; decide +kernel
      have hl : raw12519step0Labels = raw12519Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12519 raw12519Labels permutation212 permutation4
    mixedMoment B raw12519step0 raw12519step0Labels = mixedMoment B raw12519step1 raw12519step1Labels := by
      have ha : raw12519step1 = -raw12519step0 := by apply Matrix.ext; change ∀ i j, raw12519step1 i j = -(raw12519step0 i j); unfold raw12519step1 raw12519step0; decide +kernel
      have hl : raw12519step1Labels = raw12519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3550 node3550Labels := by rfl

def raw12520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12520 raw12520Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw12520 raw12520Labels = mixedMoment B raw12520step0 raw12520step0Labels := by
      have ha : raw12520step0 = (fun i j => raw12520 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12520step0 raw12520; decide +kernel
      have hl : raw12520step0Labels = raw12520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12520 raw12520Labels permutation212 permutation4
    mixedMoment B raw12520step0 raw12520step0Labels = mixedMoment B raw12520step1 raw12520step1Labels := by
      have ha : raw12520step1 = -raw12520step0 := by apply Matrix.ext; change ∀ i j, raw12520step1 i j = -(raw12520step0 i j); unfold raw12520step1 raw12520step0; decide +kernel
      have hl : raw12520step1Labels = raw12520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw12521 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw12521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw12521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12521 raw12521Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw12521 raw12521Labels = mixedMoment B raw12521step0 raw12521step0Labels := by
      have hz : ∀ j, raw12521 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12521step0 = (fun i j => raw12521 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12521step0 raw12521; decide +kernel
      have hl : raw12521step0Labels = raw12521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12521 raw12521Labels permutation265 hz
    mixedMoment B raw12521step0 raw12521step0Labels = mixedMoment B raw12521step1 raw12521step1Labels := by
      have ha : raw12521step1 = (fun i j => raw12521step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12521step1 raw12521step0; decide +kernel
      have hl : raw12521step1Labels = raw12521step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12521step0 raw12521step0Labels permutation40 permutation4
    mixedMoment B raw12521step1 raw12521step1Labels = mixedMoment B raw12521step2 raw12521step2Labels := by
      have ha : raw12521step2 = -raw12521step1 := by apply Matrix.ext; change ∀ i j, raw12521step2 i j = -(raw12521step1 i j); unfold raw12521step2 raw12521step1; decide +kernel
      have hl : raw12521step2Labels = raw12521step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw12522 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw12522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12522 raw12522Labels = mixedMoment B node2956 node2956Labels := by
  calc
    mixedMoment B raw12522 raw12522Labels = mixedMoment B raw12522step0 raw12522step0Labels := by
      have hz : ∀ j, raw12522 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12522step0 = (fun i j => raw12522 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12522step0 raw12522; decide +kernel
      have hl : raw12522step0Labels = raw12522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12522 raw12522Labels permutation265 hz
    mixedMoment B raw12522step0 raw12522step0Labels = mixedMoment B raw12522step1 raw12522step1Labels := by
      have ha : raw12522step1 = (fun i j => raw12522step0 (permutation96 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12522step1 raw12522step0; decide +kernel
      have hl : raw12522step1Labels = raw12522step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12522step0 raw12522step0Labels permutation96 permutation2
    _ = mixedMoment B node2956 node2956Labels := by rfl

def raw12523 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw12523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw12523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12523 raw12523Labels = mixedMoment B node3552 node3552Labels := by
  calc
    mixedMoment B raw12523 raw12523Labels = mixedMoment B raw12523step0 raw12523step0Labels := by
      have hz : ∀ j, raw12523 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12523step0 = (fun i j => raw12523 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12523step0 raw12523; decide +kernel
      have hl : raw12523step0Labels = raw12523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12523 raw12523Labels permutation265 hz
    mixedMoment B raw12523step0 raw12523step0Labels = mixedMoment B raw12523step1 raw12523step1Labels := by
      have ha : raw12523step1 = (fun i j => raw12523step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12523step1 raw12523step0; decide +kernel
      have hl : raw12523step1Labels = raw12523step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12523step0 raw12523step0Labels permutation40 permutation4
    mixedMoment B raw12523step1 raw12523step1Labels = mixedMoment B raw12523step2 raw12523step2Labels := by
      have ha : raw12523step2 = -raw12523step1 := by apply Matrix.ext; change ∀ i j, raw12523step2 i j = -(raw12523step1 i j); unfold raw12523step2 raw12523step1; decide +kernel
      have hl : raw12523step2Labels = raw12523step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3552 node3552Labels := by rfl

def raw12524 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12524 raw12524Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw12524 raw12524Labels = mixedMoment B raw12524step0 raw12524step0Labels := by
      have hz : ∀ j, raw12524 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12524step0 = (fun i j => raw12524 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12524step0 raw12524; decide +kernel
      have hl : raw12524step0Labels = raw12524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12524 raw12524Labels permutation265 hz
    mixedMoment B raw12524step0 raw12524step0Labels = mixedMoment B raw12524step1 raw12524step1Labels := by
      have ha : raw12524step1 = (fun i j => raw12524step0 (permutation97 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12524step1 raw12524step0; decide +kernel
      have hl : raw12524step1Labels = raw12524step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12524step0 raw12524step0Labels permutation97 permutation2
    _ = mixedMoment B node3096 node3096Labels := by rfl

def raw12525 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw12525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12525 raw12525Labels = mixedMoment B node2962 node2962Labels := by
  calc
    mixedMoment B raw12525 raw12525Labels = mixedMoment B raw12525step0 raw12525step0Labels := by
      have hz : ∀ j, raw12525 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12525step0 = (fun i j => raw12525 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12525step0 raw12525; decide +kernel
      have hl : raw12525step0Labels = raw12525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12525 raw12525Labels permutation265 hz
    mixedMoment B raw12525step0 raw12525step0Labels = mixedMoment B raw12525step1 raw12525step1Labels := by
      have ha : raw12525step1 = (fun i j => raw12525step0 (permutation94 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12525step1 raw12525step0; decide +kernel
      have hl : raw12525step1Labels = raw12525step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12525step0 raw12525step0Labels permutation94 permutation2
    _ = mixedMoment B node2962 node2962Labels := by rfl

def raw12526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12526 raw12526Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw12526 raw12526Labels = mixedMoment B raw12526step0 raw12526step0Labels := by
      have hz : ∀ j, raw12526 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12526step0 = (fun i j => raw12526 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12526step0 raw12526; decide +kernel
      have hl : raw12526step0Labels = raw12526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12526 raw12526Labels permutation265 hz
    mixedMoment B raw12526step0 raw12526step0Labels = mixedMoment B raw12526step1 raw12526step1Labels := by
      have ha : raw12526step1 = (fun i j => raw12526step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12526step1 raw12526step0; decide +kernel
      have hl : raw12526step1Labels = raw12526step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12526step0 raw12526step0Labels permutation38 permutation4
    mixedMoment B raw12526step1 raw12526step1Labels = mixedMoment B raw12526step2 raw12526step2Labels := by
      have ha : raw12526step2 = -raw12526step1 := by apply Matrix.ext; change ∀ i j, raw12526step2 i j = -(raw12526step1 i j); unfold raw12526step2 raw12526step1; decide +kernel
      have hl : raw12526step2Labels = raw12526step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw12527 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12527 raw12527Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw12527 raw12527Labels = mixedMoment B raw12527step0 raw12527step0Labels := by
      have hz : ∀ j, raw12527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12527step0 = (fun i j => raw12527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12527step0 raw12527; decide +kernel
      have hl : raw12527step0Labels = raw12527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12527 raw12527Labels permutation346 hz
    mixedMoment B raw12527step0 raw12527step0Labels = mixedMoment B raw12527step1 raw12527step1Labels := by
      have hz : ∀ j, raw12527step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12527step1 = (fun i j => raw12527step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12527step1 raw12527step0; decide +kernel
      have hl : raw12527step1Labels = raw12527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12527step0 raw12527step0Labels permutation56 hz
    mixedMoment B raw12527step1 raw12527step1Labels = mixedMoment B raw12527step2 raw12527step2Labels := by
      have ha : raw12527step2 = (fun i j => raw12527step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12527step2 raw12527step1; decide +kernel
      have hl : raw12527step2Labels = raw12527step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12527step1 raw12527step1Labels permutation8 permutation4
    mixedMoment B raw12527step2 raw12527step2Labels = mixedMoment B raw12527step3 raw12527step3Labels := by
      have ha : raw12527step3 = -raw12527step2 := by apply Matrix.ext; change ∀ i j, raw12527step3 i j = -(raw12527step2 i j); unfold raw12527step3 raw12527step2; decide +kernel
      have hl : raw12527step3Labels = raw12527step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw12528 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw12528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12528 raw12528Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw12528 raw12528Labels = mixedMoment B raw12528step0 raw12528step0Labels := by
      have hz : ∀ j, raw12528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12528step0 = (fun i j => raw12528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12528step0 raw12528; decide +kernel
      have hl : raw12528step0Labels = raw12528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12528 raw12528Labels permutation265 hz
    mixedMoment B raw12528step0 raw12528step0Labels = mixedMoment B raw12528step1 raw12528step1Labels := by
      have ha : raw12528step1 = (fun i j => raw12528step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12528step1 raw12528step0; decide +kernel
      have hl : raw12528step1Labels = raw12528step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12528step0 raw12528step0Labels permutation38 permutation4
    mixedMoment B raw12528step1 raw12528step1Labels = mixedMoment B raw12528step2 raw12528step2Labels := by
      have ha : raw12528step2 = -raw12528step1 := by apply Matrix.ext; change ∀ i j, raw12528step2 i j = -(raw12528step1 i j); unfold raw12528step2 raw12528step1; decide +kernel
      have hl : raw12528step2Labels = raw12528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw12529 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12529 raw12529Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw12529 raw12529Labels = mixedMoment B raw12529step0 raw12529step0Labels := by
      have hz : ∀ j, raw12529 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12529step0 = (fun i j => raw12529 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12529step0 raw12529; decide +kernel
      have hl : raw12529step0Labels = raw12529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12529 raw12529Labels permutation265 hz
    mixedMoment B raw12529step0 raw12529step0Labels = mixedMoment B raw12529step1 raw12529step1Labels := by
      have ha : raw12529step1 = (fun i j => raw12529step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12529step1 raw12529step0; decide +kernel
      have hl : raw12529step1Labels = raw12529step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12529step0 raw12529step0Labels permutation46 permutation4
    mixedMoment B raw12529step1 raw12529step1Labels = mixedMoment B raw12529step2 raw12529step2Labels := by
      have ha : raw12529step2 = -raw12529step1 := by apply Matrix.ext; change ∀ i j, raw12529step2 i j = -(raw12529step1 i j); unfold raw12529step2 raw12529step1; decide +kernel
      have hl : raw12529step2Labels = raw12529step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw12530 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw12530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12530 raw12530Labels = mixedMoment B node2995 node2995Labels := by
  calc
    mixedMoment B raw12530 raw12530Labels = mixedMoment B raw12530step0 raw12530step0Labels := by
      have hz : ∀ j, raw12530 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12530step0 = (fun i j => raw12530 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12530step0 raw12530; decide +kernel
      have hl : raw12530step0Labels = raw12530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12530 raw12530Labels permutation265 hz
    mixedMoment B raw12530step0 raw12530step0Labels = mixedMoment B raw12530step1 raw12530step1Labels := by
      have ha : raw12530step1 = (fun i j => raw12530step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12530step1 raw12530step0; decide +kernel
      have hl : raw12530step1Labels = raw12530step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12530step0 raw12530step0Labels permutation137 permutation4
    _ = mixedMoment B node2995 node2995Labels := by rfl

def raw12531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12531 raw12531Labels = mixedMoment B node5433 node5433Labels := by
  calc
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw12532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12532 raw12532Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw12532 raw12532Labels = mixedMoment B raw12532step0 raw12532step0Labels := by
      have hz : ∀ j, raw12532 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12532step0 = (fun i j => raw12532 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12532step0 raw12532; decide +kernel
      have hl : raw12532step0Labels = raw12532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12532 raw12532Labels permutation265 hz
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw12533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12533 raw12533Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw12533 raw12533Labels = mixedMoment B raw12533step0 raw12533step0Labels := by
      have hz : ∀ j, raw12533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12533step0 = (fun i j => raw12533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12533step0 raw12533; decide +kernel
      have hl : raw12533step0Labels = raw12533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12533 raw12533Labels permutation434 hz
    mixedMoment B raw12533step0 raw12533step0Labels = mixedMoment B raw12533step1 raw12533step1Labels := by
      have hz : ∀ j, raw12533step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12533step1 = (fun i j => raw12533step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12533step1 raw12533step0; decide +kernel
      have hl : raw12533step1Labels = raw12533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12533step0 raw12533step0Labels permutation56 hz
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw12534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12534 raw12534Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw12534 raw12534Labels = mixedMoment B raw12534step0 raw12534step0Labels := by
      have hz : ∀ j, raw12534 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12534step0 = (fun i j => raw12534 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12534step0 raw12534; decide +kernel
      have hl : raw12534step0Labels = raw12534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12534 raw12534Labels permutation520 hz
    mixedMoment B raw12534step0 raw12534step0Labels = mixedMoment B raw12534step1 raw12534step1Labels := by
      have hz : ∀ j, raw12534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12534step1 = (fun i j => raw12534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12534step1 raw12534step0; decide +kernel
      have hl : raw12534step1Labels = raw12534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12534step0 raw12534step0Labels permutation56 hz
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw12535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw12535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12535 raw12535Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw12535 raw12535Labels = mixedMoment B raw12535step0 raw12535step0Labels := by
      have hz : ∀ j, raw12535 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12535step0 = (fun i j => raw12535 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12535step0 raw12535; decide +kernel
      have hl : raw12535step0Labels = raw12535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12535 raw12535Labels permutation265 hz
    mixedMoment B raw12535step0 raw12535step0Labels = mixedMoment B raw12535step1 raw12535step1Labels := by
      have ha : raw12535step1 = (fun i j => raw12535step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12535step1 raw12535step0; decide +kernel
      have hl : raw12535step1Labels = raw12535step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12535step0 raw12535step0Labels permutation36 permutation2
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw12536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12536step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12536 raw12536Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw12536 raw12536Labels = mixedMoment B raw12536step0 raw12536step0Labels := by
      have ha : raw12536step0 = (fun i j => raw12536 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12536step0 raw12536; decide +kernel
      have hl : raw12536step0Labels = raw12536Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12536 raw12536Labels permutation194 permutation3
    mixedMoment B raw12536step0 raw12536step0Labels = mixedMoment B raw12536step1 raw12536step1Labels := by
      have ha : raw12536step1 = raw12536step0 := by apply Matrix.ext; unfold raw12536step1 raw12536step0; decide +kernel
      have hl : raw12536step0Labels = labelEmbedding6 ∘ raw12536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12536step0 raw12536step0Labels raw12536step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw12537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12537 raw12537Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw12537 raw12537Labels = mixedMoment B raw12537step0 raw12537step0Labels := by
      have ha : raw12537step0 = (fun i j => raw12537 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12537step0 raw12537; decide +kernel
      have hl : raw12537step0Labels = raw12537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12537 raw12537Labels permutation176 permutation2
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw12538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12538 raw12538Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12538 raw12538Labels = mixedMoment B raw12538step0 raw12538step0Labels := by
      have hz : ∀ j, raw12538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12538step0 = (fun i j => raw12538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12538step0 raw12538; decide +kernel
      have hl : raw12538step0Labels = raw12538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12538 raw12538Labels permutation434 hz
    mixedMoment B raw12538step0 raw12538step0Labels = mixedMoment B raw12538step1 raw12538step1Labels := by
      have ha : raw12538step1 = (fun i j => raw12538step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12538step1 raw12538step0; decide +kernel
      have hl : raw12538step1Labels = raw12538step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12538step0 raw12538step0Labels permutation38 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw12539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12539 raw12539Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12539 raw12539Labels = mixedMoment B raw12539step0 raw12539step0Labels := by
      have hz : ∀ j, raw12539 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12539step0 = (fun i j => raw12539 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12539step0 raw12539; decide +kernel
      have hl : raw12539step0Labels = raw12539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12539 raw12539Labels permutation520 hz
    mixedMoment B raw12539step0 raw12539step0Labels = mixedMoment B raw12539step1 raw12539step1Labels := by
      have ha : raw12539step1 = (fun i j => raw12539step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12539step1 raw12539step0; decide +kernel
      have hl : raw12539step1Labels = raw12539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12539step0 raw12539step0Labels permutation38 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw12540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12540 raw12540Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw12540 raw12540Labels = mixedMoment B raw12540step0 raw12540step0Labels := by
      have ha : raw12540step0 = (fun i j => raw12540 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12540step0 raw12540; decide +kernel
      have hl : raw12540step0Labels = raw12540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12540 raw12540Labels permutation194 permutation2
    _ = mixedMoment B node5283 node5283Labels := by rfl

def raw12541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12541 raw12541Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw12541 raw12541Labels = mixedMoment B raw12541step0 raw12541step0Labels := by
      have hz : ∀ j, raw12541 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12541step0 = (fun i j => raw12541 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12541step0 raw12541; decide +kernel
      have hl : raw12541step0Labels = raw12541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12541 raw12541Labels permutation265 hz
    mixedMoment B raw12541step0 raw12541step0Labels = mixedMoment B raw12541step1 raw12541step1Labels := by
      have ha : raw12541step1 = (fun i j => raw12541step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12541step1 raw12541step0; decide +kernel
      have hl : raw12541step1Labels = raw12541step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12541step0 raw12541step0Labels permutation40 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw12542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12542 raw12542Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw12542 raw12542Labels = mixedMoment B raw12542step0 raw12542step0Labels := by
      have ha : raw12542step0 = (fun i j => raw12542 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12542step0 raw12542; decide +kernel
      have hl : raw12542step0Labels = raw12542Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12542 raw12542Labels permutation160 permutation2
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw12543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12543 raw12543Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12543 raw12543Labels = mixedMoment B raw12543step0 raw12543step0Labels := by
      have hz : ∀ j, raw12543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12543step0 = (fun i j => raw12543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12543step0 raw12543; decide +kernel
      have hl : raw12543step0Labels = raw12543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12543 raw12543Labels permutation434 hz
    mixedMoment B raw12543step0 raw12543step0Labels = mixedMoment B raw12543step1 raw12543step1Labels := by
      have hz : ∀ j, raw12543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12543step1 = (fun i j => raw12543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12543step1 raw12543step0; decide +kernel
      have hl : raw12543step1Labels = raw12543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12543step0 raw12543step0Labels permutation56 hz
    mixedMoment B raw12543step1 raw12543step1Labels = mixedMoment B raw12543step2 raw12543step2Labels := by
      have ha : raw12543step2 = (fun i j => raw12543step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12543step2 raw12543step1; decide +kernel
      have hl : raw12543step2Labels = raw12543step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12543step1 raw12543step1Labels permutation10 permutation2
    _ = mixedMoment B node5307 node5307Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
