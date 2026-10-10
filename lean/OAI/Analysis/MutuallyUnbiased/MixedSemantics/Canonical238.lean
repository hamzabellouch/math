import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30464step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30464step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30464 raw30464Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw30464 raw30464Labels = mixedMoment B raw30464step0 raw30464step0Labels := by
      have hz : ∀ j, raw30464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30464step0 = (fun i j => raw30464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30464step0 raw30464; decide +kernel
      have hl : raw30464step0Labels = raw30464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30464 raw30464Labels permutation434 hz
    mixedMoment B raw30464step0 raw30464step0Labels = mixedMoment B raw30464step1 raw30464step1Labels := by
      have ha : raw30464step1 = (fun i j => raw30464step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30464step1 raw30464step0; decide +kernel
      have hl : raw30464step1Labels = raw30464step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30464step0 raw30464step0Labels permutation124 permutation5
    mixedMoment B raw30464step1 raw30464step1Labels = mixedMoment B raw30464step2 raw30464step2Labels := by
      have ha : raw30464step2 = raw30464step1 := by apply Matrix.ext; unfold raw30464step2 raw30464step1; decide +kernel
      have hl : raw30464step1Labels = labelEmbedding1 ∘ raw30464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30464step1 raw30464step1Labels raw30464step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw30465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30465Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30465step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30465 raw30465Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw30465 raw30465Labels = mixedMoment B raw30465step0 raw30465step0Labels := by
      have ha : raw30465step0 = (fun i j => raw30465 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30465step0 raw30465; decide +kernel
      have hl : raw30465step0Labels = raw30465Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30465 raw30465Labels permutation577 permutation5
    mixedMoment B raw30465step0 raw30465step0Labels = mixedMoment B raw30465step1 raw30465step1Labels := by
      have ha : raw30465step1 = raw30465step0 := by apply Matrix.ext; unfold raw30465step1 raw30465step0; decide +kernel
      have hl : raw30465step0Labels = labelEmbedding1 ∘ raw30465step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30465step0 raw30465step0Labels raw30465step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw30466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw30466Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw30466step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw30466step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30466step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30466step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30466step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30466 raw30466Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw30466 raw30466Labels = mixedMoment B raw30466step0 raw30466step0Labels := by
      have hz : ∀ j, raw30466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30466step0 = (fun i j => raw30466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30466step0 raw30466; decide +kernel
      have hl : raw30466step0Labels = raw30466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30466 raw30466Labels permutation434 hz
    mixedMoment B raw30466step0 raw30466step0Labels = mixedMoment B raw30466step1 raw30466step1Labels := by
      have ha : raw30466step1 = (fun i j => raw30466step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30466step1 raw30466step0; decide +kernel
      have hl : raw30466step1Labels = raw30466step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30466step0 raw30466step0Labels permutation33 permutation7
    mixedMoment B raw30466step1 raw30466step1Labels = mixedMoment B raw30466step2 raw30466step2Labels := by
      have ha : raw30466step2 = -raw30466step1 := by apply Matrix.ext; change ∀ i j, raw30466step2 i j = -(raw30466step1 i j); unfold raw30466step2 raw30466step1; decide +kernel
      have hl : raw30466step2Labels = raw30466step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30466step2 raw30466step2Labels = mixedMoment B raw30466step3 raw30466step3Labels := by
      have ha : raw30466step3 = raw30466step2 := by apply Matrix.ext; unfold raw30466step3 raw30466step2; decide +kernel
      have hl : raw30466step2Labels = labelEmbedding1 ∘ raw30466step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30466step2 raw30466step2Labels raw30466step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw30467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30467Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30467step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw30467step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30467step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30467step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30467step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30467 raw30467Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw30467 raw30467Labels = mixedMoment B raw30467step0 raw30467step0Labels := by
      have hz : ∀ j, raw30467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30467step0 = (fun i j => raw30467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30467step0 raw30467; decide +kernel
      have hl : raw30467step0Labels = raw30467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30467 raw30467Labels permutation434 hz
    mixedMoment B raw30467step0 raw30467step0Labels = mixedMoment B raw30467step1 raw30467step1Labels := by
      have ha : raw30467step1 = (fun i j => raw30467step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30467step1 raw30467step0; decide +kernel
      have hl : raw30467step1Labels = raw30467step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30467step0 raw30467step0Labels permutation32 permutation7
    mixedMoment B raw30467step1 raw30467step1Labels = mixedMoment B raw30467step2 raw30467step2Labels := by
      have ha : raw30467step2 = -raw30467step1 := by apply Matrix.ext; change ∀ i j, raw30467step2 i j = -(raw30467step1 i j); unfold raw30467step2 raw30467step1; decide +kernel
      have hl : raw30467step2Labels = raw30467step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30467step2 raw30467step2Labels = mixedMoment B raw30467step3 raw30467step3Labels := by
      have ha : raw30467step3 = raw30467step2 := by apply Matrix.ext; unfold raw30467step3 raw30467step2; decide +kernel
      have hl : raw30467step2Labels = labelEmbedding1 ∘ raw30467step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30467step2 raw30467step2Labels raw30467step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw30468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30468Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30468step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30468step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30468 raw30468Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw30468 raw30468Labels = mixedMoment B raw30468step0 raw30468step0Labels := by
      have hz : ∀ j, raw30468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30468step0 = (fun i j => raw30468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30468step0 raw30468; decide +kernel
      have hl : raw30468step0Labels = raw30468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30468 raw30468Labels permutation434 hz
    mixedMoment B raw30468step0 raw30468step0Labels = mixedMoment B raw30468step1 raw30468step1Labels := by
      have ha : raw30468step1 = (fun i j => raw30468step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30468step1 raw30468step0; decide +kernel
      have hl : raw30468step1Labels = raw30468step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30468step0 raw30468step0Labels permutation151 permutation5
    mixedMoment B raw30468step1 raw30468step1Labels = mixedMoment B raw30468step2 raw30468step2Labels := by
      have ha : raw30468step2 = raw30468step1 := by apply Matrix.ext; unfold raw30468step2 raw30468step1; decide +kernel
      have hl : raw30468step1Labels = labelEmbedding1 ∘ raw30468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30468step1 raw30468step1Labels raw30468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

def raw30469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30469Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30469step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30469step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30469 raw30469Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw30469 raw30469Labels = mixedMoment B raw30469step0 raw30469step0Labels := by
      have hz : ∀ j, raw30469 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30469step0 = (fun i j => raw30469 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30469step0 raw30469; decide +kernel
      have hl : raw30469step0Labels = raw30469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30469 raw30469Labels permutation434 hz
    mixedMoment B raw30469step0 raw30469step0Labels = mixedMoment B raw30469step1 raw30469step1Labels := by
      have ha : raw30469step1 = (fun i j => raw30469step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30469step1 raw30469step0; decide +kernel
      have hl : raw30469step1Labels = raw30469step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30469step0 raw30469step0Labels permutation148 permutation5
    mixedMoment B raw30469step1 raw30469step1Labels = mixedMoment B raw30469step2 raw30469step2Labels := by
      have ha : raw30469step2 = raw30469step1 := by apply Matrix.ext; unfold raw30469step2 raw30469step1; decide +kernel
      have hl : raw30469step1Labels = labelEmbedding1 ∘ raw30469step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30469step1 raw30469step1Labels raw30469step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw30470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30470step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30470 raw30470Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw30470 raw30470Labels = mixedMoment B raw30470step0 raw30470step0Labels := by
      have ha : raw30470step0 = (fun i j => raw30470 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30470step0 raw30470; decide +kernel
      have hl : raw30470step0Labels = raw30470Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30470 raw30470Labels permutation674 permutation5
    mixedMoment B raw30470step0 raw30470step0Labels = mixedMoment B raw30470step1 raw30470step1Labels := by
      have ha : raw30470step1 = raw30470step0 := by apply Matrix.ext; unfold raw30470step1 raw30470step0; decide +kernel
      have hl : raw30470step0Labels = labelEmbedding1 ∘ raw30470step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30470step0 raw30470step0Labels raw30470step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw30471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30471Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30471step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw30471step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30471step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30471step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30471step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30471 raw30471Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw30471 raw30471Labels = mixedMoment B raw30471step0 raw30471step0Labels := by
      have hz : ∀ j, raw30471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30471step0 = (fun i j => raw30471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30471step0 raw30471; decide +kernel
      have hl : raw30471step0Labels = raw30471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30471 raw30471Labels permutation434 hz
    mixedMoment B raw30471step0 raw30471step0Labels = mixedMoment B raw30471step1 raw30471step1Labels := by
      have ha : raw30471step1 = (fun i j => raw30471step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30471step1 raw30471step0; decide +kernel
      have hl : raw30471step1Labels = raw30471step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30471step0 raw30471step0Labels permutation32 permutation7
    mixedMoment B raw30471step1 raw30471step1Labels = mixedMoment B raw30471step2 raw30471step2Labels := by
      have ha : raw30471step2 = -raw30471step1 := by apply Matrix.ext; change ∀ i j, raw30471step2 i j = -(raw30471step1 i j); unfold raw30471step2 raw30471step1; decide +kernel
      have hl : raw30471step2Labels = raw30471step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30471step2 raw30471step2Labels = mixedMoment B raw30471step3 raw30471step3Labels := by
      have ha : raw30471step3 = raw30471step2 := by apply Matrix.ext; unfold raw30471step3 raw30471step2; decide +kernel
      have hl : raw30471step2Labels = labelEmbedding1 ∘ raw30471step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30471step2 raw30471step2Labels raw30471step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw30472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30472 raw30472Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw30472 raw30472Labels = mixedMoment B raw30472step0 raw30472step0Labels := by
      have hz : ∀ j, raw30472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30472step0 = (fun i j => raw30472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30472step0 raw30472; decide +kernel
      have hl : raw30472step0Labels = raw30472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30472 raw30472Labels permutation434 hz
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw30473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30473 raw30473Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw30473 raw30473Labels = mixedMoment B raw30473step0 raw30473step0Labels := by
      have hz : ∀ j, raw30473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30473step0 = (fun i j => raw30473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30473step0 raw30473; decide +kernel
      have hl : raw30473step0Labels = raw30473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30473 raw30473Labels permutation434 hz
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw30474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30474 raw30474Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw30474 raw30474Labels = mixedMoment B raw30474step0 raw30474step0Labels := by
      have hz : ∀ j, raw30474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30474step0 = (fun i j => raw30474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30474step0 raw30474; decide +kernel
      have hl : raw30474step0Labels = raw30474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30474 raw30474Labels permutation434 hz
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw30475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30475 raw30475Labels = mixedMoment B node2322 node2322Labels := by
  calc
    _ = mixedMoment B node2322 node2322Labels := by rfl

def raw30476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30476 raw30476Labels = mixedMoment B node2326 node2326Labels := by
  calc
    mixedMoment B raw30476 raw30476Labels = mixedMoment B raw30476step0 raw30476step0Labels := by
      have hz : ∀ j, raw30476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30476step0 = (fun i j => raw30476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30476step0 raw30476; decide +kernel
      have hl : raw30476step0Labels = raw30476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30476 raw30476Labels permutation434 hz
    mixedMoment B raw30476step0 raw30476step0Labels = mixedMoment B raw30476step1 raw30476step1Labels := by
      have ha : raw30476step1 = (fun i j => raw30476step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30476step1 raw30476step0; decide +kernel
      have hl : raw30476step1Labels = raw30476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30476step0 raw30476step0Labels permutation33 permutation2
    _ = mixedMoment B node2326 node2326Labels := by rfl

def raw30477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30477 raw30477Labels = mixedMoment B node2326 node2326Labels := by
  calc
    mixedMoment B raw30477 raw30477Labels = mixedMoment B raw30477step0 raw30477step0Labels := by
      have hz : ∀ j, raw30477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30477step0 = (fun i j => raw30477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30477step0 raw30477; decide +kernel
      have hl : raw30477step0Labels = raw30477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30477 raw30477Labels permutation434 hz
    _ = mixedMoment B node2326 node2326Labels := by rfl

def raw30478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30478step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30478step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30478step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30478 raw30478Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw30478 raw30478Labels = mixedMoment B raw30478step0 raw30478step0Labels := by
      have hz : ∀ j, raw30478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30478step0 = (fun i j => raw30478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30478step0 raw30478; decide +kernel
      have hl : raw30478step0Labels = raw30478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30478 raw30478Labels permutation434 hz
    mixedMoment B raw30478step0 raw30478step0Labels = mixedMoment B raw30478step1 raw30478step1Labels := by
      have ha : raw30478step1 = (fun i j => raw30478step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30478step1 raw30478step0; decide +kernel
      have hl : raw30478step1Labels = raw30478step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30478step0 raw30478step0Labels permutation56 permutation3
    mixedMoment B raw30478step1 raw30478step1Labels = mixedMoment B raw30478step2 raw30478step2Labels := by
      have ha : raw30478step2 = raw30478step1 := by apply Matrix.ext; unfold raw30478step2 raw30478step1; decide +kernel
      have hl : raw30478step1Labels = labelEmbedding6 ∘ raw30478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30478step1 raw30478step1Labels raw30478step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw30479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw30479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30479step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30479 raw30479Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw30479 raw30479Labels = mixedMoment B raw30479step0 raw30479step0Labels := by
      have hz : ∀ j, raw30479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30479step0 = (fun i j => raw30479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30479step0 raw30479; decide +kernel
      have hl : raw30479step0Labels = raw30479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30479 raw30479Labels permutation434 hz
    mixedMoment B raw30479step0 raw30479step0Labels = mixedMoment B raw30479step1 raw30479step1Labels := by
      have ha : raw30479step1 = (fun i j => raw30479step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30479step1 raw30479step0; decide +kernel
      have hl : raw30479step1Labels = raw30479step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30479step0 raw30479step0Labels permutation125 permutation2
    mixedMoment B raw30479step1 raw30479step1Labels = mixedMoment B raw30479step2 raw30479step2Labels := by
      have ha : raw30479step2 = -raw30479step1 := by apply Matrix.ext; change ∀ i j, raw30479step2 i j = -(raw30479step1 i j); unfold raw30479step2 raw30479step1; decide +kernel
      have hl : raw30479step2Labels = raw30479step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw30480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw30480step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30480step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30480step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30480step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30480 raw30480Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw30480 raw30480Labels = mixedMoment B raw30480step0 raw30480step0Labels := by
      have ha : raw30480step0 = (fun i j => raw30480 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30480step0 raw30480; decide +kernel
      have hl : raw30480step0Labels = raw30480Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30480 raw30480Labels permutation582 permutation3
    mixedMoment B raw30480step0 raw30480step0Labels = mixedMoment B raw30480step1 raw30480step1Labels := by
      have ha : raw30480step1 = -raw30480step0 := by apply Matrix.ext; change ∀ i j, raw30480step1 i j = -(raw30480step0 i j); unfold raw30480step1 raw30480step0; decide +kernel
      have hl : raw30480step1Labels = raw30480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30480step1 raw30480step1Labels = mixedMoment B raw30480step2 raw30480step2Labels := by
      have ha : raw30480step2 = raw30480step1 := by apply Matrix.ext; unfold raw30480step2 raw30480step1; decide +kernel
      have hl : raw30480step1Labels = labelEmbedding6 ∘ raw30480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30480step1 raw30480step1Labels raw30480step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

def raw30481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw30481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw30481step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30481 raw30481Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw30481 raw30481Labels = mixedMoment B raw30481step0 raw30481step0Labels := by
      have hz : ∀ j, raw30481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30481step0 = (fun i j => raw30481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30481step0 raw30481; decide +kernel
      have hl : raw30481step0Labels = raw30481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30481 raw30481Labels permutation434 hz
    mixedMoment B raw30481step0 raw30481step0Labels = mixedMoment B raw30481step1 raw30481step1Labels := by
      have ha : raw30481step1 = (fun i j => raw30481step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30481step1 raw30481step0; decide +kernel
      have hl : raw30481step1Labels = raw30481step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30481step0 raw30481step0Labels permutation151 permutation2
    mixedMoment B raw30481step1 raw30481step1Labels = mixedMoment B raw30481step2 raw30481step2Labels := by
      have ha : raw30481step2 = -raw30481step1 := by apply Matrix.ext; change ∀ i j, raw30481step2 i j = -(raw30481step1 i j); unfold raw30481step2 raw30481step1; decide +kernel
      have hl : raw30481step2Labels = raw30481step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw30482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw30482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw30482step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30482 raw30482Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw30482 raw30482Labels = mixedMoment B raw30482step0 raw30482step0Labels := by
      have hz : ∀ j, raw30482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30482step0 = (fun i j => raw30482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30482step0 raw30482; decide +kernel
      have hl : raw30482step0Labels = raw30482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30482 raw30482Labels permutation434 hz
    mixedMoment B raw30482step0 raw30482step0Labels = mixedMoment B raw30482step1 raw30482step1Labels := by
      have ha : raw30482step1 = (fun i j => raw30482step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30482step1 raw30482step0; decide +kernel
      have hl : raw30482step1Labels = raw30482step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30482step0 raw30482step0Labels permutation127 permutation2
    mixedMoment B raw30482step1 raw30482step1Labels = mixedMoment B raw30482step2 raw30482step2Labels := by
      have ha : raw30482step2 = -raw30482step1 := by apply Matrix.ext; change ∀ i j, raw30482step2 i j = -(raw30482step1 i j); unfold raw30482step2 raw30482step1; decide +kernel
      have hl : raw30482step2Labels = raw30482step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw30483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30483step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30483step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30483 raw30483Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw30483 raw30483Labels = mixedMoment B raw30483step0 raw30483step0Labels := by
      have hz : ∀ j, raw30483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30483step0 = (fun i j => raw30483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30483step0 raw30483; decide +kernel
      have hl : raw30483step0Labels = raw30483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30483 raw30483Labels permutation434 hz
    mixedMoment B raw30483step0 raw30483step0Labels = mixedMoment B raw30483step1 raw30483step1Labels := by
      have hz : ∀ j, raw30483step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30483step1 = (fun i j => raw30483step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30483step1 raw30483step0; decide +kernel
      have hl : raw30483step1Labels = raw30483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30483step0 raw30483step0Labels permutation56 hz
    mixedMoment B raw30483step1 raw30483step1Labels = mixedMoment B raw30483step2 raw30483step2Labels := by
      have ha : raw30483step2 = (fun i j => raw30483step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30483step2 raw30483step1; decide +kernel
      have hl : raw30483step2Labels = raw30483step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30483step1 raw30483step1Labels permutation8 permutation3
    mixedMoment B raw30483step2 raw30483step2Labels = mixedMoment B raw30483step3 raw30483step3Labels := by
      have ha : raw30483step3 = raw30483step2 := by apply Matrix.ext; unfold raw30483step3 raw30483step2; decide +kernel
      have hl : raw30483step2Labels = labelEmbedding6 ∘ raw30483step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30483step2 raw30483step2Labels raw30483step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw30484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30484step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30484step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30484step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30484 raw30484Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw30484 raw30484Labels = mixedMoment B raw30484step0 raw30484step0Labels := by
      have hz : ∀ j, raw30484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30484step0 = (fun i j => raw30484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30484step0 raw30484; decide +kernel
      have hl : raw30484step0Labels = raw30484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30484 raw30484Labels permutation434 hz
    mixedMoment B raw30484step0 raw30484step0Labels = mixedMoment B raw30484step1 raw30484step1Labels := by
      have hz : ∀ j, raw30484step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30484step1 = (fun i j => raw30484step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30484step1 raw30484step0; decide +kernel
      have hl : raw30484step1Labels = raw30484step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30484step0 raw30484step0Labels permutation56 hz
    mixedMoment B raw30484step1 raw30484step1Labels = mixedMoment B raw30484step2 raw30484step2Labels := by
      have ha : raw30484step2 = (fun i j => raw30484step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30484step2 raw30484step1; decide +kernel
      have hl : raw30484step2Labels = raw30484step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30484step1 raw30484step1Labels permutation8 permutation3
    mixedMoment B raw30484step2 raw30484step2Labels = mixedMoment B raw30484step3 raw30484step3Labels := by
      have ha : raw30484step3 = raw30484step2 := by apply Matrix.ext; unfold raw30484step3 raw30484step2; decide +kernel
      have hl : raw30484step2Labels = labelEmbedding6 ∘ raw30484step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30484step2 raw30484step2Labels raw30484step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw30485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30485 raw30485Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw30485 raw30485Labels = mixedMoment B raw30485step0 raw30485step0Labels := by
      have hz : ∀ j, raw30485 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw30485step0 = (fun i j => raw30485 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw30485step0 raw30485; decide +kernel
      have hl : raw30485step0Labels = raw30485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30485 raw30485Labels permutation265 hz
    mixedMoment B raw30485step0 raw30485step0Labels = mixedMoment B raw30485step1 raw30485step1Labels := by
      have ha : raw30485step1 = (fun i j => raw30485step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30485step1 raw30485step0; decide +kernel
      have hl : raw30485step1Labels = raw30485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30485step0 raw30485step0Labels permutation38 permutation3
    mixedMoment B raw30485step1 raw30485step1Labels = mixedMoment B raw30485step2 raw30485step2Labels := by
      have ha : raw30485step2 = raw30485step1 := by apply Matrix.ext; unfold raw30485step2 raw30485step1; decide +kernel
      have hl : raw30485step1Labels = labelEmbedding6 ∘ raw30485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30485step1 raw30485step1Labels raw30485step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw30486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw30486step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30486step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw30486step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30486 raw30486Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw30486 raw30486Labels = mixedMoment B raw30486step0 raw30486step0Labels := by
      have hz : ∀ j, raw30486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30486step0 = (fun i j => raw30486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30486step0 raw30486; decide +kernel
      have hl : raw30486step0Labels = raw30486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30486 raw30486Labels permutation434 hz
    mixedMoment B raw30486step0 raw30486step0Labels = mixedMoment B raw30486step1 raw30486step1Labels := by
      have hz : ∀ j, raw30486step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30486step1 = (fun i j => raw30486step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30486step1 raw30486step0; decide +kernel
      have hl : raw30486step1Labels = raw30486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30486step0 raw30486step0Labels permutation56 hz
    mixedMoment B raw30486step1 raw30486step1Labels = mixedMoment B raw30486step2 raw30486step2Labels := by
      have ha : raw30486step2 = (fun i j => raw30486step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30486step2 raw30486step1; decide +kernel
      have hl : raw30486step2Labels = raw30486step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30486step1 raw30486step1Labels permutation8 permutation3
    mixedMoment B raw30486step2 raw30486step2Labels = mixedMoment B raw30486step3 raw30486step3Labels := by
      have ha : raw30486step3 = raw30486step2 := by apply Matrix.ext; unfold raw30486step3 raw30486step2; decide +kernel
      have hl : raw30486step2Labels = labelEmbedding6 ∘ raw30486step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30486step2 raw30486step2Labels raw30486step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw30487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30487step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw30487step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30487step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw30487step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30487 raw30487Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw30487 raw30487Labels = mixedMoment B raw30487step0 raw30487step0Labels := by
      have hz : ∀ j, raw30487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30487step0 = (fun i j => raw30487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30487step0 raw30487; decide +kernel
      have hl : raw30487step0Labels = raw30487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30487 raw30487Labels permutation434 hz
    mixedMoment B raw30487step0 raw30487step0Labels = mixedMoment B raw30487step1 raw30487step1Labels := by
      have hz : ∀ j, raw30487step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30487step1 = (fun i j => raw30487step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30487step1 raw30487step0; decide +kernel
      have hl : raw30487step1Labels = raw30487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30487step0 raw30487step0Labels permutation56 hz
    mixedMoment B raw30487step1 raw30487step1Labels = mixedMoment B raw30487step2 raw30487step2Labels := by
      have ha : raw30487step2 = (fun i j => raw30487step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30487step2 raw30487step1; decide +kernel
      have hl : raw30487step2Labels = raw30487step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30487step1 raw30487step1Labels permutation9 permutation3
    mixedMoment B raw30487step2 raw30487step2Labels = mixedMoment B raw30487step3 raw30487step3Labels := by
      have ha : raw30487step3 = raw30487step2 := by apply Matrix.ext; unfold raw30487step3 raw30487step2; decide +kernel
      have hl : raw30487step2Labels = labelEmbedding6 ∘ raw30487step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30487step2 raw30487step2Labels raw30487step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw30488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30488step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30488step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30488 raw30488Labels = mixedMoment B node4314 node4314Labels := by
  calc
    mixedMoment B raw30488 raw30488Labels = mixedMoment B raw30488step0 raw30488step0Labels := by
      have hz : ∀ j, raw30488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30488step0 = (fun i j => raw30488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30488step0 raw30488; decide +kernel
      have hl : raw30488step0Labels = raw30488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30488 raw30488Labels permutation434 hz
    mixedMoment B raw30488step0 raw30488step0Labels = mixedMoment B raw30488step1 raw30488step1Labels := by
      have ha : raw30488step1 = (fun i j => raw30488step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30488step1 raw30488step0; decide +kernel
      have hl : raw30488step1Labels = raw30488step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30488step0 raw30488step0Labels permutation32 permutation3
    mixedMoment B raw30488step1 raw30488step1Labels = mixedMoment B raw30488step2 raw30488step2Labels := by
      have ha : raw30488step2 = raw30488step1 := by apply Matrix.ext; unfold raw30488step2 raw30488step1; decide +kernel
      have hl : raw30488step1Labels = labelEmbedding6 ∘ raw30488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30488step1 raw30488step1Labels raw30488step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4314 node4314Labels := by rfl

def raw30489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30489step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30489step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30489 raw30489Labels = mixedMoment B node4923 node4923Labels := by
  calc
    mixedMoment B raw30489 raw30489Labels = mixedMoment B raw30489step0 raw30489step0Labels := by
      have hz : ∀ j, raw30489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30489step0 = (fun i j => raw30489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30489step0 raw30489; decide +kernel
      have hl : raw30489step0Labels = raw30489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30489 raw30489Labels permutation434 hz
    mixedMoment B raw30489step0 raw30489step0Labels = mixedMoment B raw30489step1 raw30489step1Labels := by
      have ha : raw30489step1 = (fun i j => raw30489step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30489step1 raw30489step0; decide +kernel
      have hl : raw30489step1Labels = raw30489step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30489step0 raw30489step0Labels permutation32 permutation3
    mixedMoment B raw30489step1 raw30489step1Labels = mixedMoment B raw30489step2 raw30489step2Labels := by
      have ha : raw30489step2 = raw30489step1 := by apply Matrix.ext; unfold raw30489step2 raw30489step1; decide +kernel
      have hl : raw30489step1Labels = labelEmbedding6 ∘ raw30489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30489step1 raw30489step1Labels raw30489step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4923 node4923Labels := by rfl

def raw30490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30490step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30490 raw30490Labels = mixedMoment B node5031 node5031Labels := by
  calc
    mixedMoment B raw30490 raw30490Labels = mixedMoment B raw30490step0 raw30490step0Labels := by
      have ha : raw30490step0 = (fun i j => raw30490 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30490step0 raw30490; decide +kernel
      have hl : raw30490step0Labels = raw30490Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30490 raw30490Labels permutation158 permutation3
    mixedMoment B raw30490step0 raw30490step0Labels = mixedMoment B raw30490step1 raw30490step1Labels := by
      have ha : raw30490step1 = raw30490step0 := by apply Matrix.ext; unfold raw30490step1 raw30490step0; decide +kernel
      have hl : raw30490step0Labels = labelEmbedding6 ∘ raw30490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30490step0 raw30490step0Labels raw30490step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5031 node5031Labels := by rfl

def raw30491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30491step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30491step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30491 raw30491Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw30491 raw30491Labels = mixedMoment B raw30491step0 raw30491step0Labels := by
      have hz : ∀ j, raw30491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30491step0 = (fun i j => raw30491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30491step0 raw30491; decide +kernel
      have hl : raw30491step0Labels = raw30491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30491 raw30491Labels permutation434 hz
    mixedMoment B raw30491step0 raw30491step0Labels = mixedMoment B raw30491step1 raw30491step1Labels := by
      have ha : raw30491step1 = (fun i j => raw30491step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30491step1 raw30491step0; decide +kernel
      have hl : raw30491step1Labels = raw30491step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30491step0 raw30491step0Labels permutation34 permutation3
    mixedMoment B raw30491step1 raw30491step1Labels = mixedMoment B raw30491step2 raw30491step2Labels := by
      have ha : raw30491step2 = raw30491step1 := by apply Matrix.ext; unfold raw30491step2 raw30491step1; decide +kernel
      have hl : raw30491step1Labels = labelEmbedding6 ∘ raw30491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30491step1 raw30491step1Labels raw30491step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw30492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30492step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30492step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30492 raw30492Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw30492 raw30492Labels = mixedMoment B raw30492step0 raw30492step0Labels := by
      have hz : ∀ j, raw30492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30492step0 = (fun i j => raw30492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30492step0 raw30492; decide +kernel
      have hl : raw30492step0Labels = raw30492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30492 raw30492Labels permutation434 hz
    mixedMoment B raw30492step0 raw30492step0Labels = mixedMoment B raw30492step1 raw30492step1Labels := by
      have ha : raw30492step1 = (fun i j => raw30492step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30492step1 raw30492step0; decide +kernel
      have hl : raw30492step1Labels = raw30492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30492step0 raw30492step0Labels permutation36 permutation3
    mixedMoment B raw30492step1 raw30492step1Labels = mixedMoment B raw30492step2 raw30492step2Labels := by
      have ha : raw30492step2 = raw30492step1 := by apply Matrix.ext; unfold raw30492step2 raw30492step1; decide +kernel
      have hl : raw30492step1Labels = labelEmbedding6 ∘ raw30492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30492step1 raw30492step1Labels raw30492step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw30493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30493step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30493 raw30493Labels = mixedMoment B node4292 node4292Labels := by
  calc
    mixedMoment B raw30493 raw30493Labels = mixedMoment B raw30493step0 raw30493step0Labels := by
      have ha : raw30493step0 = (fun i j => raw30493 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30493step0 raw30493; decide +kernel
      have hl : raw30493step0Labels = raw30493Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30493 raw30493Labels permutation152 permutation3
    mixedMoment B raw30493step0 raw30493step0Labels = mixedMoment B raw30493step1 raw30493step1Labels := by
      have ha : raw30493step1 = raw30493step0 := by apply Matrix.ext; unfold raw30493step1 raw30493step0; decide +kernel
      have hl : raw30493step0Labels = labelEmbedding6 ∘ raw30493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30493step0 raw30493step0Labels raw30493step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4292 node4292Labels := by rfl

def raw30494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30494step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30494 raw30494Labels = mixedMoment B node4906 node4906Labels := by
  calc
    mixedMoment B raw30494 raw30494Labels = mixedMoment B raw30494step0 raw30494step0Labels := by
      have ha : raw30494step0 = (fun i j => raw30494 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30494step0 raw30494; decide +kernel
      have hl : raw30494step0Labels = raw30494Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30494 raw30494Labels permutation152 permutation3
    mixedMoment B raw30494step0 raw30494step0Labels = mixedMoment B raw30494step1 raw30494step1Labels := by
      have ha : raw30494step1 = raw30494step0 := by apply Matrix.ext; unfold raw30494step1 raw30494step0; decide +kernel
      have hl : raw30494step0Labels = labelEmbedding6 ∘ raw30494step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30494step0 raw30494step0Labels raw30494step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4906 node4906Labels := by rfl

def raw30495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30495step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30495 raw30495Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw30495 raw30495Labels = mixedMoment B raw30495step0 raw30495step0Labels := by
      have ha : raw30495step0 = (fun i j => raw30495 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30495step0 raw30495; decide +kernel
      have hl : raw30495step0Labels = raw30495Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30495 raw30495Labels permutation152 permutation3
    mixedMoment B raw30495step0 raw30495step0Labels = mixedMoment B raw30495step1 raw30495step1Labels := by
      have ha : raw30495step1 = raw30495step0 := by apply Matrix.ext; unfold raw30495step1 raw30495step0; decide +kernel
      have hl : raw30495step0Labels = labelEmbedding6 ∘ raw30495step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30495step0 raw30495step0Labels raw30495step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5039 node5039Labels := by rfl

def raw30496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30496step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30496 raw30496Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw30496 raw30496Labels = mixedMoment B raw30496step0 raw30496step0Labels := by
      have ha : raw30496step0 = (fun i j => raw30496 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30496step0 raw30496; decide +kernel
      have hl : raw30496step0Labels = raw30496Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30496 raw30496Labels permutation154 permutation3
    mixedMoment B raw30496step0 raw30496step0Labels = mixedMoment B raw30496step1 raw30496step1Labels := by
      have ha : raw30496step1 = raw30496step0 := by apply Matrix.ext; unfold raw30496step1 raw30496step0; decide +kernel
      have hl : raw30496step0Labels = labelEmbedding6 ∘ raw30496step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30496step0 raw30496step0Labels raw30496step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw30497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30497step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30497step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30497 raw30497Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw30497 raw30497Labels = mixedMoment B raw30497step0 raw30497step0Labels := by
      have ha : raw30497step0 = (fun i j => raw30497 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30497step0 raw30497; decide +kernel
      have hl : raw30497step0Labels = raw30497Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30497 raw30497Labels permutation156 permutation3
    mixedMoment B raw30497step0 raw30497step0Labels = mixedMoment B raw30497step1 raw30497step1Labels := by
      have ha : raw30497step1 = raw30497step0 := by apply Matrix.ext; unfold raw30497step1 raw30497step0; decide +kernel
      have hl : raw30497step0Labels = labelEmbedding6 ∘ raw30497step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30497step0 raw30497step0Labels raw30497step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw30498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw30498step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30498step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30498step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30498 raw30498Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw30498 raw30498Labels = mixedMoment B raw30498step0 raw30498step0Labels := by
      have hz : ∀ j, raw30498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30498step0 = (fun i j => raw30498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30498step0 raw30498; decide +kernel
      have hl : raw30498step0Labels = raw30498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30498 raw30498Labels permutation434 hz
    mixedMoment B raw30498step0 raw30498step0Labels = mixedMoment B raw30498step1 raw30498step1Labels := by
      have ha : raw30498step1 = (fun i j => raw30498step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30498step1 raw30498step0; decide +kernel
      have hl : raw30498step1Labels = raw30498step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30498step0 raw30498step0Labels permutation33 permutation3
    mixedMoment B raw30498step1 raw30498step1Labels = mixedMoment B raw30498step2 raw30498step2Labels := by
      have ha : raw30498step2 = raw30498step1 := by apply Matrix.ext; unfold raw30498step2 raw30498step1; decide +kernel
      have hl : raw30498step1Labels = labelEmbedding6 ∘ raw30498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30498step1 raw30498step1Labels raw30498step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

def raw30499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw30499step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30499step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30499step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30499 raw30499Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw30499 raw30499Labels = mixedMoment B raw30499step0 raw30499step0Labels := by
      have hz : ∀ j, raw30499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30499step0 = (fun i j => raw30499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30499step0 raw30499; decide +kernel
      have hl : raw30499step0Labels = raw30499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30499 raw30499Labels permutation434 hz
    mixedMoment B raw30499step0 raw30499step0Labels = mixedMoment B raw30499step1 raw30499step1Labels := by
      have ha : raw30499step1 = (fun i j => raw30499step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30499step1 raw30499step0; decide +kernel
      have hl : raw30499step1Labels = raw30499step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30499step0 raw30499step0Labels permutation33 permutation3
    mixedMoment B raw30499step1 raw30499step1Labels = mixedMoment B raw30499step2 raw30499step2Labels := by
      have ha : raw30499step2 = raw30499step1 := by apply Matrix.ext; unfold raw30499step2 raw30499step1; decide +kernel
      have hl : raw30499step1Labels = labelEmbedding6 ∘ raw30499step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30499step1 raw30499step1Labels raw30499step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4907 node4907Labels := by rfl

def raw30500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw30500step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30500step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30500step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30500step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30500step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30500 raw30500Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw30500 raw30500Labels = mixedMoment B raw30500step0 raw30500step0Labels := by
      have hz : ∀ j, raw30500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30500step0 = (fun i j => raw30500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30500step0 raw30500; decide +kernel
      have hl : raw30500step0Labels = raw30500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30500 raw30500Labels permutation434 hz
    mixedMoment B raw30500step0 raw30500step0Labels = mixedMoment B raw30500step1 raw30500step1Labels := by
      have ha : raw30500step1 = (fun i j => raw30500step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30500step1 raw30500step0; decide +kernel
      have hl : raw30500step1Labels = raw30500step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30500step0 raw30500step0Labels permutation127 permutation3
    mixedMoment B raw30500step1 raw30500step1Labels = mixedMoment B raw30500step2 raw30500step2Labels := by
      have ha : raw30500step2 = -raw30500step1 := by apply Matrix.ext; change ∀ i j, raw30500step2 i j = -(raw30500step1 i j); unfold raw30500step2 raw30500step1; decide +kernel
      have hl : raw30500step2Labels = raw30500step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30500step2 raw30500step2Labels = mixedMoment B raw30500step3 raw30500step3Labels := by
      have ha : raw30500step3 = raw30500step2 := by apply Matrix.ext; unfold raw30500step3 raw30500step2; decide +kernel
      have hl : raw30500step2Labels = labelEmbedding6 ∘ raw30500step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30500step2 raw30500step2Labels raw30500step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw30501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30501step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30501step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30501step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30501 raw30501Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw30501 raw30501Labels = mixedMoment B raw30501step0 raw30501step0Labels := by
      have ha : raw30501step0 = (fun i j => raw30501 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30501step0 raw30501; decide +kernel
      have hl : raw30501step0Labels = raw30501Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30501 raw30501Labels permutation582 permutation3
    mixedMoment B raw30501step0 raw30501step0Labels = mixedMoment B raw30501step1 raw30501step1Labels := by
      have ha : raw30501step1 = -raw30501step0 := by apply Matrix.ext; change ∀ i j, raw30501step1 i j = -(raw30501step0 i j); unfold raw30501step1 raw30501step0; decide +kernel
      have hl : raw30501step1Labels = raw30501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30501step1 raw30501step1Labels = mixedMoment B raw30501step2 raw30501step2Labels := by
      have ha : raw30501step2 = raw30501step1 := by apply Matrix.ext; unfold raw30501step2 raw30501step1; decide +kernel
      have hl : raw30501step1Labels = labelEmbedding6 ∘ raw30501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30501step1 raw30501step1Labels raw30501step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

def raw30502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw30502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw30502step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30502step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30502step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30502 raw30502Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw30502 raw30502Labels = mixedMoment B raw30502step0 raw30502step0Labels := by
      have hz : ∀ j, raw30502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30502step0 = (fun i j => raw30502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30502step0 raw30502; decide +kernel
      have hl : raw30502step0Labels = raw30502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30502 raw30502Labels permutation434 hz
    mixedMoment B raw30502step0 raw30502step0Labels = mixedMoment B raw30502step1 raw30502step1Labels := by
      have ha : raw30502step1 = (fun i j => raw30502step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30502step1 raw30502step0; decide +kernel
      have hl : raw30502step1Labels = raw30502step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30502step0 raw30502step0Labels permutation33 permutation3
    mixedMoment B raw30502step1 raw30502step1Labels = mixedMoment B raw30502step2 raw30502step2Labels := by
      have ha : raw30502step2 = raw30502step1 := by apply Matrix.ext; unfold raw30502step2 raw30502step1; decide +kernel
      have hl : raw30502step1Labels = labelEmbedding6 ∘ raw30502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30502step1 raw30502step1Labels raw30502step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw30503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw30503step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30503step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30503step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30503 raw30503Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw30503 raw30503Labels = mixedMoment B raw30503step0 raw30503step0Labels := by
      have hz : ∀ j, raw30503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30503step0 = (fun i j => raw30503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30503step0 raw30503; decide +kernel
      have hl : raw30503step0Labels = raw30503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30503 raw30503Labels permutation434 hz
    mixedMoment B raw30503step0 raw30503step0Labels = mixedMoment B raw30503step1 raw30503step1Labels := by
      have ha : raw30503step1 = (fun i j => raw30503step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30503step1 raw30503step0; decide +kernel
      have hl : raw30503step1Labels = raw30503step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30503step0 raw30503step0Labels permutation32 permutation3
    mixedMoment B raw30503step1 raw30503step1Labels = mixedMoment B raw30503step2 raw30503step2Labels := by
      have ha : raw30503step2 = raw30503step1 := by apply Matrix.ext; unfold raw30503step2 raw30503step1; decide +kernel
      have hl : raw30503step1Labels = labelEmbedding6 ∘ raw30503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30503step1 raw30503step1Labels raw30503step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

def raw30504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw30504step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30504step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30504step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30504 raw30504Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw30504 raw30504Labels = mixedMoment B raw30504step0 raw30504step0Labels := by
      have hz : ∀ j, raw30504 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30504step0 = (fun i j => raw30504 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30504step0 raw30504; decide +kernel
      have hl : raw30504step0Labels = raw30504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30504 raw30504Labels permutation434 hz
    mixedMoment B raw30504step0 raw30504step0Labels = mixedMoment B raw30504step1 raw30504step1Labels := by
      have ha : raw30504step1 = (fun i j => raw30504step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30504step1 raw30504step0; decide +kernel
      have hl : raw30504step1Labels = raw30504step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30504step0 raw30504step0Labels permutation32 permutation3
    mixedMoment B raw30504step1 raw30504step1Labels = mixedMoment B raw30504step2 raw30504step2Labels := by
      have ha : raw30504step2 = raw30504step1 := by apply Matrix.ext; unfold raw30504step2 raw30504step1; decide +kernel
      have hl : raw30504step1Labels = labelEmbedding6 ∘ raw30504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30504step1 raw30504step1Labels raw30504step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4907 node4907Labels := by rfl

def raw30505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw30505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30505step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30505step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30505step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30505 raw30505Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw30505 raw30505Labels = mixedMoment B raw30505step0 raw30505step0Labels := by
      have hz : ∀ j, raw30505 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30505step0 = (fun i j => raw30505 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30505step0 raw30505; decide +kernel
      have hl : raw30505step0Labels = raw30505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30505 raw30505Labels permutation434 hz
    mixedMoment B raw30505step0 raw30505step0Labels = mixedMoment B raw30505step1 raw30505step1Labels := by
      have ha : raw30505step1 = (fun i j => raw30505step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30505step1 raw30505step0; decide +kernel
      have hl : raw30505step1Labels = raw30505step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30505step0 raw30505step0Labels permutation151 permutation3
    mixedMoment B raw30505step1 raw30505step1Labels = mixedMoment B raw30505step2 raw30505step2Labels := by
      have ha : raw30505step2 = -raw30505step1 := by apply Matrix.ext; change ∀ i j, raw30505step2 i j = -(raw30505step1 i j); unfold raw30505step2 raw30505step1; decide +kernel
      have hl : raw30505step2Labels = raw30505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30505step2 raw30505step2Labels = mixedMoment B raw30505step3 raw30505step3Labels := by
      have ha : raw30505step3 = raw30505step2 := by apply Matrix.ext; unfold raw30505step3 raw30505step2; decide +kernel
      have hl : raw30505step2Labels = labelEmbedding6 ∘ raw30505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30505step2 raw30505step2Labels raw30505step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw30506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30506step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30506step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30506step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30506step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30506 raw30506Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw30506 raw30506Labels = mixedMoment B raw30506step0 raw30506step0Labels := by
      have ha : raw30506step0 = (fun i j => raw30506 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30506step0 raw30506; decide +kernel
      have hl : raw30506step0Labels = raw30506Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30506 raw30506Labels permutation680 permutation3
    mixedMoment B raw30506step0 raw30506step0Labels = mixedMoment B raw30506step1 raw30506step1Labels := by
      have ha : raw30506step1 = -raw30506step0 := by apply Matrix.ext; change ∀ i j, raw30506step1 i j = -(raw30506step0 i j); unfold raw30506step1 raw30506step0; decide +kernel
      have hl : raw30506step1Labels = raw30506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30506step1 raw30506step1Labels = mixedMoment B raw30506step2 raw30506step2Labels := by
      have ha : raw30506step2 = raw30506step1 := by apply Matrix.ext; unfold raw30506step2 raw30506step1; decide +kernel
      have hl : raw30506step1Labels = labelEmbedding6 ∘ raw30506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30506step1 raw30506step1Labels raw30506step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

def raw30507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw30507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30507step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30507step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30507 raw30507Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw30507 raw30507Labels = mixedMoment B raw30507step0 raw30507step0Labels := by
      have hz : ∀ j, raw30507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30507step0 = (fun i j => raw30507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30507step0 raw30507; decide +kernel
      have hl : raw30507step0Labels = raw30507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30507 raw30507Labels permutation434 hz
    mixedMoment B raw30507step0 raw30507step0Labels = mixedMoment B raw30507step1 raw30507step1Labels := by
      have ha : raw30507step1 = (fun i j => raw30507step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30507step1 raw30507step0; decide +kernel
      have hl : raw30507step1Labels = raw30507step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30507step0 raw30507step0Labels permutation32 permutation3
    mixedMoment B raw30507step1 raw30507step1Labels = mixedMoment B raw30507step2 raw30507step2Labels := by
      have ha : raw30507step2 = raw30507step1 := by apply Matrix.ext; unfold raw30507step2 raw30507step1; decide +kernel
      have hl : raw30507step1Labels = labelEmbedding6 ∘ raw30507step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30507step1 raw30507step1Labels raw30507step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw30508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30508 raw30508Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw30508 raw30508Labels = mixedMoment B raw30508step0 raw30508step0Labels := by
      have hz : ∀ j, raw30508 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30508step0 = (fun i j => raw30508 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30508step0 raw30508; decide +kernel
      have hl : raw30508step0Labels = raw30508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30508 raw30508Labels permutation434 hz
    mixedMoment B raw30508step0 raw30508step0Labels = mixedMoment B raw30508step1 raw30508step1Labels := by
      have ha : raw30508step1 = (fun i j => raw30508step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30508step1 raw30508step0; decide +kernel
      have hl : raw30508step1Labels = raw30508step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30508step0 raw30508step0Labels permutation56 permutation3
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw30509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw30509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30509 raw30509Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw30509 raw30509Labels = mixedMoment B raw30509step0 raw30509step0Labels := by
      have hz : ∀ j, raw30509 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30509step0 = (fun i j => raw30509 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30509step0 raw30509; decide +kernel
      have hl : raw30509step0Labels = raw30509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30509 raw30509Labels permutation434 hz
    mixedMoment B raw30509step0 raw30509step0Labels = mixedMoment B raw30509step1 raw30509step1Labels := by
      have ha : raw30509step1 = (fun i j => raw30509step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30509step1 raw30509step0; decide +kernel
      have hl : raw30509step1Labels = raw30509step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30509step0 raw30509step0Labels permutation127 permutation3
    mixedMoment B raw30509step1 raw30509step1Labels = mixedMoment B raw30509step2 raw30509step2Labels := by
      have ha : raw30509step2 = -raw30509step1 := by apply Matrix.ext; change ∀ i j, raw30509step2 i j = -(raw30509step1 i j); unfold raw30509step2 raw30509step1; decide +kernel
      have hl : raw30509step2Labels = raw30509step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw30510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw30510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30510 raw30510Labels = mixedMoment B node3921 node3921Labels := by
  calc
    mixedMoment B raw30510 raw30510Labels = mixedMoment B raw30510step0 raw30510step0Labels := by
      have ha : raw30510step0 = (fun i j => raw30510 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30510step0 raw30510; decide +kernel
      have hl : raw30510step0Labels = raw30510Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30510 raw30510Labels permutation582 permutation3
    mixedMoment B raw30510step0 raw30510step0Labels = mixedMoment B raw30510step1 raw30510step1Labels := by
      have ha : raw30510step1 = -raw30510step0 := by apply Matrix.ext; change ∀ i j, raw30510step1 i j = -(raw30510step0 i j); unfold raw30510step1 raw30510step0; decide +kernel
      have hl : raw30510step1Labels = raw30510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3921 node3921Labels := by rfl

def raw30511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw30511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30511 raw30511Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw30511 raw30511Labels = mixedMoment B raw30511step0 raw30511step0Labels := by
      have hz : ∀ j, raw30511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30511step0 = (fun i j => raw30511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30511step0 raw30511; decide +kernel
      have hl : raw30511step0Labels = raw30511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30511 raw30511Labels permutation434 hz
    mixedMoment B raw30511step0 raw30511step0Labels = mixedMoment B raw30511step1 raw30511step1Labels := by
      have ha : raw30511step1 = (fun i j => raw30511step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30511step1 raw30511step0; decide +kernel
      have hl : raw30511step1Labels = raw30511step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30511step0 raw30511step0Labels permutation32 permutation3
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw30512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw30512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30512 raw30512Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw30512 raw30512Labels = mixedMoment B raw30512step0 raw30512step0Labels := by
      have hz : ∀ j, raw30512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30512step0 = (fun i j => raw30512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30512step0 raw30512; decide +kernel
      have hl : raw30512step0Labels = raw30512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30512 raw30512Labels permutation434 hz
    mixedMoment B raw30512step0 raw30512step0Labels = mixedMoment B raw30512step1 raw30512step1Labels := by
      have ha : raw30512step1 = (fun i j => raw30512step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30512step1 raw30512step0; decide +kernel
      have hl : raw30512step1Labels = raw30512step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30512step0 raw30512step0Labels permutation33 permutation3
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw30513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30513step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30513 raw30513Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw30513 raw30513Labels = mixedMoment B raw30513step0 raw30513step0Labels := by
      have hz : ∀ j, raw30513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30513step0 = (fun i j => raw30513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30513step0 raw30513; decide +kernel
      have hl : raw30513step0Labels = raw30513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30513 raw30513Labels permutation434 hz
    mixedMoment B raw30513step0 raw30513step0Labels = mixedMoment B raw30513step1 raw30513step1Labels := by
      have hz : ∀ j, raw30513step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30513step1 = (fun i j => raw30513step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30513step1 raw30513step0; decide +kernel
      have hl : raw30513step1Labels = raw30513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30513step0 raw30513step0Labels permutation56 hz
    mixedMoment B raw30513step1 raw30513step1Labels = mixedMoment B raw30513step2 raw30513step2Labels := by
      have ha : raw30513step2 = (fun i j => raw30513step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30513step2 raw30513step1; decide +kernel
      have hl : raw30513step2Labels = raw30513step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30513step1 raw30513step1Labels permutation8 permutation3
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw30514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30514step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30514 raw30514Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw30514 raw30514Labels = mixedMoment B raw30514step0 raw30514step0Labels := by
      have hz : ∀ j, raw30514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30514step0 = (fun i j => raw30514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30514step0 raw30514; decide +kernel
      have hl : raw30514step0Labels = raw30514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30514 raw30514Labels permutation434 hz
    mixedMoment B raw30514step0 raw30514step0Labels = mixedMoment B raw30514step1 raw30514step1Labels := by
      have hz : ∀ j, raw30514step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30514step1 = (fun i j => raw30514step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30514step1 raw30514step0; decide +kernel
      have hl : raw30514step1Labels = raw30514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30514step0 raw30514step0Labels permutation56 hz
    mixedMoment B raw30514step1 raw30514step1Labels = mixedMoment B raw30514step2 raw30514step2Labels := by
      have ha : raw30514step2 = (fun i j => raw30514step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30514step2 raw30514step1; decide +kernel
      have hl : raw30514step2Labels = raw30514step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30514step1 raw30514step1Labels permutation8 permutation3
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw30515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30515 raw30515Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw30515 raw30515Labels = mixedMoment B raw30515step0 raw30515step0Labels := by
      have hz : ∀ j, raw30515 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw30515step0 = (fun i j => raw30515 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw30515step0 raw30515; decide +kernel
      have hl : raw30515step0Labels = raw30515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30515 raw30515Labels permutation265 hz
    mixedMoment B raw30515step0 raw30515step0Labels = mixedMoment B raw30515step1 raw30515step1Labels := by
      have ha : raw30515step1 = (fun i j => raw30515step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30515step1 raw30515step0; decide +kernel
      have hl : raw30515step1Labels = raw30515step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30515step0 raw30515step0Labels permutation38 permutation3
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw30516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30516step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw30516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30516 raw30516Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw30516 raw30516Labels = mixedMoment B raw30516step0 raw30516step0Labels := by
      have hz : ∀ j, raw30516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30516step0 = (fun i j => raw30516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30516step0 raw30516; decide +kernel
      have hl : raw30516step0Labels = raw30516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30516 raw30516Labels permutation434 hz
    mixedMoment B raw30516step0 raw30516step0Labels = mixedMoment B raw30516step1 raw30516step1Labels := by
      have hz : ∀ j, raw30516step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30516step1 = (fun i j => raw30516step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30516step1 raw30516step0; decide +kernel
      have hl : raw30516step1Labels = raw30516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30516step0 raw30516step0Labels permutation56 hz
    mixedMoment B raw30516step1 raw30516step1Labels = mixedMoment B raw30516step2 raw30516step2Labels := by
      have ha : raw30516step2 = (fun i j => raw30516step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30516step2 raw30516step1; decide +kernel
      have hl : raw30516step2Labels = raw30516step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30516step1 raw30516step1Labels permutation8 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw30517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30517step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30517step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw30517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30517 raw30517Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw30517 raw30517Labels = mixedMoment B raw30517step0 raw30517step0Labels := by
      have hz : ∀ j, raw30517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30517step0 = (fun i j => raw30517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30517step0 raw30517; decide +kernel
      have hl : raw30517step0Labels = raw30517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30517 raw30517Labels permutation434 hz
    mixedMoment B raw30517step0 raw30517step0Labels = mixedMoment B raw30517step1 raw30517step1Labels := by
      have hz : ∀ j, raw30517step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30517step1 = (fun i j => raw30517step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30517step1 raw30517step0; decide +kernel
      have hl : raw30517step1Labels = raw30517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30517step0 raw30517step0Labels permutation56 hz
    mixedMoment B raw30517step1 raw30517step1Labels = mixedMoment B raw30517step2 raw30517step2Labels := by
      have ha : raw30517step2 = (fun i j => raw30517step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30517step2 raw30517step1; decide +kernel
      have hl : raw30517step2Labels = raw30517step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30517step1 raw30517step1Labels permutation9 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw30518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30518step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30518 raw30518Labels = mixedMoment B node892 node892Labels := by
  calc
    mixedMoment B raw30518 raw30518Labels = mixedMoment B raw30518step0 raw30518step0Labels := by
      have hz : ∀ j, raw30518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30518step0 = (fun i j => raw30518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30518step0 raw30518; decide +kernel
      have hl : raw30518step0Labels = raw30518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30518 raw30518Labels permutation434 hz
    mixedMoment B raw30518step0 raw30518step0Labels = mixedMoment B raw30518step1 raw30518step1Labels := by
      have ha : raw30518step1 = (fun i j => raw30518step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30518step1 raw30518step0; decide +kernel
      have hl : raw30518step1Labels = raw30518step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30518step0 raw30518step0Labels permutation32 permutation3
    _ = mixedMoment B node892 node892Labels := by rfl

def raw30519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30519 raw30519Labels = mixedMoment B node2314 node2314Labels := by
  calc
    mixedMoment B raw30519 raw30519Labels = mixedMoment B raw30519step0 raw30519step0Labels := by
      have hz : ∀ j, raw30519 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30519step0 = (fun i j => raw30519 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30519step0 raw30519; decide +kernel
      have hl : raw30519step0Labels = raw30519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30519 raw30519Labels permutation434 hz
    mixedMoment B raw30519step0 raw30519step0Labels = mixedMoment B raw30519step1 raw30519step1Labels := by
      have ha : raw30519step1 = (fun i j => raw30519step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30519step1 raw30519step0; decide +kernel
      have hl : raw30519step1Labels = raw30519step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30519step0 raw30519step0Labels permutation32 permutation3
    _ = mixedMoment B node2314 node2314Labels := by rfl

def raw30520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30520 raw30520Labels = mixedMoment B node2420 node2420Labels := by
  calc
    mixedMoment B raw30520 raw30520Labels = mixedMoment B raw30520step0 raw30520step0Labels := by
      have ha : raw30520step0 = (fun i j => raw30520 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30520step0 raw30520; decide +kernel
      have hl : raw30520step0Labels = raw30520Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30520 raw30520Labels permutation158 permutation3
    _ = mixedMoment B node2420 node2420Labels := by rfl

def raw30521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30521Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30521step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30521 raw30521Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw30521 raw30521Labels = mixedMoment B raw30521step0 raw30521step0Labels := by
      have hz : ∀ j, raw30521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30521step0 = (fun i j => raw30521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30521step0 raw30521; decide +kernel
      have hl : raw30521step0Labels = raw30521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30521 raw30521Labels permutation434 hz
    mixedMoment B raw30521step0 raw30521step0Labels = mixedMoment B raw30521step1 raw30521step1Labels := by
      have ha : raw30521step1 = (fun i j => raw30521step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30521step1 raw30521step0; decide +kernel
      have hl : raw30521step1Labels = raw30521step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30521step0 raw30521step0Labels permutation34 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw30522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30522Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30522step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30522 raw30522Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw30522 raw30522Labels = mixedMoment B raw30522step0 raw30522step0Labels := by
      have hz : ∀ j, raw30522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30522step0 = (fun i j => raw30522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30522step0 raw30522; decide +kernel
      have hl : raw30522step0Labels = raw30522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30522 raw30522Labels permutation434 hz
    mixedMoment B raw30522step0 raw30522step0Labels = mixedMoment B raw30522step1 raw30522step1Labels := by
      have ha : raw30522step1 = (fun i j => raw30522step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30522step1 raw30522step0; decide +kernel
      have hl : raw30522step1Labels = raw30522step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30522step0 raw30522step0Labels permutation36 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw30523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30523Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30523 raw30523Labels = mixedMoment B node870 node870Labels := by
  calc
    mixedMoment B raw30523 raw30523Labels = mixedMoment B raw30523step0 raw30523step0Labels := by
      have ha : raw30523step0 = (fun i j => raw30523 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30523step0 raw30523; decide +kernel
      have hl : raw30523step0Labels = raw30523Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30523 raw30523Labels permutation152 permutation3
    _ = mixedMoment B node870 node870Labels := by rfl

def raw30524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30524Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30524 raw30524Labels = mixedMoment B node2299 node2299Labels := by
  calc
    mixedMoment B raw30524 raw30524Labels = mixedMoment B raw30524step0 raw30524step0Labels := by
      have ha : raw30524step0 = (fun i j => raw30524 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30524step0 raw30524; decide +kernel
      have hl : raw30524step0Labels = raw30524Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30524 raw30524Labels permutation152 permutation3
    _ = mixedMoment B node2299 node2299Labels := by rfl

def raw30525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30525 raw30525Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw30525 raw30525Labels = mixedMoment B raw30525step0 raw30525step0Labels := by
      have ha : raw30525step0 = (fun i j => raw30525 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30525step0 raw30525; decide +kernel
      have hl : raw30525step0Labels = raw30525Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30525 raw30525Labels permutation152 permutation3
    _ = mixedMoment B node2432 node2432Labels := by rfl

def raw30526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30526 raw30526Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw30526 raw30526Labels = mixedMoment B raw30526step0 raw30526step0Labels := by
      have ha : raw30526step0 = (fun i j => raw30526 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30526step0 raw30526; decide +kernel
      have hl : raw30526step0Labels = raw30526Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30526 raw30526Labels permutation154 permutation3
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw30527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30527 raw30527Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw30527 raw30527Labels = mixedMoment B raw30527step0 raw30527step0Labels := by
      have ha : raw30527step0 = (fun i j => raw30527 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30527step0 raw30527; decide +kernel
      have hl : raw30527step0Labels = raw30527Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30527 raw30527Labels permutation156 permutation3
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw30528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw30528step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30528 raw30528Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw30528 raw30528Labels = mixedMoment B raw30528step0 raw30528step0Labels := by
      have hz : ∀ j, raw30528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30528step0 = (fun i j => raw30528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30528step0 raw30528; decide +kernel
      have hl : raw30528step0Labels = raw30528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30528 raw30528Labels permutation434 hz
    mixedMoment B raw30528step0 raw30528step0Labels = mixedMoment B raw30528step1 raw30528step1Labels := by
      have ha : raw30528step1 = (fun i j => raw30528step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30528step1 raw30528step0; decide +kernel
      have hl : raw30528step1Labels = raw30528step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30528step0 raw30528step0Labels permutation33 permutation3
    _ = mixedMoment B node873 node873Labels := by rfl

def raw30529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw30529step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30529 raw30529Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw30529 raw30529Labels = mixedMoment B raw30529step0 raw30529step0Labels := by
      have hz : ∀ j, raw30529 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30529step0 = (fun i j => raw30529 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30529step0 raw30529; decide +kernel
      have hl : raw30529step0Labels = raw30529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30529 raw30529Labels permutation434 hz
    mixedMoment B raw30529step0 raw30529step0Labels = mixedMoment B raw30529step1 raw30529step1Labels := by
      have ha : raw30529step1 = (fun i j => raw30529step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30529step1 raw30529step0; decide +kernel
      have hl : raw30529step1Labels = raw30529step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30529step0 raw30529step0Labels permutation33 permutation3
    _ = mixedMoment B node2300 node2300Labels := by rfl

def raw30530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw30530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30530 raw30530Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw30530 raw30530Labels = mixedMoment B raw30530step0 raw30530step0Labels := by
      have hz : ∀ j, raw30530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30530step0 = (fun i j => raw30530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30530step0 raw30530; decide +kernel
      have hl : raw30530step0Labels = raw30530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30530 raw30530Labels permutation434 hz
    mixedMoment B raw30530step0 raw30530step0Labels = mixedMoment B raw30530step1 raw30530step1Labels := by
      have ha : raw30530step1 = (fun i j => raw30530step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30530step1 raw30530step0; decide +kernel
      have hl : raw30530step1Labels = raw30530step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30530step0 raw30530step0Labels permutation127 permutation3
    mixedMoment B raw30530step1 raw30530step1Labels = mixedMoment B raw30530step2 raw30530step2Labels := by
      have ha : raw30530step2 = -raw30530step1 := by apply Matrix.ext; change ∀ i j, raw30530step2 i j = -(raw30530step1 i j); unfold raw30530step2 raw30530step1; decide +kernel
      have hl : raw30530step2Labels = raw30530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw30531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30531 raw30531Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw30531 raw30531Labels = mixedMoment B raw30531step0 raw30531step0Labels := by
      have ha : raw30531step0 = (fun i j => raw30531 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30531step0 raw30531; decide +kernel
      have hl : raw30531step0Labels = raw30531Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30531 raw30531Labels permutation582 permutation3
    mixedMoment B raw30531step0 raw30531step0Labels = mixedMoment B raw30531step1 raw30531step1Labels := by
      have ha : raw30531step1 = -raw30531step0 := by apply Matrix.ext; change ∀ i j, raw30531step1 i j = -(raw30531step0 i j); unfold raw30531step1 raw30531step0; decide +kernel
      have hl : raw30531step1Labels = raw30531step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2317 node2317Labels := by rfl

def raw30532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw30532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw30532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30532 raw30532Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw30532 raw30532Labels = mixedMoment B raw30532step0 raw30532step0Labels := by
      have hz : ∀ j, raw30532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30532step0 = (fun i j => raw30532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30532step0 raw30532; decide +kernel
      have hl : raw30532step0Labels = raw30532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30532 raw30532Labels permutation434 hz
    mixedMoment B raw30532step0 raw30532step0Labels = mixedMoment B raw30532step1 raw30532step1Labels := by
      have ha : raw30532step1 = (fun i j => raw30532step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30532step1 raw30532step0; decide +kernel
      have hl : raw30532step1Labels = raw30532step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30532step0 raw30532step0Labels permutation33 permutation3
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw30533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw30533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30533 raw30533Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw30533 raw30533Labels = mixedMoment B raw30533step0 raw30533step0Labels := by
      have hz : ∀ j, raw30533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30533step0 = (fun i j => raw30533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30533step0 raw30533; decide +kernel
      have hl : raw30533step0Labels = raw30533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30533 raw30533Labels permutation434 hz
    mixedMoment B raw30533step0 raw30533step0Labels = mixedMoment B raw30533step1 raw30533step1Labels := by
      have ha : raw30533step1 = (fun i j => raw30533step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30533step1 raw30533step0; decide +kernel
      have hl : raw30533step1Labels = raw30533step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30533step0 raw30533step0Labels permutation32 permutation3
    _ = mixedMoment B node873 node873Labels := by rfl

def raw30534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw30534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30534 raw30534Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw30534 raw30534Labels = mixedMoment B raw30534step0 raw30534step0Labels := by
      have hz : ∀ j, raw30534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30534step0 = (fun i j => raw30534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30534step0 raw30534; decide +kernel
      have hl : raw30534step0Labels = raw30534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30534 raw30534Labels permutation434 hz
    mixedMoment B raw30534step0 raw30534step0Labels = mixedMoment B raw30534step1 raw30534step1Labels := by
      have ha : raw30534step1 = (fun i j => raw30534step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30534step1 raw30534step0; decide +kernel
      have hl : raw30534step1Labels = raw30534step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30534step0 raw30534step0Labels permutation32 permutation3
    _ = mixedMoment B node2300 node2300Labels := by rfl

def raw30535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw30535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30535 raw30535Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw30535 raw30535Labels = mixedMoment B raw30535step0 raw30535step0Labels := by
      have hz : ∀ j, raw30535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30535step0 = (fun i j => raw30535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30535step0 raw30535; decide +kernel
      have hl : raw30535step0Labels = raw30535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30535 raw30535Labels permutation434 hz
    mixedMoment B raw30535step0 raw30535step0Labels = mixedMoment B raw30535step1 raw30535step1Labels := by
      have ha : raw30535step1 = (fun i j => raw30535step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30535step1 raw30535step0; decide +kernel
      have hl : raw30535step1Labels = raw30535step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30535step0 raw30535step0Labels permutation151 permutation3
    mixedMoment B raw30535step1 raw30535step1Labels = mixedMoment B raw30535step2 raw30535step2Labels := by
      have ha : raw30535step2 = -raw30535step1 := by apply Matrix.ext; change ∀ i j, raw30535step2 i j = -(raw30535step1 i j); unfold raw30535step2 raw30535step1; decide +kernel
      have hl : raw30535step2Labels = raw30535step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw30536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30536 raw30536Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw30536 raw30536Labels = mixedMoment B raw30536step0 raw30536step0Labels := by
      have ha : raw30536step0 = (fun i j => raw30536 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30536step0 raw30536; decide +kernel
      have hl : raw30536step0Labels = raw30536Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30536 raw30536Labels permutation680 permutation3
    mixedMoment B raw30536step0 raw30536step0Labels = mixedMoment B raw30536step1 raw30536step1Labels := by
      have ha : raw30536step1 = -raw30536step0 := by apply Matrix.ext; change ∀ i j, raw30536step1 i j = -(raw30536step0 i j); unfold raw30536step1 raw30536step0; decide +kernel
      have hl : raw30536step1Labels = raw30536step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2317 node2317Labels := by rfl

def raw30537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw30537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30537 raw30537Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw30537 raw30537Labels = mixedMoment B raw30537step0 raw30537step0Labels := by
      have hz : ∀ j, raw30537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30537step0 = (fun i j => raw30537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30537step0 raw30537; decide +kernel
      have hl : raw30537step0Labels = raw30537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30537 raw30537Labels permutation434 hz
    mixedMoment B raw30537step0 raw30537step0Labels = mixedMoment B raw30537step1 raw30537step1Labels := by
      have ha : raw30537step1 = (fun i j => raw30537step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30537step1 raw30537step0; decide +kernel
      have hl : raw30537step1Labels = raw30537step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30537step0 raw30537step0Labels permutation32 permutation3
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw30538 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30538step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30538step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30538 raw30538Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw30538 raw30538Labels = mixedMoment B raw30538step0 raw30538step0Labels := by
      have hz : ∀ j, raw30538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30538step0 = (fun i j => raw30538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30538step0 raw30538; decide +kernel
      have hl : raw30538step0Labels = raw30538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30538 raw30538Labels permutation434 hz
    mixedMoment B raw30538step0 raw30538step0Labels = mixedMoment B raw30538step1 raw30538step1Labels := by
      have ha : raw30538step1 = (fun i j => raw30538step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30538step1 raw30538step0; decide +kernel
      have hl : raw30538step1Labels = raw30538step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30538step0 raw30538step0Labels permutation32 permutation7
    mixedMoment B raw30538step1 raw30538step1Labels = mixedMoment B raw30538step2 raw30538step2Labels := by
      have ha : raw30538step2 = raw30538step1 := by apply Matrix.ext; unfold raw30538step2 raw30538step1; decide +kernel
      have hl : raw30538step1Labels = labelEmbedding10 ∘ raw30538step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30538step1 raw30538step1Labels raw30538step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw30539 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30539step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30539 raw30539Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw30539 raw30539Labels = mixedMoment B raw30539step0 raw30539step0Labels := by
      have ha : raw30539step0 = (fun i j => raw30539 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30539step0 raw30539; decide +kernel
      have hl : raw30539step0Labels = raw30539Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30539 raw30539Labels permutation152 permutation7
    mixedMoment B raw30539step0 raw30539step0Labels = mixedMoment B raw30539step1 raw30539step1Labels := by
      have ha : raw30539step1 = raw30539step0 := by apply Matrix.ext; unfold raw30539step1 raw30539step0; decide +kernel
      have hl : raw30539step0Labels = labelEmbedding10 ∘ raw30539step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30539step0 raw30539step0Labels raw30539step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5130 node5130Labels := by rfl

def raw30540 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30540step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30540step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30540 raw30540Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw30540 raw30540Labels = mixedMoment B raw30540step0 raw30540step0Labels := by
      have hz : ∀ j, raw30540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30540step0 = (fun i j => raw30540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30540step0 raw30540; decide +kernel
      have hl : raw30540step0Labels = raw30540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30540 raw30540Labels permutation434 hz
    mixedMoment B raw30540step0 raw30540step0Labels = mixedMoment B raw30540step1 raw30540step1Labels := by
      have ha : raw30540step1 = (fun i j => raw30540step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30540step1 raw30540step0; decide +kernel
      have hl : raw30540step1Labels = raw30540step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30540step0 raw30540step0Labels permutation33 permutation7
    mixedMoment B raw30540step1 raw30540step1Labels = mixedMoment B raw30540step2 raw30540step2Labels := by
      have ha : raw30540step2 = raw30540step1 := by apply Matrix.ext; unfold raw30540step2 raw30540step1; decide +kernel
      have hl : raw30540step1Labels = labelEmbedding10 ∘ raw30540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30540step1 raw30540step1Labels raw30540step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw30541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30541step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30541step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30541 raw30541Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw30541 raw30541Labels = mixedMoment B raw30541step0 raw30541step0Labels := by
      have hz : ∀ j, raw30541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30541step0 = (fun i j => raw30541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30541step0 raw30541; decide +kernel
      have hl : raw30541step0Labels = raw30541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30541 raw30541Labels permutation434 hz
    mixedMoment B raw30541step0 raw30541step0Labels = mixedMoment B raw30541step1 raw30541step1Labels := by
      have ha : raw30541step1 = (fun i j => raw30541step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30541step1 raw30541step0; decide +kernel
      have hl : raw30541step1Labels = raw30541step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30541step0 raw30541step0Labels permutation32 permutation6
    mixedMoment B raw30541step1 raw30541step1Labels = mixedMoment B raw30541step2 raw30541step2Labels := by
      have ha : raw30541step2 = raw30541step1 := by apply Matrix.ext; unfold raw30541step2 raw30541step1; decide +kernel
      have hl : raw30541step1Labels = labelEmbedding9 ∘ raw30541step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30541step1 raw30541step1Labels raw30541step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

def raw30542 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30542step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30542step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30542 raw30542Labels = mixedMoment B node5010 node5010Labels := by
  calc
    mixedMoment B raw30542 raw30542Labels = mixedMoment B raw30542step0 raw30542step0Labels := by
      have hz : ∀ j, raw30542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30542step0 = (fun i j => raw30542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30542step0 raw30542; decide +kernel
      have hl : raw30542step0Labels = raw30542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30542 raw30542Labels permutation434 hz
    mixedMoment B raw30542step0 raw30542step0Labels = mixedMoment B raw30542step1 raw30542step1Labels := by
      have ha : raw30542step1 = (fun i j => raw30542step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30542step1 raw30542step0; decide +kernel
      have hl : raw30542step1Labels = raw30542step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30542step0 raw30542step0Labels permutation32 permutation6
    mixedMoment B raw30542step1 raw30542step1Labels = mixedMoment B raw30542step2 raw30542step2Labels := by
      have ha : raw30542step2 = raw30542step1 := by apply Matrix.ext; unfold raw30542step2 raw30542step1; decide +kernel
      have hl : raw30542step1Labels = labelEmbedding9 ∘ raw30542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30542step1 raw30542step1Labels raw30542step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5010 node5010Labels := by rfl

def raw30543 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30543step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30543 raw30543Labels = mixedMoment B node5054 node5054Labels := by
  calc
    mixedMoment B raw30543 raw30543Labels = mixedMoment B raw30543step0 raw30543step0Labels := by
      have ha : raw30543step0 = (fun i j => raw30543 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30543step0 raw30543; decide +kernel
      have hl : raw30543step0Labels = raw30543Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30543 raw30543Labels permutation158 permutation6
    mixedMoment B raw30543step0 raw30543step0Labels = mixedMoment B raw30543step1 raw30543step1Labels := by
      have ha : raw30543step1 = raw30543step0 := by apply Matrix.ext; unfold raw30543step1 raw30543step0; decide +kernel
      have hl : raw30543step0Labels = labelEmbedding9 ∘ raw30543step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30543step0 raw30543step0Labels raw30543step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5054 node5054Labels := by rfl

def raw30544 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30544step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30544step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30544 raw30544Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw30544 raw30544Labels = mixedMoment B raw30544step0 raw30544step0Labels := by
      have hz : ∀ j, raw30544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30544step0 = (fun i j => raw30544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30544step0 raw30544; decide +kernel
      have hl : raw30544step0Labels = raw30544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30544 raw30544Labels permutation434 hz
    mixedMoment B raw30544step0 raw30544step0Labels = mixedMoment B raw30544step1 raw30544step1Labels := by
      have ha : raw30544step1 = (fun i j => raw30544step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30544step1 raw30544step0; decide +kernel
      have hl : raw30544step1Labels = raw30544step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30544step0 raw30544step0Labels permutation32 permutation6
    mixedMoment B raw30544step1 raw30544step1Labels = mixedMoment B raw30544step2 raw30544step2Labels := by
      have ha : raw30544step2 = raw30544step1 := by apply Matrix.ext; unfold raw30544step2 raw30544step1; decide +kernel
      have hl : raw30544step1Labels = labelEmbedding9 ∘ raw30544step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30544step1 raw30544step1Labels raw30544step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw30545 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30545step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30545 raw30545Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw30545 raw30545Labels = mixedMoment B raw30545step0 raw30545step0Labels := by
      have ha : raw30545step0 = (fun i j => raw30545 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30545step0 raw30545; decide +kernel
      have hl : raw30545step0Labels = raw30545Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30545 raw30545Labels permutation152 permutation6
    mixedMoment B raw30545step0 raw30545step0Labels = mixedMoment B raw30545step1 raw30545step1Labels := by
      have ha : raw30545step1 = raw30545step0 := by apply Matrix.ext; unfold raw30545step1 raw30545step0; decide +kernel
      have hl : raw30545step0Labels = labelEmbedding9 ∘ raw30545step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30545step0 raw30545step0Labels raw30545step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

def raw30546 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30546step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30546 raw30546Labels = mixedMoment B node4994 node4994Labels := by
  calc
    mixedMoment B raw30546 raw30546Labels = mixedMoment B raw30546step0 raw30546step0Labels := by
      have ha : raw30546step0 = (fun i j => raw30546 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30546step0 raw30546; decide +kernel
      have hl : raw30546step0Labels = raw30546Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30546 raw30546Labels permutation152 permutation6
    mixedMoment B raw30546step0 raw30546step0Labels = mixedMoment B raw30546step1 raw30546step1Labels := by
      have ha : raw30546step1 = raw30546step0 := by apply Matrix.ext; unfold raw30546step1 raw30546step0; decide +kernel
      have hl : raw30546step0Labels = labelEmbedding9 ∘ raw30546step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30546step0 raw30546step0Labels raw30546step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4994 node4994Labels := by rfl

def raw30547 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30547step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30547step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30547 raw30547Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw30547 raw30547Labels = mixedMoment B raw30547step0 raw30547step0Labels := by
      have hz : ∀ j, raw30547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30547step0 = (fun i j => raw30547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30547step0 raw30547; decide +kernel
      have hl : raw30547step0Labels = raw30547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30547 raw30547Labels permutation434 hz
    mixedMoment B raw30547step0 raw30547step0Labels = mixedMoment B raw30547step1 raw30547step1Labels := by
      have ha : raw30547step1 = (fun i j => raw30547step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30547step1 raw30547step0; decide +kernel
      have hl : raw30547step1Labels = raw30547step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30547step0 raw30547step0Labels permutation33 permutation6
    mixedMoment B raw30547step1 raw30547step1Labels = mixedMoment B raw30547step2 raw30547step2Labels := by
      have ha : raw30547step2 = raw30547step1 := by apply Matrix.ext; unfold raw30547step2 raw30547step1; decide +kernel
      have hl : raw30547step1Labels = labelEmbedding9 ∘ raw30547step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30547step1 raw30547step1Labels raw30547step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw30548 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30548step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30548step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30548step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30548 raw30548Labels = mixedMoment B node4745 node4745Labels := by
  calc
    mixedMoment B raw30548 raw30548Labels = mixedMoment B raw30548step0 raw30548step0Labels := by
      have hz : ∀ j, raw30548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30548step0 = (fun i j => raw30548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30548step0 raw30548; decide +kernel
      have hl : raw30548step0Labels = raw30548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30548 raw30548Labels permutation434 hz
    mixedMoment B raw30548step0 raw30548step0Labels = mixedMoment B raw30548step1 raw30548step1Labels := by
      have ha : raw30548step1 = (fun i j => raw30548step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30548step1 raw30548step0; decide +kernel
      have hl : raw30548step1Labels = raw30548step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30548step0 raw30548step0Labels permutation32 permutation6
    mixedMoment B raw30548step1 raw30548step1Labels = mixedMoment B raw30548step2 raw30548step2Labels := by
      have ha : raw30548step2 = raw30548step1 := by apply Matrix.ext; unfold raw30548step2 raw30548step1; decide +kernel
      have hl : raw30548step1Labels = labelEmbedding9 ∘ raw30548step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30548step1 raw30548step1Labels raw30548step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4745 node4745Labels := by rfl

def raw30549 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30549step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30549step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30549 raw30549Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw30549 raw30549Labels = mixedMoment B raw30549step0 raw30549step0Labels := by
      have hz : ∀ j, raw30549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30549step0 = (fun i j => raw30549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30549step0 raw30549; decide +kernel
      have hl : raw30549step0Labels = raw30549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30549 raw30549Labels permutation434 hz
    mixedMoment B raw30549step0 raw30549step0Labels = mixedMoment B raw30549step1 raw30549step1Labels := by
      have ha : raw30549step1 = (fun i j => raw30549step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30549step1 raw30549step0; decide +kernel
      have hl : raw30549step1Labels = raw30549step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30549step0 raw30549step0Labels permutation32 permutation6
    mixedMoment B raw30549step1 raw30549step1Labels = mixedMoment B raw30549step2 raw30549step2Labels := by
      have ha : raw30549step2 = raw30549step1 := by apply Matrix.ext; unfold raw30549step2 raw30549step1; decide +kernel
      have hl : raw30549step1Labels = labelEmbedding9 ∘ raw30549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30549step1 raw30549step1Labels raw30549step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw30550 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30550step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30550 raw30550Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw30550 raw30550Labels = mixedMoment B raw30550step0 raw30550step0Labels := by
      have ha : raw30550step0 = (fun i j => raw30550 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30550step0 raw30550; decide +kernel
      have hl : raw30550step0Labels = raw30550Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30550 raw30550Labels permutation158 permutation6
    mixedMoment B raw30550step0 raw30550step0Labels = mixedMoment B raw30550step1 raw30550step1Labels := by
      have ha : raw30550step1 = raw30550step0 := by apply Matrix.ext; unfold raw30550step1 raw30550step0; decide +kernel
      have hl : raw30550step0Labels = labelEmbedding9 ∘ raw30550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30550step0 raw30550step0Labels raw30550step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw30551 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30551 raw30551Labels = mixedMoment B node2868 node2868Labels := by
  calc
    mixedMoment B raw30551 raw30551Labels = mixedMoment B raw30551step0 raw30551step0Labels := by
      have hz : ∀ j, raw30551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30551step0 = (fun i j => raw30551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30551step0 raw30551; decide +kernel
      have hl : raw30551step0Labels = raw30551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30551 raw30551Labels permutation434 hz
    mixedMoment B raw30551step0 raw30551step0Labels = mixedMoment B raw30551step1 raw30551step1Labels := by
      have ha : raw30551step1 = (fun i j => raw30551step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30551step1 raw30551step0; decide +kernel
      have hl : raw30551step1Labels = raw30551step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30551step0 raw30551step0Labels permutation32 permutation6
    _ = mixedMoment B node2868 node2868Labels := by rfl

def raw30552 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30552step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30552 raw30552Labels = mixedMoment B node2969 node2969Labels := by
  calc
    mixedMoment B raw30552 raw30552Labels = mixedMoment B raw30552step0 raw30552step0Labels := by
      have hz : ∀ j, raw30552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30552step0 = (fun i j => raw30552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30552step0 raw30552; decide +kernel
      have hl : raw30552step0Labels = raw30552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30552 raw30552Labels permutation434 hz
    mixedMoment B raw30552step0 raw30552step0Labels = mixedMoment B raw30552step1 raw30552step1Labels := by
      have hz : ∀ j, raw30552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30552step1 = (fun i j => raw30552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30552step1 raw30552step0; decide +kernel
      have hl : raw30552step1Labels = raw30552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30552step0 raw30552step0Labels permutation80 hz
    mixedMoment B raw30552step1 raw30552step1Labels = mixedMoment B raw30552step2 raw30552step2Labels := by
      have ha : raw30552step2 = (fun i j => raw30552step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30552step2 raw30552step1; decide +kernel
      have hl : raw30552step2Labels = raw30552step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30552step1 raw30552step1Labels permutation8 permutation6
    _ = mixedMoment B node2969 node2969Labels := by rfl

def raw30553 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30553 raw30553Labels = mixedMoment B node2917 node2917Labels := by
  calc
    mixedMoment B raw30553 raw30553Labels = mixedMoment B raw30553step0 raw30553step0Labels := by
      have ha : raw30553step0 = (fun i j => raw30553 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30553step0 raw30553; decide +kernel
      have hl : raw30553step0Labels = raw30553Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30553 raw30553Labels permutation158 permutation6
    _ = mixedMoment B node2917 node2917Labels := by rfl

def raw30554 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30554 raw30554Labels = mixedMoment B node2943 node2943Labels := by
  calc
    mixedMoment B raw30554 raw30554Labels = mixedMoment B raw30554step0 raw30554step0Labels := by
      have hz : ∀ j, raw30554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30554step0 = (fun i j => raw30554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30554step0 raw30554; decide +kernel
      have hl : raw30554step0Labels = raw30554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30554 raw30554Labels permutation434 hz
    mixedMoment B raw30554step0 raw30554step0Labels = mixedMoment B raw30554step1 raw30554step1Labels := by
      have ha : raw30554step1 = (fun i j => raw30554step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30554step1 raw30554step0; decide +kernel
      have hl : raw30554step1Labels = raw30554step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30554step0 raw30554step0Labels permutation32 permutation6
    _ = mixedMoment B node2943 node2943Labels := by rfl

def raw30555 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30555 raw30555Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw30555 raw30555Labels = mixedMoment B raw30555step0 raw30555step0Labels := by
      have hz : ∀ j, raw30555 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30555step0 = (fun i j => raw30555 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30555step0 raw30555; decide +kernel
      have hl : raw30555step0Labels = raw30555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30555 raw30555Labels permutation434 hz
    mixedMoment B raw30555step0 raw30555step0Labels = mixedMoment B raw30555step1 raw30555step1Labels := by
      have ha : raw30555step1 = (fun i j => raw30555step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30555step1 raw30555step0; decide +kernel
      have hl : raw30555step1Labels = raw30555step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30555step0 raw30555step0Labels permutation32 permutation6
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw30556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30556step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30556 raw30556Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw30556 raw30556Labels = mixedMoment B raw30556step0 raw30556step0Labels := by
      have hz : ∀ j, raw30556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30556step0 = (fun i j => raw30556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30556step0 raw30556; decide +kernel
      have hl : raw30556step0Labels = raw30556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30556 raw30556Labels permutation434 hz
    mixedMoment B raw30556step0 raw30556step0Labels = mixedMoment B raw30556step1 raw30556step1Labels := by
      have hz : ∀ j, raw30556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30556step1 = (fun i j => raw30556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30556step1 raw30556step0; decide +kernel
      have hl : raw30556step1Labels = raw30556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30556step0 raw30556step0Labels permutation80 hz
    mixedMoment B raw30556step1 raw30556step1Labels = mixedMoment B raw30556step2 raw30556step2Labels := by
      have ha : raw30556step2 = (fun i j => raw30556step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30556step2 raw30556step1; decide +kernel
      have hl : raw30556step2Labels = raw30556step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30556step1 raw30556step1Labels permutation8 permutation6
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw30557 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30557 raw30557Labels = mixedMoment B node2546 node2546Labels := by
  calc
    mixedMoment B raw30557 raw30557Labels = mixedMoment B raw30557step0 raw30557step0Labels := by
      have ha : raw30557step0 = (fun i j => raw30557 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30557step0 raw30557; decide +kernel
      have hl : raw30557step0Labels = raw30557Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30557 raw30557Labels permutation158 permutation6
    _ = mixedMoment B node2546 node2546Labels := by rfl

def raw30558 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30558 raw30558Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw30558 raw30558Labels = mixedMoment B raw30558step0 raw30558step0Labels := by
      have hz : ∀ j, raw30558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30558step0 = (fun i j => raw30558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30558step0 raw30558; decide +kernel
      have hl : raw30558step0Labels = raw30558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30558 raw30558Labels permutation434 hz
    mixedMoment B raw30558step0 raw30558step0Labels = mixedMoment B raw30558step1 raw30558step1Labels := by
      have ha : raw30558step1 = (fun i j => raw30558step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30558step1 raw30558step0; decide +kernel
      have hl : raw30558step1Labels = raw30558step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30558step0 raw30558step0Labels permutation32 permutation6
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw30559 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30559 raw30559Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw30559 raw30559Labels = mixedMoment B raw30559step0 raw30559step0Labels := by
      have hz : ∀ j, raw30559 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30559step0 = (fun i j => raw30559 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30559step0 raw30559; decide +kernel
      have hl : raw30559step0Labels = raw30559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30559 raw30559Labels permutation434 hz
    mixedMoment B raw30559step0 raw30559step0Labels = mixedMoment B raw30559step1 raw30559step1Labels := by
      have ha : raw30559step1 = (fun i j => raw30559step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30559step1 raw30559step0; decide +kernel
      have hl : raw30559step1Labels = raw30559step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30559step0 raw30559step0Labels permutation32 permutation6
    _ = mixedMoment B node1929 node1929Labels := by rfl

def raw30560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30560 raw30560Labels = mixedMoment B node2395 node2395Labels := by
  calc
    mixedMoment B raw30560 raw30560Labels = mixedMoment B raw30560step0 raw30560step0Labels := by
      have hz : ∀ j, raw30560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30560step0 = (fun i j => raw30560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30560step0 raw30560; decide +kernel
      have hl : raw30560step0Labels = raw30560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30560 raw30560Labels permutation434 hz
    mixedMoment B raw30560step0 raw30560step0Labels = mixedMoment B raw30560step1 raw30560step1Labels := by
      have ha : raw30560step1 = (fun i j => raw30560step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30560step1 raw30560step0; decide +kernel
      have hl : raw30560step1Labels = raw30560step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30560step0 raw30560step0Labels permutation32 permutation6
    _ = mixedMoment B node2395 node2395Labels := by rfl

def raw30561 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30561 raw30561Labels = mixedMoment B node2456 node2456Labels := by
  calc
    mixedMoment B raw30561 raw30561Labels = mixedMoment B raw30561step0 raw30561step0Labels := by
      have ha : raw30561step0 = (fun i j => raw30561 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30561step0 raw30561; decide +kernel
      have hl : raw30561step0Labels = raw30561Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30561 raw30561Labels permutation158 permutation6
    _ = mixedMoment B node2456 node2456Labels := by rfl

def raw30562 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30562 raw30562Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw30562 raw30562Labels = mixedMoment B raw30562step0 raw30562step0Labels := by
      have hz : ∀ j, raw30562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30562step0 = (fun i j => raw30562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30562step0 raw30562; decide +kernel
      have hl : raw30562step0Labels = raw30562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30562 raw30562Labels permutation434 hz
    mixedMoment B raw30562step0 raw30562step0Labels = mixedMoment B raw30562step1 raw30562step1Labels := by
      have ha : raw30562step1 = (fun i j => raw30562step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30562step1 raw30562step0; decide +kernel
      have hl : raw30562step1Labels = raw30562step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30562step0 raw30562step0Labels permutation32 permutation6
    _ = mixedMoment B node2499 node2499Labels := by rfl

def raw30563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30563 raw30563Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw30563 raw30563Labels = mixedMoment B raw30563step0 raw30563step0Labels := by
      have ha : raw30563step0 = (fun i j => raw30563 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30563step0 raw30563; decide +kernel
      have hl : raw30563step0Labels = raw30563Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30563 raw30563Labels permutation152 permutation6
    _ = mixedMoment B node1901 node1901Labels := by rfl

def raw30564 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30564 raw30564Labels = mixedMoment B node2380 node2380Labels := by
  calc
    mixedMoment B raw30564 raw30564Labels = mixedMoment B raw30564step0 raw30564step0Labels := by
      have ha : raw30564step0 = (fun i j => raw30564 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30564step0 raw30564; decide +kernel
      have hl : raw30564step0Labels = raw30564Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30564 raw30564Labels permutation152 permutation6
    _ = mixedMoment B node2380 node2380Labels := by rfl

def raw30565 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30565 raw30565Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw30565 raw30565Labels = mixedMoment B raw30565step0 raw30565step0Labels := by
      have hz : ∀ j, raw30565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30565step0 = (fun i j => raw30565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30565step0 raw30565; decide +kernel
      have hl : raw30565step0Labels = raw30565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30565 raw30565Labels permutation346 hz
    mixedMoment B raw30565step0 raw30565step0Labels = mixedMoment B raw30565step1 raw30565step1Labels := by
      have ha : raw30565step1 = (fun i j => raw30565step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30565step1 raw30565step0; decide +kernel
      have hl : raw30565step1Labels = raw30565step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30565step0 raw30565step0Labels permutation32 permutation6
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw30566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30566 raw30566Labels = mixedMoment B node2473 node2473Labels := by
  calc
    mixedMoment B raw30566 raw30566Labels = mixedMoment B raw30566step0 raw30566step0Labels := by
      have ha : raw30566step0 = (fun i j => raw30566 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30566step0 raw30566; decide +kernel
      have hl : raw30566step0Labels = raw30566Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30566 raw30566Labels permutation152 permutation6
    _ = mixedMoment B node2473 node2473Labels := by rfl

def raw30567 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30567 raw30567Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw30567 raw30567Labels = mixedMoment B raw30567step0 raw30567step0Labels := by
      have hz : ∀ j, raw30567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30567step0 = (fun i j => raw30567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30567step0 raw30567; decide +kernel
      have hl : raw30567step0Labels = raw30567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30567 raw30567Labels permutation434 hz
    mixedMoment B raw30567step0 raw30567step0Labels = mixedMoment B raw30567step1 raw30567step1Labels := by
      have ha : raw30567step1 = (fun i j => raw30567step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30567step1 raw30567step0; decide +kernel
      have hl : raw30567step1Labels = raw30567step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30567step0 raw30567step0Labels permutation33 permutation6
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw30568 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30568 raw30568Labels = mixedMoment B node1918 node1918Labels := by
  calc
    mixedMoment B raw30568 raw30568Labels = mixedMoment B raw30568step0 raw30568step0Labels := by
      have hz : ∀ j, raw30568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30568step0 = (fun i j => raw30568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30568step0 raw30568; decide +kernel
      have hl : raw30568step0Labels = raw30568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30568 raw30568Labels permutation434 hz
    mixedMoment B raw30568step0 raw30568step0Labels = mixedMoment B raw30568step1 raw30568step1Labels := by
      have ha : raw30568step1 = (fun i j => raw30568step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30568step1 raw30568step0; decide +kernel
      have hl : raw30568step1Labels = raw30568step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30568step0 raw30568step0Labels permutation32 permutation6
    _ = mixedMoment B node1918 node1918Labels := by rfl

def raw30569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30569 raw30569Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw30569 raw30569Labels = mixedMoment B raw30569step0 raw30569step0Labels := by
      have hz : ∀ j, raw30569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30569step0 = (fun i j => raw30569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30569step0 raw30569; decide +kernel
      have hl : raw30569step0Labels = raw30569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30569 raw30569Labels permutation434 hz
    mixedMoment B raw30569step0 raw30569step0Labels = mixedMoment B raw30569step1 raw30569step1Labels := by
      have ha : raw30569step1 = (fun i j => raw30569step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30569step1 raw30569step0; decide +kernel
      have hl : raw30569step1Labels = raw30569step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30569step0 raw30569step0Labels permutation32 permutation6
    _ = mixedMoment B node2388 node2388Labels := by rfl

def raw30570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw30570step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30570 raw30570Labels = mixedMoment B node2523 node2523Labels := by
  calc
    mixedMoment B raw30570 raw30570Labels = mixedMoment B raw30570step0 raw30570step0Labels := by
      have hz : ∀ j, raw30570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30570step0 = (fun i j => raw30570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30570step0 raw30570; decide +kernel
      have hl : raw30570step0Labels = raw30570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30570 raw30570Labels permutation434 hz
    mixedMoment B raw30570step0 raw30570step0Labels = mixedMoment B raw30570step1 raw30570step1Labels := by
      have hz : ∀ j, raw30570step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30570step1 = (fun i j => raw30570step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30570step1 raw30570step0; decide +kernel
      have hl : raw30570step1Labels = raw30570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30570step0 raw30570step0Labels permutation80 hz
    mixedMoment B raw30570step1 raw30570step1Labels = mixedMoment B raw30570step2 raw30570step2Labels := by
      have ha : raw30570step2 = (fun i j => raw30570step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30570step2 raw30570step1; decide +kernel
      have hl : raw30570step2Labels = raw30570step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30570step1 raw30570step1Labels permutation8 permutation6
    _ = mixedMoment B node2523 node2523Labels := by rfl

def raw30571 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30571 raw30571Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw30571 raw30571Labels = mixedMoment B raw30571step0 raw30571step0Labels := by
      have ha : raw30571step0 = (fun i j => raw30571 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30571step0 raw30571; decide +kernel
      have hl : raw30571step0Labels = raw30571Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30571 raw30571Labels permutation158 permutation6
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw30572 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw30572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw30572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30572 raw30572Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw30572 raw30572Labels = mixedMoment B raw30572step0 raw30572step0Labels := by
      have hz : ∀ j, raw30572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30572step0 = (fun i j => raw30572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30572step0 raw30572; decide +kernel
      have hl : raw30572step0Labels = raw30572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30572 raw30572Labels permutation434 hz
    mixedMoment B raw30572step0 raw30572step0Labels = mixedMoment B raw30572step1 raw30572step1Labels := by
      have ha : raw30572step1 = (fun i j => raw30572step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30572step1 raw30572step0; decide +kernel
      have hl : raw30572step1Labels = raw30572step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30572step0 raw30572step0Labels permutation32 permutation6
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw30573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw30573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30573 raw30573Labels = mixedMoment B node2451 node2451Labels := by
  calc
    mixedMoment B raw30573 raw30573Labels = mixedMoment B raw30573step0 raw30573step0Labels := by
      have ha : raw30573step0 = (fun i j => raw30573 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30573step0 raw30573; decide +kernel
      have hl : raw30573step0Labels = raw30573Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30573 raw30573Labels permutation159 permutation2
    _ = mixedMoment B node2451 node2451Labels := by rfl

def raw30574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw30574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw30574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30574 raw30574Labels = mixedMoment B node3367 node3367Labels := by
  calc
    mixedMoment B raw30574 raw30574Labels = mixedMoment B raw30574step0 raw30574step0Labels := by
      have ha : raw30574step0 = (fun i j => raw30574 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30574step0 raw30574; decide +kernel
      have hl : raw30574step0Labels = raw30574Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30574 raw30574Labels permutation584 permutation2
    mixedMoment B raw30574step0 raw30574step0Labels = mixedMoment B raw30574step1 raw30574step1Labels := by
      have ha : raw30574step1 = -raw30574step0 := by apply Matrix.ext; change ∀ i j, raw30574step1 i j = -(raw30574step0 i j); unfold raw30574step1 raw30574step0; decide +kernel
      have hl : raw30574step1Labels = raw30574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3367 node3367Labels := by rfl

def raw30575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw30575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30575 raw30575Labels = mixedMoment B node3374 node3374Labels := by
  calc
    mixedMoment B raw30575 raw30575Labels = mixedMoment B raw30575step0 raw30575step0Labels := by
      have ha : raw30575step0 = (fun i j => raw30575 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30575step0 raw30575; decide +kernel
      have hl : raw30575step0Labels = raw30575Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30575 raw30575Labels permutation589 permutation2
    mixedMoment B raw30575step0 raw30575step0Labels = mixedMoment B raw30575step1 raw30575step1Labels := by
      have ha : raw30575step1 = -raw30575step0 := by apply Matrix.ext; change ∀ i j, raw30575step1 i j = -(raw30575step0 i j); unfold raw30575step1 raw30575step0; decide +kernel
      have hl : raw30575step1Labels = raw30575step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3374 node3374Labels := by rfl

def raw30576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw30576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30576 raw30576Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw30576 raw30576Labels = mixedMoment B raw30576step0 raw30576step0Labels := by
      have ha : raw30576step0 = (fun i j => raw30576 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30576step0 raw30576; decide +kernel
      have hl : raw30576step0Labels = raw30576Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30576 raw30576Labels permutation582 permutation2
    mixedMoment B raw30576step0 raw30576step0Labels = mixedMoment B raw30576step1 raw30576step1Labels := by
      have ha : raw30576step1 = -raw30576step0 := by apply Matrix.ext; change ∀ i j, raw30576step1 i j = -(raw30576step0 i j); unfold raw30576step1 raw30576step0; decide +kernel
      have hl : raw30576step1Labels = raw30576step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3370 node3370Labels := by rfl

def raw30577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw30577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw30577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw30577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30577 raw30577Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw30577 raw30577Labels = mixedMoment B raw30577step0 raw30577step0Labels := by
      have ha : raw30577step0 = (fun i j => raw30577 (permutation543 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30577step0 raw30577; decide +kernel
      have hl : raw30577step0Labels = raw30577Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30577 raw30577Labels permutation543 permutation4
    mixedMoment B raw30577step0 raw30577step0Labels = mixedMoment B raw30577step1 raw30577step1Labels := by
      have ha : raw30577step1 = -raw30577step0 := by apply Matrix.ext; change ∀ i j, raw30577step1 i j = -(raw30577step0 i j); unfold raw30577step1 raw30577step0; decide +kernel
      have hl : raw30577step1Labels = raw30577step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw30578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw30578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30578 raw30578Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw30578 raw30578Labels = mixedMoment B raw30578step0 raw30578step0Labels := by
      have ha : raw30578step0 = (fun i j => raw30578 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30578step0 raw30578; decide +kernel
      have hl : raw30578step0Labels = raw30578Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30578 raw30578Labels permutation584 permutation2
    mixedMoment B raw30578step0 raw30578step0Labels = mixedMoment B raw30578step1 raw30578step1Labels := by
      have ha : raw30578step1 = -raw30578step0 := by apply Matrix.ext; change ∀ i j, raw30578step1 i j = -(raw30578step0 i j); unfold raw30578step1 raw30578step0; decide +kernel
      have hl : raw30578step1Labels = raw30578step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw30579 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3], ![0, 0]]
def raw30579Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30579step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw30579step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30579step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw30579step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30579step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw30579step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30579 raw30579Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw30579 raw30579Labels = mixedMoment B raw30579step0 raw30579step0Labels := by
      have hz : ∀ j, raw30579 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw30579step0 = (fun i j => raw30579 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw30579step0 raw30579; decide +kernel
      have hl : raw30579step0Labels = raw30579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30579 raw30579Labels permutation590 hz
    mixedMoment B raw30579step0 raw30579step0Labels = mixedMoment B raw30579step1 raw30579step1Labels := by
      have ha : raw30579step1 = (fun i j => raw30579step0 (permutation143 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30579step1 raw30579step0; decide +kernel
      have hl : raw30579step1Labels = raw30579step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30579step0 raw30579step0Labels permutation143 permutation0
    mixedMoment B raw30579step1 raw30579step1Labels = mixedMoment B raw30579step2 raw30579step2Labels := by
      have ha : raw30579step2 = -raw30579step1 := by apply Matrix.ext; change ∀ i j, raw30579step2 i j = -(raw30579step1 i j); unfold raw30579step2 raw30579step1; decide +kernel
      have hl : raw30579step2Labels = raw30579step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw30580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30580 raw30580Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw30580 raw30580Labels = mixedMoment B raw30580step0 raw30580step0Labels := by
      have ha : raw30580step0 = (fun i j => raw30580 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30580step0 raw30580; decide +kernel
      have hl : raw30580step0Labels = raw30580Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30580 raw30580Labels permutation159 permutation2
    _ = mixedMoment B node1108 node1108Labels := by rfl

def raw30581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30581 raw30581Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw30581 raw30581Labels = mixedMoment B raw30581step0 raw30581step0Labels := by
      have ha : raw30581step0 = (fun i j => raw30581 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30581step0 raw30581; decide +kernel
      have hl : raw30581step0Labels = raw30581Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30581 raw30581Labels permutation159 permutation2
    _ = mixedMoment B node2318 node2318Labels := by rfl

def raw30582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30582 raw30582Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw30582 raw30582Labels = mixedMoment B raw30582step0 raw30582step0Labels := by
      have ha : raw30582step0 = (fun i j => raw30582 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30582step0 raw30582; decide +kernel
      have hl : raw30582step0Labels = raw30582Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30582 raw30582Labels permutation159 permutation2
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw30583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30583 raw30583Labels = mixedMoment B node2418 node2418Labels := by
  calc
    mixedMoment B raw30583 raw30583Labels = mixedMoment B raw30583step0 raw30583step0Labels := by
      have ha : raw30583step0 = (fun i j => raw30583 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30583step0 raw30583; decide +kernel
      have hl : raw30583step0Labels = raw30583Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30583 raw30583Labels permutation159 permutation2
    _ = mixedMoment B node2418 node2418Labels := by rfl

def raw30584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw30584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30584 raw30584Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw30584 raw30584Labels = mixedMoment B raw30584step0 raw30584step0Labels := by
      have ha : raw30584step0 = (fun i j => raw30584 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30584step0 raw30584; decide +kernel
      have hl : raw30584step0Labels = raw30584Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30584 raw30584Labels permutation158 permutation2
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw30585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30585 raw30585Labels = mixedMoment B node2461 node2461Labels := by
  calc
    mixedMoment B raw30585 raw30585Labels = mixedMoment B raw30585step0 raw30585step0Labels := by
      have ha : raw30585step0 = (fun i j => raw30585 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30585step0 raw30585; decide +kernel
      have hl : raw30585step0Labels = raw30585Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30585 raw30585Labels permutation159 permutation2
    _ = mixedMoment B node2461 node2461Labels := by rfl

def raw30586 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw30586Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30586step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw30586step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30586 raw30586Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw30586 raw30586Labels = mixedMoment B raw30586step0 raw30586step0Labels := by
      have ha : raw30586step0 = (fun i j => raw30586 (permutation159 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30586step0 raw30586; decide +kernel
      have hl : raw30586step0Labels = raw30586Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30586 raw30586Labels permutation159 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw30587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30587step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30587 raw30587Labels = mixedMoment B node3682 node3682Labels := by
  calc
    mixedMoment B raw30587 raw30587Labels = mixedMoment B raw30587step0 raw30587step0Labels := by
      have ha : raw30587step0 = (fun i j => raw30587 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30587step0 raw30587; decide +kernel
      have hl : raw30587step0Labels = raw30587Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30587 raw30587Labels permutation582 permutation2
    mixedMoment B raw30587step0 raw30587step0Labels = mixedMoment B raw30587step1 raw30587step1Labels := by
      have ha : raw30587step1 = -raw30587step0 := by apply Matrix.ext; change ∀ i j, raw30587step1 i j = -(raw30587step0 i j); unfold raw30587step1 raw30587step0; decide +kernel
      have hl : raw30587step1Labels = raw30587step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3682 node3682Labels := by rfl

def raw30588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30588 raw30588Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw30588 raw30588Labels = mixedMoment B raw30588step0 raw30588step0Labels := by
      have ha : raw30588step0 = (fun i j => raw30588 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30588step0 raw30588; decide +kernel
      have hl : raw30588step0Labels = raw30588Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30588 raw30588Labels permutation201 permutation2
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw30589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30589 raw30589Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw30589 raw30589Labels = mixedMoment B raw30589step0 raw30589step0Labels := by
      have ha : raw30589step0 = (fun i j => raw30589 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30589step0 raw30589; decide +kernel
      have hl : raw30589step0Labels = raw30589Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30589 raw30589Labels permutation582 permutation2
    mixedMoment B raw30589step0 raw30589step0Labels = mixedMoment B raw30589step1 raw30589step1Labels := by
      have ha : raw30589step1 = -raw30589step0 := by apply Matrix.ext; change ∀ i j, raw30589step1 i j = -(raw30589step0 i j); unfold raw30589step1 raw30589step0; decide +kernel
      have hl : raw30589step1Labels = raw30589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2317 node2317Labels := by rfl

def raw30590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30590 raw30590Labels = mixedMoment B node2412 node2412Labels := by
  calc
    mixedMoment B raw30590 raw30590Labels = mixedMoment B raw30590step0 raw30590step0Labels := by
      have ha : raw30590step0 = (fun i j => raw30590 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30590step0 raw30590; decide +kernel
      have hl : raw30590step0Labels = raw30590Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30590 raw30590Labels permutation158 permutation2
    _ = mixedMoment B node2412 node2412Labels := by rfl

def raw30591 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30591 raw30591Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw30591 raw30591Labels = mixedMoment B raw30591step0 raw30591step0Labels := by
      have ha : raw30591step0 = (fun i j => raw30591 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30591step0 raw30591; decide +kernel
      have hl : raw30591step0Labels = raw30591Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30591 raw30591Labels permutation159 permutation4
    mixedMoment B raw30591step0 raw30591step0Labels = mixedMoment B raw30591step1 raw30591step1Labels := by
      have ha : raw30591step1 = -raw30591step0 := by apply Matrix.ext; change ∀ i j, raw30591step1 i j = -(raw30591step0 i j); unfold raw30591step1 raw30591step0; decide +kernel
      have hl : raw30591step1Labels = raw30591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3433 node3433Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
