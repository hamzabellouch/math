import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11520step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11520step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11520step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11520step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11520step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11520 raw11520Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11520 raw11520Labels = mixedMoment B raw11520step0 raw11520step0Labels := by
      have hz : ∀ j, raw11520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11520step0 = (fun i j => raw11520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11520step0 raw11520; decide +kernel
      have hl : raw11520step0Labels = raw11520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11520 raw11520Labels permutation346 hz
    mixedMoment B raw11520step0 raw11520step0Labels = mixedMoment B raw11520step1 raw11520step1Labels := by
      have hz : ∀ j, raw11520step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11520step1 = (fun i j => raw11520step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11520step1 raw11520step0; decide +kernel
      have hl : raw11520step1Labels = raw11520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11520step0 raw11520step0Labels permutation56 hz
    mixedMoment B raw11520step1 raw11520step1Labels = mixedMoment B raw11520step2 raw11520step2Labels := by
      have ha : raw11520step2 = (fun i j => raw11520step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11520step2 raw11520step1; decide +kernel
      have hl : raw11520step2Labels = raw11520step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11520step1 raw11520step1Labels permutation9 permutation7
    mixedMoment B raw11520step2 raw11520step2Labels = mixedMoment B raw11520step3 raw11520step3Labels := by
      have ha : raw11520step3 = -raw11520step2 := by apply Matrix.ext; change ∀ i j, raw11520step3 i j = -(raw11520step2 i j); unfold raw11520step3 raw11520step2; decide +kernel
      have hl : raw11520step3Labels = raw11520step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11520step3 raw11520step3Labels = mixedMoment B raw11520step4 raw11520step4Labels := by
      have ha : raw11520step4 = raw11520step3 := by apply Matrix.ext; unfold raw11520step4 raw11520step3; decide +kernel
      have hl : raw11520step3Labels = labelEmbedding10 ∘ raw11520step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11520step3 raw11520step3Labels raw11520step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw11521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw11521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11521step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw11521step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11521 raw11521Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw11521 raw11521Labels = mixedMoment B raw11521step0 raw11521step0Labels := by
      have hz : ∀ j, raw11521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11521step0 = (fun i j => raw11521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11521step0 raw11521; decide +kernel
      have hl : raw11521step0Labels = raw11521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11521 raw11521Labels permutation434 hz
    mixedMoment B raw11521step0 raw11521step0Labels = mixedMoment B raw11521step1 raw11521step1Labels := by
      have hz : ∀ j, raw11521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11521step1 = (fun i j => raw11521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11521step1 raw11521step0; decide +kernel
      have hl : raw11521step1Labels = raw11521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11521step0 raw11521step0Labels permutation80 hz
    mixedMoment B raw11521step1 raw11521step1Labels = mixedMoment B raw11521step2 raw11521step2Labels := by
      have hz : ∀ j, raw11521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11521step2 = (fun i j => raw11521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11521step2 raw11521step1; decide +kernel
      have hl : raw11521step2Labels = raw11521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11521step1 raw11521step1Labels permutation14 hz
    mixedMoment B raw11521step2 raw11521step2Labels = mixedMoment B raw11521step3 raw11521step3Labels := by
      have ha : raw11521step3 = (fun i j => raw11521step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11521step3 raw11521step2; decide +kernel
      have hl : raw11521step3Labels = raw11521step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11521step2 raw11521step2Labels permutation3 permutation2
    _ = mixedMoment B node4511 node4511Labels := by rfl

def raw11522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw11522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11522 raw11522Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw11522 raw11522Labels = mixedMoment B raw11522step0 raw11522step0Labels := by
      have hz : ∀ j, raw11522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11522step0 = (fun i j => raw11522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11522step0 raw11522; decide +kernel
      have hl : raw11522step0Labels = raw11522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11522 raw11522Labels permutation434 hz
    mixedMoment B raw11522step0 raw11522step0Labels = mixedMoment B raw11522step1 raw11522step1Labels := by
      have hz : ∀ j, raw11522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11522step1 = (fun i j => raw11522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11522step1 raw11522step0; decide +kernel
      have hl : raw11522step1Labels = raw11522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11522step0 raw11522step0Labels permutation80 hz
    mixedMoment B raw11522step1 raw11522step1Labels = mixedMoment B raw11522step2 raw11522step2Labels := by
      have ha : raw11522step2 = (fun i j => raw11522step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11522step2 raw11522step1; decide +kernel
      have hl : raw11522step2Labels = raw11522step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11522step1 raw11522step1Labels permutation9 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw11523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw11523step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11523 raw11523Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw11523 raw11523Labels = mixedMoment B raw11523step0 raw11523step0Labels := by
      have hz : ∀ j, raw11523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11523step0 = (fun i j => raw11523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11523step0 raw11523; decide +kernel
      have hl : raw11523step0Labels = raw11523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11523 raw11523Labels permutation434 hz
    mixedMoment B raw11523step0 raw11523step0Labels = mixedMoment B raw11523step1 raw11523step1Labels := by
      have hz : ∀ j, raw11523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11523step1 = (fun i j => raw11523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11523step1 raw11523step0; decide +kernel
      have hl : raw11523step1Labels = raw11523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11523step0 raw11523step0Labels permutation56 hz
    mixedMoment B raw11523step1 raw11523step1Labels = mixedMoment B raw11523step2 raw11523step2Labels := by
      have ha : raw11523step2 = (fun i j => raw11523step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11523step2 raw11523step1; decide +kernel
      have hl : raw11523step2Labels = raw11523step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11523step1 raw11523step1Labels permutation9 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw11524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw11524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw11524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11524 raw11524Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw11524 raw11524Labels = mixedMoment B raw11524step0 raw11524step0Labels := by
      have hz : ∀ j, raw11524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11524step0 = (fun i j => raw11524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11524step0 raw11524; decide +kernel
      have hl : raw11524step0Labels = raw11524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11524 raw11524Labels permutation346 hz
    mixedMoment B raw11524step0 raw11524step0Labels = mixedMoment B raw11524step1 raw11524step1Labels := by
      have hz : ∀ j, raw11524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11524step1 = (fun i j => raw11524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11524step1 raw11524step0; decide +kernel
      have hl : raw11524step1Labels = raw11524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11524step0 raw11524step0Labels permutation56 hz
    mixedMoment B raw11524step1 raw11524step1Labels = mixedMoment B raw11524step2 raw11524step2Labels := by
      have ha : raw11524step2 = (fun i j => raw11524step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11524step2 raw11524step1; decide +kernel
      have hl : raw11524step2Labels = raw11524step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11524step1 raw11524step1Labels permutation9 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw11525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw11525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw11525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw11525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11525step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 0, -2], ![1, 0, -1]]
def raw11525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11525step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw11525step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw11525step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw11525step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw11525step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw11525step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11525 raw11525Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw11525 raw11525Labels = mixedMoment B raw11525step0 raw11525step0Labels := by
      have hz : ∀ j, raw11525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11525step0 = (fun i j => raw11525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11525step0 raw11525; decide +kernel
      have hl : raw11525step0Labels = raw11525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11525 raw11525Labels permutation434 hz
    mixedMoment B raw11525step0 raw11525step0Labels = mixedMoment B raw11525step1 raw11525step1Labels := by
      have hz : ∀ j, raw11525step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11525step1 = (fun i j => raw11525step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11525step1 raw11525step0; decide +kernel
      have hl : raw11525step1Labels = raw11525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11525step0 raw11525step0Labels permutation80 hz
    mixedMoment B raw11525step1 raw11525step1Labels = mixedMoment B raw11525step2 raw11525step2Labels := by
      have hz : ∀ j, raw11525step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11525step2 = (fun i j => raw11525step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11525step2 raw11525step1; decide +kernel
      have hl : raw11525step2Labels = raw11525step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11525step1 raw11525step1Labels permutation14 hz
    mixedMoment B raw11525step2 raw11525step2Labels = mixedMoment B raw11525step3 raw11525step3Labels := by
      have hz : ∀ i, raw11525step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw11525step3 = (fun i j => raw11525step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw11525step3 raw11525step2; decide +kernel
      have hl : raw11525step3Labels = (fun j => raw11525step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11525step2 raw11525step2Labels permutation4 hz
    mixedMoment B raw11525step3 raw11525step3Labels = mixedMoment B raw11525step4 raw11525step4Labels := by
      have ha : raw11525step4 = (fun i j => raw11525step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11525step4 raw11525step3; decide +kernel
      have hl : raw11525step4Labels = raw11525step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11525step3 raw11525step3Labels permutation3 permutation0
    mixedMoment B raw11525step4 raw11525step4Labels = mixedMoment B raw11525step5 raw11525step5Labels := by
      have ha : raw11525step5 = raw11525step4 := by apply Matrix.ext; unfold raw11525step5 raw11525step4; decide +kernel
      have hl : raw11525step4Labels = labelEmbedding2 ∘ raw11525step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11525step4 raw11525step4Labels raw11525step5Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw11526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11526step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw11526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11526 raw11526Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw11526 raw11526Labels = mixedMoment B raw11526step0 raw11526step0Labels := by
      have hz : ∀ j, raw11526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11526step0 = (fun i j => raw11526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11526step0 raw11526; decide +kernel
      have hl : raw11526step0Labels = raw11526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11526 raw11526Labels permutation434 hz
    mixedMoment B raw11526step0 raw11526step0Labels = mixedMoment B raw11526step1 raw11526step1Labels := by
      have hz : ∀ j, raw11526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11526step1 = (fun i j => raw11526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11526step1 raw11526step0; decide +kernel
      have hl : raw11526step1Labels = raw11526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11526step0 raw11526step0Labels permutation80 hz
    mixedMoment B raw11526step1 raw11526step1Labels = mixedMoment B raw11526step2 raw11526step2Labels := by
      have hz : ∀ j, raw11526step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11526step2 = (fun i j => raw11526step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11526step2 raw11526step1; decide +kernel
      have hl : raw11526step2Labels = raw11526step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11526step1 raw11526step1Labels permutation14 hz
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw11527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11527 raw11527Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw11527 raw11527Labels = mixedMoment B raw11527step0 raw11527step0Labels := by
      have hz : ∀ j, raw11527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11527step0 = (fun i j => raw11527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11527step0 raw11527; decide +kernel
      have hl : raw11527step0Labels = raw11527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11527 raw11527Labels permutation434 hz
    mixedMoment B raw11527step0 raw11527step0Labels = mixedMoment B raw11527step1 raw11527step1Labels := by
      have hz : ∀ j, raw11527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11527step1 = (fun i j => raw11527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11527step1 raw11527step0; decide +kernel
      have hl : raw11527step1Labels = raw11527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11527step0 raw11527step0Labels permutation80 hz
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw11528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11528 raw11528Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw11528 raw11528Labels = mixedMoment B raw11528step0 raw11528step0Labels := by
      have hz : ∀ j, raw11528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11528step0 = (fun i j => raw11528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11528step0 raw11528; decide +kernel
      have hl : raw11528step0Labels = raw11528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11528 raw11528Labels permutation434 hz
    mixedMoment B raw11528step0 raw11528step0Labels = mixedMoment B raw11528step1 raw11528step1Labels := by
      have hz : ∀ j, raw11528step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11528step1 = (fun i j => raw11528step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11528step1 raw11528step0; decide +kernel
      have hl : raw11528step1Labels = raw11528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11528step0 raw11528step0Labels permutation56 hz
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw11529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw11529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11529 raw11529Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw11529 raw11529Labels = mixedMoment B raw11529step0 raw11529step0Labels := by
      have hz : ∀ j, raw11529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11529step0 = (fun i j => raw11529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11529step0 raw11529; decide +kernel
      have hl : raw11529step0Labels = raw11529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11529 raw11529Labels permutation346 hz
    mixedMoment B raw11529step0 raw11529step0Labels = mixedMoment B raw11529step1 raw11529step1Labels := by
      have hz : ∀ j, raw11529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11529step1 = (fun i j => raw11529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11529step1 raw11529step0; decide +kernel
      have hl : raw11529step1Labels = raw11529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11529step0 raw11529step0Labels permutation56 hz
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw11530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw11530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw11530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw11530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw11530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11530 raw11530Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw11530 raw11530Labels = mixedMoment B raw11530step0 raw11530step0Labels := by
      have hz : ∀ j, raw11530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11530step0 = (fun i j => raw11530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11530step0 raw11530; decide +kernel
      have hl : raw11530step0Labels = raw11530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11530 raw11530Labels permutation434 hz
    mixedMoment B raw11530step0 raw11530step0Labels = mixedMoment B raw11530step1 raw11530step1Labels := by
      have hz : ∀ j, raw11530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11530step1 = (fun i j => raw11530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11530step1 raw11530step0; decide +kernel
      have hl : raw11530step1Labels = raw11530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11530step0 raw11530step0Labels permutation80 hz
    mixedMoment B raw11530step1 raw11530step1Labels = mixedMoment B raw11530step2 raw11530step2Labels := by
      have hz : ∀ j, raw11530step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11530step2 = (fun i j => raw11530step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11530step2 raw11530step1; decide +kernel
      have hl : raw11530step2Labels = raw11530step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11530step1 raw11530step1Labels permutation14 hz
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw11531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11531step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11531step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw11531step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11531 raw11531Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11531 raw11531Labels = mixedMoment B raw11531step0 raw11531step0Labels := by
      have hz : ∀ j, raw11531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11531step0 = (fun i j => raw11531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11531step0 raw11531; decide +kernel
      have hl : raw11531step0Labels = raw11531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11531 raw11531Labels permutation434 hz
    mixedMoment B raw11531step0 raw11531step0Labels = mixedMoment B raw11531step1 raw11531step1Labels := by
      have hz : ∀ j, raw11531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11531step1 = (fun i j => raw11531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11531step1 raw11531step0; decide +kernel
      have hl : raw11531step1Labels = raw11531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11531step0 raw11531step0Labels permutation80 hz
    mixedMoment B raw11531step1 raw11531step1Labels = mixedMoment B raw11531step2 raw11531step2Labels := by
      have hz : ∀ i, raw11531step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11531step2 = (fun i j => raw11531step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11531step2 raw11531step1; decide +kernel
      have hl : raw11531step2Labels = (fun j => raw11531step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11531step1 raw11531step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw11532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11532step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw11532step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11532step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11532step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11532 raw11532Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11532 raw11532Labels = mixedMoment B raw11532step0 raw11532step0Labels := by
      have hz : ∀ j, raw11532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11532step0 = (fun i j => raw11532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11532step0 raw11532; decide +kernel
      have hl : raw11532step0Labels = raw11532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11532 raw11532Labels permutation434 hz
    mixedMoment B raw11532step0 raw11532step0Labels = mixedMoment B raw11532step1 raw11532step1Labels := by
      have hz : ∀ i, raw11532step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11532step1 = (fun i j => raw11532step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11532step1 raw11532step0; decide +kernel
      have hl : raw11532step1Labels = (fun j => raw11532step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11532step0 raw11532step0Labels permutation6 hz
    mixedMoment B raw11532step1 raw11532step1Labels = mixedMoment B raw11532step2 raw11532step2Labels := by
      have ha : raw11532step2 = (fun i j => raw11532step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11532step2 raw11532step1; decide +kernel
      have hl : raw11532step2Labels = raw11532step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11532step1 raw11532step1Labels permutation38 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw11533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11533step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw11533step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11533step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11533step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11533 raw11533Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11533 raw11533Labels = mixedMoment B raw11533step0 raw11533step0Labels := by
      have hz : ∀ j, raw11533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11533step0 = (fun i j => raw11533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11533step0 raw11533; decide +kernel
      have hl : raw11533step0Labels = raw11533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11533 raw11533Labels permutation346 hz
    mixedMoment B raw11533step0 raw11533step0Labels = mixedMoment B raw11533step1 raw11533step1Labels := by
      have hz : ∀ i, raw11533step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11533step1 = (fun i j => raw11533step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11533step1 raw11533step0; decide +kernel
      have hl : raw11533step1Labels = (fun j => raw11533step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11533step0 raw11533step0Labels permutation6 hz
    mixedMoment B raw11533step1 raw11533step1Labels = mixedMoment B raw11533step2 raw11533step2Labels := by
      have ha : raw11533step2 = (fun i j => raw11533step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11533step2 raw11533step1; decide +kernel
      have hl : raw11533step2Labels = raw11533step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11533step1 raw11533step1Labels permutation38 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw11534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11534step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw11534step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11534 raw11534Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11534 raw11534Labels = mixedMoment B raw11534step0 raw11534step0Labels := by
      have hz : ∀ j, raw11534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11534step0 = (fun i j => raw11534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11534step0 raw11534; decide +kernel
      have hl : raw11534step0Labels = raw11534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11534 raw11534Labels permutation434 hz
    mixedMoment B raw11534step0 raw11534step0Labels = mixedMoment B raw11534step1 raw11534step1Labels := by
      have hz : ∀ j, raw11534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11534step1 = (fun i j => raw11534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11534step1 raw11534step0; decide +kernel
      have hl : raw11534step1Labels = raw11534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11534step0 raw11534step0Labels permutation56 hz
    mixedMoment B raw11534step1 raw11534step1Labels = mixedMoment B raw11534step2 raw11534step2Labels := by
      have hz : ∀ i, raw11534step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11534step2 = (fun i j => raw11534step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11534step2 raw11534step1; decide +kernel
      have hl : raw11534step2Labels = (fun j => raw11534step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11534step1 raw11534step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw11535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11535step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11535step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11535 raw11535Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11535 raw11535Labels = mixedMoment B raw11535step0 raw11535step0Labels := by
      have hz : ∀ j, raw11535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11535step0 = (fun i j => raw11535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11535step0 raw11535; decide +kernel
      have hl : raw11535step0Labels = raw11535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11535 raw11535Labels permutation434 hz
    mixedMoment B raw11535step0 raw11535step0Labels = mixedMoment B raw11535step1 raw11535step1Labels := by
      have hz : ∀ i, raw11535step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11535step1 = (fun i j => raw11535step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11535step1 raw11535step0; decide +kernel
      have hl : raw11535step1Labels = (fun j => raw11535step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11535step0 raw11535step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw11536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11536step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw11536step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11536step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11536step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11536 raw11536Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11536 raw11536Labels = mixedMoment B raw11536step0 raw11536step0Labels := by
      have hz : ∀ j, raw11536 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11536step0 = (fun i j => raw11536 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11536step0 raw11536; decide +kernel
      have hl : raw11536step0Labels = raw11536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11536 raw11536Labels permutation265 hz
    mixedMoment B raw11536step0 raw11536step0Labels = mixedMoment B raw11536step1 raw11536step1Labels := by
      have hz : ∀ i, raw11536step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11536step1 = (fun i j => raw11536step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11536step1 raw11536step0; decide +kernel
      have hl : raw11536step1Labels = (fun j => raw11536step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11536step0 raw11536step0Labels permutation6 hz
    mixedMoment B raw11536step1 raw11536step1Labels = mixedMoment B raw11536step2 raw11536step2Labels := by
      have ha : raw11536step2 = (fun i j => raw11536step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11536step2 raw11536step1; decide +kernel
      have hl : raw11536step2Labels = raw11536step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11536step1 raw11536step1Labels permutation38 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw11537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11537step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11537step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw11537step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11537 raw11537Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11537 raw11537Labels = mixedMoment B raw11537step0 raw11537step0Labels := by
      have hz : ∀ j, raw11537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11537step0 = (fun i j => raw11537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11537step0 raw11537; decide +kernel
      have hl : raw11537step0Labels = raw11537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11537 raw11537Labels permutation346 hz
    mixedMoment B raw11537step0 raw11537step0Labels = mixedMoment B raw11537step1 raw11537step1Labels := by
      have hz : ∀ j, raw11537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11537step1 = (fun i j => raw11537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11537step1 raw11537step0; decide +kernel
      have hl : raw11537step1Labels = raw11537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11537step0 raw11537step0Labels permutation56 hz
    mixedMoment B raw11537step1 raw11537step1Labels = mixedMoment B raw11537step2 raw11537step2Labels := by
      have hz : ∀ i, raw11537step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11537step2 = (fun i j => raw11537step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11537step2 raw11537step1; decide +kernel
      have hl : raw11537step2Labels = (fun j => raw11537step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11537step1 raw11537step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw11538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11538step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11538step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11538 raw11538Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11538 raw11538Labels = mixedMoment B raw11538step0 raw11538step0Labels := by
      have hz : ∀ j, raw11538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11538step0 = (fun i j => raw11538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11538step0 raw11538; decide +kernel
      have hl : raw11538step0Labels = raw11538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11538 raw11538Labels permutation346 hz
    mixedMoment B raw11538step0 raw11538step0Labels = mixedMoment B raw11538step1 raw11538step1Labels := by
      have hz : ∀ i, raw11538step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11538step1 = (fun i j => raw11538step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11538step1 raw11538step0; decide +kernel
      have hl : raw11538step1Labels = (fun j => raw11538step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11538step0 raw11538step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw11539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw11539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11539step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw11539step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11539 raw11539Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11539 raw11539Labels = mixedMoment B raw11539step0 raw11539step0Labels := by
      have hz : ∀ j, raw11539 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11539step0 = (fun i j => raw11539 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11539step0 raw11539; decide +kernel
      have hl : raw11539step0Labels = raw11539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11539 raw11539Labels permutation265 hz
    mixedMoment B raw11539step0 raw11539step0Labels = mixedMoment B raw11539step1 raw11539step1Labels := by
      have hz : ∀ i, raw11539step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11539step1 = (fun i j => raw11539step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11539step1 raw11539step0; decide +kernel
      have hl : raw11539step1Labels = (fun j => raw11539step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11539step0 raw11539step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw11540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11540step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11540step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11540step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11540step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw11540step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11540 raw11540Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw11540 raw11540Labels = mixedMoment B raw11540step0 raw11540step0Labels := by
      have hz : ∀ j, raw11540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11540step0 = (fun i j => raw11540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11540step0 raw11540; decide +kernel
      have hl : raw11540step0Labels = raw11540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540 raw11540Labels permutation434 hz
    mixedMoment B raw11540step0 raw11540step0Labels = mixedMoment B raw11540step1 raw11540step1Labels := by
      have hz : ∀ j, raw11540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11540step1 = (fun i j => raw11540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11540step1 raw11540step0; decide +kernel
      have hl : raw11540step1Labels = raw11540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540step0 raw11540step0Labels permutation80 hz
    mixedMoment B raw11540step1 raw11540step1Labels = mixedMoment B raw11540step2 raw11540step2Labels := by
      have hz : ∀ j, raw11540step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11540step2 = (fun i j => raw11540step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11540step2 raw11540step1; decide +kernel
      have hl : raw11540step2Labels = raw11540step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540step1 raw11540step1Labels permutation14 hz
    mixedMoment B raw11540step2 raw11540step2Labels = mixedMoment B raw11540step3 raw11540step3Labels := by
      have hz : ∀ i, raw11540step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11540step3 = (fun i j => raw11540step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11540step3 raw11540step2; decide +kernel
      have hl : raw11540step3Labels = (fun j => raw11540step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11540step2 raw11540step2Labels permutation6 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

def raw11541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11541step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11541step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw11541step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11541 raw11541Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11541 raw11541Labels = mixedMoment B raw11541step0 raw11541step0Labels := by
      have hz : ∀ j, raw11541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11541step0 = (fun i j => raw11541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11541step0 raw11541; decide +kernel
      have hl : raw11541step0Labels = raw11541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11541 raw11541Labels permutation434 hz
    mixedMoment B raw11541step0 raw11541step0Labels = mixedMoment B raw11541step1 raw11541step1Labels := by
      have hz : ∀ j, raw11541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11541step1 = (fun i j => raw11541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11541step1 raw11541step0; decide +kernel
      have hl : raw11541step1Labels = raw11541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11541step0 raw11541step0Labels permutation80 hz
    mixedMoment B raw11541step1 raw11541step1Labels = mixedMoment B raw11541step2 raw11541step2Labels := by
      have hz : ∀ i, raw11541step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11541step2 = (fun i j => raw11541step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11541step2 raw11541step1; decide +kernel
      have hl : raw11541step2Labels = (fun j => raw11541step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11541step1 raw11541step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw11542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11542step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11542step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw11542step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11542 raw11542Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11542 raw11542Labels = mixedMoment B raw11542step0 raw11542step0Labels := by
      have hz : ∀ j, raw11542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11542step0 = (fun i j => raw11542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11542step0 raw11542; decide +kernel
      have hl : raw11542step0Labels = raw11542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11542 raw11542Labels permutation434 hz
    mixedMoment B raw11542step0 raw11542step0Labels = mixedMoment B raw11542step1 raw11542step1Labels := by
      have hz : ∀ j, raw11542step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11542step1 = (fun i j => raw11542step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11542step1 raw11542step0; decide +kernel
      have hl : raw11542step1Labels = raw11542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11542step0 raw11542step0Labels permutation56 hz
    mixedMoment B raw11542step1 raw11542step1Labels = mixedMoment B raw11542step2 raw11542step2Labels := by
      have hz : ∀ i, raw11542step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11542step2 = (fun i j => raw11542step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11542step2 raw11542step1; decide +kernel
      have hl : raw11542step2Labels = (fun j => raw11542step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11542step1 raw11542step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw11543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw11543step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11543step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw11543step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11543 raw11543Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11543 raw11543Labels = mixedMoment B raw11543step0 raw11543step0Labels := by
      have hz : ∀ j, raw11543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11543step0 = (fun i j => raw11543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11543step0 raw11543; decide +kernel
      have hl : raw11543step0Labels = raw11543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11543 raw11543Labels permutation346 hz
    mixedMoment B raw11543step0 raw11543step0Labels = mixedMoment B raw11543step1 raw11543step1Labels := by
      have hz : ∀ j, raw11543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11543step1 = (fun i j => raw11543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11543step1 raw11543step0; decide +kernel
      have hl : raw11543step1Labels = raw11543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11543step0 raw11543step0Labels permutation56 hz
    mixedMoment B raw11543step1 raw11543step1Labels = mixedMoment B raw11543step2 raw11543step2Labels := by
      have hz : ∀ i, raw11543step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11543step2 = (fun i j => raw11543step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11543step2 raw11543step1; decide +kernel
      have hl : raw11543step2Labels = (fun j => raw11543step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11543step1 raw11543step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw11544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11544step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11544step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11544step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11544step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11544 raw11544Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw11544 raw11544Labels = mixedMoment B raw11544step0 raw11544step0Labels := by
      have ha : raw11544step0 = (fun i j => raw11544 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11544step0 raw11544; decide +kernel
      have hl : raw11544step0Labels = raw11544Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11544 raw11544Labels permutation160 permutation7
    mixedMoment B raw11544step0 raw11544step0Labels = mixedMoment B raw11544step1 raw11544step1Labels := by
      have ha : raw11544step1 = -raw11544step0 := by apply Matrix.ext; change ∀ i j, raw11544step1 i j = -(raw11544step0 i j); unfold raw11544step1 raw11544step0; decide +kernel
      have hl : raw11544step1Labels = raw11544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11544step1 raw11544step1Labels = mixedMoment B raw11544step2 raw11544step2Labels := by
      have ha : raw11544step2 = raw11544step1 := by apply Matrix.ext; unfold raw11544step2 raw11544step1; decide +kernel
      have hl : raw11544step1Labels = labelEmbedding10 ∘ raw11544step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11544step1 raw11544step1Labels raw11544step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw11545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw11545step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11545step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11545step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11545step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11545 raw11545Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw11545 raw11545Labels = mixedMoment B raw11545step0 raw11545step0Labels := by
      have ha : raw11545step0 = (fun i j => raw11545 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11545step0 raw11545; decide +kernel
      have hl : raw11545step0Labels = raw11545Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11545 raw11545Labels permutation160 permutation7
    mixedMoment B raw11545step0 raw11545step0Labels = mixedMoment B raw11545step1 raw11545step1Labels := by
      have ha : raw11545step1 = -raw11545step0 := by apply Matrix.ext; change ∀ i j, raw11545step1 i j = -(raw11545step0 i j); unfold raw11545step1 raw11545step0; decide +kernel
      have hl : raw11545step1Labels = raw11545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11545step1 raw11545step1Labels = mixedMoment B raw11545step2 raw11545step2Labels := by
      have ha : raw11545step2 = raw11545step1 := by apply Matrix.ext; unfold raw11545step2 raw11545step1; decide +kernel
      have hl : raw11545step1Labels = labelEmbedding10 ∘ raw11545step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11545step1 raw11545step1Labels raw11545step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw11546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11546step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11546step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11546step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11546 raw11546Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw11546 raw11546Labels = mixedMoment B raw11546step0 raw11546step0Labels := by
      have hz : ∀ j, raw11546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11546step0 = (fun i j => raw11546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11546step0 raw11546; decide +kernel
      have hl : raw11546step0Labels = raw11546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11546 raw11546Labels permutation434 hz
    mixedMoment B raw11546step0 raw11546step0Labels = mixedMoment B raw11546step1 raw11546step1Labels := by
      have ha : raw11546step1 = (fun i j => raw11546step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11546step1 raw11546step0; decide +kernel
      have hl : raw11546step1Labels = raw11546step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11546step0 raw11546step0Labels permutation34 permutation7
    mixedMoment B raw11546step1 raw11546step1Labels = mixedMoment B raw11546step2 raw11546step2Labels := by
      have ha : raw11546step2 = -raw11546step1 := by apply Matrix.ext; change ∀ i j, raw11546step2 i j = -(raw11546step1 i j); unfold raw11546step2 raw11546step1; decide +kernel
      have hl : raw11546step2Labels = raw11546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11546step2 raw11546step2Labels = mixedMoment B raw11546step3 raw11546step3Labels := by
      have ha : raw11546step3 = raw11546step2 := by apply Matrix.ext; unfold raw11546step3 raw11546step2; decide +kernel
      have hl : raw11546step2Labels = labelEmbedding10 ∘ raw11546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11546step2 raw11546step2Labels raw11546step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw11547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11547step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11547step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11547step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11547step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11547 raw11547Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw11547 raw11547Labels = mixedMoment B raw11547step0 raw11547step0Labels := by
      have hz : ∀ j, raw11547 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11547step0 = (fun i j => raw11547 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11547step0 raw11547; decide +kernel
      have hl : raw11547step0Labels = raw11547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11547 raw11547Labels permutation520 hz
    mixedMoment B raw11547step0 raw11547step0Labels = mixedMoment B raw11547step1 raw11547step1Labels := by
      have ha : raw11547step1 = (fun i j => raw11547step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11547step1 raw11547step0; decide +kernel
      have hl : raw11547step1Labels = raw11547step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11547step0 raw11547step0Labels permutation34 permutation7
    mixedMoment B raw11547step1 raw11547step1Labels = mixedMoment B raw11547step2 raw11547step2Labels := by
      have ha : raw11547step2 = -raw11547step1 := by apply Matrix.ext; change ∀ i j, raw11547step2 i j = -(raw11547step1 i j); unfold raw11547step2 raw11547step1; decide +kernel
      have hl : raw11547step2Labels = raw11547step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11547step2 raw11547step2Labels = mixedMoment B raw11547step3 raw11547step3Labels := by
      have ha : raw11547step3 = raw11547step2 := by apply Matrix.ext; unfold raw11547step3 raw11547step2; decide +kernel
      have hl : raw11547step2Labels = labelEmbedding10 ∘ raw11547step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11547step2 raw11547step2Labels raw11547step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw11548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11548step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11548 raw11548Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw11548 raw11548Labels = mixedMoment B raw11548step0 raw11548step0Labels := by
      have ha : raw11548step0 = (fun i j => raw11548 (permutation640 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11548step0 raw11548; decide +kernel
      have hl : raw11548step0Labels = raw11548Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11548 raw11548Labels permutation640 permutation6
    mixedMoment B raw11548step0 raw11548step0Labels = mixedMoment B raw11548step1 raw11548step1Labels := by
      have ha : raw11548step1 = raw11548step0 := by apply Matrix.ext; unfold raw11548step1 raw11548step0; decide +kernel
      have hl : raw11548step0Labels = labelEmbedding9 ∘ raw11548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11548step0 raw11548step0Labels raw11548step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw11549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11549step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11549 raw11549Labels = mixedMoment B node4595 node4595Labels := by
  calc
    mixedMoment B raw11549 raw11549Labels = mixedMoment B raw11549step0 raw11549step0Labels := by
      have ha : raw11549step0 = (fun i j => raw11549 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11549step0 raw11549; decide +kernel
      have hl : raw11549step0Labels = raw11549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11549 raw11549Labels permutation197 permutation3
    mixedMoment B raw11549step0 raw11549step0Labels = mixedMoment B raw11549step1 raw11549step1Labels := by
      have ha : raw11549step1 = raw11549step0 := by apply Matrix.ext; unfold raw11549step1 raw11549step0; decide +kernel
      have hl : raw11549step0Labels = labelEmbedding6 ∘ raw11549step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11549step0 raw11549step0Labels raw11549step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4595 node4595Labels := by rfl

def raw11550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11550 raw11550Labels = mixedMoment B node5196 node5196Labels := by
  calc
    mixedMoment B raw11550 raw11550Labels = mixedMoment B raw11550step0 raw11550step0Labels := by
      have ha : raw11550step0 = (fun i j => raw11550 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11550step0 raw11550; decide +kernel
      have hl : raw11550step0Labels = raw11550Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11550 raw11550Labels permutation176 permutation2
    _ = mixedMoment B node5196 node5196Labels := by rfl

def raw11551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11551step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11551 raw11551Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw11551 raw11551Labels = mixedMoment B raw11551step0 raw11551step0Labels := by
      have hz : ∀ j, raw11551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11551step0 = (fun i j => raw11551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11551step0 raw11551; decide +kernel
      have hl : raw11551step0Labels = raw11551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11551 raw11551Labels permutation434 hz
    mixedMoment B raw11551step0 raw11551step0Labels = mixedMoment B raw11551step1 raw11551step1Labels := by
      have ha : raw11551step1 = (fun i j => raw11551step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11551step1 raw11551step0; decide +kernel
      have hl : raw11551step1Labels = raw11551step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11551step0 raw11551step0Labels permutation38 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw11552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11552step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11552 raw11552Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw11552 raw11552Labels = mixedMoment B raw11552step0 raw11552step0Labels := by
      have hz : ∀ j, raw11552 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11552step0 = (fun i j => raw11552 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11552step0 raw11552; decide +kernel
      have hl : raw11552step0Labels = raw11552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11552 raw11552Labels permutation520 hz
    mixedMoment B raw11552step0 raw11552step0Labels = mixedMoment B raw11552step1 raw11552step1Labels := by
      have ha : raw11552step1 = (fun i j => raw11552step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11552step1 raw11552step0; decide +kernel
      have hl : raw11552step1Labels = raw11552step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11552step0 raw11552step0Labels permutation38 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw11553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw11553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11553 raw11553Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw11553 raw11553Labels = mixedMoment B raw11553step0 raw11553step0Labels := by
      have ha : raw11553step0 = (fun i j => raw11553 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11553step0 raw11553; decide +kernel
      have hl : raw11553step0Labels = raw11553Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11553 raw11553Labels permutation194 permutation2
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw11554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11554 raw11554Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw11554 raw11554Labels = mixedMoment B raw11554step0 raw11554step0Labels := by
      have ha : raw11554step0 = (fun i j => raw11554 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11554step0 raw11554; decide +kernel
      have hl : raw11554step0Labels = raw11554Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11554 raw11554Labels permutation160 permutation2
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw11555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11555 raw11555Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw11555 raw11555Labels = mixedMoment B raw11555step0 raw11555step0Labels := by
      have ha : raw11555step0 = (fun i j => raw11555 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11555step0 raw11555; decide +kernel
      have hl : raw11555step0Labels = raw11555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11555 raw11555Labels permutation160 permutation2
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw11556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11556 raw11556Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw11556 raw11556Labels = mixedMoment B raw11556step0 raw11556step0Labels := by
      have hz : ∀ j, raw11556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11556step0 = (fun i j => raw11556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11556step0 raw11556; decide +kernel
      have hl : raw11556step0Labels = raw11556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11556 raw11556Labels permutation434 hz
    mixedMoment B raw11556step0 raw11556step0Labels = mixedMoment B raw11556step1 raw11556step1Labels := by
      have ha : raw11556step1 = (fun i j => raw11556step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11556step1 raw11556step0; decide +kernel
      have hl : raw11556step1Labels = raw11556step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11556step0 raw11556step0Labels permutation34 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw11557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11557 raw11557Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw11557 raw11557Labels = mixedMoment B raw11557step0 raw11557step0Labels := by
      have hz : ∀ j, raw11557 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11557step0 = (fun i j => raw11557 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11557step0 raw11557; decide +kernel
      have hl : raw11557step0Labels = raw11557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11557 raw11557Labels permutation520 hz
    mixedMoment B raw11557step0 raw11557step0Labels = mixedMoment B raw11557step1 raw11557step1Labels := by
      have ha : raw11557step1 = (fun i j => raw11557step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11557step1 raw11557step0; decide +kernel
      have hl : raw11557step1Labels = raw11557step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11557step0 raw11557step0Labels permutation34 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw11558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11558 raw11558Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw11558 raw11558Labels = mixedMoment B raw11558step0 raw11558step0Labels := by
      have ha : raw11558step0 = (fun i j => raw11558 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11558step0 raw11558; decide +kernel
      have hl : raw11558step0Labels = raw11558Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11558 raw11558Labels permutation173 permutation2
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw11559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11559step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11559 raw11559Labels = mixedMoment B node4587 node4587Labels := by
  calc
    mixedMoment B raw11559 raw11559Labels = mixedMoment B raw11559step0 raw11559step0Labels := by
      have ha : raw11559step0 = (fun i j => raw11559 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11559step0 raw11559; decide +kernel
      have hl : raw11559step0Labels = raw11559Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11559 raw11559Labels permutation181 permutation3
    mixedMoment B raw11559step0 raw11559step0Labels = mixedMoment B raw11559step1 raw11559step1Labels := by
      have ha : raw11559step1 = raw11559step0 := by apply Matrix.ext; unfold raw11559step1 raw11559step0; decide +kernel
      have hl : raw11559step0Labels = labelEmbedding6 ∘ raw11559step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11559step0 raw11559step0Labels raw11559step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4587 node4587Labels := by rfl

def raw11560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11560 raw11560Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw11560 raw11560Labels = mixedMoment B raw11560step0 raw11560step0Labels := by
      have ha : raw11560step0 = (fun i j => raw11560 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11560step0 raw11560; decide +kernel
      have hl : raw11560step0Labels = raw11560Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11560 raw11560Labels permutation155 permutation2
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw11561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11561 raw11561Labels = mixedMoment B node5186 node5186Labels := by
  calc
    mixedMoment B raw11561 raw11561Labels = mixedMoment B raw11561step0 raw11561step0Labels := by
      have ha : raw11561step0 = (fun i j => raw11561 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11561step0 raw11561; decide +kernel
      have hl : raw11561step0Labels = raw11561Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11561 raw11561Labels permutation179 permutation2
    _ = mixedMoment B node5186 node5186Labels := by rfl

def raw11562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11562 raw11562Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw11562 raw11562Labels = mixedMoment B raw11562step0 raw11562step0Labels := by
      have hz : ∀ j, raw11562 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11562step0 = (fun i j => raw11562 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11562step0 raw11562; decide +kernel
      have hl : raw11562step0Labels = raw11562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11562 raw11562Labels permutation520 hz
    mixedMoment B raw11562step0 raw11562step0Labels = mixedMoment B raw11562step1 raw11562step1Labels := by
      have ha : raw11562step1 = (fun i j => raw11562step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11562step1 raw11562step0; decide +kernel
      have hl : raw11562step1Labels = raw11562step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11562step0 raw11562step0Labels permutation33 permutation2
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw11563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11563 raw11563Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw11563 raw11563Labels = mixedMoment B raw11563step0 raw11563step0Labels := by
      have ha : raw11563step0 = (fun i j => raw11563 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11563step0 raw11563; decide +kernel
      have hl : raw11563step0Labels = raw11563Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11563 raw11563Labels permutation157 permutation2
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw11564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11564step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11564 raw11564Labels = mixedMoment B node4587 node4587Labels := by
  calc
    mixedMoment B raw11564 raw11564Labels = mixedMoment B raw11564step0 raw11564step0Labels := by
      have ha : raw11564step0 = (fun i j => raw11564 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11564step0 raw11564; decide +kernel
      have hl : raw11564step0Labels = raw11564Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11564 raw11564Labels permutation180 permutation3
    mixedMoment B raw11564step0 raw11564step0Labels = mixedMoment B raw11564step1 raw11564step1Labels := by
      have ha : raw11564step1 = raw11564step0 := by apply Matrix.ext; unfold raw11564step1 raw11564step0; decide +kernel
      have hl : raw11564step0Labels = labelEmbedding6 ∘ raw11564step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11564step0 raw11564step0Labels raw11564step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4587 node4587Labels := by rfl

def raw11565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11565 raw11565Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw11565 raw11565Labels = mixedMoment B raw11565step0 raw11565step0Labels := by
      have ha : raw11565step0 = (fun i j => raw11565 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11565step0 raw11565; decide +kernel
      have hl : raw11565step0Labels = raw11565Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11565 raw11565Labels permutation153 permutation2
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw11566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11566 raw11566Labels = mixedMoment B node5186 node5186Labels := by
  calc
    mixedMoment B raw11566 raw11566Labels = mixedMoment B raw11566step0 raw11566step0Labels := by
      have ha : raw11566step0 = (fun i j => raw11566 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11566step0 raw11566; decide +kernel
      have hl : raw11566step0Labels = raw11566Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11566 raw11566Labels permutation177 permutation2
    _ = mixedMoment B node5186 node5186Labels := by rfl

def raw11567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11567 raw11567Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw11567 raw11567Labels = mixedMoment B raw11567step0 raw11567step0Labels := by
      have hz : ∀ j, raw11567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11567step0 = (fun i j => raw11567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11567step0 raw11567; decide +kernel
      have hl : raw11567step0Labels = raw11567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11567 raw11567Labels permutation434 hz
    mixedMoment B raw11567step0 raw11567step0Labels = mixedMoment B raw11567step1 raw11567step1Labels := by
      have ha : raw11567step1 = (fun i j => raw11567step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11567step1 raw11567step0; decide +kernel
      have hl : raw11567step1Labels = raw11567step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11567step0 raw11567step0Labels permutation33 permutation2
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw11568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw11568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11568 raw11568Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw11568 raw11568Labels = mixedMoment B raw11568step0 raw11568step0Labels := by
      have ha : raw11568step0 = (fun i j => raw11568 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11568step0 raw11568; decide +kernel
      have hl : raw11568step0Labels = raw11568Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11568 raw11568Labels permutation156 permutation2
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw11569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11569 raw11569Labels = mixedMoment B node4589 node4589Labels := by
  calc
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw11570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11570 raw11570Labels = mixedMoment B node5072 node5072Labels := by
  calc
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw11571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11571 raw11571Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw11571 raw11571Labels = mixedMoment B raw11571step0 raw11571step0Labels := by
      have ha : raw11571step0 = (fun i j => raw11571 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11571step0 raw11571; decide +kernel
      have hl : raw11571step0Labels = raw11571Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11571 raw11571Labels permutation176 permutation2
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw11572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11572 raw11572Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw11572 raw11572Labels = mixedMoment B raw11572step0 raw11572step0Labels := by
      have hz : ∀ j, raw11572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11572step0 = (fun i j => raw11572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11572step0 raw11572; decide +kernel
      have hl : raw11572step0Labels = raw11572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11572 raw11572Labels permutation434 hz
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw11573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11573 raw11573Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw11573 raw11573Labels = mixedMoment B raw11573step0 raw11573step0Labels := by
      have hz : ∀ j, raw11573 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11573step0 = (fun i j => raw11573 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11573step0 raw11573; decide +kernel
      have hl : raw11573step0Labels = raw11573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11573 raw11573Labels permutation520 hz
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw11574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11574 raw11574Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw11574 raw11574Labels = mixedMoment B raw11574step0 raw11574step0Labels := by
      have ha : raw11574step0 = (fun i j => raw11574 (permutation640 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11574step0 raw11574; decide +kernel
      have hl : raw11574step0Labels = raw11574Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11574 raw11574Labels permutation640 permutation6
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw11575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11575 raw11575Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw11575 raw11575Labels = mixedMoment B raw11575step0 raw11575step0Labels := by
      have ha : raw11575step0 = (fun i j => raw11575 (permutation640 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11575step0 raw11575; decide +kernel
      have hl : raw11575step0Labels = raw11575Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11575 raw11575Labels permutation640 permutation6
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw11576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11576 raw11576Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw11576 raw11576Labels = mixedMoment B raw11576step0 raw11576step0Labels := by
      have hz : ∀ j, raw11576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11576step0 = (fun i j => raw11576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11576step0 raw11576; decide +kernel
      have hl : raw11576step0Labels = raw11576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11576 raw11576Labels permutation434 hz
    mixedMoment B raw11576step0 raw11576step0Labels = mixedMoment B raw11576step1 raw11576step1Labels := by
      have ha : raw11576step1 = (fun i j => raw11576step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11576step1 raw11576step0; decide +kernel
      have hl : raw11576step1Labels = raw11576step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11576step0 raw11576step0Labels permutation145 permutation6
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw11577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11577 raw11577Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw11577 raw11577Labels = mixedMoment B raw11577step0 raw11577step0Labels := by
      have hz : ∀ j, raw11577 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11577step0 = (fun i j => raw11577 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11577step0 raw11577; decide +kernel
      have hl : raw11577step0Labels = raw11577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11577 raw11577Labels permutation520 hz
    mixedMoment B raw11577step0 raw11577step0Labels = mixedMoment B raw11577step1 raw11577step1Labels := by
      have ha : raw11577step1 = (fun i j => raw11577step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11577step1 raw11577step0; decide +kernel
      have hl : raw11577step1Labels = raw11577step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11577step0 raw11577step0Labels permutation145 permutation6
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw11578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11578 raw11578Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw11578 raw11578Labels = mixedMoment B raw11578step0 raw11578step0Labels := by
      have ha : raw11578step0 = (fun i j => raw11578 (permutation640 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11578step0 raw11578; decide +kernel
      have hl : raw11578step0Labels = raw11578Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11578 raw11578Labels permutation640 permutation6
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw11579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11579 raw11579Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw11579 raw11579Labels = mixedMoment B raw11579step0 raw11579step0Labels := by
      have ha : raw11579step0 = (fun i j => raw11579 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11579step0 raw11579; decide +kernel
      have hl : raw11579step0Labels = raw11579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11579 raw11579Labels permutation197 permutation3
    _ = mixedMoment B node1228 node1228Labels := by rfl

def raw11580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11580 raw11580Labels = mixedMoment B node2874 node2874Labels := by
  calc
    mixedMoment B raw11580 raw11580Labels = mixedMoment B raw11580step0 raw11580step0Labels := by
      have ha : raw11580step0 = (fun i j => raw11580 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11580step0 raw11580; decide +kernel
      have hl : raw11580step0Labels = raw11580Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11580 raw11580Labels permutation197 permutation3
    _ = mixedMoment B node2874 node2874Labels := by rfl

def raw11581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11581 raw11581Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11581 raw11581Labels = mixedMoment B raw11581step0 raw11581step0Labels := by
      have hz : ∀ j, raw11581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11581step0 = (fun i j => raw11581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11581step0 raw11581; decide +kernel
      have hl : raw11581step0Labels = raw11581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11581 raw11581Labels permutation434 hz
    mixedMoment B raw11581step0 raw11581step0Labels = mixedMoment B raw11581step1 raw11581step1Labels := by
      have ha : raw11581step1 = (fun i j => raw11581step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11581step1 raw11581step0; decide +kernel
      have hl : raw11581step1Labels = raw11581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11581step0 raw11581step0Labels permutation43 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw11582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11582 raw11582Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11582 raw11582Labels = mixedMoment B raw11582step0 raw11582step0Labels := by
      have hz : ∀ j, raw11582 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11582step0 = (fun i j => raw11582 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11582step0 raw11582; decide +kernel
      have hl : raw11582step0Labels = raw11582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11582 raw11582Labels permutation520 hz
    mixedMoment B raw11582step0 raw11582step0Labels = mixedMoment B raw11582step1 raw11582step1Labels := by
      have ha : raw11582step1 = (fun i j => raw11582step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11582step1 raw11582step0; decide +kernel
      have hl : raw11582step1Labels = raw11582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11582step0 raw11582step0Labels permutation43 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw11583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11583 raw11583Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw11583 raw11583Labels = mixedMoment B raw11583step0 raw11583step0Labels := by
      have ha : raw11583step0 = (fun i j => raw11583 (permutation255 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11583step0 raw11583; decide +kernel
      have hl : raw11583step0Labels = raw11583Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11583 raw11583Labels permutation255 permutation3
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw11584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11584 raw11584Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw11584 raw11584Labels = mixedMoment B raw11584step0 raw11584step0Labels := by
      have ha : raw11584step0 = (fun i j => raw11584 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11584step0 raw11584; decide +kernel
      have hl : raw11584step0Labels = raw11584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11584 raw11584Labels permutation170 permutation3
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw11585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11585 raw11585Labels = mixedMoment B node2996 node2996Labels := by
  calc
    mixedMoment B raw11585 raw11585Labels = mixedMoment B raw11585step0 raw11585step0Labels := by
      have ha : raw11585step0 = (fun i j => raw11585 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11585step0 raw11585; decide +kernel
      have hl : raw11585step0Labels = raw11585Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11585 raw11585Labels permutation170 permutation3
    _ = mixedMoment B node2996 node2996Labels := by rfl

def raw11586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11586 raw11586Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11586 raw11586Labels = mixedMoment B raw11586step0 raw11586step0Labels := by
      have hz : ∀ j, raw11586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11586step0 = (fun i j => raw11586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11586step0 raw11586; decide +kernel
      have hl : raw11586step0Labels = raw11586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11586 raw11586Labels permutation434 hz
    mixedMoment B raw11586step0 raw11586step0Labels = mixedMoment B raw11586step1 raw11586step1Labels := by
      have ha : raw11586step1 = (fun i j => raw11586step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11586step1 raw11586step0; decide +kernel
      have hl : raw11586step1Labels = raw11586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11586step0 raw11586step0Labels permutation36 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw11587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11587 raw11587Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11587 raw11587Labels = mixedMoment B raw11587step0 raw11587step0Labels := by
      have hz : ∀ j, raw11587 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11587step0 = (fun i j => raw11587 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11587step0 raw11587; decide +kernel
      have hl : raw11587step0Labels = raw11587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11587 raw11587Labels permutation520 hz
    mixedMoment B raw11587step0 raw11587step0Labels = mixedMoment B raw11587step1 raw11587step1Labels := by
      have ha : raw11587step1 = (fun i j => raw11587step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11587step1 raw11587step0; decide +kernel
      have hl : raw11587step1Labels = raw11587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11587step0 raw11587step0Labels permutation36 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw11588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11588 raw11588Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11588 raw11588Labels = mixedMoment B raw11588step0 raw11588step0Labels := by
      have ha : raw11588step0 = (fun i j => raw11588 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11588step0 raw11588; decide +kernel
      have hl : raw11588step0Labels = raw11588Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11588 raw11588Labels permutation246 permutation3
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw11589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11589 raw11589Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw11589 raw11589Labels = mixedMoment B raw11589step0 raw11589step0Labels := by
      have ha : raw11589step0 = (fun i j => raw11589 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11589step0 raw11589; decide +kernel
      have hl : raw11589step0Labels = raw11589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11589 raw11589Labels permutation181 permutation3
    _ = mixedMoment B node1210 node1210Labels := by rfl

def raw11590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11590 raw11590Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw11590 raw11590Labels = mixedMoment B raw11590step0 raw11590step0Labels := by
      have ha : raw11590step0 = (fun i j => raw11590 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11590step0 raw11590; decide +kernel
      have hl : raw11590step0Labels = raw11590Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11590 raw11590Labels permutation157 permutation3
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw11591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11591 raw11591Labels = mixedMoment B node2860 node2860Labels := by
  calc
    mixedMoment B raw11591 raw11591Labels = mixedMoment B raw11591step0 raw11591step0Labels := by
      have ha : raw11591step0 = (fun i j => raw11591 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11591step0 raw11591; decide +kernel
      have hl : raw11591step0Labels = raw11591Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11591 raw11591Labels permutation181 permutation3
    _ = mixedMoment B node2860 node2860Labels := by rfl

def raw11592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11592 raw11592Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw11592 raw11592Labels = mixedMoment B raw11592step0 raw11592step0Labels := by
      have hz : ∀ j, raw11592 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11592step0 = (fun i j => raw11592 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11592step0 raw11592; decide +kernel
      have hl : raw11592step0Labels = raw11592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11592 raw11592Labels permutation520 hz
    mixedMoment B raw11592step0 raw11592step0Labels = mixedMoment B raw11592step1 raw11592step1Labels := by
      have ha : raw11592step1 = (fun i j => raw11592step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11592step1 raw11592step0; decide +kernel
      have hl : raw11592step1Labels = raw11592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11592step0 raw11592step0Labels permutation39 permutation3
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw11593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw11593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11593 raw11593Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw11593 raw11593Labels = mixedMoment B raw11593step0 raw11593step0Labels := by
      have ha : raw11593step0 = (fun i j => raw11593 (permutation253 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11593step0 raw11593; decide +kernel
      have hl : raw11593step0Labels = raw11593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11593 raw11593Labels permutation253 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw11594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11594 raw11594Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw11594 raw11594Labels = mixedMoment B raw11594step0 raw11594step0Labels := by
      have ha : raw11594step0 = (fun i j => raw11594 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11594step0 raw11594; decide +kernel
      have hl : raw11594step0Labels = raw11594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11594 raw11594Labels permutation180 permutation3
    _ = mixedMoment B node1210 node1210Labels := by rfl

def raw11595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11595 raw11595Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw11595 raw11595Labels = mixedMoment B raw11595step0 raw11595step0Labels := by
      have ha : raw11595step0 = (fun i j => raw11595 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11595step0 raw11595; decide +kernel
      have hl : raw11595step0Labels = raw11595Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11595 raw11595Labels permutation156 permutation3
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw11596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11596 raw11596Labels = mixedMoment B node2860 node2860Labels := by
  calc
    mixedMoment B raw11596 raw11596Labels = mixedMoment B raw11596step0 raw11596step0Labels := by
      have ha : raw11596step0 = (fun i j => raw11596 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11596step0 raw11596; decide +kernel
      have hl : raw11596step0Labels = raw11596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11596 raw11596Labels permutation180 permutation3
    _ = mixedMoment B node2860 node2860Labels := by rfl

def raw11597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11597 raw11597Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw11597 raw11597Labels = mixedMoment B raw11597step0 raw11597step0Labels := by
      have hz : ∀ j, raw11597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11597step0 = (fun i j => raw11597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11597step0 raw11597; decide +kernel
      have hl : raw11597step0Labels = raw11597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11597 raw11597Labels permutation434 hz
    mixedMoment B raw11597step0 raw11597step0Labels = mixedMoment B raw11597step1 raw11597step1Labels := by
      have ha : raw11597step1 = (fun i j => raw11597step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11597step1 raw11597step0; decide +kernel
      have hl : raw11597step1Labels = raw11597step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11597step0 raw11597step0Labels permutation39 permutation3
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw11598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw11598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw11598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11598 raw11598Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw11598 raw11598Labels = mixedMoment B raw11598step0 raw11598step0Labels := by
      have ha : raw11598step0 = (fun i j => raw11598 (permutation252 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11598step0 raw11598; decide +kernel
      have hl : raw11598step0Labels = raw11598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11598 raw11598Labels permutation252 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw11599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11599 raw11599Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw11599 raw11599Labels = mixedMoment B raw11599step0 raw11599step0Labels := by
      have ha : raw11599step0 = (fun i j => raw11599 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11599step0 raw11599; decide +kernel
      have hl : raw11599step0Labels = raw11599Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11599 raw11599Labels permutation176 permutation3
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw11600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11600 raw11600Labels = mixedMoment B node2988 node2988Labels := by
  calc
    mixedMoment B raw11600 raw11600Labels = mixedMoment B raw11600step0 raw11600step0Labels := by
      have ha : raw11600step0 = (fun i j => raw11600 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11600step0 raw11600; decide +kernel
      have hl : raw11600step0Labels = raw11600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11600 raw11600Labels permutation152 permutation3
    _ = mixedMoment B node2988 node2988Labels := by rfl

def raw11601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11601 raw11601Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw11601 raw11601Labels = mixedMoment B raw11601step0 raw11601step0Labels := by
      have ha : raw11601step0 = (fun i j => raw11601 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11601step0 raw11601; decide +kernel
      have hl : raw11601step0Labels = raw11601Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11601 raw11601Labels permutation176 permutation3
    _ = mixedMoment B node2864 node2864Labels := by rfl

def raw11602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11602 raw11602Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw11602 raw11602Labels = mixedMoment B raw11602step0 raw11602step0Labels := by
      have hz : ∀ j, raw11602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11602step0 = (fun i j => raw11602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11602step0 raw11602; decide +kernel
      have hl : raw11602step0Labels = raw11602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11602 raw11602Labels permutation434 hz
    mixedMoment B raw11602step0 raw11602step0Labels = mixedMoment B raw11602step1 raw11602step1Labels := by
      have ha : raw11602step1 = (fun i j => raw11602step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11602step1 raw11602step0; decide +kernel
      have hl : raw11602step1Labels = raw11602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11602step0 raw11602step0Labels permutation38 permutation3
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw11603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11603step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11603 raw11603Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw11603 raw11603Labels = mixedMoment B raw11603step0 raw11603step0Labels := by
      have hz : ∀ j, raw11603 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11603step0 = (fun i j => raw11603 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11603step0 raw11603; decide +kernel
      have hl : raw11603step0Labels = raw11603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11603 raw11603Labels permutation520 hz
    mixedMoment B raw11603step0 raw11603step0Labels = mixedMoment B raw11603step1 raw11603step1Labels := by
      have ha : raw11603step1 = (fun i j => raw11603step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11603step1 raw11603step0; decide +kernel
      have hl : raw11603step1Labels = raw11603step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11603step0 raw11603step0Labels permutation38 permutation3
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw11604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11604 raw11604Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw11604 raw11604Labels = mixedMoment B raw11604step0 raw11604step0Labels := by
      have ha : raw11604step0 = (fun i j => raw11604 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11604step0 raw11604; decide +kernel
      have hl : raw11604step0Labels = raw11604Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11604 raw11604Labels permutation160 permutation7
    mixedMoment B raw11604step0 raw11604step0Labels = mixedMoment B raw11604step1 raw11604step1Labels := by
      have ha : raw11604step1 = -raw11604step0 := by apply Matrix.ext; change ∀ i j, raw11604step1 i j = -(raw11604step0 i j); unfold raw11604step1 raw11604step0; decide +kernel
      have hl : raw11604step1Labels = raw11604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11604step1 raw11604step1Labels = mixedMoment B raw11604step2 raw11604step2Labels := by
      have ha : raw11604step2 = raw11604step1 := by apply Matrix.ext; unfold raw11604step2 raw11604step1; decide +kernel
      have hl : raw11604step1Labels = labelEmbedding1 ∘ raw11604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11604step1 raw11604step1Labels raw11604step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw11605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw11605step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11605step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11605 raw11605Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw11605 raw11605Labels = mixedMoment B raw11605step0 raw11605step0Labels := by
      have ha : raw11605step0 = (fun i j => raw11605 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11605step0 raw11605; decide +kernel
      have hl : raw11605step0Labels = raw11605Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11605 raw11605Labels permutation160 permutation7
    mixedMoment B raw11605step0 raw11605step0Labels = mixedMoment B raw11605step1 raw11605step1Labels := by
      have ha : raw11605step1 = -raw11605step0 := by apply Matrix.ext; change ∀ i j, raw11605step1 i j = -(raw11605step0 i j); unfold raw11605step1 raw11605step0; decide +kernel
      have hl : raw11605step1Labels = raw11605step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11605step1 raw11605step1Labels = mixedMoment B raw11605step2 raw11605step2Labels := by
      have ha : raw11605step2 = raw11605step1 := by apply Matrix.ext; unfold raw11605step2 raw11605step1; decide +kernel
      have hl : raw11605step1Labels = labelEmbedding1 ∘ raw11605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11605step1 raw11605step1Labels raw11605step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw11606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11606step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11606step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11606step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11606step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11606 raw11606Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw11606 raw11606Labels = mixedMoment B raw11606step0 raw11606step0Labels := by
      have hz : ∀ j, raw11606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11606step0 = (fun i j => raw11606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11606step0 raw11606; decide +kernel
      have hl : raw11606step0Labels = raw11606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11606 raw11606Labels permutation434 hz
    mixedMoment B raw11606step0 raw11606step0Labels = mixedMoment B raw11606step1 raw11606step1Labels := by
      have ha : raw11606step1 = (fun i j => raw11606step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11606step1 raw11606step0; decide +kernel
      have hl : raw11606step1Labels = raw11606step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11606step0 raw11606step0Labels permutation34 permutation7
    mixedMoment B raw11606step1 raw11606step1Labels = mixedMoment B raw11606step2 raw11606step2Labels := by
      have ha : raw11606step2 = -raw11606step1 := by apply Matrix.ext; change ∀ i j, raw11606step2 i j = -(raw11606step1 i j); unfold raw11606step2 raw11606step1; decide +kernel
      have hl : raw11606step2Labels = raw11606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11606step2 raw11606step2Labels = mixedMoment B raw11606step3 raw11606step3Labels := by
      have ha : raw11606step3 = raw11606step2 := by apply Matrix.ext; unfold raw11606step3 raw11606step2; decide +kernel
      have hl : raw11606step2Labels = labelEmbedding1 ∘ raw11606step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11606step2 raw11606step2Labels raw11606step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw11607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11607step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11607step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11607step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11607step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11607 raw11607Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw11607 raw11607Labels = mixedMoment B raw11607step0 raw11607step0Labels := by
      have hz : ∀ j, raw11607 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11607step0 = (fun i j => raw11607 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11607step0 raw11607; decide +kernel
      have hl : raw11607step0Labels = raw11607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11607 raw11607Labels permutation520 hz
    mixedMoment B raw11607step0 raw11607step0Labels = mixedMoment B raw11607step1 raw11607step1Labels := by
      have ha : raw11607step1 = (fun i j => raw11607step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11607step1 raw11607step0; decide +kernel
      have hl : raw11607step1Labels = raw11607step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11607step0 raw11607step0Labels permutation34 permutation7
    mixedMoment B raw11607step1 raw11607step1Labels = mixedMoment B raw11607step2 raw11607step2Labels := by
      have ha : raw11607step2 = -raw11607step1 := by apply Matrix.ext; change ∀ i j, raw11607step2 i j = -(raw11607step1 i j); unfold raw11607step2 raw11607step1; decide +kernel
      have hl : raw11607step2Labels = raw11607step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11607step2 raw11607step2Labels = mixedMoment B raw11607step3 raw11607step3Labels := by
      have ha : raw11607step3 = raw11607step2 := by apply Matrix.ext; unfold raw11607step3 raw11607step2; decide +kernel
      have hl : raw11607step2Labels = labelEmbedding1 ∘ raw11607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11607step2 raw11607step2Labels raw11607step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw11608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw11608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11608 raw11608Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw11608 raw11608Labels = mixedMoment B raw11608step0 raw11608step0Labels := by
      have ha : raw11608step0 = (fun i j => raw11608 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11608step0 raw11608; decide +kernel
      have hl : raw11608step0Labels = raw11608Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11608 raw11608Labels permutation160 permutation7
    mixedMoment B raw11608step0 raw11608step0Labels = mixedMoment B raw11608step1 raw11608step1Labels := by
      have ha : raw11608step1 = -raw11608step0 := by apply Matrix.ext; change ∀ i j, raw11608step1 i j = -(raw11608step0 i j); unfold raw11608step1 raw11608step0; decide +kernel
      have hl : raw11608step1Labels = raw11608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11608step1 raw11608step1Labels = mixedMoment B raw11608step2 raw11608step2Labels := by
      have ha : raw11608step2 = raw11608step1 := by apply Matrix.ext; unfold raw11608step2 raw11608step1; decide +kernel
      have hl : raw11608step1Labels = labelEmbedding1 ∘ raw11608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11608step1 raw11608step1Labels raw11608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw11609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11609 raw11609Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw11609 raw11609Labels = mixedMoment B raw11609step0 raw11609step0Labels := by
      have ha : raw11609step0 = (fun i j => raw11609 (permutation197 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11609step0 raw11609; decide +kernel
      have hl : raw11609step0Labels = raw11609Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11609 raw11609Labels permutation197 permutation5
    mixedMoment B raw11609step0 raw11609step0Labels = mixedMoment B raw11609step1 raw11609step1Labels := by
      have ha : raw11609step1 = -raw11609step0 := by apply Matrix.ext; change ∀ i j, raw11609step1 i j = -(raw11609step0 i j); unfold raw11609step1 raw11609step0; decide +kernel
      have hl : raw11609step1Labels = raw11609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11609step1 raw11609step1Labels = mixedMoment B raw11609step2 raw11609step2Labels := by
      have ha : raw11609step2 = raw11609step1 := by apply Matrix.ext; unfold raw11609step2 raw11609step1; decide +kernel
      have hl : raw11609step1Labels = labelEmbedding1 ∘ raw11609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11609step1 raw11609step1Labels raw11609step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3286 node3286Labels := by rfl

def raw11610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw11610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11610 raw11610Labels = mixedMoment B node3566 node3566Labels := by
  calc
    mixedMoment B raw11610 raw11610Labels = mixedMoment B raw11610step0 raw11610step0Labels := by
      have ha : raw11610step0 = (fun i j => raw11610 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11610step0 raw11610; decide +kernel
      have hl : raw11610step0Labels = raw11610Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11610 raw11610Labels permutation160 permutation7
    mixedMoment B raw11610step0 raw11610step0Labels = mixedMoment B raw11610step1 raw11610step1Labels := by
      have ha : raw11610step1 = -raw11610step0 := by apply Matrix.ext; change ∀ i j, raw11610step1 i j = -(raw11610step0 i j); unfold raw11610step1 raw11610step0; decide +kernel
      have hl : raw11610step1Labels = raw11610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11610step1 raw11610step1Labels = mixedMoment B raw11610step2 raw11610step2Labels := by
      have ha : raw11610step2 = raw11610step1 := by apply Matrix.ext; unfold raw11610step2 raw11610step1; decide +kernel
      have hl : raw11610step1Labels = labelEmbedding1 ∘ raw11610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11610step1 raw11610step1Labels raw11610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3566 node3566Labels := by rfl

def raw11611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11611step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11611step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11611step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11611 raw11611Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11611 raw11611Labels = mixedMoment B raw11611step0 raw11611step0Labels := by
      have hz : ∀ j, raw11611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11611step0 = (fun i j => raw11611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11611step0 raw11611; decide +kernel
      have hl : raw11611step0Labels = raw11611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11611 raw11611Labels permutation434 hz
    mixedMoment B raw11611step0 raw11611step0Labels = mixedMoment B raw11611step1 raw11611step1Labels := by
      have ha : raw11611step1 = (fun i j => raw11611step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11611step1 raw11611step0; decide +kernel
      have hl : raw11611step1Labels = raw11611step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11611step0 raw11611step0Labels permutation34 permutation7
    mixedMoment B raw11611step1 raw11611step1Labels = mixedMoment B raw11611step2 raw11611step2Labels := by
      have ha : raw11611step2 = -raw11611step1 := by apply Matrix.ext; change ∀ i j, raw11611step2 i j = -(raw11611step1 i j); unfold raw11611step2 raw11611step1; decide +kernel
      have hl : raw11611step2Labels = raw11611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11611step2 raw11611step2Labels = mixedMoment B raw11611step3 raw11611step3Labels := by
      have ha : raw11611step3 = raw11611step2 := by apply Matrix.ext; unfold raw11611step3 raw11611step2; decide +kernel
      have hl : raw11611step2Labels = labelEmbedding1 ∘ raw11611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11611step2 raw11611step2Labels raw11611step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw11612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11612step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11612step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11612 raw11612Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11612 raw11612Labels = mixedMoment B raw11612step0 raw11612step0Labels := by
      have hz : ∀ j, raw11612 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11612step0 = (fun i j => raw11612 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11612step0 raw11612; decide +kernel
      have hl : raw11612step0Labels = raw11612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11612 raw11612Labels permutation520 hz
    mixedMoment B raw11612step0 raw11612step0Labels = mixedMoment B raw11612step1 raw11612step1Labels := by
      have ha : raw11612step1 = (fun i j => raw11612step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11612step1 raw11612step0; decide +kernel
      have hl : raw11612step1Labels = raw11612step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11612step0 raw11612step0Labels permutation34 permutation7
    mixedMoment B raw11612step1 raw11612step1Labels = mixedMoment B raw11612step2 raw11612step2Labels := by
      have ha : raw11612step2 = -raw11612step1 := by apply Matrix.ext; change ∀ i j, raw11612step2 i j = -(raw11612step1 i j); unfold raw11612step2 raw11612step1; decide +kernel
      have hl : raw11612step2Labels = raw11612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11612step2 raw11612step2Labels = mixedMoment B raw11612step3 raw11612step3Labels := by
      have ha : raw11612step3 = raw11612step2 := by apply Matrix.ext; unfold raw11612step3 raw11612step2; decide +kernel
      have hl : raw11612step2Labels = labelEmbedding1 ∘ raw11612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11612step2 raw11612step2Labels raw11612step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw11613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw11613step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11613step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw11613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11613 raw11613Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw11613 raw11613Labels = mixedMoment B raw11613step0 raw11613step0Labels := by
      have ha : raw11613step0 = (fun i j => raw11613 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11613step0 raw11613; decide +kernel
      have hl : raw11613step0Labels = raw11613Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11613 raw11613Labels permutation160 permutation7
    mixedMoment B raw11613step0 raw11613step0Labels = mixedMoment B raw11613step1 raw11613step1Labels := by
      have ha : raw11613step1 = -raw11613step0 := by apply Matrix.ext; change ∀ i j, raw11613step1 i j = -(raw11613step0 i j); unfold raw11613step1 raw11613step0; decide +kernel
      have hl : raw11613step1Labels = raw11613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11613step1 raw11613step1Labels = mixedMoment B raw11613step2 raw11613step2Labels := by
      have ha : raw11613step2 = raw11613step1 := by apply Matrix.ext; unfold raw11613step2 raw11613step1; decide +kernel
      have hl : raw11613step1Labels = labelEmbedding1 ∘ raw11613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11613step1 raw11613step1Labels raw11613step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3567 node3567Labels := by rfl

def raw11614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11614 raw11614Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw11614 raw11614Labels = mixedMoment B raw11614step0 raw11614step0Labels := by
      have ha : raw11614step0 = (fun i j => raw11614 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11614step0 raw11614; decide +kernel
      have hl : raw11614step0Labels = raw11614Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11614 raw11614Labels permutation160 permutation7
    mixedMoment B raw11614step0 raw11614step0Labels = mixedMoment B raw11614step1 raw11614step1Labels := by
      have ha : raw11614step1 = -raw11614step0 := by apply Matrix.ext; change ∀ i j, raw11614step1 i j = -(raw11614step0 i j); unfold raw11614step1 raw11614step0; decide +kernel
      have hl : raw11614step1Labels = raw11614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11614step1 raw11614step1Labels = mixedMoment B raw11614step2 raw11614step2Labels := by
      have ha : raw11614step2 = raw11614step1 := by apply Matrix.ext; unfold raw11614step2 raw11614step1; decide +kernel
      have hl : raw11614step1Labels = labelEmbedding1 ∘ raw11614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11614step1 raw11614step1Labels raw11614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw11615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11615step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11615 raw11615Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw11615 raw11615Labels = mixedMoment B raw11615step0 raw11615step0Labels := by
      have ha : raw11615step0 = (fun i j => raw11615 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11615step0 raw11615; decide +kernel
      have hl : raw11615step0Labels = raw11615Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11615 raw11615Labels permutation160 permutation7
    mixedMoment B raw11615step0 raw11615step0Labels = mixedMoment B raw11615step1 raw11615step1Labels := by
      have ha : raw11615step1 = -raw11615step0 := by apply Matrix.ext; change ∀ i j, raw11615step1 i j = -(raw11615step0 i j); unfold raw11615step1 raw11615step0; decide +kernel
      have hl : raw11615step1Labels = raw11615step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11615step1 raw11615step1Labels = mixedMoment B raw11615step2 raw11615step2Labels := by
      have ha : raw11615step2 = raw11615step1 := by apply Matrix.ext; unfold raw11615step2 raw11615step1; decide +kernel
      have hl : raw11615step1Labels = labelEmbedding1 ∘ raw11615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11615step1 raw11615step1Labels raw11615step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

def raw11616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11616step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11616step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11616 raw11616Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw11616 raw11616Labels = mixedMoment B raw11616step0 raw11616step0Labels := by
      have hz : ∀ j, raw11616 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11616step0 = (fun i j => raw11616 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11616step0 raw11616; decide +kernel
      have hl : raw11616step0Labels = raw11616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11616 raw11616Labels permutation434 hz
    mixedMoment B raw11616step0 raw11616step0Labels = mixedMoment B raw11616step1 raw11616step1Labels := by
      have ha : raw11616step1 = (fun i j => raw11616step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11616step1 raw11616step0; decide +kernel
      have hl : raw11616step1Labels = raw11616step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11616step0 raw11616step0Labels permutation34 permutation7
    mixedMoment B raw11616step1 raw11616step1Labels = mixedMoment B raw11616step2 raw11616step2Labels := by
      have ha : raw11616step2 = -raw11616step1 := by apply Matrix.ext; change ∀ i j, raw11616step2 i j = -(raw11616step1 i j); unfold raw11616step2 raw11616step1; decide +kernel
      have hl : raw11616step2Labels = raw11616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11616step2 raw11616step2Labels = mixedMoment B raw11616step3 raw11616step3Labels := by
      have ha : raw11616step3 = raw11616step2 := by apply Matrix.ext; unfold raw11616step3 raw11616step2; decide +kernel
      have hl : raw11616step2Labels = labelEmbedding1 ∘ raw11616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11616step2 raw11616step2Labels raw11616step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw11617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11617step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11617 raw11617Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw11617 raw11617Labels = mixedMoment B raw11617step0 raw11617step0Labels := by
      have hz : ∀ j, raw11617 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11617step0 = (fun i j => raw11617 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11617step0 raw11617; decide +kernel
      have hl : raw11617step0Labels = raw11617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11617 raw11617Labels permutation520 hz
    mixedMoment B raw11617step0 raw11617step0Labels = mixedMoment B raw11617step1 raw11617step1Labels := by
      have ha : raw11617step1 = (fun i j => raw11617step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11617step1 raw11617step0; decide +kernel
      have hl : raw11617step1Labels = raw11617step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11617step0 raw11617step0Labels permutation34 permutation7
    mixedMoment B raw11617step1 raw11617step1Labels = mixedMoment B raw11617step2 raw11617step2Labels := by
      have ha : raw11617step2 = -raw11617step1 := by apply Matrix.ext; change ∀ i j, raw11617step2 i j = -(raw11617step1 i j); unfold raw11617step2 raw11617step1; decide +kernel
      have hl : raw11617step2Labels = raw11617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11617step2 raw11617step2Labels = mixedMoment B raw11617step3 raw11617step3Labels := by
      have ha : raw11617step3 = raw11617step2 := by apply Matrix.ext; unfold raw11617step3 raw11617step2; decide +kernel
      have hl : raw11617step2Labels = labelEmbedding1 ∘ raw11617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11617step2 raw11617step2Labels raw11617step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw11618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11618 raw11618Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11618 raw11618Labels = mixedMoment B raw11618step0 raw11618step0Labels := by
      have ha : raw11618step0 = (fun i j => raw11618 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11618step0 raw11618; decide +kernel
      have hl : raw11618step0Labels = raw11618Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11618 raw11618Labels permutation160 permutation7
    mixedMoment B raw11618step0 raw11618step0Labels = mixedMoment B raw11618step1 raw11618step1Labels := by
      have ha : raw11618step1 = -raw11618step0 := by apply Matrix.ext; change ∀ i j, raw11618step1 i j = -(raw11618step0 i j); unfold raw11618step1 raw11618step0; decide +kernel
      have hl : raw11618step1Labels = raw11618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11618step1 raw11618step1Labels = mixedMoment B raw11618step2 raw11618step2Labels := by
      have ha : raw11618step2 = raw11618step1 := by apply Matrix.ext; unfold raw11618step2 raw11618step1; decide +kernel
      have hl : raw11618step1Labels = labelEmbedding1 ∘ raw11618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11618step1 raw11618step1Labels raw11618step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw11619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11619step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11619 raw11619Labels = mixedMoment B node3285 node3285Labels := by
  calc
    mixedMoment B raw11619 raw11619Labels = mixedMoment B raw11619step0 raw11619step0Labels := by
      have ha : raw11619step0 = (fun i j => raw11619 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11619step0 raw11619; decide +kernel
      have hl : raw11619step0Labels = raw11619Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11619 raw11619Labels permutation195 permutation5
    mixedMoment B raw11619step0 raw11619step0Labels = mixedMoment B raw11619step1 raw11619step1Labels := by
      have ha : raw11619step1 = -raw11619step0 := by apply Matrix.ext; change ∀ i j, raw11619step1 i j = -(raw11619step0 i j); unfold raw11619step1 raw11619step0; decide +kernel
      have hl : raw11619step1Labels = raw11619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11619step1 raw11619step1Labels = mixedMoment B raw11619step2 raw11619step2Labels := by
      have ha : raw11619step2 = raw11619step1 := by apply Matrix.ext; unfold raw11619step2 raw11619step1; decide +kernel
      have hl : raw11619step1Labels = labelEmbedding1 ∘ raw11619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11619step1 raw11619step1Labels raw11619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3285 node3285Labels := by rfl

def raw11620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw11620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11620step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11620 raw11620Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw11620 raw11620Labels = mixedMoment B raw11620step0 raw11620step0Labels := by
      have ha : raw11620step0 = (fun i j => raw11620 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11620step0 raw11620; decide +kernel
      have hl : raw11620step0Labels = raw11620Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11620 raw11620Labels permutation166 permutation7
    mixedMoment B raw11620step0 raw11620step0Labels = mixedMoment B raw11620step1 raw11620step1Labels := by
      have ha : raw11620step1 = -raw11620step0 := by apply Matrix.ext; change ∀ i j, raw11620step1 i j = -(raw11620step0 i j); unfold raw11620step1 raw11620step0; decide +kernel
      have hl : raw11620step1Labels = raw11620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11620step1 raw11620step1Labels = mixedMoment B raw11620step2 raw11620step2Labels := by
      have ha : raw11620step2 = raw11620step1 := by apply Matrix.ext; unfold raw11620step2 raw11620step1; decide +kernel
      have hl : raw11620step1Labels = labelEmbedding1 ∘ raw11620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11620step1 raw11620step1Labels raw11620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw11621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw11621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw11621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11621step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw11621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11621 raw11621Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw11621 raw11621Labels = mixedMoment B raw11621step0 raw11621step0Labels := by
      have ha : raw11621step0 = (fun i j => raw11621 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11621step0 raw11621; decide +kernel
      have hl : raw11621step0Labels = raw11621Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11621 raw11621Labels permutation166 permutation7
    mixedMoment B raw11621step0 raw11621step0Labels = mixedMoment B raw11621step1 raw11621step1Labels := by
      have ha : raw11621step1 = -raw11621step0 := by apply Matrix.ext; change ∀ i j, raw11621step1 i j = -(raw11621step0 i j); unfold raw11621step1 raw11621step0; decide +kernel
      have hl : raw11621step1Labels = raw11621step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11621step1 raw11621step1Labels = mixedMoment B raw11621step2 raw11621step2Labels := by
      have ha : raw11621step2 = raw11621step1 := by apply Matrix.ext; unfold raw11621step2 raw11621step1; decide +kernel
      have hl : raw11621step1Labels = labelEmbedding1 ∘ raw11621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11621step1 raw11621step1Labels raw11621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3527 node3527Labels := by rfl

def raw11622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw11622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11622 raw11622Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw11622 raw11622Labels = mixedMoment B raw11622step0 raw11622step0Labels := by
      have hz : ∀ j, raw11622 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11622step0 = (fun i j => raw11622 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11622step0 raw11622; decide +kernel
      have hl : raw11622step0Labels = raw11622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11622 raw11622Labels permutation520 hz
    mixedMoment B raw11622step0 raw11622step0Labels = mixedMoment B raw11622step1 raw11622step1Labels := by
      have ha : raw11622step1 = (fun i j => raw11622step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11622step1 raw11622step0; decide +kernel
      have hl : raw11622step1Labels = raw11622step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11622step0 raw11622step0Labels permutation34 permutation7
    mixedMoment B raw11622step1 raw11622step1Labels = mixedMoment B raw11622step2 raw11622step2Labels := by
      have ha : raw11622step2 = -raw11622step1 := by apply Matrix.ext; change ∀ i j, raw11622step2 i j = -(raw11622step1 i j); unfold raw11622step2 raw11622step1; decide +kernel
      have hl : raw11622step2Labels = raw11622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11622step2 raw11622step2Labels = mixedMoment B raw11622step3 raw11622step3Labels := by
      have ha : raw11622step3 = raw11622step2 := by apply Matrix.ext; unfold raw11622step3 raw11622step2; decide +kernel
      have hl : raw11622step2Labels = labelEmbedding1 ∘ raw11622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11622step2 raw11622step2Labels raw11622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw11623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw11623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11623step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11623 raw11623Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw11623 raw11623Labels = mixedMoment B raw11623step0 raw11623step0Labels := by
      have ha : raw11623step0 = (fun i j => raw11623 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11623step0 raw11623; decide +kernel
      have hl : raw11623step0Labels = raw11623Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11623 raw11623Labels permutation166 permutation7
    mixedMoment B raw11623step0 raw11623step0Labels = mixedMoment B raw11623step1 raw11623step1Labels := by
      have ha : raw11623step1 = -raw11623step0 := by apply Matrix.ext; change ∀ i j, raw11623step1 i j = -(raw11623step0 i j); unfold raw11623step1 raw11623step0; decide +kernel
      have hl : raw11623step1Labels = raw11623step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11623step1 raw11623step1Labels = mixedMoment B raw11623step2 raw11623step2Labels := by
      have ha : raw11623step2 = raw11623step1 := by apply Matrix.ext; unfold raw11623step2 raw11623step1; decide +kernel
      have hl : raw11623step1Labels = labelEmbedding1 ∘ raw11623step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11623step1 raw11623step1Labels raw11623step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw11624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11624 raw11624Labels = mixedMoment B node3285 node3285Labels := by
  calc
    mixedMoment B raw11624 raw11624Labels = mixedMoment B raw11624step0 raw11624step0Labels := by
      have ha : raw11624step0 = (fun i j => raw11624 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11624step0 raw11624; decide +kernel
      have hl : raw11624step0Labels = raw11624Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11624 raw11624Labels permutation194 permutation5
    mixedMoment B raw11624step0 raw11624step0Labels = mixedMoment B raw11624step1 raw11624step1Labels := by
      have ha : raw11624step1 = -raw11624step0 := by apply Matrix.ext; change ∀ i j, raw11624step1 i j = -(raw11624step0 i j); unfold raw11624step1 raw11624step0; decide +kernel
      have hl : raw11624step1Labels = raw11624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11624step1 raw11624step1Labels = mixedMoment B raw11624step2 raw11624step2Labels := by
      have ha : raw11624step2 = raw11624step1 := by apply Matrix.ext; unfold raw11624step2 raw11624step1; decide +kernel
      have hl : raw11624step1Labels = labelEmbedding1 ∘ raw11624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11624step1 raw11624step1Labels raw11624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3285 node3285Labels := by rfl

def raw11625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw11625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11625 raw11625Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw11625 raw11625Labels = mixedMoment B raw11625step0 raw11625step0Labels := by
      have ha : raw11625step0 = (fun i j => raw11625 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11625step0 raw11625; decide +kernel
      have hl : raw11625step0Labels = raw11625Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11625 raw11625Labels permutation160 permutation7
    mixedMoment B raw11625step0 raw11625step0Labels = mixedMoment B raw11625step1 raw11625step1Labels := by
      have ha : raw11625step1 = -raw11625step0 := by apply Matrix.ext; change ∀ i j, raw11625step1 i j = -(raw11625step0 i j); unfold raw11625step1 raw11625step0; decide +kernel
      have hl : raw11625step1Labels = raw11625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11625step1 raw11625step1Labels = mixedMoment B raw11625step2 raw11625step2Labels := by
      have ha : raw11625step2 = raw11625step1 := by apply Matrix.ext; unfold raw11625step2 raw11625step1; decide +kernel
      have hl : raw11625step1Labels = labelEmbedding1 ∘ raw11625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11625step1 raw11625step1Labels raw11625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw11626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw11626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw11626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11626step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw11626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11626 raw11626Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw11626 raw11626Labels = mixedMoment B raw11626step0 raw11626step0Labels := by
      have ha : raw11626step0 = (fun i j => raw11626 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11626step0 raw11626; decide +kernel
      have hl : raw11626step0Labels = raw11626Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11626 raw11626Labels permutation160 permutation7
    mixedMoment B raw11626step0 raw11626step0Labels = mixedMoment B raw11626step1 raw11626step1Labels := by
      have ha : raw11626step1 = -raw11626step0 := by apply Matrix.ext; change ∀ i j, raw11626step1 i j = -(raw11626step0 i j); unfold raw11626step1 raw11626step0; decide +kernel
      have hl : raw11626step1Labels = raw11626step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11626step1 raw11626step1Labels = mixedMoment B raw11626step2 raw11626step2Labels := by
      have ha : raw11626step2 = raw11626step1 := by apply Matrix.ext; unfold raw11626step2 raw11626step1; decide +kernel
      have hl : raw11626step1Labels = labelEmbedding1 ∘ raw11626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11626step1 raw11626step1Labels raw11626step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3527 node3527Labels := by rfl

def raw11627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw11627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11627step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11627step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11627 raw11627Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw11627 raw11627Labels = mixedMoment B raw11627step0 raw11627step0Labels := by
      have hz : ∀ j, raw11627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11627step0 = (fun i j => raw11627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11627step0 raw11627; decide +kernel
      have hl : raw11627step0Labels = raw11627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11627 raw11627Labels permutation434 hz
    mixedMoment B raw11627step0 raw11627step0Labels = mixedMoment B raw11627step1 raw11627step1Labels := by
      have ha : raw11627step1 = (fun i j => raw11627step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11627step1 raw11627step0; decide +kernel
      have hl : raw11627step1Labels = raw11627step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11627step0 raw11627step0Labels permutation34 permutation7
    mixedMoment B raw11627step1 raw11627step1Labels = mixedMoment B raw11627step2 raw11627step2Labels := by
      have ha : raw11627step2 = -raw11627step1 := by apply Matrix.ext; change ∀ i j, raw11627step2 i j = -(raw11627step1 i j); unfold raw11627step2 raw11627step1; decide +kernel
      have hl : raw11627step2Labels = raw11627step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11627step2 raw11627step2Labels = mixedMoment B raw11627step3 raw11627step3Labels := by
      have ha : raw11627step3 = raw11627step2 := by apply Matrix.ext; unfold raw11627step3 raw11627step2; decide +kernel
      have hl : raw11627step2Labels = labelEmbedding1 ∘ raw11627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11627step2 raw11627step2Labels raw11627step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw11628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw11628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw11628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw11628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11628 raw11628Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw11628 raw11628Labels = mixedMoment B raw11628step0 raw11628step0Labels := by
      have ha : raw11628step0 = (fun i j => raw11628 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11628step0 raw11628; decide +kernel
      have hl : raw11628step0Labels = raw11628Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11628 raw11628Labels permutation160 permutation7
    mixedMoment B raw11628step0 raw11628step0Labels = mixedMoment B raw11628step1 raw11628step1Labels := by
      have ha : raw11628step1 = -raw11628step0 := by apply Matrix.ext; change ∀ i j, raw11628step1 i j = -(raw11628step0 i j); unfold raw11628step1 raw11628step0; decide +kernel
      have hl : raw11628step1Labels = raw11628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11628step1 raw11628step1Labels = mixedMoment B raw11628step2 raw11628step2Labels := by
      have ha : raw11628step2 = raw11628step1 := by apply Matrix.ext; unfold raw11628step2 raw11628step1; decide +kernel
      have hl : raw11628step1Labels = labelEmbedding1 ∘ raw11628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11628step1 raw11628step1Labels raw11628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw11629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11629step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11629 raw11629Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw11629 raw11629Labels = mixedMoment B raw11629step0 raw11629step0Labels := by
      have ha : raw11629step0 = (fun i j => raw11629 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11629step0 raw11629; decide +kernel
      have hl : raw11629step0Labels = raw11629Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11629 raw11629Labels permutation160 permutation7
    mixedMoment B raw11629step0 raw11629step0Labels = mixedMoment B raw11629step1 raw11629step1Labels := by
      have ha : raw11629step1 = -raw11629step0 := by apply Matrix.ext; change ∀ i j, raw11629step1 i j = -(raw11629step0 i j); unfold raw11629step1 raw11629step0; decide +kernel
      have hl : raw11629step1Labels = raw11629step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11629step1 raw11629step1Labels = mixedMoment B raw11629step2 raw11629step2Labels := by
      have ha : raw11629step2 = raw11629step1 := by apply Matrix.ext; unfold raw11629step2 raw11629step1; decide +kernel
      have hl : raw11629step1Labels = labelEmbedding1 ∘ raw11629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11629step1 raw11629step1Labels raw11629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw11630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11630step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11630 raw11630Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw11630 raw11630Labels = mixedMoment B raw11630step0 raw11630step0Labels := by
      have ha : raw11630step0 = (fun i j => raw11630 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11630step0 raw11630; decide +kernel
      have hl : raw11630step0Labels = raw11630Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11630 raw11630Labels permutation160 permutation7
    mixedMoment B raw11630step0 raw11630step0Labels = mixedMoment B raw11630step1 raw11630step1Labels := by
      have ha : raw11630step1 = -raw11630step0 := by apply Matrix.ext; change ∀ i j, raw11630step1 i j = -(raw11630step0 i j); unfold raw11630step1 raw11630step0; decide +kernel
      have hl : raw11630step1Labels = raw11630step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11630step1 raw11630step1Labels = mixedMoment B raw11630step2 raw11630step2Labels := by
      have ha : raw11630step2 = raw11630step1 := by apply Matrix.ext; unfold raw11630step2 raw11630step1; decide +kernel
      have hl : raw11630step1Labels = labelEmbedding1 ∘ raw11630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11630step1 raw11630step1Labels raw11630step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

def raw11631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw11631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11631step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11631 raw11631Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw11631 raw11631Labels = mixedMoment B raw11631step0 raw11631step0Labels := by
      have ha : raw11631step0 = (fun i j => raw11631 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11631step0 raw11631; decide +kernel
      have hl : raw11631step0Labels = raw11631Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11631 raw11631Labels permutation160 permutation7
    mixedMoment B raw11631step0 raw11631step0Labels = mixedMoment B raw11631step1 raw11631step1Labels := by
      have ha : raw11631step1 = -raw11631step0 := by apply Matrix.ext; change ∀ i j, raw11631step1 i j = -(raw11631step0 i j); unfold raw11631step1 raw11631step0; decide +kernel
      have hl : raw11631step1Labels = raw11631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11631step1 raw11631step1Labels = mixedMoment B raw11631step2 raw11631step2Labels := by
      have ha : raw11631step2 = raw11631step1 := by apply Matrix.ext; unfold raw11631step2 raw11631step1; decide +kernel
      have hl : raw11631step1Labels = labelEmbedding1 ∘ raw11631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11631step1 raw11631step1Labels raw11631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw11632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11632step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11632step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11632 raw11632Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw11632 raw11632Labels = mixedMoment B raw11632step0 raw11632step0Labels := by
      have hz : ∀ j, raw11632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11632step0 = (fun i j => raw11632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11632step0 raw11632; decide +kernel
      have hl : raw11632step0Labels = raw11632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11632 raw11632Labels permutation434 hz
    mixedMoment B raw11632step0 raw11632step0Labels = mixedMoment B raw11632step1 raw11632step1Labels := by
      have ha : raw11632step1 = (fun i j => raw11632step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11632step1 raw11632step0; decide +kernel
      have hl : raw11632step1Labels = raw11632step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11632step0 raw11632step0Labels permutation34 permutation7
    mixedMoment B raw11632step1 raw11632step1Labels = mixedMoment B raw11632step2 raw11632step2Labels := by
      have ha : raw11632step2 = -raw11632step1 := by apply Matrix.ext; change ∀ i j, raw11632step2 i j = -(raw11632step1 i j); unfold raw11632step2 raw11632step1; decide +kernel
      have hl : raw11632step2Labels = raw11632step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11632step2 raw11632step2Labels = mixedMoment B raw11632step3 raw11632step3Labels := by
      have ha : raw11632step3 = raw11632step2 := by apply Matrix.ext; unfold raw11632step3 raw11632step2; decide +kernel
      have hl : raw11632step2Labels = labelEmbedding1 ∘ raw11632step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11632step2 raw11632step2Labels raw11632step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw11633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11633step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11633 raw11633Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw11633 raw11633Labels = mixedMoment B raw11633step0 raw11633step0Labels := by
      have hz : ∀ j, raw11633 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11633step0 = (fun i j => raw11633 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11633step0 raw11633; decide +kernel
      have hl : raw11633step0Labels = raw11633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11633 raw11633Labels permutation520 hz
    mixedMoment B raw11633step0 raw11633step0Labels = mixedMoment B raw11633step1 raw11633step1Labels := by
      have ha : raw11633step1 = (fun i j => raw11633step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11633step1 raw11633step0; decide +kernel
      have hl : raw11633step1Labels = raw11633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11633step0 raw11633step0Labels permutation34 permutation7
    mixedMoment B raw11633step1 raw11633step1Labels = mixedMoment B raw11633step2 raw11633step2Labels := by
      have ha : raw11633step2 = -raw11633step1 := by apply Matrix.ext; change ∀ i j, raw11633step2 i j = -(raw11633step1 i j); unfold raw11633step2 raw11633step1; decide +kernel
      have hl : raw11633step2Labels = raw11633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11633step2 raw11633step2Labels = mixedMoment B raw11633step3 raw11633step3Labels := by
      have ha : raw11633step3 = raw11633step2 := by apply Matrix.ext; unfold raw11633step3 raw11633step2; decide +kernel
      have hl : raw11633step2Labels = labelEmbedding1 ∘ raw11633step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11633step2 raw11633step2Labels raw11633step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw11634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11634 raw11634Labels = mixedMoment B node2720 node2720Labels := by
  calc
    _ = mixedMoment B node2720 node2720Labels := by rfl

def raw11635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11635 raw11635Labels = mixedMoment B node3805 node3805Labels := by
  calc
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw11636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11636 raw11636Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw11636 raw11636Labels = mixedMoment B raw11636step0 raw11636step0Labels := by
      have ha : raw11636step0 = (fun i j => raw11636 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11636step0 raw11636; decide +kernel
      have hl : raw11636step0Labels = raw11636Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11636 raw11636Labels permutation176 permutation2
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw11637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11637 raw11637Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw11637 raw11637Labels = mixedMoment B raw11637step0 raw11637step0Labels := by
      have hz : ∀ j, raw11637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11637step0 = (fun i j => raw11637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11637step0 raw11637; decide +kernel
      have hl : raw11637step0Labels = raw11637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11637 raw11637Labels permutation434 hz
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw11638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11638 raw11638Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw11638 raw11638Labels = mixedMoment B raw11638step0 raw11638step0Labels := by
      have hz : ∀ j, raw11638 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11638step0 = (fun i j => raw11638 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11638step0 raw11638; decide +kernel
      have hl : raw11638step0Labels = raw11638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11638 raw11638Labels permutation520 hz
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw11639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11639 raw11639Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw11639 raw11639Labels = mixedMoment B raw11639step0 raw11639step0Labels := by
      have ha : raw11639step0 = (fun i j => raw11639 (permutation626 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11639step0 raw11639; decide +kernel
      have hl : raw11639step0Labels = raw11639Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11639 raw11639Labels permutation626 permutation4
    mixedMoment B raw11639step0 raw11639step0Labels = mixedMoment B raw11639step1 raw11639step1Labels := by
      have ha : raw11639step1 = -raw11639step0 := by apply Matrix.ext; change ∀ i j, raw11639step1 i j = -(raw11639step0 i j); unfold raw11639step1 raw11639step0; decide +kernel
      have hl : raw11639step1Labels = raw11639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw11640 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw11640Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11640step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw11640step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11640step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw11640step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11640 raw11640Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw11640 raw11640Labels = mixedMoment B raw11640step0 raw11640step0Labels := by
      have hz : ∀ j, raw11640 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11640step0 = (fun i j => raw11640 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11640step0 raw11640; decide +kernel
      have hl : raw11640step0Labels = raw11640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11640 raw11640Labels permutation520 hz
    mixedMoment B raw11640step0 raw11640step0Labels = mixedMoment B raw11640step1 raw11640step1Labels := by
      have hz : ∀ j, raw11640step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11640step1 = (fun i j => raw11640step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11640step1 raw11640step0; decide +kernel
      have hl : raw11640step1Labels = raw11640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11640step0 raw11640step0Labels permutation104 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw11641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11641 raw11641Labels = mixedMoment B node1259 node1259Labels := by
  calc
    mixedMoment B raw11641 raw11641Labels = mixedMoment B raw11641step0 raw11641step0Labels := by
      have ha : raw11641step0 = (fun i j => raw11641 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11641step0 raw11641; decide +kernel
      have hl : raw11641step0Labels = raw11641Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11641 raw11641Labels permutation176 permutation2
    _ = mixedMoment B node1259 node1259Labels := by rfl

def raw11642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11642 raw11642Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw11642 raw11642Labels = mixedMoment B raw11642step0 raw11642step0Labels := by
      have ha : raw11642step0 = (fun i j => raw11642 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11642step0 raw11642; decide +kernel
      have hl : raw11642step0Labels = raw11642Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11642 raw11642Labels permutation160 permutation2
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw11643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11643 raw11643Labels = mixedMoment B node1214 node1214Labels := by
  calc
    mixedMoment B raw11643 raw11643Labels = mixedMoment B raw11643step0 raw11643step0Labels := by
      have ha : raw11643step0 = (fun i j => raw11643 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11643step0 raw11643; decide +kernel
      have hl : raw11643step0Labels = raw11643Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11643 raw11643Labels permutation155 permutation2
    _ = mixedMoment B node1214 node1214Labels := by rfl

def raw11644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11644 raw11644Labels = mixedMoment B node1214 node1214Labels := by
  calc
    mixedMoment B raw11644 raw11644Labels = mixedMoment B raw11644step0 raw11644step0Labels := by
      have ha : raw11644step0 = (fun i j => raw11644 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11644step0 raw11644; decide +kernel
      have hl : raw11644step0Labels = raw11644Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11644 raw11644Labels permutation153 permutation2
    _ = mixedMoment B node1214 node1214Labels := by rfl

def raw11645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11645 raw11645Labels = mixedMoment B node1212 node1212Labels := by
  calc
    _ = mixedMoment B node1212 node1212Labels := by rfl

def raw11646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11646 raw11646Labels = mixedMoment B node2630 node2630Labels := by
  calc
    mixedMoment B raw11646 raw11646Labels = mixedMoment B raw11646step0 raw11646step0Labels := by
      have ha : raw11646step0 = (fun i j => raw11646 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11646step0 raw11646; decide +kernel
      have hl : raw11646step0Labels = raw11646Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11646 raw11646Labels permutation176 permutation2
    _ = mixedMoment B node2630 node2630Labels := by rfl

def raw11647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11647 raw11647Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw11647 raw11647Labels = mixedMoment B raw11647step0 raw11647step0Labels := by
      have hz : ∀ j, raw11647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11647step0 = (fun i j => raw11647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11647step0 raw11647; decide +kernel
      have hl : raw11647step0Labels = raw11647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11647 raw11647Labels permutation434 hz
    mixedMoment B raw11647step0 raw11647step0Labels = mixedMoment B raw11647step1 raw11647step1Labels := by
      have ha : raw11647step1 = (fun i j => raw11647step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11647step1 raw11647step0; decide +kernel
      have hl : raw11647step1Labels = raw11647step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11647step0 raw11647step0Labels permutation38 permutation2
    _ = mixedMoment B node2763 node2763Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
