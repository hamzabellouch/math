import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4352 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4352step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4352step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4352step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4352step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4352step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4352 raw4352Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw4352 raw4352Labels = mixedMoment B raw4352step0 raw4352step0Labels := by
      have hz : ∀ j, raw4352 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4352step0 = (fun i j => raw4352 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4352step0 raw4352; decide +kernel
      have hl : raw4352step0Labels = raw4352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4352 raw4352Labels permutation520 hz
    mixedMoment B raw4352step0 raw4352step0Labels = mixedMoment B raw4352step1 raw4352step1Labels := by
      have hz : ∀ j, raw4352step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4352step1 = (fun i j => raw4352step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4352step1 raw4352step0; decide +kernel
      have hl : raw4352step1Labels = raw4352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4352step0 raw4352step0Labels permutation104 hz
    mixedMoment B raw4352step1 raw4352step1Labels = mixedMoment B raw4352step2 raw4352step2Labels := by
      have hz : ∀ j, raw4352step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4352step2 = (fun i j => raw4352step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4352step2 raw4352step1; decide +kernel
      have hl : raw4352step2Labels = raw4352step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4352step1 raw4352step1Labels permutation14 hz
    mixedMoment B raw4352step2 raw4352step2Labels = mixedMoment B raw4352step3 raw4352step3Labels := by
      have ha : raw4352step3 = (fun i j => raw4352step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4352step3 raw4352step2; decide +kernel
      have hl : raw4352step3Labels = raw4352step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4352step2 raw4352step2Labels permutation2 permutation6
    mixedMoment B raw4352step3 raw4352step3Labels = mixedMoment B raw4352step4 raw4352step4Labels := by
      have ha : raw4352step4 = raw4352step3 := by apply Matrix.ext; unfold raw4352step4 raw4352step3; decide +kernel
      have hl : raw4352step3Labels = labelEmbedding9 ∘ raw4352step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4352step3 raw4352step3Labels raw4352step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw4353 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4353step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4353step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw4353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4353step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4353step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4353step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4353step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4353 raw4353Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw4353 raw4353Labels = mixedMoment B raw4353step0 raw4353step0Labels := by
      have hz : ∀ j, raw4353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4353step0 = (fun i j => raw4353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4353step0 raw4353; decide +kernel
      have hl : raw4353step0Labels = raw4353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4353 raw4353Labels permutation434 hz
    mixedMoment B raw4353step0 raw4353step0Labels = mixedMoment B raw4353step1 raw4353step1Labels := by
      have hz : ∀ j, raw4353step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4353step1 = (fun i j => raw4353step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4353step1 raw4353step0; decide +kernel
      have hl : raw4353step1Labels = raw4353step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4353step0 raw4353step0Labels permutation80 hz
    mixedMoment B raw4353step1 raw4353step1Labels = mixedMoment B raw4353step2 raw4353step2Labels := by
      have hz : ∀ j, raw4353step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4353step2 = (fun i j => raw4353step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4353step2 raw4353step1; decide +kernel
      have hl : raw4353step2Labels = raw4353step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4353step1 raw4353step1Labels permutation14 hz
    mixedMoment B raw4353step2 raw4353step2Labels = mixedMoment B raw4353step3 raw4353step3Labels := by
      have ha : raw4353step3 = (fun i j => raw4353step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4353step3 raw4353step2; decide +kernel
      have hl : raw4353step3Labels = raw4353step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4353step2 raw4353step2Labels permutation2 permutation6
    mixedMoment B raw4353step3 raw4353step3Labels = mixedMoment B raw4353step4 raw4353step4Labels := by
      have ha : raw4353step4 = raw4353step3 := by apply Matrix.ext; unfold raw4353step4 raw4353step3; decide +kernel
      have hl : raw4353step3Labels = labelEmbedding9 ∘ raw4353step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4353step3 raw4353step3Labels raw4353step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw4354 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4354step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4354step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4354step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4354 raw4354Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4354 raw4354Labels = mixedMoment B raw4354step0 raw4354step0Labels := by
      have hz : ∀ j, raw4354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4354step0 = (fun i j => raw4354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4354step0 raw4354; decide +kernel
      have hl : raw4354step0Labels = raw4354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4354 raw4354Labels permutation434 hz
    mixedMoment B raw4354step0 raw4354step0Labels = mixedMoment B raw4354step1 raw4354step1Labels := by
      have hz : ∀ j, raw4354step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4354step1 = (fun i j => raw4354step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4354step1 raw4354step0; decide +kernel
      have hl : raw4354step1Labels = raw4354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4354step0 raw4354step0Labels permutation56 hz
    mixedMoment B raw4354step1 raw4354step1Labels = mixedMoment B raw4354step2 raw4354step2Labels := by
      have ha : raw4354step2 = (fun i j => raw4354step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4354step2 raw4354step1; decide +kernel
      have hl : raw4354step2Labels = raw4354step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4354step1 raw4354step1Labels permutation8 permutation6
    mixedMoment B raw4354step2 raw4354step2Labels = mixedMoment B raw4354step3 raw4354step3Labels := by
      have ha : raw4354step3 = raw4354step2 := by apply Matrix.ext; unfold raw4354step3 raw4354step2; decide +kernel
      have hl : raw4354step2Labels = labelEmbedding9 ∘ raw4354step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4354step2 raw4354step2Labels raw4354step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4355 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4355step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4355step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4355 raw4355Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4355 raw4355Labels = mixedMoment B raw4355step0 raw4355step0Labels := by
      have hz : ∀ j, raw4355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4355step0 = (fun i j => raw4355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4355step0 raw4355; decide +kernel
      have hl : raw4355step0Labels = raw4355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4355 raw4355Labels permutation346 hz
    mixedMoment B raw4355step0 raw4355step0Labels = mixedMoment B raw4355step1 raw4355step1Labels := by
      have hz : ∀ j, raw4355step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4355step1 = (fun i j => raw4355step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4355step1 raw4355step0; decide +kernel
      have hl : raw4355step1Labels = raw4355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4355step0 raw4355step0Labels permutation56 hz
    mixedMoment B raw4355step1 raw4355step1Labels = mixedMoment B raw4355step2 raw4355step2Labels := by
      have ha : raw4355step2 = (fun i j => raw4355step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4355step2 raw4355step1; decide +kernel
      have hl : raw4355step2Labels = raw4355step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4355step1 raw4355step1Labels permutation8 permutation6
    mixedMoment B raw4355step2 raw4355step2Labels = mixedMoment B raw4355step3 raw4355step3Labels := by
      have ha : raw4355step3 = raw4355step2 := by apply Matrix.ext; unfold raw4355step3 raw4355step2; decide +kernel
      have hl : raw4355step2Labels = labelEmbedding9 ∘ raw4355step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4355step2 raw4355step2Labels raw4355step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4356 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, -2, 3]]
def raw4356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -2, 3]]
def raw4356step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw4356step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4356step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw4356step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4356 raw4356Labels = mixedMoment B node5312 node5312Labels := by
  calc
    mixedMoment B raw4356 raw4356Labels = mixedMoment B raw4356step0 raw4356step0Labels := by
      have hz : ∀ j, raw4356 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4356step0 = (fun i j => raw4356 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4356step0 raw4356; decide +kernel
      have hl : raw4356step0Labels = raw4356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4356 raw4356Labels permutation520 hz
    mixedMoment B raw4356step0 raw4356step0Labels = mixedMoment B raw4356step1 raw4356step1Labels := by
      have hz : ∀ j, raw4356step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4356step1 = (fun i j => raw4356step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4356step1 raw4356step0; decide +kernel
      have hl : raw4356step1Labels = raw4356step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4356step0 raw4356step0Labels permutation104 hz
    mixedMoment B raw4356step1 raw4356step1Labels = mixedMoment B raw4356step2 raw4356step2Labels := by
      have hz : ∀ j, raw4356step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4356step2 = (fun i j => raw4356step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4356step2 raw4356step1; decide +kernel
      have hl : raw4356step2Labels = raw4356step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4356step1 raw4356step1Labels permutation20 hz
    mixedMoment B raw4356step2 raw4356step2Labels = mixedMoment B raw4356step3 raw4356step3Labels := by
      have hz : ∀ j, raw4356step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw4356step3 = (fun i j => raw4356step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw4356step3 raw4356step2; decide +kernel
      have hl : raw4356step3Labels = raw4356step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4356step2 raw4356step2Labels permutation4 hz
    mixedMoment B raw4356step3 raw4356step3Labels = mixedMoment B raw4356step4 raw4356step4Labels := by
      have ha : raw4356step4 = (fun i j => raw4356step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4356step4 raw4356step3; decide +kernel
      have hl : raw4356step4Labels = raw4356step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4356step3 raw4356step3Labels permutation0 permutation6
    mixedMoment B raw4356step4 raw4356step4Labels = mixedMoment B raw4356step5 raw4356step5Labels := by
      have ha : raw4356step5 = raw4356step4 := by apply Matrix.ext; unfold raw4356step5 raw4356step4; decide +kernel
      have hl : raw4356step4Labels = labelEmbedding9 ∘ raw4356step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4356step4 raw4356step4Labels raw4356step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5312 node5312Labels := by rfl

def raw4357 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4357step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4357step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4357 raw4357Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw4357 raw4357Labels = mixedMoment B raw4357step0 raw4357step0Labels := by
      have hz : ∀ j, raw4357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4357step0 = (fun i j => raw4357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4357step0 raw4357; decide +kernel
      have hl : raw4357step0Labels = raw4357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4357 raw4357Labels permutation434 hz
    mixedMoment B raw4357step0 raw4357step0Labels = mixedMoment B raw4357step1 raw4357step1Labels := by
      have hz : ∀ j, raw4357step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4357step1 = (fun i j => raw4357step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4357step1 raw4357step0; decide +kernel
      have hl : raw4357step1Labels = raw4357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4357step0 raw4357step0Labels permutation56 hz
    mixedMoment B raw4357step1 raw4357step1Labels = mixedMoment B raw4357step2 raw4357step2Labels := by
      have ha : raw4357step2 = (fun i j => raw4357step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4357step2 raw4357step1; decide +kernel
      have hl : raw4357step2Labels = raw4357step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4357step1 raw4357step1Labels permutation8 permutation6
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw4358 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4358step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4358step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4358 raw4358Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw4358 raw4358Labels = mixedMoment B raw4358step0 raw4358step0Labels := by
      have hz : ∀ j, raw4358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4358step0 = (fun i j => raw4358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4358step0 raw4358; decide +kernel
      have hl : raw4358step0Labels = raw4358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4358 raw4358Labels permutation346 hz
    mixedMoment B raw4358step0 raw4358step0Labels = mixedMoment B raw4358step1 raw4358step1Labels := by
      have hz : ∀ j, raw4358step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4358step1 = (fun i j => raw4358step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4358step1 raw4358step0; decide +kernel
      have hl : raw4358step1Labels = raw4358step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4358step0 raw4358step0Labels permutation56 hz
    mixedMoment B raw4358step1 raw4358step1Labels = mixedMoment B raw4358step2 raw4358step2Labels := by
      have ha : raw4358step2 = (fun i j => raw4358step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4358step2 raw4358step1; decide +kernel
      have hl : raw4358step2Labels = raw4358step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4358step1 raw4358step1Labels permutation8 permutation6
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw4359 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4359step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4359step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, -1, 3]]
def raw4359step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4359step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 1, -3], ![-2, -1, 3]]
def raw4359step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4359step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]
def raw4359step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4359 raw4359Labels = mixedMoment B node3126 node3126Labels := by
  calc
    mixedMoment B raw4359 raw4359Labels = mixedMoment B raw4359step0 raw4359step0Labels := by
      have hz : ∀ j, raw4359 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4359step0 = (fun i j => raw4359 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4359step0 raw4359; decide +kernel
      have hl : raw4359step0Labels = raw4359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4359 raw4359Labels permutation520 hz
    mixedMoment B raw4359step0 raw4359step0Labels = mixedMoment B raw4359step1 raw4359step1Labels := by
      have hz : ∀ j, raw4359step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4359step1 = (fun i j => raw4359step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4359step1 raw4359step0; decide +kernel
      have hl : raw4359step1Labels = raw4359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4359step0 raw4359step0Labels permutation104 hz
    mixedMoment B raw4359step1 raw4359step1Labels = mixedMoment B raw4359step2 raw4359step2Labels := by
      have hz : ∀ j, raw4359step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4359step2 = (fun i j => raw4359step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4359step2 raw4359step1; decide +kernel
      have hl : raw4359step2Labels = raw4359step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4359step1 raw4359step1Labels permutation20 hz
    mixedMoment B raw4359step2 raw4359step2Labels = mixedMoment B raw4359step3 raw4359step3Labels := by
      have hz : ∀ j, raw4359step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw4359step3 = (fun i j => raw4359step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw4359step3 raw4359step2; decide +kernel
      have hl : raw4359step3Labels = raw4359step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4359step2 raw4359step2Labels permutation4 hz
    mixedMoment B raw4359step3 raw4359step3Labels = mixedMoment B raw4359step4 raw4359step4Labels := by
      have ha : raw4359step4 = (fun i j => raw4359step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4359step4 raw4359step3; decide +kernel
      have hl : raw4359step4Labels = raw4359step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4359step3 raw4359step3Labels permutation0 permutation6
    _ = mixedMoment B node3126 node3126Labels := by rfl

def raw4360 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4360step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4360step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4360step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4360step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw4360step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4360 raw4360Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw4360 raw4360Labels = mixedMoment B raw4360step0 raw4360step0Labels := by
      have hz : ∀ j, raw4360 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4360step0 = (fun i j => raw4360 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4360step0 raw4360; decide +kernel
      have hl : raw4360step0Labels = raw4360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4360 raw4360Labels permutation434 hz
    mixedMoment B raw4360step0 raw4360step0Labels = mixedMoment B raw4360step1 raw4360step1Labels := by
      have hz : ∀ j, raw4360step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4360step1 = (fun i j => raw4360step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4360step1 raw4360step0; decide +kernel
      have hl : raw4360step1Labels = raw4360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4360step0 raw4360step0Labels permutation80 hz
    mixedMoment B raw4360step1 raw4360step1Labels = mixedMoment B raw4360step2 raw4360step2Labels := by
      have hz : ∀ j, raw4360step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4360step2 = (fun i j => raw4360step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4360step2 raw4360step1; decide +kernel
      have hl : raw4360step2Labels = raw4360step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4360step1 raw4360step1Labels permutation14 hz
    mixedMoment B raw4360step2 raw4360step2Labels = mixedMoment B raw4360step3 raw4360step3Labels := by
      have ha : raw4360step3 = (fun i j => raw4360step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4360step3 raw4360step2; decide +kernel
      have hl : raw4360step3Labels = raw4360step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4360step2 raw4360step2Labels permutation2 permutation6
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw4361 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4361step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4361 raw4361Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw4361 raw4361Labels = mixedMoment B raw4361step0 raw4361step0Labels := by
      have hz : ∀ j, raw4361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4361step0 = (fun i j => raw4361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4361step0 raw4361; decide +kernel
      have hl : raw4361step0Labels = raw4361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4361 raw4361Labels permutation434 hz
    mixedMoment B raw4361step0 raw4361step0Labels = mixedMoment B raw4361step1 raw4361step1Labels := by
      have hz : ∀ j, raw4361step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4361step1 = (fun i j => raw4361step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4361step1 raw4361step0; decide +kernel
      have hl : raw4361step1Labels = raw4361step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4361step0 raw4361step0Labels permutation80 hz
    mixedMoment B raw4361step1 raw4361step1Labels = mixedMoment B raw4361step2 raw4361step2Labels := by
      have ha : raw4361step2 = (fun i j => raw4361step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4361step2 raw4361step1; decide +kernel
      have hl : raw4361step2Labels = raw4361step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4361step1 raw4361step1Labels permutation8 permutation6
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw4362 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4362 raw4362Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4362 raw4362Labels = mixedMoment B raw4362step0 raw4362step0Labels := by
      have hz : ∀ j, raw4362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4362step0 = (fun i j => raw4362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4362step0 raw4362; decide +kernel
      have hl : raw4362step0Labels = raw4362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4362 raw4362Labels permutation434 hz
    mixedMoment B raw4362step0 raw4362step0Labels = mixedMoment B raw4362step1 raw4362step1Labels := by
      have ha : raw4362step1 = (fun i j => raw4362step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4362step1 raw4362step0; decide +kernel
      have hl : raw4362step1Labels = raw4362step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4362step0 raw4362step0Labels permutation38 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4363 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4363 raw4363Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4363 raw4363Labels = mixedMoment B raw4363step0 raw4363step0Labels := by
      have hz : ∀ j, raw4363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4363step0 = (fun i j => raw4363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4363step0 raw4363; decide +kernel
      have hl : raw4363step0Labels = raw4363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4363 raw4363Labels permutation346 hz
    mixedMoment B raw4363step0 raw4363step0Labels = mixedMoment B raw4363step1 raw4363step1Labels := by
      have ha : raw4363step1 = (fun i j => raw4363step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4363step1 raw4363step0; decide +kernel
      have hl : raw4363step1Labels = raw4363step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4363step0 raw4363step0Labels permutation38 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4364 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4364step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4364step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4364step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4364step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4364step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4364 raw4364Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw4364 raw4364Labels = mixedMoment B raw4364step0 raw4364step0Labels := by
      have hz : ∀ j, raw4364 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4364step0 = (fun i j => raw4364 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4364step0 raw4364; decide +kernel
      have hl : raw4364step0Labels = raw4364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4364 raw4364Labels permutation520 hz
    mixedMoment B raw4364step0 raw4364step0Labels = mixedMoment B raw4364step1 raw4364step1Labels := by
      have hz : ∀ j, raw4364step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4364step1 = (fun i j => raw4364step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4364step1 raw4364step0; decide +kernel
      have hl : raw4364step1Labels = raw4364step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4364step0 raw4364step0Labels permutation104 hz
    mixedMoment B raw4364step1 raw4364step1Labels = mixedMoment B raw4364step2 raw4364step2Labels := by
      have hz : ∀ j, raw4364step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4364step2 = (fun i j => raw4364step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4364step2 raw4364step1; decide +kernel
      have hl : raw4364step2Labels = raw4364step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4364step1 raw4364step1Labels permutation20 hz
    mixedMoment B raw4364step2 raw4364step2Labels = mixedMoment B raw4364step3 raw4364step3Labels := by
      have ha : raw4364step3 = (fun i j => raw4364step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4364step3 raw4364step2; decide +kernel
      have hl : raw4364step3Labels = raw4364step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4364step2 raw4364step2Labels permutation2 permutation6
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw4365 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4365 raw4365Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw4365 raw4365Labels = mixedMoment B raw4365step0 raw4365step0Labels := by
      have hz : ∀ j, raw4365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4365step0 = (fun i j => raw4365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4365step0 raw4365; decide +kernel
      have hl : raw4365step0Labels = raw4365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4365 raw4365Labels permutation434 hz
    mixedMoment B raw4365step0 raw4365step0Labels = mixedMoment B raw4365step1 raw4365step1Labels := by
      have hz : ∀ j, raw4365step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4365step1 = (fun i j => raw4365step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4365step1 raw4365step0; decide +kernel
      have hl : raw4365step1Labels = raw4365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4365step0 raw4365step0Labels permutation80 hz
    mixedMoment B raw4365step1 raw4365step1Labels = mixedMoment B raw4365step2 raw4365step2Labels := by
      have ha : raw4365step2 = (fun i j => raw4365step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4365step2 raw4365step1; decide +kernel
      have hl : raw4365step2Labels = raw4365step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4365step1 raw4365step1Labels permutation8 permutation6
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw4366 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4366 raw4366Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4366 raw4366Labels = mixedMoment B raw4366step0 raw4366step0Labels := by
      have hz : ∀ j, raw4366 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4366step0 = (fun i j => raw4366 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4366step0 raw4366; decide +kernel
      have hl : raw4366step0Labels = raw4366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4366 raw4366Labels permutation265 hz
    mixedMoment B raw4366step0 raw4366step0Labels = mixedMoment B raw4366step1 raw4366step1Labels := by
      have ha : raw4366step1 = (fun i j => raw4366step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4366step1 raw4366step0; decide +kernel
      have hl : raw4366step1Labels = raw4366step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4366step0 raw4366step0Labels permutation38 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4367 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4367step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4367step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4367step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4367step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4367step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4367 raw4367Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw4367 raw4367Labels = mixedMoment B raw4367step0 raw4367step0Labels := by
      have hz : ∀ j, raw4367 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4367step0 = (fun i j => raw4367 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4367step0 raw4367; decide +kernel
      have hl : raw4367step0Labels = raw4367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4367 raw4367Labels permutation520 hz
    mixedMoment B raw4367step0 raw4367step0Labels = mixedMoment B raw4367step1 raw4367step1Labels := by
      have hz : ∀ j, raw4367step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4367step1 = (fun i j => raw4367step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4367step1 raw4367step0; decide +kernel
      have hl : raw4367step1Labels = raw4367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4367step0 raw4367step0Labels permutation104 hz
    mixedMoment B raw4367step1 raw4367step1Labels = mixedMoment B raw4367step2 raw4367step2Labels := by
      have hz : ∀ j, raw4367step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4367step2 = (fun i j => raw4367step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4367step2 raw4367step1; decide +kernel
      have hl : raw4367step2Labels = raw4367step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4367step1 raw4367step1Labels permutation14 hz
    mixedMoment B raw4367step2 raw4367step2Labels = mixedMoment B raw4367step3 raw4367step3Labels := by
      have ha : raw4367step3 = (fun i j => raw4367step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4367step3 raw4367step2; decide +kernel
      have hl : raw4367step3Labels = raw4367step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4367step2 raw4367step2Labels permutation2 permutation6
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw4368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4368step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4368step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw4368step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4368step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4368step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4368 raw4368Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw4368 raw4368Labels = mixedMoment B raw4368step0 raw4368step0Labels := by
      have hz : ∀ j, raw4368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4368step0 = (fun i j => raw4368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4368step0 raw4368; decide +kernel
      have hl : raw4368step0Labels = raw4368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4368 raw4368Labels permutation434 hz
    mixedMoment B raw4368step0 raw4368step0Labels = mixedMoment B raw4368step1 raw4368step1Labels := by
      have hz : ∀ j, raw4368step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4368step1 = (fun i j => raw4368step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4368step1 raw4368step0; decide +kernel
      have hl : raw4368step1Labels = raw4368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4368step0 raw4368step0Labels permutation80 hz
    mixedMoment B raw4368step1 raw4368step1Labels = mixedMoment B raw4368step2 raw4368step2Labels := by
      have hz : ∀ j, raw4368step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4368step2 = (fun i j => raw4368step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4368step2 raw4368step1; decide +kernel
      have hl : raw4368step2Labels = raw4368step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4368step1 raw4368step1Labels permutation14 hz
    mixedMoment B raw4368step2 raw4368step2Labels = mixedMoment B raw4368step3 raw4368step3Labels := by
      have ha : raw4368step3 = (fun i j => raw4368step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4368step3 raw4368step2; decide +kernel
      have hl : raw4368step3Labels = raw4368step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4368step2 raw4368step2Labels permutation2 permutation6
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw4369 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4369step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4369step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4369step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4369 raw4369Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw4369 raw4369Labels = mixedMoment B raw4369step0 raw4369step0Labels := by
      have hz : ∀ j, raw4369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4369step0 = (fun i j => raw4369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4369step0 raw4369; decide +kernel
      have hl : raw4369step0Labels = raw4369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4369 raw4369Labels permutation434 hz
    mixedMoment B raw4369step0 raw4369step0Labels = mixedMoment B raw4369step1 raw4369step1Labels := by
      have hz : ∀ j, raw4369step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4369step1 = (fun i j => raw4369step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4369step1 raw4369step0; decide +kernel
      have hl : raw4369step1Labels = raw4369step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4369step0 raw4369step0Labels permutation56 hz
    mixedMoment B raw4369step1 raw4369step1Labels = mixedMoment B raw4369step2 raw4369step2Labels := by
      have ha : raw4369step2 = (fun i j => raw4369step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4369step2 raw4369step1; decide +kernel
      have hl : raw4369step2Labels = raw4369step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4369step1 raw4369step1Labels permutation8 permutation6
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw4370 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4370step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4370 raw4370Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw4370 raw4370Labels = mixedMoment B raw4370step0 raw4370step0Labels := by
      have hz : ∀ j, raw4370 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4370step0 = (fun i j => raw4370 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4370step0 raw4370; decide +kernel
      have hl : raw4370step0Labels = raw4370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4370 raw4370Labels permutation346 hz
    mixedMoment B raw4370step0 raw4370step0Labels = mixedMoment B raw4370step1 raw4370step1Labels := by
      have hz : ∀ j, raw4370step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4370step1 = (fun i j => raw4370step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4370step1 raw4370step0; decide +kernel
      have hl : raw4370step1Labels = raw4370step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4370step0 raw4370step0Labels permutation56 hz
    mixedMoment B raw4370step1 raw4370step1Labels = mixedMoment B raw4370step2 raw4370step2Labels := by
      have ha : raw4370step2 = (fun i j => raw4370step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4370step2 raw4370step1; decide +kernel
      have hl : raw4370step2Labels = raw4370step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4370step1 raw4370step1Labels permutation8 permutation6
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw4371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4371step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, -2, 3]]
def raw4371step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4371step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -2, 3]]
def raw4371step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4371step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw4371step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4371 raw4371Labels = mixedMoment B node2790 node2790Labels := by
  calc
    mixedMoment B raw4371 raw4371Labels = mixedMoment B raw4371step0 raw4371step0Labels := by
      have hz : ∀ j, raw4371 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4371step0 = (fun i j => raw4371 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4371step0 raw4371; decide +kernel
      have hl : raw4371step0Labels = raw4371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4371 raw4371Labels permutation520 hz
    mixedMoment B raw4371step0 raw4371step0Labels = mixedMoment B raw4371step1 raw4371step1Labels := by
      have hz : ∀ j, raw4371step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4371step1 = (fun i j => raw4371step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4371step1 raw4371step0; decide +kernel
      have hl : raw4371step1Labels = raw4371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4371step0 raw4371step0Labels permutation104 hz
    mixedMoment B raw4371step1 raw4371step1Labels = mixedMoment B raw4371step2 raw4371step2Labels := by
      have hz : ∀ j, raw4371step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4371step2 = (fun i j => raw4371step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4371step2 raw4371step1; decide +kernel
      have hl : raw4371step2Labels = raw4371step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4371step1 raw4371step1Labels permutation20 hz
    mixedMoment B raw4371step2 raw4371step2Labels = mixedMoment B raw4371step3 raw4371step3Labels := by
      have hz : ∀ j, raw4371step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw4371step3 = (fun i j => raw4371step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw4371step3 raw4371step2; decide +kernel
      have hl : raw4371step3Labels = raw4371step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4371step2 raw4371step2Labels permutation4 hz
    mixedMoment B raw4371step3 raw4371step3Labels = mixedMoment B raw4371step4 raw4371step4Labels := by
      have ha : raw4371step4 = (fun i j => raw4371step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4371step4 raw4371step3; decide +kernel
      have hl : raw4371step4Labels = raw4371step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4371step3 raw4371step3Labels permutation0 permutation6
    _ = mixedMoment B node2790 node2790Labels := by rfl

def raw4372 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4372step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4372 raw4372Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw4372 raw4372Labels = mixedMoment B raw4372step0 raw4372step0Labels := by
      have hz : ∀ j, raw4372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4372step0 = (fun i j => raw4372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4372step0 raw4372; decide +kernel
      have hl : raw4372step0Labels = raw4372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4372 raw4372Labels permutation434 hz
    mixedMoment B raw4372step0 raw4372step0Labels = mixedMoment B raw4372step1 raw4372step1Labels := by
      have hz : ∀ j, raw4372step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4372step1 = (fun i j => raw4372step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4372step1 raw4372step0; decide +kernel
      have hl : raw4372step1Labels = raw4372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4372step0 raw4372step0Labels permutation56 hz
    mixedMoment B raw4372step1 raw4372step1Labels = mixedMoment B raw4372step2 raw4372step2Labels := by
      have ha : raw4372step2 = (fun i j => raw4372step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4372step2 raw4372step1; decide +kernel
      have hl : raw4372step2Labels = raw4372step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4372step1 raw4372step1Labels permutation29 permutation2
    _ = mixedMoment B node3545 node3545Labels := by rfl

def raw4373 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4373 raw4373Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw4373 raw4373Labels = mixedMoment B raw4373step0 raw4373step0Labels := by
      have hz : ∀ j, raw4373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4373step0 = (fun i j => raw4373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4373step0 raw4373; decide +kernel
      have hl : raw4373step0Labels = raw4373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4373 raw4373Labels permutation346 hz
    mixedMoment B raw4373step0 raw4373step0Labels = mixedMoment B raw4373step1 raw4373step1Labels := by
      have hz : ∀ j, raw4373step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4373step1 = (fun i j => raw4373step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4373step1 raw4373step0; decide +kernel
      have hl : raw4373step1Labels = raw4373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4373step0 raw4373step0Labels permutation56 hz
    mixedMoment B raw4373step1 raw4373step1Labels = mixedMoment B raw4373step2 raw4373step2Labels := by
      have ha : raw4373step2 = (fun i j => raw4373step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4373step2 raw4373step1; decide +kernel
      have hl : raw4373step2Labels = raw4373step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4373step1 raw4373step1Labels permutation29 permutation2
    _ = mixedMoment B node3545 node3545Labels := by rfl

def raw4374 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, -1, 3]]
def raw4374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 1, -3], ![-2, -1, 3]]
def raw4374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -1, 3], ![2, 1, -3]]
def raw4374step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4374 raw4374Labels = mixedMoment B node3636 node3636Labels := by
  calc
    mixedMoment B raw4374 raw4374Labels = mixedMoment B raw4374step0 raw4374step0Labels := by
      have hz : ∀ j, raw4374 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4374step0 = (fun i j => raw4374 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4374step0 raw4374; decide +kernel
      have hl : raw4374step0Labels = raw4374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4374 raw4374Labels permutation520 hz
    mixedMoment B raw4374step0 raw4374step0Labels = mixedMoment B raw4374step1 raw4374step1Labels := by
      have hz : ∀ j, raw4374step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4374step1 = (fun i j => raw4374step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4374step1 raw4374step0; decide +kernel
      have hl : raw4374step1Labels = raw4374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4374step0 raw4374step0Labels permutation104 hz
    mixedMoment B raw4374step1 raw4374step1Labels = mixedMoment B raw4374step2 raw4374step2Labels := by
      have hz : ∀ j, raw4374step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4374step2 = (fun i j => raw4374step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4374step2 raw4374step1; decide +kernel
      have hl : raw4374step2Labels = raw4374step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4374step1 raw4374step1Labels permutation20 hz
    mixedMoment B raw4374step2 raw4374step2Labels = mixedMoment B raw4374step3 raw4374step3Labels := by
      have hz : ∀ j, raw4374step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw4374step3 = (fun i j => raw4374step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw4374step3 raw4374step2; decide +kernel
      have hl : raw4374step3Labels = raw4374step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4374step2 raw4374step2Labels permutation4 hz
    mixedMoment B raw4374step3 raw4374step3Labels = mixedMoment B raw4374step4 raw4374step4Labels := by
      have ha : raw4374step4 = (fun i j => raw4374step3 (permutation1 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4374step4 raw4374step3; decide +kernel
      have hl : raw4374step4Labels = raw4374step3Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4374step3 raw4374step3Labels permutation1 permutation2
    _ = mixedMoment B node3636 node3636Labels := by rfl

def raw4375 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4375step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4375step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw4375step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4375 raw4375Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw4375 raw4375Labels = mixedMoment B raw4375step0 raw4375step0Labels := by
      have hz : ∀ j, raw4375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4375step0 = (fun i j => raw4375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4375step0 raw4375; decide +kernel
      have hl : raw4375step0Labels = raw4375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4375 raw4375Labels permutation434 hz
    mixedMoment B raw4375step0 raw4375step0Labels = mixedMoment B raw4375step1 raw4375step1Labels := by
      have hz : ∀ j, raw4375step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4375step1 = (fun i j => raw4375step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4375step1 raw4375step0; decide +kernel
      have hl : raw4375step1Labels = raw4375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4375step0 raw4375step0Labels permutation80 hz
    mixedMoment B raw4375step1 raw4375step1Labels = mixedMoment B raw4375step2 raw4375step2Labels := by
      have hz : ∀ j, raw4375step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4375step2 = (fun i j => raw4375step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4375step2 raw4375step1; decide +kernel
      have hl : raw4375step2Labels = raw4375step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4375step1 raw4375step1Labels permutation14 hz
    mixedMoment B raw4375step2 raw4375step2Labels = mixedMoment B raw4375step3 raw4375step3Labels := by
      have ha : raw4375step3 = (fun i j => raw4375step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4375step3 raw4375step2; decide +kernel
      have hl : raw4375step3Labels = raw4375step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4375step2 raw4375step2Labels permutation7 permutation2
    _ = mixedMoment B node2292 node2292Labels := by rfl

def raw4376 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4376step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4376step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4376 raw4376Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw4376 raw4376Labels = mixedMoment B raw4376step0 raw4376step0Labels := by
      have hz : ∀ j, raw4376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4376step0 = (fun i j => raw4376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4376step0 raw4376; decide +kernel
      have hl : raw4376step0Labels = raw4376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4376 raw4376Labels permutation434 hz
    mixedMoment B raw4376step0 raw4376step0Labels = mixedMoment B raw4376step1 raw4376step1Labels := by
      have hz : ∀ j, raw4376step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4376step1 = (fun i j => raw4376step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4376step1 raw4376step0; decide +kernel
      have hl : raw4376step1Labels = raw4376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4376step0 raw4376step0Labels permutation80 hz
    mixedMoment B raw4376step1 raw4376step1Labels = mixedMoment B raw4376step2 raw4376step2Labels := by
      have ha : raw4376step2 = (fun i j => raw4376step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4376step2 raw4376step1; decide +kernel
      have hl : raw4376step2Labels = raw4376step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4376step1 raw4376step1Labels permutation8 permutation4
    mixedMoment B raw4376step2 raw4376step2Labels = mixedMoment B raw4376step3 raw4376step3Labels := by
      have ha : raw4376step3 = -raw4376step2 := by apply Matrix.ext; change ∀ i j, raw4376step3 i j = -(raw4376step2 i j); unfold raw4376step3 raw4376step2; decide +kernel
      have hl : raw4376step3Labels = raw4376step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw4377 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4377step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4377step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4377step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4377 raw4377Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw4377 raw4377Labels = mixedMoment B raw4377step0 raw4377step0Labels := by
      have hz : ∀ j, raw4377 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4377step0 = (fun i j => raw4377 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4377step0 raw4377; decide +kernel
      have hl : raw4377step0Labels = raw4377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4377 raw4377Labels permutation434 hz
    mixedMoment B raw4377step0 raw4377step0Labels = mixedMoment B raw4377step1 raw4377step1Labels := by
      have hz : ∀ j, raw4377step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4377step1 = (fun i j => raw4377step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4377step1 raw4377step0; decide +kernel
      have hl : raw4377step1Labels = raw4377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4377step0 raw4377step0Labels permutation56 hz
    mixedMoment B raw4377step1 raw4377step1Labels = mixedMoment B raw4377step2 raw4377step2Labels := by
      have ha : raw4377step2 = (fun i j => raw4377step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4377step2 raw4377step1; decide +kernel
      have hl : raw4377step2Labels = raw4377step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4377step1 raw4377step1Labels permutation8 permutation4
    mixedMoment B raw4377step2 raw4377step2Labels = mixedMoment B raw4377step3 raw4377step3Labels := by
      have ha : raw4377step3 = -raw4377step2 := by apply Matrix.ext; change ∀ i j, raw4377step3 i j = -(raw4377step2 i j); unfold raw4377step3 raw4377step2; decide +kernel
      have hl : raw4377step3Labels = raw4377step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw4378 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw4378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-2, -1, 3]]
def raw4378step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw4378step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4378 raw4378Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw4378 raw4378Labels = mixedMoment B raw4378step0 raw4378step0Labels := by
      have hz : ∀ j, raw4378 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4378step0 = (fun i j => raw4378 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4378step0 raw4378; decide +kernel
      have hl : raw4378step0Labels = raw4378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4378 raw4378Labels permutation434 hz
    mixedMoment B raw4378step0 raw4378step0Labels = mixedMoment B raw4378step1 raw4378step1Labels := by
      have hz : ∀ j, raw4378step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4378step1 = (fun i j => raw4378step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4378step1 raw4378step0; decide +kernel
      have hl : raw4378step1Labels = raw4378step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4378step0 raw4378step0Labels permutation80 hz
    mixedMoment B raw4378step1 raw4378step1Labels = mixedMoment B raw4378step2 raw4378step2Labels := by
      have hz : ∀ j, raw4378step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4378step2 = (fun i j => raw4378step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4378step2 raw4378step1; decide +kernel
      have hl : raw4378step2Labels = raw4378step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4378step1 raw4378step1Labels permutation14 hz
    mixedMoment B raw4378step2 raw4378step2Labels = mixedMoment B raw4378step3 raw4378step3Labels := by
      have ha : raw4378step3 = (fun i j => raw4378step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4378step3 raw4378step2; decide +kernel
      have hl : raw4378step3Labels = raw4378step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4378step2 raw4378step2Labels permutation2 permutation4
    mixedMoment B raw4378step3 raw4378step3Labels = mixedMoment B raw4378step4 raw4378step4Labels := by
      have ha : raw4378step4 = -raw4378step3 := by apply Matrix.ext; change ∀ i j, raw4378step4 i j = -(raw4378step3 i j); unfold raw4378step4 raw4378step3; decide +kernel
      have hl : raw4378step4Labels = raw4378step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2292 node2292Labels := by rfl

def raw4379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4379step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw4379step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4379 raw4379Labels = mixedMoment B node5456 node5456Labels := by
  calc
    mixedMoment B raw4379 raw4379Labels = mixedMoment B raw4379step0 raw4379step0Labels := by
      have hz : ∀ j, raw4379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4379step0 = (fun i j => raw4379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4379step0 raw4379; decide +kernel
      have hl : raw4379step0Labels = raw4379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4379 raw4379Labels permutation434 hz
    mixedMoment B raw4379step0 raw4379step0Labels = mixedMoment B raw4379step1 raw4379step1Labels := by
      have hz : ∀ j, raw4379step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4379step1 = (fun i j => raw4379step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4379step1 raw4379step0; decide +kernel
      have hl : raw4379step1Labels = raw4379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4379step0 raw4379step0Labels permutation80 hz
    mixedMoment B raw4379step1 raw4379step1Labels = mixedMoment B raw4379step2 raw4379step2Labels := by
      have hz : ∀ j, raw4379step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4379step2 = (fun i j => raw4379step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4379step2 raw4379step1; decide +kernel
      have hl : raw4379step2Labels = raw4379step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4379step1 raw4379step1Labels permutation14 hz
    _ = mixedMoment B node5456 node5456Labels := by rfl

def raw4380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4380step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4380step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4380step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4380 raw4380Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw4380 raw4380Labels = mixedMoment B raw4380step0 raw4380step0Labels := by
      have hz : ∀ j, raw4380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4380step0 = (fun i j => raw4380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4380step0 raw4380; decide +kernel
      have hl : raw4380step0Labels = raw4380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4380 raw4380Labels permutation434 hz
    mixedMoment B raw4380step0 raw4380step0Labels = mixedMoment B raw4380step1 raw4380step1Labels := by
      have hz : ∀ j, raw4380step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4380step1 = (fun i j => raw4380step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4380step1 raw4380step0; decide +kernel
      have hl : raw4380step1Labels = raw4380step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4380step0 raw4380step0Labels permutation80 hz
    mixedMoment B raw4380step1 raw4380step1Labels = mixedMoment B raw4380step2 raw4380step2Labels := by
      have ha : raw4380step2 = (fun i j => raw4380step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4380step2 raw4380step1; decide +kernel
      have hl : raw4380step2Labels = raw4380step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4380step1 raw4380step1Labels permutation10 permutation3
    mixedMoment B raw4380step2 raw4380step2Labels = mixedMoment B raw4380step3 raw4380step3Labels := by
      have ha : raw4380step3 = raw4380step2 := by apply Matrix.ext; unfold raw4380step3 raw4380step2; decide +kernel
      have hl : raw4380step2Labels = labelEmbedding6 ∘ raw4380step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4380step2 raw4380step2Labels raw4380step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

def raw4381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4381step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4381step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4381step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4381 raw4381Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4381 raw4381Labels = mixedMoment B raw4381step0 raw4381step0Labels := by
      have hz : ∀ j, raw4381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4381step0 = (fun i j => raw4381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4381step0 raw4381; decide +kernel
      have hl : raw4381step0Labels = raw4381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4381 raw4381Labels permutation434 hz
    mixedMoment B raw4381step0 raw4381step0Labels = mixedMoment B raw4381step1 raw4381step1Labels := by
      have ha : raw4381step1 = (fun i j => raw4381step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4381step1 raw4381step0; decide +kernel
      have hl : raw4381step1Labels = raw4381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4381step0 raw4381step0Labels permutation139 permutation3
    mixedMoment B raw4381step1 raw4381step1Labels = mixedMoment B raw4381step2 raw4381step2Labels := by
      have ha : raw4381step2 = -raw4381step1 := by apply Matrix.ext; change ∀ i j, raw4381step2 i j = -(raw4381step1 i j); unfold raw4381step2 raw4381step1; decide +kernel
      have hl : raw4381step2Labels = raw4381step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4381step2 raw4381step2Labels = mixedMoment B raw4381step3 raw4381step3Labels := by
      have ha : raw4381step3 = raw4381step2 := by apply Matrix.ext; unfold raw4381step3 raw4381step2; decide +kernel
      have hl : raw4381step2Labels = labelEmbedding6 ∘ raw4381step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4381step2 raw4381step2Labels raw4381step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw4382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4382step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4382step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4382step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4382step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4382 raw4382Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4382 raw4382Labels = mixedMoment B raw4382step0 raw4382step0Labels := by
      have hz : ∀ j, raw4382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4382step0 = (fun i j => raw4382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4382step0 raw4382; decide +kernel
      have hl : raw4382step0Labels = raw4382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4382 raw4382Labels permutation346 hz
    mixedMoment B raw4382step0 raw4382step0Labels = mixedMoment B raw4382step1 raw4382step1Labels := by
      have ha : raw4382step1 = (fun i j => raw4382step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4382step1 raw4382step0; decide +kernel
      have hl : raw4382step1Labels = raw4382step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4382step0 raw4382step0Labels permutation139 permutation3
    mixedMoment B raw4382step1 raw4382step1Labels = mixedMoment B raw4382step2 raw4382step2Labels := by
      have ha : raw4382step2 = -raw4382step1 := by apply Matrix.ext; change ∀ i j, raw4382step2 i j = -(raw4382step1 i j); unfold raw4382step2 raw4382step1; decide +kernel
      have hl : raw4382step2Labels = raw4382step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4382step2 raw4382step2Labels = mixedMoment B raw4382step3 raw4382step3Labels := by
      have ha : raw4382step3 = raw4382step2 := by apply Matrix.ext; unfold raw4382step3 raw4382step2; decide +kernel
      have hl : raw4382step2Labels = labelEmbedding6 ∘ raw4382step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4382step2 raw4382step2Labels raw4382step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw4383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4383step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4383step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4383step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4383step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4383step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4383step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4383 raw4383Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw4383 raw4383Labels = mixedMoment B raw4383step0 raw4383step0Labels := by
      have hz : ∀ j, raw4383 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4383step0 = (fun i j => raw4383 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4383step0 raw4383; decide +kernel
      have hl : raw4383step0Labels = raw4383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4383 raw4383Labels permutation434 hz
    mixedMoment B raw4383step0 raw4383step0Labels = mixedMoment B raw4383step1 raw4383step1Labels := by
      have hz : ∀ j, raw4383step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4383step1 = (fun i j => raw4383step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4383step1 raw4383step0; decide +kernel
      have hl : raw4383step1Labels = raw4383step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4383step0 raw4383step0Labels permutation80 hz
    mixedMoment B raw4383step1 raw4383step1Labels = mixedMoment B raw4383step2 raw4383step2Labels := by
      have ha : raw4383step2 = (fun i j => raw4383step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4383step2 raw4383step1; decide +kernel
      have hl : raw4383step2Labels = raw4383step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4383step1 raw4383step1Labels permutation29 permutation3
    mixedMoment B raw4383step2 raw4383step2Labels = mixedMoment B raw4383step3 raw4383step3Labels := by
      have ha : raw4383step3 = -raw4383step2 := by apply Matrix.ext; change ∀ i j, raw4383step3 i j = -(raw4383step2 i j); unfold raw4383step3 raw4383step2; decide +kernel
      have hl : raw4383step3Labels = raw4383step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4383step3 raw4383step3Labels = mixedMoment B raw4383step4 raw4383step4Labels := by
      have ha : raw4383step4 = raw4383step3 := by apply Matrix.ext; unfold raw4383step4 raw4383step3; decide +kernel
      have hl : raw4383step3Labels = labelEmbedding6 ∘ raw4383step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4383step3 raw4383step3Labels raw4383step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

def raw4384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4384step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4384step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4384 raw4384Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw4384 raw4384Labels = mixedMoment B raw4384step0 raw4384step0Labels := by
      have hz : ∀ j, raw4384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4384step0 = (fun i j => raw4384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4384step0 raw4384; decide +kernel
      have hl : raw4384step0Labels = raw4384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4384 raw4384Labels permutation434 hz
    mixedMoment B raw4384step0 raw4384step0Labels = mixedMoment B raw4384step1 raw4384step1Labels := by
      have hz : ∀ j, raw4384step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4384step1 = (fun i j => raw4384step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4384step1 raw4384step0; decide +kernel
      have hl : raw4384step1Labels = raw4384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4384step0 raw4384step0Labels permutation56 hz
    mixedMoment B raw4384step1 raw4384step1Labels = mixedMoment B raw4384step2 raw4384step2Labels := by
      have ha : raw4384step2 = (fun i j => raw4384step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4384step2 raw4384step1; decide +kernel
      have hl : raw4384step2Labels = raw4384step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4384step1 raw4384step1Labels permutation10 permutation3
    mixedMoment B raw4384step2 raw4384step2Labels = mixedMoment B raw4384step3 raw4384step3Labels := by
      have ha : raw4384step3 = raw4384step2 := by apply Matrix.ext; unfold raw4384step3 raw4384step2; decide +kernel
      have hl : raw4384step2Labels = labelEmbedding6 ∘ raw4384step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4384step2 raw4384step2Labels raw4384step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

def raw4385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4385step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4385step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4385step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4385 raw4385Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4385 raw4385Labels = mixedMoment B raw4385step0 raw4385step0Labels := by
      have hz : ∀ j, raw4385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4385step0 = (fun i j => raw4385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4385step0 raw4385; decide +kernel
      have hl : raw4385step0Labels = raw4385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4385 raw4385Labels permutation434 hz
    mixedMoment B raw4385step0 raw4385step0Labels = mixedMoment B raw4385step1 raw4385step1Labels := by
      have ha : raw4385step1 = (fun i j => raw4385step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4385step1 raw4385step0; decide +kernel
      have hl : raw4385step1Labels = raw4385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4385step0 raw4385step0Labels permutation145 permutation3
    mixedMoment B raw4385step1 raw4385step1Labels = mixedMoment B raw4385step2 raw4385step2Labels := by
      have ha : raw4385step2 = -raw4385step1 := by apply Matrix.ext; change ∀ i j, raw4385step2 i j = -(raw4385step1 i j); unfold raw4385step2 raw4385step1; decide +kernel
      have hl : raw4385step2Labels = raw4385step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4385step2 raw4385step2Labels = mixedMoment B raw4385step3 raw4385step3Labels := by
      have ha : raw4385step3 = raw4385step2 := by apply Matrix.ext; unfold raw4385step3 raw4385step2; decide +kernel
      have hl : raw4385step2Labels = labelEmbedding6 ∘ raw4385step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4385step2 raw4385step2Labels raw4385step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw4386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4386step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4386step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4386step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4386 raw4386Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4386 raw4386Labels = mixedMoment B raw4386step0 raw4386step0Labels := by
      have hz : ∀ j, raw4386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4386step0 = (fun i j => raw4386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4386step0 raw4386; decide +kernel
      have hl : raw4386step0Labels = raw4386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4386 raw4386Labels permutation265 hz
    mixedMoment B raw4386step0 raw4386step0Labels = mixedMoment B raw4386step1 raw4386step1Labels := by
      have ha : raw4386step1 = (fun i j => raw4386step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4386step1 raw4386step0; decide +kernel
      have hl : raw4386step1Labels = raw4386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4386step0 raw4386step0Labels permutation139 permutation3
    mixedMoment B raw4386step1 raw4386step1Labels = mixedMoment B raw4386step2 raw4386step2Labels := by
      have ha : raw4386step2 = -raw4386step1 := by apply Matrix.ext; change ∀ i j, raw4386step2 i j = -(raw4386step1 i j); unfold raw4386step2 raw4386step1; decide +kernel
      have hl : raw4386step2Labels = raw4386step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4386step2 raw4386step2Labels = mixedMoment B raw4386step3 raw4386step3Labels := by
      have ha : raw4386step3 = raw4386step2 := by apply Matrix.ext; unfold raw4386step3 raw4386step2; decide +kernel
      have hl : raw4386step2Labels = labelEmbedding6 ∘ raw4386step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4386step2 raw4386step2Labels raw4386step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw4387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4387step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4387step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4387step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4387step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4387 raw4387Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw4387 raw4387Labels = mixedMoment B raw4387step0 raw4387step0Labels := by
      have hz : ∀ j, raw4387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4387step0 = (fun i j => raw4387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4387step0 raw4387; decide +kernel
      have hl : raw4387step0Labels = raw4387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4387 raw4387Labels permutation434 hz
    mixedMoment B raw4387step0 raw4387step0Labels = mixedMoment B raw4387step1 raw4387step1Labels := by
      have hz : ∀ j, raw4387step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4387step1 = (fun i j => raw4387step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4387step1 raw4387step0; decide +kernel
      have hl : raw4387step1Labels = raw4387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4387step0 raw4387step0Labels permutation56 hz
    mixedMoment B raw4387step1 raw4387step1Labels = mixedMoment B raw4387step2 raw4387step2Labels := by
      have ha : raw4387step2 = (fun i j => raw4387step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4387step2 raw4387step1; decide +kernel
      have hl : raw4387step2Labels = raw4387step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4387step1 raw4387step1Labels permutation29 permutation3
    mixedMoment B raw4387step2 raw4387step2Labels = mixedMoment B raw4387step3 raw4387step3Labels := by
      have ha : raw4387step3 = -raw4387step2 := by apply Matrix.ext; change ∀ i j, raw4387step3 i j = -(raw4387step2 i j); unfold raw4387step3 raw4387step2; decide +kernel
      have hl : raw4387step3Labels = raw4387step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4387step3 raw4387step3Labels = mixedMoment B raw4387step4 raw4387step4Labels := by
      have ha : raw4387step4 = raw4387step3 := by apply Matrix.ext; unfold raw4387step4 raw4387step3; decide +kernel
      have hl : raw4387step3Labels = labelEmbedding6 ∘ raw4387step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4387step3 raw4387step3Labels raw4387step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

def raw4388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4388step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4388step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4388step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4388 raw4388Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw4388 raw4388Labels = mixedMoment B raw4388step0 raw4388step0Labels := by
      have hz : ∀ j, raw4388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4388step0 = (fun i j => raw4388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4388step0 raw4388; decide +kernel
      have hl : raw4388step0Labels = raw4388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4388 raw4388Labels permutation346 hz
    mixedMoment B raw4388step0 raw4388step0Labels = mixedMoment B raw4388step1 raw4388step1Labels := by
      have hz : ∀ j, raw4388step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4388step1 = (fun i j => raw4388step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4388step1 raw4388step0; decide +kernel
      have hl : raw4388step1Labels = raw4388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4388step0 raw4388step0Labels permutation56 hz
    mixedMoment B raw4388step1 raw4388step1Labels = mixedMoment B raw4388step2 raw4388step2Labels := by
      have ha : raw4388step2 = (fun i j => raw4388step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4388step2 raw4388step1; decide +kernel
      have hl : raw4388step2Labels = raw4388step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4388step1 raw4388step1Labels permutation10 permutation3
    mixedMoment B raw4388step2 raw4388step2Labels = mixedMoment B raw4388step3 raw4388step3Labels := by
      have ha : raw4388step3 = raw4388step2 := by apply Matrix.ext; unfold raw4388step3 raw4388step2; decide +kernel
      have hl : raw4388step2Labels = labelEmbedding6 ∘ raw4388step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4388step2 raw4388step2Labels raw4388step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

def raw4389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4389step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4389step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4389step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4389step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4389 raw4389Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4389 raw4389Labels = mixedMoment B raw4389step0 raw4389step0Labels := by
      have hz : ∀ j, raw4389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4389step0 = (fun i j => raw4389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4389step0 raw4389; decide +kernel
      have hl : raw4389step0Labels = raw4389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4389 raw4389Labels permutation346 hz
    mixedMoment B raw4389step0 raw4389step0Labels = mixedMoment B raw4389step1 raw4389step1Labels := by
      have ha : raw4389step1 = (fun i j => raw4389step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4389step1 raw4389step0; decide +kernel
      have hl : raw4389step1Labels = raw4389step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4389step0 raw4389step0Labels permutation145 permutation3
    mixedMoment B raw4389step1 raw4389step1Labels = mixedMoment B raw4389step2 raw4389step2Labels := by
      have ha : raw4389step2 = -raw4389step1 := by apply Matrix.ext; change ∀ i j, raw4389step2 i j = -(raw4389step1 i j); unfold raw4389step2 raw4389step1; decide +kernel
      have hl : raw4389step2Labels = raw4389step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4389step2 raw4389step2Labels = mixedMoment B raw4389step3 raw4389step3Labels := by
      have ha : raw4389step3 = raw4389step2 := by apply Matrix.ext; unfold raw4389step3 raw4389step2; decide +kernel
      have hl : raw4389step2Labels = labelEmbedding6 ∘ raw4389step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4389step2 raw4389step2Labels raw4389step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw4390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4390step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4390step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4390step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4390step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4390 raw4390Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4390 raw4390Labels = mixedMoment B raw4390step0 raw4390step0Labels := by
      have hz : ∀ j, raw4390 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4390step0 = (fun i j => raw4390 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4390step0 raw4390; decide +kernel
      have hl : raw4390step0Labels = raw4390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4390 raw4390Labels permutation265 hz
    mixedMoment B raw4390step0 raw4390step0Labels = mixedMoment B raw4390step1 raw4390step1Labels := by
      have ha : raw4390step1 = (fun i j => raw4390step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4390step1 raw4390step0; decide +kernel
      have hl : raw4390step1Labels = raw4390step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4390step0 raw4390step0Labels permutation145 permutation3
    mixedMoment B raw4390step1 raw4390step1Labels = mixedMoment B raw4390step2 raw4390step2Labels := by
      have ha : raw4390step2 = -raw4390step1 := by apply Matrix.ext; change ∀ i j, raw4390step2 i j = -(raw4390step1 i j); unfold raw4390step2 raw4390step1; decide +kernel
      have hl : raw4390step2Labels = raw4390step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4390step2 raw4390step2Labels = mixedMoment B raw4390step3 raw4390step3Labels := by
      have ha : raw4390step3 = raw4390step2 := by apply Matrix.ext; unfold raw4390step3 raw4390step2; decide +kernel
      have hl : raw4390step2Labels = labelEmbedding6 ∘ raw4390step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4390step2 raw4390step2Labels raw4390step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw4391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4391step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4391step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4391step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4391step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4391step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4391 raw4391Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw4391 raw4391Labels = mixedMoment B raw4391step0 raw4391step0Labels := by
      have hz : ∀ j, raw4391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4391step0 = (fun i j => raw4391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4391step0 raw4391; decide +kernel
      have hl : raw4391step0Labels = raw4391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4391 raw4391Labels permutation346 hz
    mixedMoment B raw4391step0 raw4391step0Labels = mixedMoment B raw4391step1 raw4391step1Labels := by
      have hz : ∀ j, raw4391step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4391step1 = (fun i j => raw4391step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4391step1 raw4391step0; decide +kernel
      have hl : raw4391step1Labels = raw4391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4391step0 raw4391step0Labels permutation56 hz
    mixedMoment B raw4391step1 raw4391step1Labels = mixedMoment B raw4391step2 raw4391step2Labels := by
      have ha : raw4391step2 = (fun i j => raw4391step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4391step2 raw4391step1; decide +kernel
      have hl : raw4391step2Labels = raw4391step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4391step1 raw4391step1Labels permutation29 permutation3
    mixedMoment B raw4391step2 raw4391step2Labels = mixedMoment B raw4391step3 raw4391step3Labels := by
      have ha : raw4391step3 = -raw4391step2 := by apply Matrix.ext; change ∀ i j, raw4391step3 i j = -(raw4391step2 i j); unfold raw4391step3 raw4391step2; decide +kernel
      have hl : raw4391step3Labels = raw4391step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4391step3 raw4391step3Labels = mixedMoment B raw4391step4 raw4391step4Labels := by
      have ha : raw4391step4 = raw4391step3 := by apply Matrix.ext; unfold raw4391step4 raw4391step3; decide +kernel
      have hl : raw4391step3Labels = labelEmbedding6 ∘ raw4391step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4391step3 raw4391step3Labels raw4391step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

def raw4392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4392step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw4392step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4392step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw4392step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4392step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw4392step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4392 raw4392Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw4392 raw4392Labels = mixedMoment B raw4392step0 raw4392step0Labels := by
      have hz : ∀ j, raw4392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4392step0 = (fun i j => raw4392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4392step0 raw4392; decide +kernel
      have hl : raw4392step0Labels = raw4392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4392 raw4392Labels permutation434 hz
    mixedMoment B raw4392step0 raw4392step0Labels = mixedMoment B raw4392step1 raw4392step1Labels := by
      have hz : ∀ j, raw4392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4392step1 = (fun i j => raw4392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4392step1 raw4392step0; decide +kernel
      have hl : raw4392step1Labels = raw4392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4392step0 raw4392step0Labels permutation80 hz
    mixedMoment B raw4392step1 raw4392step1Labels = mixedMoment B raw4392step2 raw4392step2Labels := by
      have hz : ∀ j, raw4392step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4392step2 = (fun i j => raw4392step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4392step2 raw4392step1; decide +kernel
      have hl : raw4392step2Labels = raw4392step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4392step1 raw4392step1Labels permutation14 hz
    mixedMoment B raw4392step2 raw4392step2Labels = mixedMoment B raw4392step3 raw4392step3Labels := by
      have ha : raw4392step3 = (fun i j => raw4392step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4392step3 raw4392step2; decide +kernel
      have hl : raw4392step3Labels = raw4392step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4392step2 raw4392step2Labels permutation2 permutation3
    mixedMoment B raw4392step3 raw4392step3Labels = mixedMoment B raw4392step4 raw4392step4Labels := by
      have ha : raw4392step4 = raw4392step3 := by apply Matrix.ext; unfold raw4392step4 raw4392step3; decide +kernel
      have hl : raw4392step3Labels = labelEmbedding6 ∘ raw4392step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4392step3 raw4392step3Labels raw4392step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

def raw4393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4393step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4393step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4393step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4393step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4393step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4393 raw4393Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw4393 raw4393Labels = mixedMoment B raw4393step0 raw4393step0Labels := by
      have hz : ∀ j, raw4393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4393step0 = (fun i j => raw4393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4393step0 raw4393; decide +kernel
      have hl : raw4393step0Labels = raw4393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4393 raw4393Labels permutation434 hz
    mixedMoment B raw4393step0 raw4393step0Labels = mixedMoment B raw4393step1 raw4393step1Labels := by
      have hz : ∀ j, raw4393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4393step1 = (fun i j => raw4393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4393step1 raw4393step0; decide +kernel
      have hl : raw4393step1Labels = raw4393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4393step0 raw4393step0Labels permutation80 hz
    mixedMoment B raw4393step1 raw4393step1Labels = mixedMoment B raw4393step2 raw4393step2Labels := by
      have ha : raw4393step2 = (fun i j => raw4393step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4393step2 raw4393step1; decide +kernel
      have hl : raw4393step2Labels = raw4393step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4393step1 raw4393step1Labels permutation31 permutation3
    mixedMoment B raw4393step2 raw4393step2Labels = mixedMoment B raw4393step3 raw4393step3Labels := by
      have ha : raw4393step3 = -raw4393step2 := by apply Matrix.ext; change ∀ i j, raw4393step3 i j = -(raw4393step2 i j); unfold raw4393step3 raw4393step2; decide +kernel
      have hl : raw4393step3Labels = raw4393step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4393step3 raw4393step3Labels = mixedMoment B raw4393step4 raw4393step4Labels := by
      have ha : raw4393step4 = raw4393step3 := by apply Matrix.ext; unfold raw4393step4 raw4393step3; decide +kernel
      have hl : raw4393step3Labels = labelEmbedding6 ∘ raw4393step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4393step3 raw4393step3Labels raw4393step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw4394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4394step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4394step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4394step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4394step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4394step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4394 raw4394Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw4394 raw4394Labels = mixedMoment B raw4394step0 raw4394step0Labels := by
      have hz : ∀ j, raw4394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4394step0 = (fun i j => raw4394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4394step0 raw4394; decide +kernel
      have hl : raw4394step0Labels = raw4394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4394 raw4394Labels permutation434 hz
    mixedMoment B raw4394step0 raw4394step0Labels = mixedMoment B raw4394step1 raw4394step1Labels := by
      have hz : ∀ j, raw4394step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4394step1 = (fun i j => raw4394step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4394step1 raw4394step0; decide +kernel
      have hl : raw4394step1Labels = raw4394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4394step0 raw4394step0Labels permutation56 hz
    mixedMoment B raw4394step1 raw4394step1Labels = mixedMoment B raw4394step2 raw4394step2Labels := by
      have ha : raw4394step2 = (fun i j => raw4394step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4394step2 raw4394step1; decide +kernel
      have hl : raw4394step2Labels = raw4394step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4394step1 raw4394step1Labels permutation31 permutation3
    mixedMoment B raw4394step2 raw4394step2Labels = mixedMoment B raw4394step3 raw4394step3Labels := by
      have ha : raw4394step3 = -raw4394step2 := by apply Matrix.ext; change ∀ i j, raw4394step3 i j = -(raw4394step2 i j); unfold raw4394step3 raw4394step2; decide +kernel
      have hl : raw4394step3Labels = raw4394step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4394step3 raw4394step3Labels = mixedMoment B raw4394step4 raw4394step4Labels := by
      have ha : raw4394step4 = raw4394step3 := by apply Matrix.ext; unfold raw4394step4 raw4394step3; decide +kernel
      have hl : raw4394step3Labels = labelEmbedding6 ∘ raw4394step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4394step3 raw4394step3Labels raw4394step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw4395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4395step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4395step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4395step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4395step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4395 raw4395Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw4395 raw4395Labels = mixedMoment B raw4395step0 raw4395step0Labels := by
      have hz : ∀ j, raw4395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4395step0 = (fun i j => raw4395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4395step0 raw4395; decide +kernel
      have hl : raw4395step0Labels = raw4395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4395 raw4395Labels permutation346 hz
    mixedMoment B raw4395step0 raw4395step0Labels = mixedMoment B raw4395step1 raw4395step1Labels := by
      have hz : ∀ j, raw4395step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4395step1 = (fun i j => raw4395step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4395step1 raw4395step0; decide +kernel
      have hl : raw4395step1Labels = raw4395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4395step0 raw4395step0Labels permutation56 hz
    mixedMoment B raw4395step1 raw4395step1Labels = mixedMoment B raw4395step2 raw4395step2Labels := by
      have ha : raw4395step2 = (fun i j => raw4395step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4395step2 raw4395step1; decide +kernel
      have hl : raw4395step2Labels = raw4395step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4395step1 raw4395step1Labels permutation31 permutation3
    mixedMoment B raw4395step2 raw4395step2Labels = mixedMoment B raw4395step3 raw4395step3Labels := by
      have ha : raw4395step3 = -raw4395step2 := by apply Matrix.ext; change ∀ i j, raw4395step3 i j = -(raw4395step2 i j); unfold raw4395step3 raw4395step2; decide +kernel
      have hl : raw4395step3Labels = raw4395step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4395step3 raw4395step3Labels = mixedMoment B raw4395step4 raw4395step4Labels := by
      have ha : raw4395step4 = raw4395step3 := by apply Matrix.ext; unfold raw4395step4 raw4395step3; decide +kernel
      have hl : raw4395step3Labels = labelEmbedding6 ∘ raw4395step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4395step3 raw4395step3Labels raw4395step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw4396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4396step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw4396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4396step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw4396step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4396step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw4396step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4396step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw4396step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4396 raw4396Labels = mixedMoment B node4280 node4280Labels := by
  calc
    mixedMoment B raw4396 raw4396Labels = mixedMoment B raw4396step0 raw4396step0Labels := by
      have hz : ∀ j, raw4396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4396step0 = (fun i j => raw4396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4396step0 raw4396; decide +kernel
      have hl : raw4396step0Labels = raw4396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4396 raw4396Labels permutation434 hz
    mixedMoment B raw4396step0 raw4396step0Labels = mixedMoment B raw4396step1 raw4396step1Labels := by
      have hz : ∀ j, raw4396step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4396step1 = (fun i j => raw4396step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4396step1 raw4396step0; decide +kernel
      have hl : raw4396step1Labels = raw4396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4396step0 raw4396step0Labels permutation80 hz
    mixedMoment B raw4396step1 raw4396step1Labels = mixedMoment B raw4396step2 raw4396step2Labels := by
      have hz : ∀ j, raw4396step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4396step2 = (fun i j => raw4396step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4396step2 raw4396step1; decide +kernel
      have hl : raw4396step2Labels = raw4396step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4396step1 raw4396step1Labels permutation14 hz
    mixedMoment B raw4396step2 raw4396step2Labels = mixedMoment B raw4396step3 raw4396step3Labels := by
      have ha : raw4396step3 = (fun i j => raw4396step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4396step3 raw4396step2; decide +kernel
      have hl : raw4396step3Labels = raw4396step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4396step2 raw4396step2Labels permutation7 permutation3
    mixedMoment B raw4396step3 raw4396step3Labels = mixedMoment B raw4396step4 raw4396step4Labels := by
      have ha : raw4396step4 = -raw4396step3 := by apply Matrix.ext; change ∀ i j, raw4396step4 i j = -(raw4396step3 i j); unfold raw4396step4 raw4396step3; decide +kernel
      have hl : raw4396step4Labels = raw4396step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4396step4 raw4396step4Labels = mixedMoment B raw4396step5 raw4396step5Labels := by
      have ha : raw4396step5 = raw4396step4 := by apply Matrix.ext; unfold raw4396step5 raw4396step4; decide +kernel
      have hl : raw4396step4Labels = labelEmbedding6 ∘ raw4396step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4396step4 raw4396step4Labels raw4396step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4280 node4280Labels := by rfl

def raw4397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4397step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4397step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4397step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4397step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4397step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4397 raw4397Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw4397 raw4397Labels = mixedMoment B raw4397step0 raw4397step0Labels := by
      have hz : ∀ j, raw4397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4397step0 = (fun i j => raw4397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4397step0 raw4397; decide +kernel
      have hl : raw4397step0Labels = raw4397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4397 raw4397Labels permutation434 hz
    mixedMoment B raw4397step0 raw4397step0Labels = mixedMoment B raw4397step1 raw4397step1Labels := by
      have hz : ∀ j, raw4397step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4397step1 = (fun i j => raw4397step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4397step1 raw4397step0; decide +kernel
      have hl : raw4397step1Labels = raw4397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4397step0 raw4397step0Labels permutation80 hz
    mixedMoment B raw4397step1 raw4397step1Labels = mixedMoment B raw4397step2 raw4397step2Labels := by
      have ha : raw4397step2 = (fun i j => raw4397step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4397step2 raw4397step1; decide +kernel
      have hl : raw4397step2Labels = raw4397step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4397step1 raw4397step1Labels permutation31 permutation3
    mixedMoment B raw4397step2 raw4397step2Labels = mixedMoment B raw4397step3 raw4397step3Labels := by
      have ha : raw4397step3 = -raw4397step2 := by apply Matrix.ext; change ∀ i j, raw4397step3 i j = -(raw4397step2 i j); unfold raw4397step3 raw4397step2; decide +kernel
      have hl : raw4397step3Labels = raw4397step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4397step3 raw4397step3Labels = mixedMoment B raw4397step4 raw4397step4Labels := by
      have ha : raw4397step4 = raw4397step3 := by apply Matrix.ext; unfold raw4397step4 raw4397step3; decide +kernel
      have hl : raw4397step3Labels = labelEmbedding6 ∘ raw4397step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4397step3 raw4397step3Labels raw4397step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

def raw4398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4398step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4398step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4398step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4398step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4398step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4398step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4398step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4398 raw4398Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw4398 raw4398Labels = mixedMoment B raw4398step0 raw4398step0Labels := by
      have hz : ∀ j, raw4398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4398step0 = (fun i j => raw4398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4398step0 raw4398; decide +kernel
      have hl : raw4398step0Labels = raw4398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4398 raw4398Labels permutation434 hz
    mixedMoment B raw4398step0 raw4398step0Labels = mixedMoment B raw4398step1 raw4398step1Labels := by
      have hz : ∀ j, raw4398step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4398step1 = (fun i j => raw4398step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4398step1 raw4398step0; decide +kernel
      have hl : raw4398step1Labels = raw4398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4398step0 raw4398step0Labels permutation56 hz
    mixedMoment B raw4398step1 raw4398step1Labels = mixedMoment B raw4398step2 raw4398step2Labels := by
      have ha : raw4398step2 = (fun i j => raw4398step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4398step2 raw4398step1; decide +kernel
      have hl : raw4398step2Labels = raw4398step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4398step1 raw4398step1Labels permutation31 permutation3
    mixedMoment B raw4398step2 raw4398step2Labels = mixedMoment B raw4398step3 raw4398step3Labels := by
      have ha : raw4398step3 = -raw4398step2 := by apply Matrix.ext; change ∀ i j, raw4398step3 i j = -(raw4398step2 i j); unfold raw4398step3 raw4398step2; decide +kernel
      have hl : raw4398step3Labels = raw4398step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4398step3 raw4398step3Labels = mixedMoment B raw4398step4 raw4398step4Labels := by
      have ha : raw4398step4 = raw4398step3 := by apply Matrix.ext; unfold raw4398step4 raw4398step3; decide +kernel
      have hl : raw4398step3Labels = labelEmbedding6 ∘ raw4398step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4398step3 raw4398step3Labels raw4398step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

def raw4399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4399step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4399step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4399step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4399step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4399step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4399 raw4399Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw4399 raw4399Labels = mixedMoment B raw4399step0 raw4399step0Labels := by
      have hz : ∀ j, raw4399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4399step0 = (fun i j => raw4399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4399step0 raw4399; decide +kernel
      have hl : raw4399step0Labels = raw4399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4399 raw4399Labels permutation346 hz
    mixedMoment B raw4399step0 raw4399step0Labels = mixedMoment B raw4399step1 raw4399step1Labels := by
      have hz : ∀ j, raw4399step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4399step1 = (fun i j => raw4399step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4399step1 raw4399step0; decide +kernel
      have hl : raw4399step1Labels = raw4399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4399step0 raw4399step0Labels permutation56 hz
    mixedMoment B raw4399step1 raw4399step1Labels = mixedMoment B raw4399step2 raw4399step2Labels := by
      have ha : raw4399step2 = (fun i j => raw4399step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4399step2 raw4399step1; decide +kernel
      have hl : raw4399step2Labels = raw4399step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4399step1 raw4399step1Labels permutation31 permutation3
    mixedMoment B raw4399step2 raw4399step2Labels = mixedMoment B raw4399step3 raw4399step3Labels := by
      have ha : raw4399step3 = -raw4399step2 := by apply Matrix.ext; change ∀ i j, raw4399step3 i j = -(raw4399step2 i j); unfold raw4399step3 raw4399step2; decide +kernel
      have hl : raw4399step3Labels = raw4399step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4399step3 raw4399step3Labels = mixedMoment B raw4399step4 raw4399step4Labels := by
      have ha : raw4399step4 = raw4399step3 := by apply Matrix.ext; unfold raw4399step4 raw4399step3; decide +kernel
      have hl : raw4399step3Labels = labelEmbedding6 ∘ raw4399step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4399step3 raw4399step3Labels raw4399step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

def raw4400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4400step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![4, -4, 0]]
def raw4400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4400step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw4400step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4400step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw4400step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4400step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw4400step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4400 raw4400Labels = mixedMoment B node4285 node4285Labels := by
  calc
    mixedMoment B raw4400 raw4400Labels = mixedMoment B raw4400step0 raw4400step0Labels := by
      have hz : ∀ j, raw4400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4400step0 = (fun i j => raw4400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4400step0 raw4400; decide +kernel
      have hl : raw4400step0Labels = raw4400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4400 raw4400Labels permutation434 hz
    mixedMoment B raw4400step0 raw4400step0Labels = mixedMoment B raw4400step1 raw4400step1Labels := by
      have hz : ∀ j, raw4400step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4400step1 = (fun i j => raw4400step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4400step1 raw4400step0; decide +kernel
      have hl : raw4400step1Labels = raw4400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4400step0 raw4400step0Labels permutation80 hz
    mixedMoment B raw4400step1 raw4400step1Labels = mixedMoment B raw4400step2 raw4400step2Labels := by
      have hz : ∀ j, raw4400step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4400step2 = (fun i j => raw4400step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4400step2 raw4400step1; decide +kernel
      have hl : raw4400step2Labels = raw4400step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4400step1 raw4400step1Labels permutation14 hz
    mixedMoment B raw4400step2 raw4400step2Labels = mixedMoment B raw4400step3 raw4400step3Labels := by
      have ha : raw4400step3 = (fun i j => raw4400step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4400step3 raw4400step2; decide +kernel
      have hl : raw4400step3Labels = raw4400step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4400step2 raw4400step2Labels permutation7 permutation3
    mixedMoment B raw4400step3 raw4400step3Labels = mixedMoment B raw4400step4 raw4400step4Labels := by
      have ha : raw4400step4 = -raw4400step3 := by apply Matrix.ext; change ∀ i j, raw4400step4 i j = -(raw4400step3 i j); unfold raw4400step4 raw4400step3; decide +kernel
      have hl : raw4400step4Labels = raw4400step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4400step4 raw4400step4Labels = mixedMoment B raw4400step5 raw4400step5Labels := by
      have ha : raw4400step5 = raw4400step4 := by apply Matrix.ext; unfold raw4400step5 raw4400step4; decide +kernel
      have hl : raw4400step4Labels = labelEmbedding6 ∘ raw4400step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4400step4 raw4400step4Labels raw4400step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4285 node4285Labels := by rfl

def raw4401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4401step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw4401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4401step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw4401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4401 raw4401Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw4401 raw4401Labels = mixedMoment B raw4401step0 raw4401step0Labels := by
      have hz : ∀ j, raw4401 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4401step0 = (fun i j => raw4401 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4401step0 raw4401; decide +kernel
      have hl : raw4401step0Labels = raw4401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4401 raw4401Labels permutation434 hz
    mixedMoment B raw4401step0 raw4401step0Labels = mixedMoment B raw4401step1 raw4401step1Labels := by
      have hz : ∀ j, raw4401step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4401step1 = (fun i j => raw4401step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4401step1 raw4401step0; decide +kernel
      have hl : raw4401step1Labels = raw4401step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4401step0 raw4401step0Labels permutation80 hz
    mixedMoment B raw4401step1 raw4401step1Labels = mixedMoment B raw4401step2 raw4401step2Labels := by
      have ha : raw4401step2 = (fun i j => raw4401step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4401step2 raw4401step1; decide +kernel
      have hl : raw4401step2Labels = raw4401step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4401step1 raw4401step1Labels permutation31 permutation3
    mixedMoment B raw4401step2 raw4401step2Labels = mixedMoment B raw4401step3 raw4401step3Labels := by
      have ha : raw4401step3 = -raw4401step2 := by apply Matrix.ext; change ∀ i j, raw4401step3 i j = -(raw4401step2 i j); unfold raw4401step3 raw4401step2; decide +kernel
      have hl : raw4401step3Labels = raw4401step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw4402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4402step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4402step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw4402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4402step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw4402step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4402 raw4402Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw4402 raw4402Labels = mixedMoment B raw4402step0 raw4402step0Labels := by
      have hz : ∀ j, raw4402 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4402step0 = (fun i j => raw4402 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4402step0 raw4402; decide +kernel
      have hl : raw4402step0Labels = raw4402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4402 raw4402Labels permutation434 hz
    mixedMoment B raw4402step0 raw4402step0Labels = mixedMoment B raw4402step1 raw4402step1Labels := by
      have hz : ∀ j, raw4402step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4402step1 = (fun i j => raw4402step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4402step1 raw4402step0; decide +kernel
      have hl : raw4402step1Labels = raw4402step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4402step0 raw4402step0Labels permutation56 hz
    mixedMoment B raw4402step1 raw4402step1Labels = mixedMoment B raw4402step2 raw4402step2Labels := by
      have ha : raw4402step2 = (fun i j => raw4402step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4402step2 raw4402step1; decide +kernel
      have hl : raw4402step2Labels = raw4402step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4402step1 raw4402step1Labels permutation31 permutation3
    mixedMoment B raw4402step2 raw4402step2Labels = mixedMoment B raw4402step3 raw4402step3Labels := by
      have ha : raw4402step3 = -raw4402step2 := by apply Matrix.ext; change ∀ i j, raw4402step3 i j = -(raw4402step2 i j); unfold raw4402step3 raw4402step2; decide +kernel
      have hl : raw4402step3Labels = raw4402step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw4403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4403step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4403step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw4403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4403step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw4403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4403 raw4403Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw4403 raw4403Labels = mixedMoment B raw4403step0 raw4403step0Labels := by
      have hz : ∀ j, raw4403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4403step0 = (fun i j => raw4403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4403step0 raw4403; decide +kernel
      have hl : raw4403step0Labels = raw4403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4403 raw4403Labels permutation346 hz
    mixedMoment B raw4403step0 raw4403step0Labels = mixedMoment B raw4403step1 raw4403step1Labels := by
      have hz : ∀ j, raw4403step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4403step1 = (fun i j => raw4403step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4403step1 raw4403step0; decide +kernel
      have hl : raw4403step1Labels = raw4403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4403step0 raw4403step0Labels permutation56 hz
    mixedMoment B raw4403step1 raw4403step1Labels = mixedMoment B raw4403step2 raw4403step2Labels := by
      have ha : raw4403step2 = (fun i j => raw4403step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4403step2 raw4403step1; decide +kernel
      have hl : raw4403step2Labels = raw4403step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4403step1 raw4403step1Labels permutation31 permutation3
    mixedMoment B raw4403step2 raw4403step2Labels = mixedMoment B raw4403step3 raw4403step3Labels := by
      have ha : raw4403step3 = -raw4403step2 := by apply Matrix.ext; change ∀ i j, raw4403step3 i j = -(raw4403step2 i j); unfold raw4403step3 raw4403step2; decide +kernel
      have hl : raw4403step3Labels = raw4403step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw4404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4404step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4404step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw4404step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4404step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw4404step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4404step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw4404step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4404 raw4404Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw4404 raw4404Labels = mixedMoment B raw4404step0 raw4404step0Labels := by
      have hz : ∀ j, raw4404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4404step0 = (fun i j => raw4404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4404step0 raw4404; decide +kernel
      have hl : raw4404step0Labels = raw4404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4404 raw4404Labels permutation434 hz
    mixedMoment B raw4404step0 raw4404step0Labels = mixedMoment B raw4404step1 raw4404step1Labels := by
      have hz : ∀ j, raw4404step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4404step1 = (fun i j => raw4404step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4404step1 raw4404step0; decide +kernel
      have hl : raw4404step1Labels = raw4404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4404step0 raw4404step0Labels permutation80 hz
    mixedMoment B raw4404step1 raw4404step1Labels = mixedMoment B raw4404step2 raw4404step2Labels := by
      have hz : ∀ j, raw4404step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4404step2 = (fun i j => raw4404step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4404step2 raw4404step1; decide +kernel
      have hl : raw4404step2Labels = raw4404step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4404step1 raw4404step1Labels permutation14 hz
    mixedMoment B raw4404step2 raw4404step2Labels = mixedMoment B raw4404step3 raw4404step3Labels := by
      have ha : raw4404step3 = (fun i j => raw4404step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4404step3 raw4404step2; decide +kernel
      have hl : raw4404step3Labels = raw4404step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4404step2 raw4404step2Labels permutation7 permutation3
    mixedMoment B raw4404step3 raw4404step3Labels = mixedMoment B raw4404step4 raw4404step4Labels := by
      have ha : raw4404step4 = -raw4404step3 := by apply Matrix.ext; change ∀ i j, raw4404step4 i j = -(raw4404step3 i j); unfold raw4404step4 raw4404step3; decide +kernel
      have hl : raw4404step4Labels = raw4404step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw4405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4405step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4405step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4405step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw4405step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4405step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw4405step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4405step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw4405step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4405 raw4405Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw4405 raw4405Labels = mixedMoment B raw4405step0 raw4405step0Labels := by
      have hz : ∀ j, raw4405 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4405step0 = (fun i j => raw4405 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4405step0 raw4405; decide +kernel
      have hl : raw4405step0Labels = raw4405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4405 raw4405Labels permutation434 hz
    mixedMoment B raw4405step0 raw4405step0Labels = mixedMoment B raw4405step1 raw4405step1Labels := by
      have hz : ∀ j, raw4405step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4405step1 = (fun i j => raw4405step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4405step1 raw4405step0; decide +kernel
      have hl : raw4405step1Labels = raw4405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4405step0 raw4405step0Labels permutation80 hz
    mixedMoment B raw4405step1 raw4405step1Labels = mixedMoment B raw4405step2 raw4405step2Labels := by
      have hz : ∀ j, raw4405step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4405step2 = (fun i j => raw4405step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4405step2 raw4405step1; decide +kernel
      have hl : raw4405step2Labels = raw4405step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4405step1 raw4405step1Labels permutation14 hz
    mixedMoment B raw4405step2 raw4405step2Labels = mixedMoment B raw4405step3 raw4405step3Labels := by
      have ha : raw4405step3 = (fun i j => raw4405step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4405step3 raw4405step2; decide +kernel
      have hl : raw4405step3Labels = raw4405step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4405step2 raw4405step2Labels permutation7 permutation3
    mixedMoment B raw4405step3 raw4405step3Labels = mixedMoment B raw4405step4 raw4405step4Labels := by
      have ha : raw4405step4 = -raw4405step3 := by apply Matrix.ext; change ∀ i j, raw4405step4 i j = -(raw4405step3 i j); unfold raw4405step4 raw4405step3; decide +kernel
      have hl : raw4405step4Labels = raw4405step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3916 node3916Labels := by rfl

def raw4406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4406step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4406 raw4406Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw4406 raw4406Labels = mixedMoment B raw4406step0 raw4406step0Labels := by
      have hz : ∀ j, raw4406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4406step0 = (fun i j => raw4406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4406step0 raw4406; decide +kernel
      have hl : raw4406step0Labels = raw4406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4406 raw4406Labels permutation434 hz
    mixedMoment B raw4406step0 raw4406step0Labels = mixedMoment B raw4406step1 raw4406step1Labels := by
      have hz : ∀ j, raw4406step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4406step1 = (fun i j => raw4406step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4406step1 raw4406step0; decide +kernel
      have hl : raw4406step1Labels = raw4406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4406step0 raw4406step0Labels permutation80 hz
    mixedMoment B raw4406step1 raw4406step1Labels = mixedMoment B raw4406step2 raw4406step2Labels := by
      have ha : raw4406step2 = (fun i j => raw4406step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4406step2 raw4406step1; decide +kernel
      have hl : raw4406step2Labels = raw4406step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4406step1 raw4406step1Labels permutation10 permutation3
    _ = mixedMoment B node1190 node1190Labels := by rfl

def raw4407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4407 raw4407Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4407 raw4407Labels = mixedMoment B raw4407step0 raw4407step0Labels := by
      have hz : ∀ j, raw4407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4407step0 = (fun i j => raw4407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4407step0 raw4407; decide +kernel
      have hl : raw4407step0Labels = raw4407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4407 raw4407Labels permutation434 hz
    mixedMoment B raw4407step0 raw4407step0Labels = mixedMoment B raw4407step1 raw4407step1Labels := by
      have ha : raw4407step1 = (fun i j => raw4407step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4407step1 raw4407step0; decide +kernel
      have hl : raw4407step1Labels = raw4407step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4407step0 raw4407step0Labels permutation139 permutation3
    mixedMoment B raw4407step1 raw4407step1Labels = mixedMoment B raw4407step2 raw4407step2Labels := by
      have ha : raw4407step2 = -raw4407step1 := by apply Matrix.ext; change ∀ i j, raw4407step2 i j = -(raw4407step1 i j); unfold raw4407step2 raw4407step1; decide +kernel
      have hl : raw4407step2Labels = raw4407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw4408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4408 raw4408Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4408 raw4408Labels = mixedMoment B raw4408step0 raw4408step0Labels := by
      have hz : ∀ j, raw4408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4408step0 = (fun i j => raw4408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4408step0 raw4408; decide +kernel
      have hl : raw4408step0Labels = raw4408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4408 raw4408Labels permutation346 hz
    mixedMoment B raw4408step0 raw4408step0Labels = mixedMoment B raw4408step1 raw4408step1Labels := by
      have ha : raw4408step1 = (fun i j => raw4408step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4408step1 raw4408step0; decide +kernel
      have hl : raw4408step1Labels = raw4408step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4408step0 raw4408step0Labels permutation139 permutation3
    mixedMoment B raw4408step1 raw4408step1Labels = mixedMoment B raw4408step2 raw4408step2Labels := by
      have ha : raw4408step2 = -raw4408step1 := by apply Matrix.ext; change ∀ i j, raw4408step2 i j = -(raw4408step1 i j); unfold raw4408step2 raw4408step1; decide +kernel
      have hl : raw4408step2Labels = raw4408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw4409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4409step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4409step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4409step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4409 raw4409Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw4409 raw4409Labels = mixedMoment B raw4409step0 raw4409step0Labels := by
      have hz : ∀ j, raw4409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4409step0 = (fun i j => raw4409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4409step0 raw4409; decide +kernel
      have hl : raw4409step0Labels = raw4409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4409 raw4409Labels permutation434 hz
    mixedMoment B raw4409step0 raw4409step0Labels = mixedMoment B raw4409step1 raw4409step1Labels := by
      have hz : ∀ j, raw4409step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4409step1 = (fun i j => raw4409step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4409step1 raw4409step0; decide +kernel
      have hl : raw4409step1Labels = raw4409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4409step0 raw4409step0Labels permutation80 hz
    mixedMoment B raw4409step1 raw4409step1Labels = mixedMoment B raw4409step2 raw4409step2Labels := by
      have ha : raw4409step2 = (fun i j => raw4409step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4409step2 raw4409step1; decide +kernel
      have hl : raw4409step2Labels = raw4409step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4409step1 raw4409step1Labels permutation29 permutation3
    mixedMoment B raw4409step2 raw4409step2Labels = mixedMoment B raw4409step3 raw4409step3Labels := by
      have ha : raw4409step3 = -raw4409step2 := by apply Matrix.ext; change ∀ i j, raw4409step3 i j = -(raw4409step2 i j); unfold raw4409step3 raw4409step2; decide +kernel
      have hl : raw4409step3Labels = raw4409step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1951 node1951Labels := by rfl

def raw4410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4410step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4410 raw4410Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw4410 raw4410Labels = mixedMoment B raw4410step0 raw4410step0Labels := by
      have hz : ∀ j, raw4410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4410step0 = (fun i j => raw4410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4410step0 raw4410; decide +kernel
      have hl : raw4410step0Labels = raw4410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4410 raw4410Labels permutation434 hz
    mixedMoment B raw4410step0 raw4410step0Labels = mixedMoment B raw4410step1 raw4410step1Labels := by
      have hz : ∀ j, raw4410step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4410step1 = (fun i j => raw4410step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4410step1 raw4410step0; decide +kernel
      have hl : raw4410step1Labels = raw4410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4410step0 raw4410step0Labels permutation80 hz
    mixedMoment B raw4410step1 raw4410step1Labels = mixedMoment B raw4410step2 raw4410step2Labels := by
      have ha : raw4410step2 = (fun i j => raw4410step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4410step2 raw4410step1; decide +kernel
      have hl : raw4410step2Labels = raw4410step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4410step1 raw4410step1Labels permutation10 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw4411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4411step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4411 raw4411Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw4411 raw4411Labels = mixedMoment B raw4411step0 raw4411step0Labels := by
      have hz : ∀ j, raw4411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4411step0 = (fun i j => raw4411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4411step0 raw4411; decide +kernel
      have hl : raw4411step0Labels = raw4411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4411 raw4411Labels permutation434 hz
    mixedMoment B raw4411step0 raw4411step0Labels = mixedMoment B raw4411step1 raw4411step1Labels := by
      have hz : ∀ j, raw4411step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4411step1 = (fun i j => raw4411step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4411step1 raw4411step0; decide +kernel
      have hl : raw4411step1Labels = raw4411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4411step0 raw4411step0Labels permutation56 hz
    mixedMoment B raw4411step1 raw4411step1Labels = mixedMoment B raw4411step2 raw4411step2Labels := by
      have ha : raw4411step2 = (fun i j => raw4411step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4411step2 raw4411step1; decide +kernel
      have hl : raw4411step2Labels = raw4411step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4411step1 raw4411step1Labels permutation10 permutation3
    _ = mixedMoment B node1190 node1190Labels := by rfl

def raw4412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4412step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4412 raw4412Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4412 raw4412Labels = mixedMoment B raw4412step0 raw4412step0Labels := by
      have hz : ∀ j, raw4412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4412step0 = (fun i j => raw4412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4412step0 raw4412; decide +kernel
      have hl : raw4412step0Labels = raw4412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4412 raw4412Labels permutation434 hz
    mixedMoment B raw4412step0 raw4412step0Labels = mixedMoment B raw4412step1 raw4412step1Labels := by
      have ha : raw4412step1 = (fun i j => raw4412step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4412step1 raw4412step0; decide +kernel
      have hl : raw4412step1Labels = raw4412step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4412step0 raw4412step0Labels permutation145 permutation3
    mixedMoment B raw4412step1 raw4412step1Labels = mixedMoment B raw4412step2 raw4412step2Labels := by
      have ha : raw4412step2 = -raw4412step1 := by apply Matrix.ext; change ∀ i j, raw4412step2 i j = -(raw4412step1 i j); unfold raw4412step2 raw4412step1; decide +kernel
      have hl : raw4412step2Labels = raw4412step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw4413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4413 raw4413Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4413 raw4413Labels = mixedMoment B raw4413step0 raw4413step0Labels := by
      have hz : ∀ j, raw4413 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4413step0 = (fun i j => raw4413 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4413step0 raw4413; decide +kernel
      have hl : raw4413step0Labels = raw4413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4413 raw4413Labels permutation265 hz
    mixedMoment B raw4413step0 raw4413step0Labels = mixedMoment B raw4413step1 raw4413step1Labels := by
      have ha : raw4413step1 = (fun i j => raw4413step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4413step1 raw4413step0; decide +kernel
      have hl : raw4413step1Labels = raw4413step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4413step0 raw4413step0Labels permutation139 permutation3
    mixedMoment B raw4413step1 raw4413step1Labels = mixedMoment B raw4413step2 raw4413step2Labels := by
      have ha : raw4413step2 = -raw4413step1 := by apply Matrix.ext; change ∀ i j, raw4413step2 i j = -(raw4413step1 i j); unfold raw4413step2 raw4413step1; decide +kernel
      have hl : raw4413step2Labels = raw4413step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw4414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4414step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4414step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4414step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4414 raw4414Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw4414 raw4414Labels = mixedMoment B raw4414step0 raw4414step0Labels := by
      have hz : ∀ j, raw4414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4414step0 = (fun i j => raw4414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4414step0 raw4414; decide +kernel
      have hl : raw4414step0Labels = raw4414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4414 raw4414Labels permutation434 hz
    mixedMoment B raw4414step0 raw4414step0Labels = mixedMoment B raw4414step1 raw4414step1Labels := by
      have hz : ∀ j, raw4414step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4414step1 = (fun i j => raw4414step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4414step1 raw4414step0; decide +kernel
      have hl : raw4414step1Labels = raw4414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4414step0 raw4414step0Labels permutation56 hz
    mixedMoment B raw4414step1 raw4414step1Labels = mixedMoment B raw4414step2 raw4414step2Labels := by
      have ha : raw4414step2 = (fun i j => raw4414step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4414step2 raw4414step1; decide +kernel
      have hl : raw4414step2Labels = raw4414step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4414step1 raw4414step1Labels permutation29 permutation3
    mixedMoment B raw4414step2 raw4414step2Labels = mixedMoment B raw4414step3 raw4414step3Labels := by
      have ha : raw4414step3 = -raw4414step2 := by apply Matrix.ext; change ∀ i j, raw4414step3 i j = -(raw4414step2 i j); unfold raw4414step3 raw4414step2; decide +kernel
      have hl : raw4414step3Labels = raw4414step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1951 node1951Labels := by rfl

def raw4415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4415step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4415 raw4415Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw4415 raw4415Labels = mixedMoment B raw4415step0 raw4415step0Labels := by
      have hz : ∀ j, raw4415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4415step0 = (fun i j => raw4415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4415step0 raw4415; decide +kernel
      have hl : raw4415step0Labels = raw4415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4415 raw4415Labels permutation434 hz
    mixedMoment B raw4415step0 raw4415step0Labels = mixedMoment B raw4415step1 raw4415step1Labels := by
      have hz : ∀ j, raw4415step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4415step1 = (fun i j => raw4415step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4415step1 raw4415step0; decide +kernel
      have hl : raw4415step1Labels = raw4415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4415step0 raw4415step0Labels permutation56 hz
    mixedMoment B raw4415step1 raw4415step1Labels = mixedMoment B raw4415step2 raw4415step2Labels := by
      have ha : raw4415step2 = (fun i j => raw4415step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4415step2 raw4415step1; decide +kernel
      have hl : raw4415step2Labels = raw4415step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4415step1 raw4415step1Labels permutation10 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw4416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4416step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4416step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4416 raw4416Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw4416 raw4416Labels = mixedMoment B raw4416step0 raw4416step0Labels := by
      have hz : ∀ j, raw4416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4416step0 = (fun i j => raw4416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4416step0 raw4416; decide +kernel
      have hl : raw4416step0Labels = raw4416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4416 raw4416Labels permutation346 hz
    mixedMoment B raw4416step0 raw4416step0Labels = mixedMoment B raw4416step1 raw4416step1Labels := by
      have hz : ∀ j, raw4416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4416step1 = (fun i j => raw4416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4416step1 raw4416step0; decide +kernel
      have hl : raw4416step1Labels = raw4416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4416step0 raw4416step0Labels permutation56 hz
    mixedMoment B raw4416step1 raw4416step1Labels = mixedMoment B raw4416step2 raw4416step2Labels := by
      have ha : raw4416step2 = (fun i j => raw4416step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4416step2 raw4416step1; decide +kernel
      have hl : raw4416step2Labels = raw4416step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4416step1 raw4416step1Labels permutation10 permutation3
    _ = mixedMoment B node1190 node1190Labels := by rfl

def raw4417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4417step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4417 raw4417Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4417 raw4417Labels = mixedMoment B raw4417step0 raw4417step0Labels := by
      have hz : ∀ j, raw4417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4417step0 = (fun i j => raw4417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4417step0 raw4417; decide +kernel
      have hl : raw4417step0Labels = raw4417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4417 raw4417Labels permutation346 hz
    mixedMoment B raw4417step0 raw4417step0Labels = mixedMoment B raw4417step1 raw4417step1Labels := by
      have ha : raw4417step1 = (fun i j => raw4417step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4417step1 raw4417step0; decide +kernel
      have hl : raw4417step1Labels = raw4417step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4417step0 raw4417step0Labels permutation145 permutation3
    mixedMoment B raw4417step1 raw4417step1Labels = mixedMoment B raw4417step2 raw4417step2Labels := by
      have ha : raw4417step2 = -raw4417step1 := by apply Matrix.ext; change ∀ i j, raw4417step2 i j = -(raw4417step1 i j); unfold raw4417step2 raw4417step1; decide +kernel
      have hl : raw4417step2Labels = raw4417step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw4418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4418step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4418 raw4418Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4418 raw4418Labels = mixedMoment B raw4418step0 raw4418step0Labels := by
      have hz : ∀ j, raw4418 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4418step0 = (fun i j => raw4418 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4418step0 raw4418; decide +kernel
      have hl : raw4418step0Labels = raw4418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4418 raw4418Labels permutation265 hz
    mixedMoment B raw4418step0 raw4418step0Labels = mixedMoment B raw4418step1 raw4418step1Labels := by
      have ha : raw4418step1 = (fun i j => raw4418step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4418step1 raw4418step0; decide +kernel
      have hl : raw4418step1Labels = raw4418step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4418step0 raw4418step0Labels permutation145 permutation3
    mixedMoment B raw4418step1 raw4418step1Labels = mixedMoment B raw4418step2 raw4418step2Labels := by
      have ha : raw4418step2 = -raw4418step1 := by apply Matrix.ext; change ∀ i j, raw4418step2 i j = -(raw4418step1 i j); unfold raw4418step2 raw4418step1; decide +kernel
      have hl : raw4418step2Labels = raw4418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw4419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4419step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4419step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4419step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4419step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4419 raw4419Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw4419 raw4419Labels = mixedMoment B raw4419step0 raw4419step0Labels := by
      have hz : ∀ j, raw4419 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4419step0 = (fun i j => raw4419 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4419step0 raw4419; decide +kernel
      have hl : raw4419step0Labels = raw4419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4419 raw4419Labels permutation346 hz
    mixedMoment B raw4419step0 raw4419step0Labels = mixedMoment B raw4419step1 raw4419step1Labels := by
      have hz : ∀ j, raw4419step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4419step1 = (fun i j => raw4419step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4419step1 raw4419step0; decide +kernel
      have hl : raw4419step1Labels = raw4419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4419step0 raw4419step0Labels permutation56 hz
    mixedMoment B raw4419step1 raw4419step1Labels = mixedMoment B raw4419step2 raw4419step2Labels := by
      have ha : raw4419step2 = (fun i j => raw4419step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4419step2 raw4419step1; decide +kernel
      have hl : raw4419step2Labels = raw4419step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4419step1 raw4419step1Labels permutation29 permutation3
    mixedMoment B raw4419step2 raw4419step2Labels = mixedMoment B raw4419step3 raw4419step3Labels := by
      have ha : raw4419step3 = -raw4419step2 := by apply Matrix.ext; change ∀ i j, raw4419step3 i j = -(raw4419step2 i j); unfold raw4419step3 raw4419step2; decide +kernel
      have hl : raw4419step3Labels = raw4419step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1951 node1951Labels := by rfl

def raw4420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4420step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4420 raw4420Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw4420 raw4420Labels = mixedMoment B raw4420step0 raw4420step0Labels := by
      have hz : ∀ j, raw4420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4420step0 = (fun i j => raw4420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4420step0 raw4420; decide +kernel
      have hl : raw4420step0Labels = raw4420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4420 raw4420Labels permutation346 hz
    mixedMoment B raw4420step0 raw4420step0Labels = mixedMoment B raw4420step1 raw4420step1Labels := by
      have hz : ∀ j, raw4420step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4420step1 = (fun i j => raw4420step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4420step1 raw4420step0; decide +kernel
      have hl : raw4420step1Labels = raw4420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4420step0 raw4420step0Labels permutation56 hz
    mixedMoment B raw4420step1 raw4420step1Labels = mixedMoment B raw4420step2 raw4420step2Labels := by
      have ha : raw4420step2 = (fun i j => raw4420step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4420step2 raw4420step1; decide +kernel
      have hl : raw4420step2Labels = raw4420step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4420step1 raw4420step1Labels permutation10 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw4421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4421step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4421step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4421step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw4421step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4421step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw4421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4421 raw4421Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw4421 raw4421Labels = mixedMoment B raw4421step0 raw4421step0Labels := by
      have hz : ∀ j, raw4421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4421step0 = (fun i j => raw4421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4421step0 raw4421; decide +kernel
      have hl : raw4421step0Labels = raw4421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4421 raw4421Labels permutation434 hz
    mixedMoment B raw4421step0 raw4421step0Labels = mixedMoment B raw4421step1 raw4421step1Labels := by
      have hz : ∀ j, raw4421step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4421step1 = (fun i j => raw4421step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4421step1 raw4421step0; decide +kernel
      have hl : raw4421step1Labels = raw4421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4421step0 raw4421step0Labels permutation80 hz
    mixedMoment B raw4421step1 raw4421step1Labels = mixedMoment B raw4421step2 raw4421step2Labels := by
      have hz : ∀ j, raw4421step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4421step2 = (fun i j => raw4421step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4421step2 raw4421step1; decide +kernel
      have hl : raw4421step2Labels = raw4421step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4421step1 raw4421step1Labels permutation14 hz
    mixedMoment B raw4421step2 raw4421step2Labels = mixedMoment B raw4421step3 raw4421step3Labels := by
      have ha : raw4421step3 = (fun i j => raw4421step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4421step3 raw4421step2; decide +kernel
      have hl : raw4421step3Labels = raw4421step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4421step2 raw4421step2Labels permutation2 permutation3
    _ = mixedMoment B node1297 node1297Labels := by rfl

def raw4422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4422step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4422step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4422step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4422step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4422 raw4422Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4422 raw4422Labels = mixedMoment B raw4422step0 raw4422step0Labels := by
      have hz : ∀ j, raw4422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4422step0 = (fun i j => raw4422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4422step0 raw4422; decide +kernel
      have hl : raw4422step0Labels = raw4422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4422 raw4422Labels permutation434 hz
    mixedMoment B raw4422step0 raw4422step0Labels = mixedMoment B raw4422step1 raw4422step1Labels := by
      have hz : ∀ j, raw4422step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4422step1 = (fun i j => raw4422step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4422step1 raw4422step0; decide +kernel
      have hl : raw4422step1Labels = raw4422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4422step0 raw4422step0Labels permutation80 hz
    mixedMoment B raw4422step1 raw4422step1Labels = mixedMoment B raw4422step2 raw4422step2Labels := by
      have ha : raw4422step2 = (fun i j => raw4422step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4422step2 raw4422step1; decide +kernel
      have hl : raw4422step2Labels = raw4422step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4422step1 raw4422step1Labels permutation31 permutation3
    mixedMoment B raw4422step2 raw4422step2Labels = mixedMoment B raw4422step3 raw4422step3Labels := by
      have ha : raw4422step3 = -raw4422step2 := by apply Matrix.ext; change ∀ i j, raw4422step3 i j = -(raw4422step2 i j); unfold raw4422step3 raw4422step2; decide +kernel
      have hl : raw4422step3Labels = raw4422step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw4423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4423step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4423step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4423step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4423step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4423step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4423step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4423 raw4423Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4423 raw4423Labels = mixedMoment B raw4423step0 raw4423step0Labels := by
      have hz : ∀ j, raw4423 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4423step0 = (fun i j => raw4423 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4423step0 raw4423; decide +kernel
      have hl : raw4423step0Labels = raw4423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4423 raw4423Labels permutation434 hz
    mixedMoment B raw4423step0 raw4423step0Labels = mixedMoment B raw4423step1 raw4423step1Labels := by
      have hz : ∀ j, raw4423step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4423step1 = (fun i j => raw4423step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4423step1 raw4423step0; decide +kernel
      have hl : raw4423step1Labels = raw4423step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4423step0 raw4423step0Labels permutation56 hz
    mixedMoment B raw4423step1 raw4423step1Labels = mixedMoment B raw4423step2 raw4423step2Labels := by
      have ha : raw4423step2 = (fun i j => raw4423step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4423step2 raw4423step1; decide +kernel
      have hl : raw4423step2Labels = raw4423step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4423step1 raw4423step1Labels permutation31 permutation3
    mixedMoment B raw4423step2 raw4423step2Labels = mixedMoment B raw4423step3 raw4423step3Labels := by
      have ha : raw4423step3 = -raw4423step2 := by apply Matrix.ext; change ∀ i j, raw4423step3 i j = -(raw4423step2 i j); unfold raw4423step3 raw4423step2; decide +kernel
      have hl : raw4423step3Labels = raw4423step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw4424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4424step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4424step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4424step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4424step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4424 raw4424Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4424 raw4424Labels = mixedMoment B raw4424step0 raw4424step0Labels := by
      have hz : ∀ j, raw4424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4424step0 = (fun i j => raw4424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4424step0 raw4424; decide +kernel
      have hl : raw4424step0Labels = raw4424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4424 raw4424Labels permutation346 hz
    mixedMoment B raw4424step0 raw4424step0Labels = mixedMoment B raw4424step1 raw4424step1Labels := by
      have hz : ∀ j, raw4424step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4424step1 = (fun i j => raw4424step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4424step1 raw4424step0; decide +kernel
      have hl : raw4424step1Labels = raw4424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4424step0 raw4424step0Labels permutation56 hz
    mixedMoment B raw4424step1 raw4424step1Labels = mixedMoment B raw4424step2 raw4424step2Labels := by
      have ha : raw4424step2 = (fun i j => raw4424step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4424step2 raw4424step1; decide +kernel
      have hl : raw4424step2Labels = raw4424step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4424step1 raw4424step1Labels permutation31 permutation3
    mixedMoment B raw4424step2 raw4424step2Labels = mixedMoment B raw4424step3 raw4424step3Labels := by
      have ha : raw4424step3 = -raw4424step2 := by apply Matrix.ext; change ∀ i j, raw4424step3 i j = -(raw4424step2 i j); unfold raw4424step3 raw4424step2; decide +kernel
      have hl : raw4424step3Labels = raw4424step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw4425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw4425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw4425step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw4425step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4425step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4425step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4425step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw4425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4425 raw4425Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw4425 raw4425Labels = mixedMoment B raw4425step0 raw4425step0Labels := by
      have hz : ∀ j, raw4425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4425step0 = (fun i j => raw4425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4425step0 raw4425; decide +kernel
      have hl : raw4425step0Labels = raw4425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4425 raw4425Labels permutation434 hz
    mixedMoment B raw4425step0 raw4425step0Labels = mixedMoment B raw4425step1 raw4425step1Labels := by
      have hz : ∀ j, raw4425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4425step1 = (fun i j => raw4425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4425step1 raw4425step0; decide +kernel
      have hl : raw4425step1Labels = raw4425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4425step0 raw4425step0Labels permutation80 hz
    mixedMoment B raw4425step1 raw4425step1Labels = mixedMoment B raw4425step2 raw4425step2Labels := by
      have hz : ∀ j, raw4425step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4425step2 = (fun i j => raw4425step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4425step2 raw4425step1; decide +kernel
      have hl : raw4425step2Labels = raw4425step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4425step1 raw4425step1Labels permutation14 hz
    mixedMoment B raw4425step2 raw4425step2Labels = mixedMoment B raw4425step3 raw4425step3Labels := by
      have ha : raw4425step3 = (fun i j => raw4425step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4425step3 raw4425step2; decide +kernel
      have hl : raw4425step3Labels = raw4425step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4425step2 raw4425step2Labels permutation2 permutation3
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw4426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4426step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4426step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4426step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw4426step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4426step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw4426step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4426step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw4426step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4426 raw4426Labels = mixedMoment B node832 node832Labels := by
  calc
    mixedMoment B raw4426 raw4426Labels = mixedMoment B raw4426step0 raw4426step0Labels := by
      have hz : ∀ j, raw4426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4426step0 = (fun i j => raw4426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4426step0 raw4426; decide +kernel
      have hl : raw4426step0Labels = raw4426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4426 raw4426Labels permutation434 hz
    mixedMoment B raw4426step0 raw4426step0Labels = mixedMoment B raw4426step1 raw4426step1Labels := by
      have hz : ∀ j, raw4426step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4426step1 = (fun i j => raw4426step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4426step1 raw4426step0; decide +kernel
      have hl : raw4426step1Labels = raw4426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4426step0 raw4426step0Labels permutation80 hz
    mixedMoment B raw4426step1 raw4426step1Labels = mixedMoment B raw4426step2 raw4426step2Labels := by
      have hz : ∀ j, raw4426step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4426step2 = (fun i j => raw4426step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4426step2 raw4426step1; decide +kernel
      have hl : raw4426step2Labels = raw4426step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4426step1 raw4426step1Labels permutation14 hz
    mixedMoment B raw4426step2 raw4426step2Labels = mixedMoment B raw4426step3 raw4426step3Labels := by
      have ha : raw4426step3 = (fun i j => raw4426step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4426step3 raw4426step2; decide +kernel
      have hl : raw4426step3Labels = raw4426step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4426step2 raw4426step2Labels permutation7 permutation3
    mixedMoment B raw4426step3 raw4426step3Labels = mixedMoment B raw4426step4 raw4426step4Labels := by
      have ha : raw4426step4 = -raw4426step3 := by apply Matrix.ext; change ∀ i j, raw4426step4 i j = -(raw4426step3 i j); unfold raw4426step4 raw4426step3; decide +kernel
      have hl : raw4426step4Labels = raw4426step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node832 node832Labels := by rfl

def raw4427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4427step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4427step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4427step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4427step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4427step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4427 raw4427Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw4427 raw4427Labels = mixedMoment B raw4427step0 raw4427step0Labels := by
      have hz : ∀ j, raw4427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4427step0 = (fun i j => raw4427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4427step0 raw4427; decide +kernel
      have hl : raw4427step0Labels = raw4427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4427 raw4427Labels permutation434 hz
    mixedMoment B raw4427step0 raw4427step0Labels = mixedMoment B raw4427step1 raw4427step1Labels := by
      have hz : ∀ j, raw4427step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4427step1 = (fun i j => raw4427step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4427step1 raw4427step0; decide +kernel
      have hl : raw4427step1Labels = raw4427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4427step0 raw4427step0Labels permutation80 hz
    mixedMoment B raw4427step1 raw4427step1Labels = mixedMoment B raw4427step2 raw4427step2Labels := by
      have ha : raw4427step2 = (fun i j => raw4427step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4427step2 raw4427step1; decide +kernel
      have hl : raw4427step2Labels = raw4427step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4427step1 raw4427step1Labels permutation31 permutation3
    mixedMoment B raw4427step2 raw4427step2Labels = mixedMoment B raw4427step3 raw4427step3Labels := by
      have ha : raw4427step3 = -raw4427step2 := by apply Matrix.ext; change ∀ i j, raw4427step3 i j = -(raw4427step2 i j); unfold raw4427step3 raw4427step2; decide +kernel
      have hl : raw4427step3Labels = raw4427step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node828 node828Labels := by rfl

def raw4428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4428step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4428step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4428step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4428step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4428step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4428 raw4428Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw4428 raw4428Labels = mixedMoment B raw4428step0 raw4428step0Labels := by
      have hz : ∀ j, raw4428 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4428step0 = (fun i j => raw4428 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4428step0 raw4428; decide +kernel
      have hl : raw4428step0Labels = raw4428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4428 raw4428Labels permutation434 hz
    mixedMoment B raw4428step0 raw4428step0Labels = mixedMoment B raw4428step1 raw4428step1Labels := by
      have hz : ∀ j, raw4428step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4428step1 = (fun i j => raw4428step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4428step1 raw4428step0; decide +kernel
      have hl : raw4428step1Labels = raw4428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4428step0 raw4428step0Labels permutation56 hz
    mixedMoment B raw4428step1 raw4428step1Labels = mixedMoment B raw4428step2 raw4428step2Labels := by
      have ha : raw4428step2 = (fun i j => raw4428step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4428step2 raw4428step1; decide +kernel
      have hl : raw4428step2Labels = raw4428step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4428step1 raw4428step1Labels permutation31 permutation3
    mixedMoment B raw4428step2 raw4428step2Labels = mixedMoment B raw4428step3 raw4428step3Labels := by
      have ha : raw4428step3 = -raw4428step2 := by apply Matrix.ext; change ∀ i j, raw4428step3 i j = -(raw4428step2 i j); unfold raw4428step3 raw4428step2; decide +kernel
      have hl : raw4428step3Labels = raw4428step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node828 node828Labels := by rfl

def raw4429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4429step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4429step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4429 raw4429Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw4429 raw4429Labels = mixedMoment B raw4429step0 raw4429step0Labels := by
      have hz : ∀ j, raw4429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4429step0 = (fun i j => raw4429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4429step0 raw4429; decide +kernel
      have hl : raw4429step0Labels = raw4429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4429 raw4429Labels permutation346 hz
    mixedMoment B raw4429step0 raw4429step0Labels = mixedMoment B raw4429step1 raw4429step1Labels := by
      have hz : ∀ j, raw4429step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4429step1 = (fun i j => raw4429step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4429step1 raw4429step0; decide +kernel
      have hl : raw4429step1Labels = raw4429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4429step0 raw4429step0Labels permutation56 hz
    mixedMoment B raw4429step1 raw4429step1Labels = mixedMoment B raw4429step2 raw4429step2Labels := by
      have ha : raw4429step2 = (fun i j => raw4429step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4429step2 raw4429step1; decide +kernel
      have hl : raw4429step2Labels = raw4429step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4429step1 raw4429step1Labels permutation31 permutation3
    mixedMoment B raw4429step2 raw4429step2Labels = mixedMoment B raw4429step3 raw4429step3Labels := by
      have ha : raw4429step3 = -raw4429step2 := by apply Matrix.ext; change ∀ i j, raw4429step3 i j = -(raw4429step2 i j); unfold raw4429step3 raw4429step2; decide +kernel
      have hl : raw4429step3Labels = raw4429step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node828 node828Labels := by rfl

def raw4430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4430step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4430step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4430step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![4, -4, 0]]
def raw4430step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4430step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw4430step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4430step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw4430step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4430 raw4430Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw4430 raw4430Labels = mixedMoment B raw4430step0 raw4430step0Labels := by
      have hz : ∀ j, raw4430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4430step0 = (fun i j => raw4430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4430step0 raw4430; decide +kernel
      have hl : raw4430step0Labels = raw4430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4430 raw4430Labels permutation434 hz
    mixedMoment B raw4430step0 raw4430step0Labels = mixedMoment B raw4430step1 raw4430step1Labels := by
      have hz : ∀ j, raw4430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4430step1 = (fun i j => raw4430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4430step1 raw4430step0; decide +kernel
      have hl : raw4430step1Labels = raw4430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4430step0 raw4430step0Labels permutation80 hz
    mixedMoment B raw4430step1 raw4430step1Labels = mixedMoment B raw4430step2 raw4430step2Labels := by
      have hz : ∀ j, raw4430step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4430step2 = (fun i j => raw4430step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4430step2 raw4430step1; decide +kernel
      have hl : raw4430step2Labels = raw4430step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4430step1 raw4430step1Labels permutation14 hz
    mixedMoment B raw4430step2 raw4430step2Labels = mixedMoment B raw4430step3 raw4430step3Labels := by
      have ha : raw4430step3 = (fun i j => raw4430step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4430step3 raw4430step2; decide +kernel
      have hl : raw4430step3Labels = raw4430step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4430step2 raw4430step2Labels permutation7 permutation3
    mixedMoment B raw4430step3 raw4430step3Labels = mixedMoment B raw4430step4 raw4430step4Labels := by
      have ha : raw4430step4 = -raw4430step3 := by apply Matrix.ext; change ∀ i j, raw4430step4 i j = -(raw4430step3 i j); unfold raw4430step4 raw4430step3; decide +kernel
      have hl : raw4430step4Labels = raw4430step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node860 node860Labels := by rfl

def raw4431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4431step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4431step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4431step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4431step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4431 raw4431Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw4431 raw4431Labels = mixedMoment B raw4431step0 raw4431step0Labels := by
      have hz : ∀ j, raw4431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4431step0 = (fun i j => raw4431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4431step0 raw4431; decide +kernel
      have hl : raw4431step0Labels = raw4431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4431 raw4431Labels permutation434 hz
    mixedMoment B raw4431step0 raw4431step0Labels = mixedMoment B raw4431step1 raw4431step1Labels := by
      have hz : ∀ j, raw4431step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4431step1 = (fun i j => raw4431step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4431step1 raw4431step0; decide +kernel
      have hl : raw4431step1Labels = raw4431step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4431step0 raw4431step0Labels permutation80 hz
    mixedMoment B raw4431step1 raw4431step1Labels = mixedMoment B raw4431step2 raw4431step2Labels := by
      have ha : raw4431step2 = (fun i j => raw4431step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4431step2 raw4431step1; decide +kernel
      have hl : raw4431step2Labels = raw4431step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4431step1 raw4431step1Labels permutation28 permutation7
    mixedMoment B raw4431step2 raw4431step2Labels = mixedMoment B raw4431step3 raw4431step3Labels := by
      have ha : raw4431step3 = raw4431step2 := by apply Matrix.ext; unfold raw4431step3 raw4431step2; decide +kernel
      have hl : raw4431step2Labels = labelEmbedding10 ∘ raw4431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4431step2 raw4431step2Labels raw4431step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw4432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4432step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4432step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4432step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4432step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4432 raw4432Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw4432 raw4432Labels = mixedMoment B raw4432step0 raw4432step0Labels := by
      have hz : ∀ j, raw4432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4432step0 = (fun i j => raw4432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4432step0 raw4432; decide +kernel
      have hl : raw4432step0Labels = raw4432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4432 raw4432Labels permutation434 hz
    mixedMoment B raw4432step0 raw4432step0Labels = mixedMoment B raw4432step1 raw4432step1Labels := by
      have hz : ∀ j, raw4432step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4432step1 = (fun i j => raw4432step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4432step1 raw4432step0; decide +kernel
      have hl : raw4432step1Labels = raw4432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4432step0 raw4432step0Labels permutation56 hz
    mixedMoment B raw4432step1 raw4432step1Labels = mixedMoment B raw4432step2 raw4432step2Labels := by
      have ha : raw4432step2 = (fun i j => raw4432step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4432step2 raw4432step1; decide +kernel
      have hl : raw4432step2Labels = raw4432step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4432step1 raw4432step1Labels permutation28 permutation7
    mixedMoment B raw4432step2 raw4432step2Labels = mixedMoment B raw4432step3 raw4432step3Labels := by
      have ha : raw4432step3 = raw4432step2 := by apply Matrix.ext; unfold raw4432step3 raw4432step2; decide +kernel
      have hl : raw4432step2Labels = labelEmbedding10 ∘ raw4432step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4432step2 raw4432step2Labels raw4432step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw4433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4433step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4433step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4433step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4433 raw4433Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw4433 raw4433Labels = mixedMoment B raw4433step0 raw4433step0Labels := by
      have hz : ∀ j, raw4433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4433step0 = (fun i j => raw4433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4433step0 raw4433; decide +kernel
      have hl : raw4433step0Labels = raw4433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4433 raw4433Labels permutation346 hz
    mixedMoment B raw4433step0 raw4433step0Labels = mixedMoment B raw4433step1 raw4433step1Labels := by
      have hz : ∀ j, raw4433step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4433step1 = (fun i j => raw4433step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4433step1 raw4433step0; decide +kernel
      have hl : raw4433step1Labels = raw4433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4433step0 raw4433step0Labels permutation56 hz
    mixedMoment B raw4433step1 raw4433step1Labels = mixedMoment B raw4433step2 raw4433step2Labels := by
      have ha : raw4433step2 = (fun i j => raw4433step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4433step2 raw4433step1; decide +kernel
      have hl : raw4433step2Labels = raw4433step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4433step1 raw4433step1Labels permutation28 permutation7
    mixedMoment B raw4433step2 raw4433step2Labels = mixedMoment B raw4433step3 raw4433step3Labels := by
      have ha : raw4433step3 = raw4433step2 := by apply Matrix.ext; unfold raw4433step3 raw4433step2; decide +kernel
      have hl : raw4433step2Labels = labelEmbedding10 ∘ raw4433step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4433step2 raw4433step2Labels raw4433step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw4434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw4434step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw4434step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw4434step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4434 raw4434Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw4434 raw4434Labels = mixedMoment B raw4434step0 raw4434step0Labels := by
      have hz : ∀ j, raw4434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4434step0 = (fun i j => raw4434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4434step0 raw4434; decide +kernel
      have hl : raw4434step0Labels = raw4434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4434 raw4434Labels permutation434 hz
    mixedMoment B raw4434step0 raw4434step0Labels = mixedMoment B raw4434step1 raw4434step1Labels := by
      have hz : ∀ j, raw4434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4434step1 = (fun i j => raw4434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4434step1 raw4434step0; decide +kernel
      have hl : raw4434step1Labels = raw4434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4434step0 raw4434step0Labels permutation80 hz
    mixedMoment B raw4434step1 raw4434step1Labels = mixedMoment B raw4434step2 raw4434step2Labels := by
      have hz : ∀ j, raw4434step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4434step2 = (fun i j => raw4434step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4434step2 raw4434step1; decide +kernel
      have hl : raw4434step2Labels = raw4434step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4434step1 raw4434step1Labels permutation14 hz
    mixedMoment B raw4434step2 raw4434step2Labels = mixedMoment B raw4434step3 raw4434step3Labels := by
      have ha : raw4434step3 = (fun i j => raw4434step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4434step3 raw4434step2; decide +kernel
      have hl : raw4434step3Labels = raw4434step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4434step2 raw4434step2Labels permutation7 permutation2
    mixedMoment B raw4434step3 raw4434step3Labels = mixedMoment B raw4434step4 raw4434step4Labels := by
      have ha : raw4434step4 = -raw4434step3 := by apply Matrix.ext; change ∀ i j, raw4434step4 i j = -(raw4434step3 i j); unfold raw4434step4 raw4434step3; decide +kernel
      have hl : raw4434step4Labels = raw4434step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4901 node4901Labels := by rfl

def raw4435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4435step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw4435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4435step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4435step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4435step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4435step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4435 raw4435Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw4435 raw4435Labels = mixedMoment B raw4435step0 raw4435step0Labels := by
      have hz : ∀ j, raw4435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4435step0 = (fun i j => raw4435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4435step0 raw4435; decide +kernel
      have hl : raw4435step0Labels = raw4435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4435 raw4435Labels permutation434 hz
    mixedMoment B raw4435step0 raw4435step0Labels = mixedMoment B raw4435step1 raw4435step1Labels := by
      have hz : ∀ j, raw4435step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4435step1 = (fun i j => raw4435step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4435step1 raw4435step0; decide +kernel
      have hl : raw4435step1Labels = raw4435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4435step0 raw4435step0Labels permutation80 hz
    mixedMoment B raw4435step1 raw4435step1Labels = mixedMoment B raw4435step2 raw4435step2Labels := by
      have hz : ∀ j, raw4435step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4435step2 = (fun i j => raw4435step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4435step2 raw4435step1; decide +kernel
      have hl : raw4435step2Labels = raw4435step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4435step1 raw4435step1Labels permutation14 hz
    mixedMoment B raw4435step2 raw4435step2Labels = mixedMoment B raw4435step3 raw4435step3Labels := by
      have ha : raw4435step3 = (fun i j => raw4435step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4435step3 raw4435step2; decide +kernel
      have hl : raw4435step3Labels = raw4435step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4435step2 raw4435step2Labels permutation6 permutation7
    mixedMoment B raw4435step3 raw4435step3Labels = mixedMoment B raw4435step4 raw4435step4Labels := by
      have ha : raw4435step4 = raw4435step3 := by apply Matrix.ext; unfold raw4435step4 raw4435step3; decide +kernel
      have hl : raw4435step3Labels = labelEmbedding10 ∘ raw4435step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4435step3 raw4435step3Labels raw4435step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw4436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4436step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4436step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4436step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4436step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4436 raw4436Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw4436 raw4436Labels = mixedMoment B raw4436step0 raw4436step0Labels := by
      have hz : ∀ j, raw4436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4436step0 = (fun i j => raw4436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4436step0 raw4436; decide +kernel
      have hl : raw4436step0Labels = raw4436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4436 raw4436Labels permutation434 hz
    mixedMoment B raw4436step0 raw4436step0Labels = mixedMoment B raw4436step1 raw4436step1Labels := by
      have hz : ∀ j, raw4436step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4436step1 = (fun i j => raw4436step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4436step1 raw4436step0; decide +kernel
      have hl : raw4436step1Labels = raw4436step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4436step0 raw4436step0Labels permutation80 hz
    mixedMoment B raw4436step1 raw4436step1Labels = mixedMoment B raw4436step2 raw4436step2Labels := by
      have ha : raw4436step2 = (fun i j => raw4436step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4436step2 raw4436step1; decide +kernel
      have hl : raw4436step2Labels = raw4436step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4436step1 raw4436step1Labels permutation10 permutation3
    mixedMoment B raw4436step2 raw4436step2Labels = mixedMoment B raw4436step3 raw4436step3Labels := by
      have ha : raw4436step3 = raw4436step2 := by apply Matrix.ext; unfold raw4436step3 raw4436step2; decide +kernel
      have hl : raw4436step2Labels = labelEmbedding6 ∘ raw4436step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4436step2 raw4436step2Labels raw4436step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw4437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4437step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4437 raw4437Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw4437 raw4437Labels = mixedMoment B raw4437step0 raw4437step0Labels := by
      have hz : ∀ j, raw4437 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4437step0 = (fun i j => raw4437 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4437step0 raw4437; decide +kernel
      have hl : raw4437step0Labels = raw4437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4437 raw4437Labels permutation434 hz
    mixedMoment B raw4437step0 raw4437step0Labels = mixedMoment B raw4437step1 raw4437step1Labels := by
      have ha : raw4437step1 = (fun i j => raw4437step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4437step1 raw4437step0; decide +kernel
      have hl : raw4437step1Labels = raw4437step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4437step0 raw4437step0Labels permutation139 permutation2
    mixedMoment B raw4437step1 raw4437step1Labels = mixedMoment B raw4437step2 raw4437step2Labels := by
      have ha : raw4437step2 = -raw4437step1 := by apply Matrix.ext; change ∀ i j, raw4437step2 i j = -(raw4437step1 i j); unfold raw4437step2 raw4437step1; decide +kernel
      have hl : raw4437step2Labels = raw4437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw4438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4438step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4438 raw4438Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw4438 raw4438Labels = mixedMoment B raw4438step0 raw4438step0Labels := by
      have hz : ∀ j, raw4438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4438step0 = (fun i j => raw4438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4438step0 raw4438; decide +kernel
      have hl : raw4438step0Labels = raw4438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4438 raw4438Labels permutation346 hz
    mixedMoment B raw4438step0 raw4438step0Labels = mixedMoment B raw4438step1 raw4438step1Labels := by
      have ha : raw4438step1 = (fun i j => raw4438step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4438step1 raw4438step0; decide +kernel
      have hl : raw4438step1Labels = raw4438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4438step0 raw4438step0Labels permutation139 permutation2
    mixedMoment B raw4438step1 raw4438step1Labels = mixedMoment B raw4438step2 raw4438step2Labels := by
      have ha : raw4438step2 = -raw4438step1 := by apply Matrix.ext; change ∀ i j, raw4438step2 i j = -(raw4438step1 i j); unfold raw4438step2 raw4438step1; decide +kernel
      have hl : raw4438step2Labels = raw4438step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw4439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4439step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4439step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4439 raw4439Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw4439 raw4439Labels = mixedMoment B raw4439step0 raw4439step0Labels := by
      have hz : ∀ j, raw4439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4439step0 = (fun i j => raw4439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4439step0 raw4439; decide +kernel
      have hl : raw4439step0Labels = raw4439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4439 raw4439Labels permutation434 hz
    mixedMoment B raw4439step0 raw4439step0Labels = mixedMoment B raw4439step1 raw4439step1Labels := by
      have hz : ∀ j, raw4439step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4439step1 = (fun i j => raw4439step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4439step1 raw4439step0; decide +kernel
      have hl : raw4439step1Labels = raw4439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4439step0 raw4439step0Labels permutation80 hz
    mixedMoment B raw4439step1 raw4439step1Labels = mixedMoment B raw4439step2 raw4439step2Labels := by
      have ha : raw4439step2 = (fun i j => raw4439step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4439step2 raw4439step1; decide +kernel
      have hl : raw4439step2Labels = raw4439step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4439step1 raw4439step1Labels permutation29 permutation2
    mixedMoment B raw4439step2 raw4439step2Labels = mixedMoment B raw4439step3 raw4439step3Labels := by
      have ha : raw4439step3 = -raw4439step2 := by apply Matrix.ext; change ∀ i j, raw4439step3 i j = -(raw4439step2 i j); unfold raw4439step3 raw4439step2; decide +kernel
      have hl : raw4439step3Labels = raw4439step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw4440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4440step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4440step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4440step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4440step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4440step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4440 raw4440Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw4440 raw4440Labels = mixedMoment B raw4440step0 raw4440step0Labels := by
      have hz : ∀ j, raw4440 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4440step0 = (fun i j => raw4440 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4440step0 raw4440; decide +kernel
      have hl : raw4440step0Labels = raw4440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4440 raw4440Labels permutation434 hz
    mixedMoment B raw4440step0 raw4440step0Labels = mixedMoment B raw4440step1 raw4440step1Labels := by
      have hz : ∀ j, raw4440step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4440step1 = (fun i j => raw4440step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4440step1 raw4440step0; decide +kernel
      have hl : raw4440step1Labels = raw4440step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4440step0 raw4440step0Labels permutation80 hz
    mixedMoment B raw4440step1 raw4440step1Labels = mixedMoment B raw4440step2 raw4440step2Labels := by
      have ha : raw4440step2 = (fun i j => raw4440step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4440step2 raw4440step1; decide +kernel
      have hl : raw4440step2Labels = raw4440step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4440step1 raw4440step1Labels permutation28 permutation7
    mixedMoment B raw4440step2 raw4440step2Labels = mixedMoment B raw4440step3 raw4440step3Labels := by
      have ha : raw4440step3 = raw4440step2 := by apply Matrix.ext; unfold raw4440step3 raw4440step2; decide +kernel
      have hl : raw4440step2Labels = labelEmbedding10 ∘ raw4440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4440step2 raw4440step2Labels raw4440step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw4441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4441step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4441step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4441step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4441step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4441 raw4441Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw4441 raw4441Labels = mixedMoment B raw4441step0 raw4441step0Labels := by
      have hz : ∀ j, raw4441 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4441step0 = (fun i j => raw4441 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4441step0 raw4441; decide +kernel
      have hl : raw4441step0Labels = raw4441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4441 raw4441Labels permutation434 hz
    mixedMoment B raw4441step0 raw4441step0Labels = mixedMoment B raw4441step1 raw4441step1Labels := by
      have hz : ∀ j, raw4441step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4441step1 = (fun i j => raw4441step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4441step1 raw4441step0; decide +kernel
      have hl : raw4441step1Labels = raw4441step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4441step0 raw4441step0Labels permutation56 hz
    mixedMoment B raw4441step1 raw4441step1Labels = mixedMoment B raw4441step2 raw4441step2Labels := by
      have ha : raw4441step2 = (fun i j => raw4441step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4441step2 raw4441step1; decide +kernel
      have hl : raw4441step2Labels = raw4441step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4441step1 raw4441step1Labels permutation10 permutation3
    mixedMoment B raw4441step2 raw4441step2Labels = mixedMoment B raw4441step3 raw4441step3Labels := by
      have ha : raw4441step3 = raw4441step2 := by apply Matrix.ext; unfold raw4441step3 raw4441step2; decide +kernel
      have hl : raw4441step2Labels = labelEmbedding6 ∘ raw4441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4441step2 raw4441step2Labels raw4441step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw4442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4442step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4442 raw4442Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw4442 raw4442Labels = mixedMoment B raw4442step0 raw4442step0Labels := by
      have hz : ∀ j, raw4442 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4442step0 = (fun i j => raw4442 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4442step0 raw4442; decide +kernel
      have hl : raw4442step0Labels = raw4442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4442 raw4442Labels permutation434 hz
    mixedMoment B raw4442step0 raw4442step0Labels = mixedMoment B raw4442step1 raw4442step1Labels := by
      have ha : raw4442step1 = (fun i j => raw4442step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4442step1 raw4442step0; decide +kernel
      have hl : raw4442step1Labels = raw4442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4442step0 raw4442step0Labels permutation145 permutation2
    mixedMoment B raw4442step1 raw4442step1Labels = mixedMoment B raw4442step2 raw4442step2Labels := by
      have ha : raw4442step2 = -raw4442step1 := by apply Matrix.ext; change ∀ i j, raw4442step2 i j = -(raw4442step1 i j); unfold raw4442step2 raw4442step1; decide +kernel
      have hl : raw4442step2Labels = raw4442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw4443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4443step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4443 raw4443Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw4443 raw4443Labels = mixedMoment B raw4443step0 raw4443step0Labels := by
      have hz : ∀ j, raw4443 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4443step0 = (fun i j => raw4443 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4443step0 raw4443; decide +kernel
      have hl : raw4443step0Labels = raw4443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4443 raw4443Labels permutation265 hz
    mixedMoment B raw4443step0 raw4443step0Labels = mixedMoment B raw4443step1 raw4443step1Labels := by
      have ha : raw4443step1 = (fun i j => raw4443step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4443step1 raw4443step0; decide +kernel
      have hl : raw4443step1Labels = raw4443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4443step0 raw4443step0Labels permutation139 permutation2
    mixedMoment B raw4443step1 raw4443step1Labels = mixedMoment B raw4443step2 raw4443step2Labels := by
      have ha : raw4443step2 = -raw4443step1 := by apply Matrix.ext; change ∀ i j, raw4443step2 i j = -(raw4443step1 i j); unfold raw4443step2 raw4443step1; decide +kernel
      have hl : raw4443step2Labels = raw4443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw4444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4444step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4444step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4444step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4444step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4444 raw4444Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw4444 raw4444Labels = mixedMoment B raw4444step0 raw4444step0Labels := by
      have hz : ∀ j, raw4444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4444step0 = (fun i j => raw4444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4444step0 raw4444; decide +kernel
      have hl : raw4444step0Labels = raw4444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4444 raw4444Labels permutation434 hz
    mixedMoment B raw4444step0 raw4444step0Labels = mixedMoment B raw4444step1 raw4444step1Labels := by
      have hz : ∀ j, raw4444step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4444step1 = (fun i j => raw4444step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4444step1 raw4444step0; decide +kernel
      have hl : raw4444step1Labels = raw4444step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4444step0 raw4444step0Labels permutation56 hz
    mixedMoment B raw4444step1 raw4444step1Labels = mixedMoment B raw4444step2 raw4444step2Labels := by
      have ha : raw4444step2 = (fun i j => raw4444step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4444step2 raw4444step1; decide +kernel
      have hl : raw4444step2Labels = raw4444step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4444step1 raw4444step1Labels permutation29 permutation2
    mixedMoment B raw4444step2 raw4444step2Labels = mixedMoment B raw4444step3 raw4444step3Labels := by
      have ha : raw4444step3 = -raw4444step2 := by apply Matrix.ext; change ∀ i j, raw4444step3 i j = -(raw4444step2 i j); unfold raw4444step3 raw4444step2; decide +kernel
      have hl : raw4444step3Labels = raw4444step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw4445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4445step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4445step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4445step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4445 raw4445Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw4445 raw4445Labels = mixedMoment B raw4445step0 raw4445step0Labels := by
      have hz : ∀ j, raw4445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4445step0 = (fun i j => raw4445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4445step0 raw4445; decide +kernel
      have hl : raw4445step0Labels = raw4445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4445 raw4445Labels permutation434 hz
    mixedMoment B raw4445step0 raw4445step0Labels = mixedMoment B raw4445step1 raw4445step1Labels := by
      have hz : ∀ j, raw4445step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4445step1 = (fun i j => raw4445step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4445step1 raw4445step0; decide +kernel
      have hl : raw4445step1Labels = raw4445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4445step0 raw4445step0Labels permutation56 hz
    mixedMoment B raw4445step1 raw4445step1Labels = mixedMoment B raw4445step2 raw4445step2Labels := by
      have ha : raw4445step2 = (fun i j => raw4445step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4445step2 raw4445step1; decide +kernel
      have hl : raw4445step2Labels = raw4445step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4445step1 raw4445step1Labels permutation28 permutation7
    mixedMoment B raw4445step2 raw4445step2Labels = mixedMoment B raw4445step3 raw4445step3Labels := by
      have ha : raw4445step3 = raw4445step2 := by apply Matrix.ext; unfold raw4445step3 raw4445step2; decide +kernel
      have hl : raw4445step2Labels = labelEmbedding10 ∘ raw4445step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4445step2 raw4445step2Labels raw4445step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw4446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4446step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4446step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4446step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4446 raw4446Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw4446 raw4446Labels = mixedMoment B raw4446step0 raw4446step0Labels := by
      have hz : ∀ j, raw4446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4446step0 = (fun i j => raw4446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4446step0 raw4446; decide +kernel
      have hl : raw4446step0Labels = raw4446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4446 raw4446Labels permutation346 hz
    mixedMoment B raw4446step0 raw4446step0Labels = mixedMoment B raw4446step1 raw4446step1Labels := by
      have hz : ∀ j, raw4446step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4446step1 = (fun i j => raw4446step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4446step1 raw4446step0; decide +kernel
      have hl : raw4446step1Labels = raw4446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4446step0 raw4446step0Labels permutation56 hz
    mixedMoment B raw4446step1 raw4446step1Labels = mixedMoment B raw4446step2 raw4446step2Labels := by
      have ha : raw4446step2 = (fun i j => raw4446step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4446step2 raw4446step1; decide +kernel
      have hl : raw4446step2Labels = raw4446step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4446step1 raw4446step1Labels permutation10 permutation3
    mixedMoment B raw4446step2 raw4446step2Labels = mixedMoment B raw4446step3 raw4446step3Labels := by
      have ha : raw4446step3 = raw4446step2 := by apply Matrix.ext; unfold raw4446step3 raw4446step2; decide +kernel
      have hl : raw4446step2Labels = labelEmbedding6 ∘ raw4446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4446step2 raw4446step2Labels raw4446step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw4447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4447step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4447step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4447 raw4447Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw4447 raw4447Labels = mixedMoment B raw4447step0 raw4447step0Labels := by
      have hz : ∀ j, raw4447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4447step0 = (fun i j => raw4447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4447step0 raw4447; decide +kernel
      have hl : raw4447step0Labels = raw4447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4447 raw4447Labels permutation346 hz
    mixedMoment B raw4447step0 raw4447step0Labels = mixedMoment B raw4447step1 raw4447step1Labels := by
      have ha : raw4447step1 = (fun i j => raw4447step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4447step1 raw4447step0; decide +kernel
      have hl : raw4447step1Labels = raw4447step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4447step0 raw4447step0Labels permutation145 permutation2
    mixedMoment B raw4447step1 raw4447step1Labels = mixedMoment B raw4447step2 raw4447step2Labels := by
      have ha : raw4447step2 = -raw4447step1 := by apply Matrix.ext; change ∀ i j, raw4447step2 i j = -(raw4447step1 i j); unfold raw4447step2 raw4447step1; decide +kernel
      have hl : raw4447step2Labels = raw4447step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw4448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4448step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4448step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4448 raw4448Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw4448 raw4448Labels = mixedMoment B raw4448step0 raw4448step0Labels := by
      have hz : ∀ j, raw4448 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4448step0 = (fun i j => raw4448 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4448step0 raw4448; decide +kernel
      have hl : raw4448step0Labels = raw4448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4448 raw4448Labels permutation265 hz
    mixedMoment B raw4448step0 raw4448step0Labels = mixedMoment B raw4448step1 raw4448step1Labels := by
      have ha : raw4448step1 = (fun i j => raw4448step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4448step1 raw4448step0; decide +kernel
      have hl : raw4448step1Labels = raw4448step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4448step0 raw4448step0Labels permutation145 permutation2
    mixedMoment B raw4448step1 raw4448step1Labels = mixedMoment B raw4448step2 raw4448step2Labels := by
      have ha : raw4448step2 = -raw4448step1 := by apply Matrix.ext; change ∀ i j, raw4448step2 i j = -(raw4448step1 i j); unfold raw4448step2 raw4448step1; decide +kernel
      have hl : raw4448step2Labels = raw4448step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw4449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4449step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4449step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4449step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4449step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4449 raw4449Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw4449 raw4449Labels = mixedMoment B raw4449step0 raw4449step0Labels := by
      have hz : ∀ j, raw4449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4449step0 = (fun i j => raw4449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4449step0 raw4449; decide +kernel
      have hl : raw4449step0Labels = raw4449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4449 raw4449Labels permutation346 hz
    mixedMoment B raw4449step0 raw4449step0Labels = mixedMoment B raw4449step1 raw4449step1Labels := by
      have hz : ∀ j, raw4449step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4449step1 = (fun i j => raw4449step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4449step1 raw4449step0; decide +kernel
      have hl : raw4449step1Labels = raw4449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4449step0 raw4449step0Labels permutation56 hz
    mixedMoment B raw4449step1 raw4449step1Labels = mixedMoment B raw4449step2 raw4449step2Labels := by
      have ha : raw4449step2 = (fun i j => raw4449step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4449step2 raw4449step1; decide +kernel
      have hl : raw4449step2Labels = raw4449step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4449step1 raw4449step1Labels permutation29 permutation2
    mixedMoment B raw4449step2 raw4449step2Labels = mixedMoment B raw4449step3 raw4449step3Labels := by
      have ha : raw4449step3 = -raw4449step2 := by apply Matrix.ext; change ∀ i j, raw4449step3 i j = -(raw4449step2 i j); unfold raw4449step3 raw4449step2; decide +kernel
      have hl : raw4449step3Labels = raw4449step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw4450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4450step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4450step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4450step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4450 raw4450Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw4450 raw4450Labels = mixedMoment B raw4450step0 raw4450step0Labels := by
      have hz : ∀ j, raw4450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4450step0 = (fun i j => raw4450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4450step0 raw4450; decide +kernel
      have hl : raw4450step0Labels = raw4450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4450 raw4450Labels permutation346 hz
    mixedMoment B raw4450step0 raw4450step0Labels = mixedMoment B raw4450step1 raw4450step1Labels := by
      have hz : ∀ j, raw4450step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4450step1 = (fun i j => raw4450step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4450step1 raw4450step0; decide +kernel
      have hl : raw4450step1Labels = raw4450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4450step0 raw4450step0Labels permutation56 hz
    mixedMoment B raw4450step1 raw4450step1Labels = mixedMoment B raw4450step2 raw4450step2Labels := by
      have ha : raw4450step2 = (fun i j => raw4450step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4450step2 raw4450step1; decide +kernel
      have hl : raw4450step2Labels = raw4450step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4450step1 raw4450step1Labels permutation28 permutation7
    mixedMoment B raw4450step2 raw4450step2Labels = mixedMoment B raw4450step3 raw4450step3Labels := by
      have ha : raw4450step3 = raw4450step2 := by apply Matrix.ext; unfold raw4450step3 raw4450step2; decide +kernel
      have hl : raw4450step2Labels = labelEmbedding10 ∘ raw4450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4450step2 raw4450step2Labels raw4450step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw4451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4451step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw4451step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4451step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw4451step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4451step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw4451step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4451 raw4451Labels = mixedMoment B node4508 node4508Labels := by
  calc
    mixedMoment B raw4451 raw4451Labels = mixedMoment B raw4451step0 raw4451step0Labels := by
      have hz : ∀ j, raw4451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4451step0 = (fun i j => raw4451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4451step0 raw4451; decide +kernel
      have hl : raw4451step0Labels = raw4451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4451 raw4451Labels permutation434 hz
    mixedMoment B raw4451step0 raw4451step0Labels = mixedMoment B raw4451step1 raw4451step1Labels := by
      have hz : ∀ j, raw4451step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4451step1 = (fun i j => raw4451step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4451step1 raw4451step0; decide +kernel
      have hl : raw4451step1Labels = raw4451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4451step0 raw4451step0Labels permutation80 hz
    mixedMoment B raw4451step1 raw4451step1Labels = mixedMoment B raw4451step2 raw4451step2Labels := by
      have hz : ∀ j, raw4451step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4451step2 = (fun i j => raw4451step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4451step2 raw4451step1; decide +kernel
      have hl : raw4451step2Labels = raw4451step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4451step1 raw4451step1Labels permutation14 hz
    mixedMoment B raw4451step2 raw4451step2Labels = mixedMoment B raw4451step3 raw4451step3Labels := by
      have ha : raw4451step3 = (fun i j => raw4451step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4451step3 raw4451step2; decide +kernel
      have hl : raw4451step3Labels = raw4451step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4451step2 raw4451step2Labels permutation2 permutation3
    mixedMoment B raw4451step3 raw4451step3Labels = mixedMoment B raw4451step4 raw4451step4Labels := by
      have ha : raw4451step4 = raw4451step3 := by apply Matrix.ext; unfold raw4451step4 raw4451step3; decide +kernel
      have hl : raw4451step3Labels = labelEmbedding6 ∘ raw4451step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4451step3 raw4451step3Labels raw4451step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4508 node4508Labels := by rfl

def raw4452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4452step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4452step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4452step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4452 raw4452Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw4452 raw4452Labels = mixedMoment B raw4452step0 raw4452step0Labels := by
      have hz : ∀ j, raw4452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4452step0 = (fun i j => raw4452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4452step0 raw4452; decide +kernel
      have hl : raw4452step0Labels = raw4452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4452 raw4452Labels permutation434 hz
    mixedMoment B raw4452step0 raw4452step0Labels = mixedMoment B raw4452step1 raw4452step1Labels := by
      have hz : ∀ j, raw4452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4452step1 = (fun i j => raw4452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4452step1 raw4452step0; decide +kernel
      have hl : raw4452step1Labels = raw4452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4452step0 raw4452step0Labels permutation80 hz
    mixedMoment B raw4452step1 raw4452step1Labels = mixedMoment B raw4452step2 raw4452step2Labels := by
      have ha : raw4452step2 = (fun i j => raw4452step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4452step2 raw4452step1; decide +kernel
      have hl : raw4452step2Labels = raw4452step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4452step1 raw4452step1Labels permutation31 permutation2
    mixedMoment B raw4452step2 raw4452step2Labels = mixedMoment B raw4452step3 raw4452step3Labels := by
      have ha : raw4452step3 = -raw4452step2 := by apply Matrix.ext; change ∀ i j, raw4452step3 i j = -(raw4452step2 i j); unfold raw4452step3 raw4452step2; decide +kernel
      have hl : raw4452step3Labels = raw4452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw4453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4453step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4453step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4453step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4453 raw4453Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw4453 raw4453Labels = mixedMoment B raw4453step0 raw4453step0Labels := by
      have hz : ∀ j, raw4453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4453step0 = (fun i j => raw4453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4453step0 raw4453; decide +kernel
      have hl : raw4453step0Labels = raw4453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4453 raw4453Labels permutation434 hz
    mixedMoment B raw4453step0 raw4453step0Labels = mixedMoment B raw4453step1 raw4453step1Labels := by
      have hz : ∀ j, raw4453step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4453step1 = (fun i j => raw4453step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4453step1 raw4453step0; decide +kernel
      have hl : raw4453step1Labels = raw4453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4453step0 raw4453step0Labels permutation56 hz
    mixedMoment B raw4453step1 raw4453step1Labels = mixedMoment B raw4453step2 raw4453step2Labels := by
      have ha : raw4453step2 = (fun i j => raw4453step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4453step2 raw4453step1; decide +kernel
      have hl : raw4453step2Labels = raw4453step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4453step1 raw4453step1Labels permutation31 permutation2
    mixedMoment B raw4453step2 raw4453step2Labels = mixedMoment B raw4453step3 raw4453step3Labels := by
      have ha : raw4453step3 = -raw4453step2 := by apply Matrix.ext; change ∀ i j, raw4453step3 i j = -(raw4453step2 i j); unfold raw4453step3 raw4453step2; decide +kernel
      have hl : raw4453step3Labels = raw4453step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw4454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4454step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4454step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4454 raw4454Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw4454 raw4454Labels = mixedMoment B raw4454step0 raw4454step0Labels := by
      have hz : ∀ j, raw4454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4454step0 = (fun i j => raw4454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4454step0 raw4454; decide +kernel
      have hl : raw4454step0Labels = raw4454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4454 raw4454Labels permutation346 hz
    mixedMoment B raw4454step0 raw4454step0Labels = mixedMoment B raw4454step1 raw4454step1Labels := by
      have hz : ∀ j, raw4454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4454step1 = (fun i j => raw4454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4454step1 raw4454step0; decide +kernel
      have hl : raw4454step1Labels = raw4454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4454step0 raw4454step0Labels permutation56 hz
    mixedMoment B raw4454step1 raw4454step1Labels = mixedMoment B raw4454step2 raw4454step2Labels := by
      have ha : raw4454step2 = (fun i j => raw4454step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4454step2 raw4454step1; decide +kernel
      have hl : raw4454step2Labels = raw4454step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4454step1 raw4454step1Labels permutation31 permutation2
    mixedMoment B raw4454step2 raw4454step2Labels = mixedMoment B raw4454step3 raw4454step3Labels := by
      have ha : raw4454step3 = -raw4454step2 := by apply Matrix.ext; change ∀ i j, raw4454step3 i j = -(raw4454step2 i j); unfold raw4454step3 raw4454step2; decide +kernel
      have hl : raw4454step3Labels = raw4454step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw4455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4455step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4455step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw4455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4455step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4455step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4455step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4455step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4455 raw4455Labels = mixedMoment B node5311 node5311Labels := by
  calc
    mixedMoment B raw4455 raw4455Labels = mixedMoment B raw4455step0 raw4455step0Labels := by
      have hz : ∀ j, raw4455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4455step0 = (fun i j => raw4455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4455step0 raw4455; decide +kernel
      have hl : raw4455step0Labels = raw4455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4455 raw4455Labels permutation434 hz
    mixedMoment B raw4455step0 raw4455step0Labels = mixedMoment B raw4455step1 raw4455step1Labels := by
      have hz : ∀ j, raw4455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4455step1 = (fun i j => raw4455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4455step1 raw4455step0; decide +kernel
      have hl : raw4455step1Labels = raw4455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4455step0 raw4455step0Labels permutation80 hz
    mixedMoment B raw4455step1 raw4455step1Labels = mixedMoment B raw4455step2 raw4455step2Labels := by
      have hz : ∀ j, raw4455step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4455step2 = (fun i j => raw4455step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4455step2 raw4455step1; decide +kernel
      have hl : raw4455step2Labels = raw4455step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4455step1 raw4455step1Labels permutation14 hz
    mixedMoment B raw4455step2 raw4455step2Labels = mixedMoment B raw4455step3 raw4455step3Labels := by
      have ha : raw4455step3 = (fun i j => raw4455step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4455step3 raw4455step2; decide +kernel
      have hl : raw4455step3Labels = raw4455step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4455step2 raw4455step2Labels permutation2 permutation3
    mixedMoment B raw4455step3 raw4455step3Labels = mixedMoment B raw4455step4 raw4455step4Labels := by
      have ha : raw4455step4 = raw4455step3 := by apply Matrix.ext; unfold raw4455step4 raw4455step3; decide +kernel
      have hl : raw4455step3Labels = labelEmbedding6 ∘ raw4455step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4455step3 raw4455step3Labels raw4455step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5311 node5311Labels := by rfl

def raw4456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4456step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![4, -1, -3]]
def raw4456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-4, 3, 1]]
def raw4456step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw4456step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4456 raw4456Labels = mixedMoment B node4481 node4481Labels := by
  calc
    mixedMoment B raw4456 raw4456Labels = mixedMoment B raw4456step0 raw4456step0Labels := by
      have hz : ∀ j, raw4456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4456step0 = (fun i j => raw4456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4456step0 raw4456; decide +kernel
      have hl : raw4456step0Labels = raw4456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4456 raw4456Labels permutation434 hz
    mixedMoment B raw4456step0 raw4456step0Labels = mixedMoment B raw4456step1 raw4456step1Labels := by
      have hz : ∀ j, raw4456step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4456step1 = (fun i j => raw4456step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4456step1 raw4456step0; decide +kernel
      have hl : raw4456step1Labels = raw4456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4456step0 raw4456step0Labels permutation80 hz
    mixedMoment B raw4456step1 raw4456step1Labels = mixedMoment B raw4456step2 raw4456step2Labels := by
      have hz : ∀ j, raw4456step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4456step2 = (fun i j => raw4456step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4456step2 raw4456step1; decide +kernel
      have hl : raw4456step2Labels = raw4456step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4456step1 raw4456step1Labels permutation14 hz
    mixedMoment B raw4456step2 raw4456step2Labels = mixedMoment B raw4456step3 raw4456step3Labels := by
      have ha : raw4456step3 = (fun i j => raw4456step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4456step3 raw4456step2; decide +kernel
      have hl : raw4456step3Labels = raw4456step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4456step2 raw4456step2Labels permutation7 permutation2
    mixedMoment B raw4456step3 raw4456step3Labels = mixedMoment B raw4456step4 raw4456step4Labels := by
      have ha : raw4456step4 = -raw4456step3 := by apply Matrix.ext; change ∀ i j, raw4456step4 i j = -(raw4456step3 i j); unfold raw4456step4 raw4456step3; decide +kernel
      have hl : raw4456step4Labels = raw4456step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4481 node4481Labels := by rfl

def raw4457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4457step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4457step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4457step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4457 raw4457Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw4457 raw4457Labels = mixedMoment B raw4457step0 raw4457step0Labels := by
      have hz : ∀ j, raw4457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4457step0 = (fun i j => raw4457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4457step0 raw4457; decide +kernel
      have hl : raw4457step0Labels = raw4457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4457 raw4457Labels permutation434 hz
    mixedMoment B raw4457step0 raw4457step0Labels = mixedMoment B raw4457step1 raw4457step1Labels := by
      have hz : ∀ j, raw4457step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4457step1 = (fun i j => raw4457step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4457step1 raw4457step0; decide +kernel
      have hl : raw4457step1Labels = raw4457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4457step0 raw4457step0Labels permutation80 hz
    mixedMoment B raw4457step1 raw4457step1Labels = mixedMoment B raw4457step2 raw4457step2Labels := by
      have ha : raw4457step2 = (fun i j => raw4457step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4457step2 raw4457step1; decide +kernel
      have hl : raw4457step2Labels = raw4457step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4457step1 raw4457step1Labels permutation31 permutation2
    mixedMoment B raw4457step2 raw4457step2Labels = mixedMoment B raw4457step3 raw4457step3Labels := by
      have ha : raw4457step3 = -raw4457step2 := by apply Matrix.ext; change ∀ i j, raw4457step3 i j = -(raw4457step2 i j); unfold raw4457step3 raw4457step2; decide +kernel
      have hl : raw4457step3Labels = raw4457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw4458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4458step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4458step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4458step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4458step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4458step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4458 raw4458Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw4458 raw4458Labels = mixedMoment B raw4458step0 raw4458step0Labels := by
      have hz : ∀ j, raw4458 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4458step0 = (fun i j => raw4458 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4458step0 raw4458; decide +kernel
      have hl : raw4458step0Labels = raw4458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4458 raw4458Labels permutation434 hz
    mixedMoment B raw4458step0 raw4458step0Labels = mixedMoment B raw4458step1 raw4458step1Labels := by
      have hz : ∀ j, raw4458step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4458step1 = (fun i j => raw4458step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4458step1 raw4458step0; decide +kernel
      have hl : raw4458step1Labels = raw4458step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4458step0 raw4458step0Labels permutation56 hz
    mixedMoment B raw4458step1 raw4458step1Labels = mixedMoment B raw4458step2 raw4458step2Labels := by
      have ha : raw4458step2 = (fun i j => raw4458step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4458step2 raw4458step1; decide +kernel
      have hl : raw4458step2Labels = raw4458step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4458step1 raw4458step1Labels permutation31 permutation2
    mixedMoment B raw4458step2 raw4458step2Labels = mixedMoment B raw4458step3 raw4458step3Labels := by
      have ha : raw4458step3 = -raw4458step2 := by apply Matrix.ext; change ∀ i j, raw4458step3 i j = -(raw4458step2 i j); unfold raw4458step3 raw4458step2; decide +kernel
      have hl : raw4458step3Labels = raw4458step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw4459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4459step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4459step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4459step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4459step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4459 raw4459Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw4459 raw4459Labels = mixedMoment B raw4459step0 raw4459step0Labels := by
      have hz : ∀ j, raw4459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4459step0 = (fun i j => raw4459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4459step0 raw4459; decide +kernel
      have hl : raw4459step0Labels = raw4459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4459 raw4459Labels permutation346 hz
    mixedMoment B raw4459step0 raw4459step0Labels = mixedMoment B raw4459step1 raw4459step1Labels := by
      have hz : ∀ j, raw4459step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4459step1 = (fun i j => raw4459step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4459step1 raw4459step0; decide +kernel
      have hl : raw4459step1Labels = raw4459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4459step0 raw4459step0Labels permutation56 hz
    mixedMoment B raw4459step1 raw4459step1Labels = mixedMoment B raw4459step2 raw4459step2Labels := by
      have ha : raw4459step2 = (fun i j => raw4459step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4459step2 raw4459step1; decide +kernel
      have hl : raw4459step2Labels = raw4459step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4459step1 raw4459step1Labels permutation31 permutation2
    mixedMoment B raw4459step2 raw4459step2Labels = mixedMoment B raw4459step3 raw4459step3Labels := by
      have ha : raw4459step3 = -raw4459step2 := by apply Matrix.ext; change ∀ i j, raw4459step3 i j = -(raw4459step2 i j); unfold raw4459step3 raw4459step2; decide +kernel
      have hl : raw4459step3Labels = raw4459step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw4460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw4460step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw4460step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw4460step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4460 raw4460Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw4460 raw4460Labels = mixedMoment B raw4460step0 raw4460step0Labels := by
      have hz : ∀ j, raw4460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4460step0 = (fun i j => raw4460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4460step0 raw4460; decide +kernel
      have hl : raw4460step0Labels = raw4460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4460 raw4460Labels permutation434 hz
    mixedMoment B raw4460step0 raw4460step0Labels = mixedMoment B raw4460step1 raw4460step1Labels := by
      have hz : ∀ j, raw4460step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4460step1 = (fun i j => raw4460step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4460step1 raw4460step0; decide +kernel
      have hl : raw4460step1Labels = raw4460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4460step0 raw4460step0Labels permutation80 hz
    mixedMoment B raw4460step1 raw4460step1Labels = mixedMoment B raw4460step2 raw4460step2Labels := by
      have hz : ∀ j, raw4460step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4460step2 = (fun i j => raw4460step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4460step2 raw4460step1; decide +kernel
      have hl : raw4460step2Labels = raw4460step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4460step1 raw4460step1Labels permutation14 hz
    mixedMoment B raw4460step2 raw4460step2Labels = mixedMoment B raw4460step3 raw4460step3Labels := by
      have ha : raw4460step3 = (fun i j => raw4460step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4460step3 raw4460step2; decide +kernel
      have hl : raw4460step3Labels = raw4460step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4460step2 raw4460step2Labels permutation7 permutation2
    mixedMoment B raw4460step3 raw4460step3Labels = mixedMoment B raw4460step4 raw4460step4Labels := by
      have ha : raw4460step4 = -raw4460step3 := by apply Matrix.ext; change ∀ i j, raw4460step4 i j = -(raw4460step3 i j); unfold raw4460step4 raw4460step3; decide +kernel
      have hl : raw4460step4Labels = raw4460step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw4461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4461step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4461step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4461step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw4461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4461step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw4461step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4461 raw4461Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw4461 raw4461Labels = mixedMoment B raw4461step0 raw4461step0Labels := by
      have hz : ∀ j, raw4461 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4461step0 = (fun i j => raw4461 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4461step0 raw4461; decide +kernel
      have hl : raw4461step0Labels = raw4461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4461 raw4461Labels permutation434 hz
    mixedMoment B raw4461step0 raw4461step0Labels = mixedMoment B raw4461step1 raw4461step1Labels := by
      have hz : ∀ j, raw4461step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4461step1 = (fun i j => raw4461step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4461step1 raw4461step0; decide +kernel
      have hl : raw4461step1Labels = raw4461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4461step0 raw4461step0Labels permutation80 hz
    mixedMoment B raw4461step1 raw4461step1Labels = mixedMoment B raw4461step2 raw4461step2Labels := by
      have ha : raw4461step2 = (fun i j => raw4461step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4461step2 raw4461step1; decide +kernel
      have hl : raw4461step2Labels = raw4461step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4461step1 raw4461step1Labels permutation31 permutation3
    mixedMoment B raw4461step2 raw4461step2Labels = mixedMoment B raw4461step3 raw4461step3Labels := by
      have ha : raw4461step3 = -raw4461step2 := by apply Matrix.ext; change ∀ i j, raw4461step3 i j = -(raw4461step2 i j); unfold raw4461step3 raw4461step2; decide +kernel
      have hl : raw4461step3Labels = raw4461step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw4462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4462step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4462step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4462step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4462step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw4462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4462step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw4462step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4462 raw4462Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw4462 raw4462Labels = mixedMoment B raw4462step0 raw4462step0Labels := by
      have hz : ∀ j, raw4462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4462step0 = (fun i j => raw4462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4462step0 raw4462; decide +kernel
      have hl : raw4462step0Labels = raw4462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4462 raw4462Labels permutation434 hz
    mixedMoment B raw4462step0 raw4462step0Labels = mixedMoment B raw4462step1 raw4462step1Labels := by
      have hz : ∀ j, raw4462step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4462step1 = (fun i j => raw4462step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4462step1 raw4462step0; decide +kernel
      have hl : raw4462step1Labels = raw4462step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4462step0 raw4462step0Labels permutation56 hz
    mixedMoment B raw4462step1 raw4462step1Labels = mixedMoment B raw4462step2 raw4462step2Labels := by
      have ha : raw4462step2 = (fun i j => raw4462step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4462step2 raw4462step1; decide +kernel
      have hl : raw4462step2Labels = raw4462step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4462step1 raw4462step1Labels permutation31 permutation3
    mixedMoment B raw4462step2 raw4462step2Labels = mixedMoment B raw4462step3 raw4462step3Labels := by
      have ha : raw4462step3 = -raw4462step2 := by apply Matrix.ext; change ∀ i j, raw4462step3 i j = -(raw4462step2 i j); unfold raw4462step3 raw4462step2; decide +kernel
      have hl : raw4462step3Labels = raw4462step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw4463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4463step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4463step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4463step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw4463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4463step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw4463step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4463 raw4463Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw4463 raw4463Labels = mixedMoment B raw4463step0 raw4463step0Labels := by
      have hz : ∀ j, raw4463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4463step0 = (fun i j => raw4463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4463step0 raw4463; decide +kernel
      have hl : raw4463step0Labels = raw4463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4463 raw4463Labels permutation346 hz
    mixedMoment B raw4463step0 raw4463step0Labels = mixedMoment B raw4463step1 raw4463step1Labels := by
      have hz : ∀ j, raw4463step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4463step1 = (fun i j => raw4463step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4463step1 raw4463step0; decide +kernel
      have hl : raw4463step1Labels = raw4463step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4463step0 raw4463step0Labels permutation56 hz
    mixedMoment B raw4463step1 raw4463step1Labels = mixedMoment B raw4463step2 raw4463step2Labels := by
      have ha : raw4463step2 = (fun i j => raw4463step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4463step2 raw4463step1; decide +kernel
      have hl : raw4463step2Labels = raw4463step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4463step1 raw4463step1Labels permutation31 permutation3
    mixedMoment B raw4463step2 raw4463step2Labels = mixedMoment B raw4463step3 raw4463step3Labels := by
      have ha : raw4463step3 = -raw4463step2 := by apply Matrix.ext; change ∀ i j, raw4463step3 i j = -(raw4463step2 i j); unfold raw4463step3 raw4463step2; decide +kernel
      have hl : raw4463step3Labels = raw4463step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw4464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4464step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4464step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4464step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw4464step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4464step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -3, 0], ![-1, 2, -1], ![-2, 1, 1]]
def raw4464step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4464step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw4464step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4464 raw4464Labels = mixedMoment B node3231 node3231Labels := by
  calc
    mixedMoment B raw4464 raw4464Labels = mixedMoment B raw4464step0 raw4464step0Labels := by
      have hz : ∀ j, raw4464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4464step0 = (fun i j => raw4464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4464step0 raw4464; decide +kernel
      have hl : raw4464step0Labels = raw4464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4464 raw4464Labels permutation434 hz
    mixedMoment B raw4464step0 raw4464step0Labels = mixedMoment B raw4464step1 raw4464step1Labels := by
      have hz : ∀ j, raw4464step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4464step1 = (fun i j => raw4464step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4464step1 raw4464step0; decide +kernel
      have hl : raw4464step1Labels = raw4464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4464step0 raw4464step0Labels permutation80 hz
    mixedMoment B raw4464step1 raw4464step1Labels = mixedMoment B raw4464step2 raw4464step2Labels := by
      have hz : ∀ j, raw4464step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4464step2 = (fun i j => raw4464step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4464step2 raw4464step1; decide +kernel
      have hl : raw4464step2Labels = raw4464step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4464step1 raw4464step1Labels permutation14 hz
    mixedMoment B raw4464step2 raw4464step2Labels = mixedMoment B raw4464step3 raw4464step3Labels := by
      have ha : raw4464step3 = (fun i j => raw4464step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4464step3 raw4464step2; decide +kernel
      have hl : raw4464step3Labels = raw4464step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4464step2 raw4464step2Labels permutation7 permutation3
    mixedMoment B raw4464step3 raw4464step3Labels = mixedMoment B raw4464step4 raw4464step4Labels := by
      have ha : raw4464step4 = -raw4464step3 := by apply Matrix.ext; change ∀ i j, raw4464step4 i j = -(raw4464step3 i j); unfold raw4464step4 raw4464step3; decide +kernel
      have hl : raw4464step4Labels = raw4464step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3231 node3231Labels := by rfl

def raw4465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4465step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4465step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4465step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw4465step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4465step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw4465step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4465 raw4465Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw4465 raw4465Labels = mixedMoment B raw4465step0 raw4465step0Labels := by
      have hz : ∀ j, raw4465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4465step0 = (fun i j => raw4465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4465step0 raw4465; decide +kernel
      have hl : raw4465step0Labels = raw4465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4465 raw4465Labels permutation434 hz
    mixedMoment B raw4465step0 raw4465step0Labels = mixedMoment B raw4465step1 raw4465step1Labels := by
      have hz : ∀ j, raw4465step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4465step1 = (fun i j => raw4465step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4465step1 raw4465step0; decide +kernel
      have hl : raw4465step1Labels = raw4465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4465step0 raw4465step0Labels permutation80 hz
    mixedMoment B raw4465step1 raw4465step1Labels = mixedMoment B raw4465step2 raw4465step2Labels := by
      have hz : ∀ j, raw4465step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4465step2 = (fun i j => raw4465step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4465step2 raw4465step1; decide +kernel
      have hl : raw4465step2Labels = raw4465step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4465step1 raw4465step1Labels permutation14 hz
    mixedMoment B raw4465step2 raw4465step2Labels = mixedMoment B raw4465step3 raw4465step3Labels := by
      have ha : raw4465step3 = (fun i j => raw4465step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4465step3 raw4465step2; decide +kernel
      have hl : raw4465step3Labels = raw4465step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4465step2 raw4465step2Labels permutation6 permutation6
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw4466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4466step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4466 raw4466Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw4466 raw4466Labels = mixedMoment B raw4466step0 raw4466step0Labels := by
      have hz : ∀ j, raw4466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4466step0 = (fun i j => raw4466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4466step0 raw4466; decide +kernel
      have hl : raw4466step0Labels = raw4466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4466 raw4466Labels permutation434 hz
    mixedMoment B raw4466step0 raw4466step0Labels = mixedMoment B raw4466step1 raw4466step1Labels := by
      have hz : ∀ j, raw4466step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4466step1 = (fun i j => raw4466step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4466step1 raw4466step0; decide +kernel
      have hl : raw4466step1Labels = raw4466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4466step0 raw4466step0Labels permutation80 hz
    mixedMoment B raw4466step1 raw4466step1Labels = mixedMoment B raw4466step2 raw4466step2Labels := by
      have ha : raw4466step2 = (fun i j => raw4466step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4466step2 raw4466step1; decide +kernel
      have hl : raw4466step2Labels = raw4466step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4466step1 raw4466step1Labels permutation10 permutation3
    _ = mixedMoment B node1061 node1061Labels := by rfl

def raw4467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4467 raw4467Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw4467 raw4467Labels = mixedMoment B raw4467step0 raw4467step0Labels := by
      have hz : ∀ j, raw4467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4467step0 = (fun i j => raw4467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4467step0 raw4467; decide +kernel
      have hl : raw4467step0Labels = raw4467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4467 raw4467Labels permutation434 hz
    mixedMoment B raw4467step0 raw4467step0Labels = mixedMoment B raw4467step1 raw4467step1Labels := by
      have ha : raw4467step1 = (fun i j => raw4467step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4467step1 raw4467step0; decide +kernel
      have hl : raw4467step1Labels = raw4467step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4467step0 raw4467step0Labels permutation40 permutation3
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw4468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4468 raw4468Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw4468 raw4468Labels = mixedMoment B raw4468step0 raw4468step0Labels := by
      have hz : ∀ j, raw4468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4468step0 = (fun i j => raw4468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4468step0 raw4468; decide +kernel
      have hl : raw4468step0Labels = raw4468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4468 raw4468Labels permutation346 hz
    mixedMoment B raw4468step0 raw4468step0Labels = mixedMoment B raw4468step1 raw4468step1Labels := by
      have ha : raw4468step1 = (fun i j => raw4468step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4468step1 raw4468step0; decide +kernel
      have hl : raw4468step1Labels = raw4468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4468step0 raw4468step0Labels permutation40 permutation3
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw4469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4469step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4469step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4469 raw4469Labels = mixedMoment B node2642 node2642Labels := by
  calc
    mixedMoment B raw4469 raw4469Labels = mixedMoment B raw4469step0 raw4469step0Labels := by
      have hz : ∀ j, raw4469 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4469step0 = (fun i j => raw4469 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4469step0 raw4469; decide +kernel
      have hl : raw4469step0Labels = raw4469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4469 raw4469Labels permutation434 hz
    mixedMoment B raw4469step0 raw4469step0Labels = mixedMoment B raw4469step1 raw4469step1Labels := by
      have hz : ∀ j, raw4469step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4469step1 = (fun i j => raw4469step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4469step1 raw4469step0; decide +kernel
      have hl : raw4469step1Labels = raw4469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4469step0 raw4469step0Labels permutation80 hz
    mixedMoment B raw4469step1 raw4469step1Labels = mixedMoment B raw4469step2 raw4469step2Labels := by
      have ha : raw4469step2 = (fun i j => raw4469step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4469step2 raw4469step1; decide +kernel
      have hl : raw4469step2Labels = raw4469step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4469step1 raw4469step1Labels permutation10 permutation3
    _ = mixedMoment B node2642 node2642Labels := by rfl

def raw4470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4470step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4470step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4470step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw4470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4470 raw4470Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw4470 raw4470Labels = mixedMoment B raw4470step0 raw4470step0Labels := by
      have hz : ∀ j, raw4470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4470step0 = (fun i j => raw4470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4470step0 raw4470; decide +kernel
      have hl : raw4470step0Labels = raw4470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4470 raw4470Labels permutation434 hz
    mixedMoment B raw4470step0 raw4470step0Labels = mixedMoment B raw4470step1 raw4470step1Labels := by
      have hz : ∀ j, raw4470step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4470step1 = (fun i j => raw4470step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4470step1 raw4470step0; decide +kernel
      have hl : raw4470step1Labels = raw4470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4470step0 raw4470step0Labels permutation80 hz
    mixedMoment B raw4470step1 raw4470step1Labels = mixedMoment B raw4470step2 raw4470step2Labels := by
      have ha : raw4470step2 = (fun i j => raw4470step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4470step2 raw4470step1; decide +kernel
      have hl : raw4470step2Labels = raw4470step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4470step1 raw4470step1Labels permutation10 permutation3
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw4471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4471Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4471step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4471step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4471 raw4471Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw4471 raw4471Labels = mixedMoment B raw4471step0 raw4471step0Labels := by
      have hz : ∀ j, raw4471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4471step0 = (fun i j => raw4471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4471step0 raw4471; decide +kernel
      have hl : raw4471step0Labels = raw4471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4471 raw4471Labels permutation434 hz
    mixedMoment B raw4471step0 raw4471step0Labels = mixedMoment B raw4471step1 raw4471step1Labels := by
      have hz : ∀ j, raw4471step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4471step1 = (fun i j => raw4471step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4471step1 raw4471step0; decide +kernel
      have hl : raw4471step1Labels = raw4471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4471step0 raw4471step0Labels permutation56 hz
    mixedMoment B raw4471step1 raw4471step1Labels = mixedMoment B raw4471step2 raw4471step2Labels := by
      have ha : raw4471step2 = (fun i j => raw4471step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4471step2 raw4471step1; decide +kernel
      have hl : raw4471step2Labels = raw4471step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4471step1 raw4471step1Labels permutation10 permutation3
    _ = mixedMoment B node1061 node1061Labels := by rfl

def raw4472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4472step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4472 raw4472Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw4472 raw4472Labels = mixedMoment B raw4472step0 raw4472step0Labels := by
      have hz : ∀ j, raw4472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4472step0 = (fun i j => raw4472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4472step0 raw4472; decide +kernel
      have hl : raw4472step0Labels = raw4472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4472 raw4472Labels permutation434 hz
    mixedMoment B raw4472step0 raw4472step0Labels = mixedMoment B raw4472step1 raw4472step1Labels := by
      have ha : raw4472step1 = (fun i j => raw4472step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4472step1 raw4472step0; decide +kernel
      have hl : raw4472step1Labels = raw4472step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4472step0 raw4472step0Labels permutation34 permutation3
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw4473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4473step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4473 raw4473Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw4473 raw4473Labels = mixedMoment B raw4473step0 raw4473step0Labels := by
      have hz : ∀ j, raw4473 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4473step0 = (fun i j => raw4473 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4473step0 raw4473; decide +kernel
      have hl : raw4473step0Labels = raw4473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4473 raw4473Labels permutation265 hz
    mixedMoment B raw4473step0 raw4473step0Labels = mixedMoment B raw4473step1 raw4473step1Labels := by
      have ha : raw4473step1 = (fun i j => raw4473step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4473step1 raw4473step0; decide +kernel
      have hl : raw4473step1Labels = raw4473step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4473step0 raw4473step0Labels permutation40 permutation3
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw4474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4474step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4474step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4474 raw4474Labels = mixedMoment B node2642 node2642Labels := by
  calc
    mixedMoment B raw4474 raw4474Labels = mixedMoment B raw4474step0 raw4474step0Labels := by
      have hz : ∀ j, raw4474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4474step0 = (fun i j => raw4474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4474step0 raw4474; decide +kernel
      have hl : raw4474step0Labels = raw4474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4474 raw4474Labels permutation434 hz
    mixedMoment B raw4474step0 raw4474step0Labels = mixedMoment B raw4474step1 raw4474step1Labels := by
      have hz : ∀ j, raw4474step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4474step1 = (fun i j => raw4474step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4474step1 raw4474step0; decide +kernel
      have hl : raw4474step1Labels = raw4474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4474step0 raw4474step0Labels permutation56 hz
    mixedMoment B raw4474step1 raw4474step1Labels = mixedMoment B raw4474step2 raw4474step2Labels := by
      have ha : raw4474step2 = (fun i j => raw4474step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4474step2 raw4474step1; decide +kernel
      have hl : raw4474step2Labels = raw4474step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4474step1 raw4474step1Labels permutation10 permutation3
    _ = mixedMoment B node2642 node2642Labels := by rfl

def raw4475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4475step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4475step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw4475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4475 raw4475Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw4475 raw4475Labels = mixedMoment B raw4475step0 raw4475step0Labels := by
      have hz : ∀ j, raw4475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4475step0 = (fun i j => raw4475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4475step0 raw4475; decide +kernel
      have hl : raw4475step0Labels = raw4475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4475 raw4475Labels permutation434 hz
    mixedMoment B raw4475step0 raw4475step0Labels = mixedMoment B raw4475step1 raw4475step1Labels := by
      have hz : ∀ j, raw4475step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4475step1 = (fun i j => raw4475step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4475step1 raw4475step0; decide +kernel
      have hl : raw4475step1Labels = raw4475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4475step0 raw4475step0Labels permutation56 hz
    mixedMoment B raw4475step1 raw4475step1Labels = mixedMoment B raw4475step2 raw4475step2Labels := by
      have ha : raw4475step2 = (fun i j => raw4475step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4475step2 raw4475step1; decide +kernel
      have hl : raw4475step2Labels = raw4475step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4475step1 raw4475step1Labels permutation10 permutation3
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw4476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4476step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4476step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4476step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4476 raw4476Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw4476 raw4476Labels = mixedMoment B raw4476step0 raw4476step0Labels := by
      have hz : ∀ j, raw4476 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4476step0 = (fun i j => raw4476 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4476step0 raw4476; decide +kernel
      have hl : raw4476step0Labels = raw4476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4476 raw4476Labels permutation346 hz
    mixedMoment B raw4476step0 raw4476step0Labels = mixedMoment B raw4476step1 raw4476step1Labels := by
      have hz : ∀ j, raw4476step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4476step1 = (fun i j => raw4476step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4476step1 raw4476step0; decide +kernel
      have hl : raw4476step1Labels = raw4476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4476step0 raw4476step0Labels permutation56 hz
    mixedMoment B raw4476step1 raw4476step1Labels = mixedMoment B raw4476step2 raw4476step2Labels := by
      have ha : raw4476step2 = (fun i j => raw4476step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4476step2 raw4476step1; decide +kernel
      have hl : raw4476step2Labels = raw4476step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4476step1 raw4476step1Labels permutation10 permutation3
    _ = mixedMoment B node1061 node1061Labels := by rfl

def raw4477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4477 raw4477Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw4477 raw4477Labels = mixedMoment B raw4477step0 raw4477step0Labels := by
      have hz : ∀ j, raw4477 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4477step0 = (fun i j => raw4477 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4477step0 raw4477; decide +kernel
      have hl : raw4477step0Labels = raw4477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4477 raw4477Labels permutation346 hz
    mixedMoment B raw4477step0 raw4477step0Labels = mixedMoment B raw4477step1 raw4477step1Labels := by
      have ha : raw4477step1 = (fun i j => raw4477step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4477step1 raw4477step0; decide +kernel
      have hl : raw4477step1Labels = raw4477step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4477step0 raw4477step0Labels permutation34 permutation3
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw4478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4478 raw4478Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw4478 raw4478Labels = mixedMoment B raw4478step0 raw4478step0Labels := by
      have hz : ∀ j, raw4478 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4478step0 = (fun i j => raw4478 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4478step0 raw4478; decide +kernel
      have hl : raw4478step0Labels = raw4478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4478 raw4478Labels permutation265 hz
    mixedMoment B raw4478step0 raw4478step0Labels = mixedMoment B raw4478step1 raw4478step1Labels := by
      have ha : raw4478step1 = (fun i j => raw4478step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4478step1 raw4478step0; decide +kernel
      have hl : raw4478step1Labels = raw4478step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4478step0 raw4478step0Labels permutation34 permutation3
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw4479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4479step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4479 raw4479Labels = mixedMoment B node2642 node2642Labels := by
  calc
    mixedMoment B raw4479 raw4479Labels = mixedMoment B raw4479step0 raw4479step0Labels := by
      have hz : ∀ j, raw4479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4479step0 = (fun i j => raw4479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4479step0 raw4479; decide +kernel
      have hl : raw4479step0Labels = raw4479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4479 raw4479Labels permutation346 hz
    mixedMoment B raw4479step0 raw4479step0Labels = mixedMoment B raw4479step1 raw4479step1Labels := by
      have hz : ∀ j, raw4479step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4479step1 = (fun i j => raw4479step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4479step1 raw4479step0; decide +kernel
      have hl : raw4479step1Labels = raw4479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4479step0 raw4479step0Labels permutation56 hz
    mixedMoment B raw4479step1 raw4479step1Labels = mixedMoment B raw4479step2 raw4479step2Labels := by
      have ha : raw4479step2 = (fun i j => raw4479step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4479step2 raw4479step1; decide +kernel
      have hl : raw4479step2Labels = raw4479step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4479step1 raw4479step1Labels permutation10 permutation3
    _ = mixedMoment B node2642 node2642Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
