import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28288step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28288step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28288 raw28288Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw28288 raw28288Labels = mixedMoment B raw28288step0 raw28288step0Labels := by
      have hz : ∀ j, raw28288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28288step0 = (fun i j => raw28288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28288step0 raw28288; decide +kernel
      have hl : raw28288step0Labels = raw28288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28288 raw28288Labels permutation434 hz
    mixedMoment B raw28288step0 raw28288step0Labels = mixedMoment B raw28288step1 raw28288step1Labels := by
      have ha : raw28288step1 = (fun i j => raw28288step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28288step1 raw28288step0; decide +kernel
      have hl : raw28288step1Labels = raw28288step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28288step0 raw28288step0Labels permutation34 permutation3
    mixedMoment B raw28288step1 raw28288step1Labels = mixedMoment B raw28288step2 raw28288step2Labels := by
      have ha : raw28288step2 = raw28288step1 := by apply Matrix.ext; unfold raw28288step2 raw28288step1; decide +kernel
      have hl : raw28288step1Labels = labelEmbedding6 ∘ raw28288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28288step1 raw28288step1Labels raw28288step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw28289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28289 raw28289Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw28289 raw28289Labels = mixedMoment B raw28289step0 raw28289step0Labels := by
      have ha : raw28289step0 = (fun i j => raw28289 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28289step0 raw28289; decide +kernel
      have hl : raw28289step0Labels = raw28289Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28289 raw28289Labels permutation682 permutation2
    mixedMoment B raw28289step0 raw28289step0Labels = mixedMoment B raw28289step1 raw28289step1Labels := by
      have ha : raw28289step1 = -raw28289step0 := by apply Matrix.ext; change ∀ i j, raw28289step1 i j = -(raw28289step0 i j); unfold raw28289step1 raw28289step0; decide +kernel
      have hl : raw28289step1Labels = raw28289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5034 node5034Labels := by rfl

def raw28290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28290step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28290 raw28290Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw28290 raw28290Labels = mixedMoment B raw28290step0 raw28290step0Labels := by
      have hz : ∀ j, raw28290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28290step0 = (fun i j => raw28290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28290step0 raw28290; decide +kernel
      have hl : raw28290step0Labels = raw28290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28290 raw28290Labels permutation434 hz
    mixedMoment B raw28290step0 raw28290step0Labels = mixedMoment B raw28290step1 raw28290step1Labels := by
      have ha : raw28290step1 = (fun i j => raw28290step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28290step1 raw28290step0; decide +kernel
      have hl : raw28290step1Labels = raw28290step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28290step0 raw28290step0Labels permutation145 permutation2
    mixedMoment B raw28290step1 raw28290step1Labels = mixedMoment B raw28290step2 raw28290step2Labels := by
      have ha : raw28290step2 = -raw28290step1 := by apply Matrix.ext; change ∀ i j, raw28290step2 i j = -(raw28290step1 i j); unfold raw28290step2 raw28290step1; decide +kernel
      have hl : raw28290step2Labels = raw28290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw28291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28291step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28291 raw28291Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw28291 raw28291Labels = mixedMoment B raw28291step0 raw28291step0Labels := by
      have hz : ∀ j, raw28291 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28291step0 = (fun i j => raw28291 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28291step0 raw28291; decide +kernel
      have hl : raw28291step0Labels = raw28291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28291 raw28291Labels permutation434 hz
    mixedMoment B raw28291step0 raw28291step0Labels = mixedMoment B raw28291step1 raw28291step1Labels := by
      have ha : raw28291step1 = (fun i j => raw28291step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28291step1 raw28291step0; decide +kernel
      have hl : raw28291step1Labels = raw28291step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28291step0 raw28291step0Labels permutation34 permutation3
    mixedMoment B raw28291step1 raw28291step1Labels = mixedMoment B raw28291step2 raw28291step2Labels := by
      have ha : raw28291step2 = raw28291step1 := by apply Matrix.ext; unfold raw28291step2 raw28291step1; decide +kernel
      have hl : raw28291step1Labels = labelEmbedding6 ∘ raw28291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28291step1 raw28291step1Labels raw28291step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw28292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28292step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28292step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28292 raw28292Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw28292 raw28292Labels = mixedMoment B raw28292step0 raw28292step0Labels := by
      have hz : ∀ j, raw28292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28292step0 = (fun i j => raw28292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28292step0 raw28292; decide +kernel
      have hl : raw28292step0Labels = raw28292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28292 raw28292Labels permutation346 hz
    mixedMoment B raw28292step0 raw28292step0Labels = mixedMoment B raw28292step1 raw28292step1Labels := by
      have ha : raw28292step1 = (fun i j => raw28292step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28292step1 raw28292step0; decide +kernel
      have hl : raw28292step1Labels = raw28292step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28292step0 raw28292step0Labels permutation34 permutation3
    mixedMoment B raw28292step1 raw28292step1Labels = mixedMoment B raw28292step2 raw28292step2Labels := by
      have ha : raw28292step2 = raw28292step1 := by apply Matrix.ext; unfold raw28292step2 raw28292step1; decide +kernel
      have hl : raw28292step1Labels = labelEmbedding6 ∘ raw28292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28292step1 raw28292step1Labels raw28292step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4367 node4367Labels := by rfl

def raw28293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28293step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28293 raw28293Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw28293 raw28293Labels = mixedMoment B raw28293step0 raw28293step0Labels := by
      have hz : ∀ j, raw28293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28293step0 = (fun i j => raw28293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28293step0 raw28293; decide +kernel
      have hl : raw28293step0Labels = raw28293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28293 raw28293Labels permutation346 hz
    mixedMoment B raw28293step0 raw28293step0Labels = mixedMoment B raw28293step1 raw28293step1Labels := by
      have ha : raw28293step1 = (fun i j => raw28293step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28293step1 raw28293step0; decide +kernel
      have hl : raw28293step1Labels = raw28293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28293step0 raw28293step0Labels permutation34 permutation3
    mixedMoment B raw28293step1 raw28293step1Labels = mixedMoment B raw28293step2 raw28293step2Labels := by
      have ha : raw28293step2 = raw28293step1 := by apply Matrix.ext; unfold raw28293step2 raw28293step1; decide +kernel
      have hl : raw28293step1Labels = labelEmbedding6 ∘ raw28293step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28293step1 raw28293step1Labels raw28293step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw28294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28294 raw28294Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw28294 raw28294Labels = mixedMoment B raw28294step0 raw28294step0Labels := by
      have ha : raw28294step0 = (fun i j => raw28294 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28294step0 raw28294; decide +kernel
      have hl : raw28294step0Labels = raw28294Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28294 raw28294Labels permutation688 permutation2
    mixedMoment B raw28294step0 raw28294step0Labels = mixedMoment B raw28294step1 raw28294step1Labels := by
      have ha : raw28294step1 = -raw28294step0 := by apply Matrix.ext; change ∀ i j, raw28294step1 i j = -(raw28294step0 i j); unfold raw28294step1 raw28294step0; decide +kernel
      have hl : raw28294step1Labels = raw28294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5034 node5034Labels := by rfl

def raw28295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28295 raw28295Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw28295 raw28295Labels = mixedMoment B raw28295step0 raw28295step0Labels := by
      have hz : ∀ j, raw28295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28295step0 = (fun i j => raw28295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28295step0 raw28295; decide +kernel
      have hl : raw28295step0Labels = raw28295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28295 raw28295Labels permutation346 hz
    mixedMoment B raw28295step0 raw28295step0Labels = mixedMoment B raw28295step1 raw28295step1Labels := by
      have ha : raw28295step1 = (fun i j => raw28295step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28295step1 raw28295step0; decide +kernel
      have hl : raw28295step1Labels = raw28295step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28295step0 raw28295step0Labels permutation145 permutation2
    mixedMoment B raw28295step1 raw28295step1Labels = mixedMoment B raw28295step2 raw28295step2Labels := by
      have ha : raw28295step2 = -raw28295step1 := by apply Matrix.ext; change ∀ i j, raw28295step2 i j = -(raw28295step1 i j); unfold raw28295step2 raw28295step1; decide +kernel
      have hl : raw28295step2Labels = raw28295step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw28296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28296step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28296step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28296 raw28296Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw28296 raw28296Labels = mixedMoment B raw28296step0 raw28296step0Labels := by
      have hz : ∀ j, raw28296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28296step0 = (fun i j => raw28296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28296step0 raw28296; decide +kernel
      have hl : raw28296step0Labels = raw28296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28296 raw28296Labels permutation346 hz
    mixedMoment B raw28296step0 raw28296step0Labels = mixedMoment B raw28296step1 raw28296step1Labels := by
      have ha : raw28296step1 = (fun i j => raw28296step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28296step1 raw28296step0; decide +kernel
      have hl : raw28296step1Labels = raw28296step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28296step0 raw28296step0Labels permutation34 permutation3
    mixedMoment B raw28296step1 raw28296step1Labels = mixedMoment B raw28296step2 raw28296step2Labels := by
      have ha : raw28296step2 = raw28296step1 := by apply Matrix.ext; unfold raw28296step2 raw28296step1; decide +kernel
      have hl : raw28296step1Labels = labelEmbedding6 ∘ raw28296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28296step1 raw28296step1Labels raw28296step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw28297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw28297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28297step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28297step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28297 raw28297Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw28297 raw28297Labels = mixedMoment B raw28297step0 raw28297step0Labels := by
      have hz : ∀ j, raw28297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28297step0 = (fun i j => raw28297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28297step0 raw28297; decide +kernel
      have hl : raw28297step0Labels = raw28297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28297 raw28297Labels permutation434 hz
    mixedMoment B raw28297step0 raw28297step0Labels = mixedMoment B raw28297step1 raw28297step1Labels := by
      have hz : ∀ j, raw28297step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28297step1 = (fun i j => raw28297step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28297step1 raw28297step0; decide +kernel
      have hl : raw28297step1Labels = raw28297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28297step0 raw28297step0Labels permutation80 hz
    mixedMoment B raw28297step1 raw28297step1Labels = mixedMoment B raw28297step2 raw28297step2Labels := by
      have ha : raw28297step2 = (fun i j => raw28297step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28297step2 raw28297step1; decide +kernel
      have hl : raw28297step2Labels = raw28297step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28297step1 raw28297step1Labels permutation8 permutation3
    mixedMoment B raw28297step2 raw28297step2Labels = mixedMoment B raw28297step3 raw28297step3Labels := by
      have ha : raw28297step3 = raw28297step2 := by apply Matrix.ext; unfold raw28297step3 raw28297step2; decide +kernel
      have hl : raw28297step2Labels = labelEmbedding6 ∘ raw28297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28297step2 raw28297step2Labels raw28297step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4374 node4374Labels := by rfl

def raw28298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![3, -1, -2]]
def raw28298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28298step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28298step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw28298step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28298 raw28298Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw28298 raw28298Labels = mixedMoment B raw28298step0 raw28298step0Labels := by
      have hz : ∀ j, raw28298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28298step0 = (fun i j => raw28298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28298step0 raw28298; decide +kernel
      have hl : raw28298step0Labels = raw28298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28298 raw28298Labels permutation434 hz
    mixedMoment B raw28298step0 raw28298step0Labels = mixedMoment B raw28298step1 raw28298step1Labels := by
      have hz : ∀ j, raw28298step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28298step1 = (fun i j => raw28298step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28298step1 raw28298step0; decide +kernel
      have hl : raw28298step1Labels = raw28298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28298step0 raw28298step0Labels permutation80 hz
    mixedMoment B raw28298step1 raw28298step1Labels = mixedMoment B raw28298step2 raw28298step2Labels := by
      have ha : raw28298step2 = (fun i j => raw28298step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28298step2 raw28298step1; decide +kernel
      have hl : raw28298step2Labels = raw28298step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28298step1 raw28298step1Labels permutation31 permutation2
    mixedMoment B raw28298step2 raw28298step2Labels = mixedMoment B raw28298step3 raw28298step3Labels := by
      have ha : raw28298step3 = -raw28298step2 := by apply Matrix.ext; change ∀ i j, raw28298step3 i j = -(raw28298step2 i j); unfold raw28298step3 raw28298step2; decide +kernel
      have hl : raw28298step3Labels = raw28298step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4953 node4953Labels := by rfl

def raw28299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28299step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28299 raw28299Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw28299 raw28299Labels = mixedMoment B raw28299step0 raw28299step0Labels := by
      have hz : ∀ j, raw28299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28299step0 = (fun i j => raw28299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28299step0 raw28299; decide +kernel
      have hl : raw28299step0Labels = raw28299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28299 raw28299Labels permutation434 hz
    mixedMoment B raw28299step0 raw28299step0Labels = mixedMoment B raw28299step1 raw28299step1Labels := by
      have ha : raw28299step1 = (fun i j => raw28299step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28299step1 raw28299step0; decide +kernel
      have hl : raw28299step1Labels = raw28299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28299step0 raw28299step0Labels permutation151 permutation2
    mixedMoment B raw28299step1 raw28299step1Labels = mixedMoment B raw28299step2 raw28299step2Labels := by
      have ha : raw28299step2 = -raw28299step1 := by apply Matrix.ext; change ∀ i j, raw28299step2 i j = -(raw28299step1 i j); unfold raw28299step2 raw28299step1; decide +kernel
      have hl : raw28299step2Labels = raw28299step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw28300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28300step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28300 raw28300Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw28300 raw28300Labels = mixedMoment B raw28300step0 raw28300step0Labels := by
      have hz : ∀ j, raw28300 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28300step0 = (fun i j => raw28300 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28300step0 raw28300; decide +kernel
      have hl : raw28300step0Labels = raw28300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28300 raw28300Labels permutation346 hz
    mixedMoment B raw28300step0 raw28300step0Labels = mixedMoment B raw28300step1 raw28300step1Labels := by
      have ha : raw28300step1 = (fun i j => raw28300step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28300step1 raw28300step0; decide +kernel
      have hl : raw28300step1Labels = raw28300step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28300step0 raw28300step0Labels permutation151 permutation2
    mixedMoment B raw28300step1 raw28300step1Labels = mixedMoment B raw28300step2 raw28300step2Labels := by
      have ha : raw28300step2 = -raw28300step1 := by apply Matrix.ext; change ∀ i j, raw28300step2 i j = -(raw28300step1 i j); unfold raw28300step2 raw28300step1; decide +kernel
      have hl : raw28300step2Labels = raw28300step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw28301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw28301step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28301step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw28301step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28301 raw28301Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw28301 raw28301Labels = mixedMoment B raw28301step0 raw28301step0Labels := by
      have hz : ∀ j, raw28301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28301step0 = (fun i j => raw28301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28301step0 raw28301; decide +kernel
      have hl : raw28301step0Labels = raw28301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28301 raw28301Labels permutation434 hz
    mixedMoment B raw28301step0 raw28301step0Labels = mixedMoment B raw28301step1 raw28301step1Labels := by
      have hz : ∀ j, raw28301step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28301step1 = (fun i j => raw28301step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28301step1 raw28301step0; decide +kernel
      have hl : raw28301step1Labels = raw28301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28301step0 raw28301step0Labels permutation80 hz
    mixedMoment B raw28301step1 raw28301step1Labels = mixedMoment B raw28301step2 raw28301step2Labels := by
      have ha : raw28301step2 = (fun i j => raw28301step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28301step2 raw28301step1; decide +kernel
      have hl : raw28301step2Labels = raw28301step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28301step1 raw28301step1Labels permutation9 permutation3
    mixedMoment B raw28301step2 raw28301step2Labels = mixedMoment B raw28301step3 raw28301step3Labels := by
      have ha : raw28301step3 = raw28301step2 := by apply Matrix.ext; unfold raw28301step3 raw28301step2; decide +kernel
      have hl : raw28301step2Labels = labelEmbedding6 ∘ raw28301step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28301step2 raw28301step2Labels raw28301step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw28302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw28302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw28302step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw28302step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28302 raw28302Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw28302 raw28302Labels = mixedMoment B raw28302step0 raw28302step0Labels := by
      have hz : ∀ j, raw28302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28302step0 = (fun i j => raw28302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28302step0 raw28302; decide +kernel
      have hl : raw28302step0Labels = raw28302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28302 raw28302Labels permutation434 hz
    mixedMoment B raw28302step0 raw28302step0Labels = mixedMoment B raw28302step1 raw28302step1Labels := by
      have hz : ∀ j, raw28302step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28302step1 = (fun i j => raw28302step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28302step1 raw28302step0; decide +kernel
      have hl : raw28302step1Labels = raw28302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28302step0 raw28302step0Labels permutation80 hz
    mixedMoment B raw28302step1 raw28302step1Labels = mixedMoment B raw28302step2 raw28302step2Labels := by
      have ha : raw28302step2 = (fun i j => raw28302step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28302step2 raw28302step1; decide +kernel
      have hl : raw28302step2Labels = raw28302step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28302step1 raw28302step1Labels permutation8 permutation3
    mixedMoment B raw28302step2 raw28302step2Labels = mixedMoment B raw28302step3 raw28302step3Labels := by
      have ha : raw28302step3 = raw28302step2 := by apply Matrix.ext; unfold raw28302step3 raw28302step2; decide +kernel
      have hl : raw28302step2Labels = labelEmbedding6 ∘ raw28302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28302step2 raw28302step2Labels raw28302step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4370 node4370Labels := by rfl

def raw28303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![4, -2, -2]]
def raw28303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28303step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28303step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw28303step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28303 raw28303Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw28303 raw28303Labels = mixedMoment B raw28303step0 raw28303step0Labels := by
      have hz : ∀ j, raw28303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28303step0 = (fun i j => raw28303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28303step0 raw28303; decide +kernel
      have hl : raw28303step0Labels = raw28303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28303 raw28303Labels permutation434 hz
    mixedMoment B raw28303step0 raw28303step0Labels = mixedMoment B raw28303step1 raw28303step1Labels := by
      have hz : ∀ j, raw28303step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28303step1 = (fun i j => raw28303step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28303step1 raw28303step0; decide +kernel
      have hl : raw28303step1Labels = raw28303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28303step0 raw28303step0Labels permutation80 hz
    mixedMoment B raw28303step1 raw28303step1Labels = mixedMoment B raw28303step2 raw28303step2Labels := by
      have ha : raw28303step2 = (fun i j => raw28303step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28303step2 raw28303step1; decide +kernel
      have hl : raw28303step2Labels = raw28303step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28303step1 raw28303step1Labels permutation31 permutation2
    mixedMoment B raw28303step2 raw28303step2Labels = mixedMoment B raw28303step3 raw28303step3Labels := by
      have ha : raw28303step3 = -raw28303step2 := by apply Matrix.ext; change ∀ i j, raw28303step3 i j = -(raw28303step2 i j); unfold raw28303step3 raw28303step2; decide +kernel
      have hl : raw28303step3Labels = raw28303step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4559 node4559Labels := by rfl

def raw28304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28304step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28304 raw28304Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw28304 raw28304Labels = mixedMoment B raw28304step0 raw28304step0Labels := by
      have hz : ∀ j, raw28304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28304step0 = (fun i j => raw28304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28304step0 raw28304; decide +kernel
      have hl : raw28304step0Labels = raw28304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28304 raw28304Labels permutation434 hz
    mixedMoment B raw28304step0 raw28304step0Labels = mixedMoment B raw28304step1 raw28304step1Labels := by
      have ha : raw28304step1 = (fun i j => raw28304step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28304step1 raw28304step0; decide +kernel
      have hl : raw28304step1Labels = raw28304step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28304step0 raw28304step0Labels permutation151 permutation2
    mixedMoment B raw28304step1 raw28304step1Labels = mixedMoment B raw28304step2 raw28304step2Labels := by
      have ha : raw28304step2 = -raw28304step1 := by apply Matrix.ext; change ∀ i j, raw28304step2 i j = -(raw28304step1 i j); unfold raw28304step2 raw28304step1; decide +kernel
      have hl : raw28304step2Labels = raw28304step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4547 node4547Labels := by rfl

def raw28305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28305step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28305 raw28305Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw28305 raw28305Labels = mixedMoment B raw28305step0 raw28305step0Labels := by
      have hz : ∀ j, raw28305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28305step0 = (fun i j => raw28305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28305step0 raw28305; decide +kernel
      have hl : raw28305step0Labels = raw28305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28305 raw28305Labels permutation346 hz
    mixedMoment B raw28305step0 raw28305step0Labels = mixedMoment B raw28305step1 raw28305step1Labels := by
      have ha : raw28305step1 = (fun i j => raw28305step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28305step1 raw28305step0; decide +kernel
      have hl : raw28305step1Labels = raw28305step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28305step0 raw28305step0Labels permutation151 permutation2
    mixedMoment B raw28305step1 raw28305step1Labels = mixedMoment B raw28305step2 raw28305step2Labels := by
      have ha : raw28305step2 = -raw28305step1 := by apply Matrix.ext; change ∀ i j, raw28305step2 i j = -(raw28305step1 i j); unfold raw28305step2 raw28305step1; decide +kernel
      have hl : raw28305step2Labels = raw28305step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4547 node4547Labels := by rfl

def raw28306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw28306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw28306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![4, -2, -2]]
def raw28306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28306step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28306step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28306 raw28306Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw28306 raw28306Labels = mixedMoment B raw28306step0 raw28306step0Labels := by
      have hz : ∀ j, raw28306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28306step0 = (fun i j => raw28306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28306step0 raw28306; decide +kernel
      have hl : raw28306step0Labels = raw28306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28306 raw28306Labels permutation434 hz
    mixedMoment B raw28306step0 raw28306step0Labels = mixedMoment B raw28306step1 raw28306step1Labels := by
      have hz : ∀ j, raw28306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28306step1 = (fun i j => raw28306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28306step1 raw28306step0; decide +kernel
      have hl : raw28306step1Labels = raw28306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28306step0 raw28306step0Labels permutation80 hz
    mixedMoment B raw28306step1 raw28306step1Labels = mixedMoment B raw28306step2 raw28306step2Labels := by
      have ha : raw28306step2 = (fun i j => raw28306step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28306step2 raw28306step1; decide +kernel
      have hl : raw28306step2Labels = raw28306step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28306step1 raw28306step1Labels permutation31 permutation2
    mixedMoment B raw28306step2 raw28306step2Labels = mixedMoment B raw28306step3 raw28306step3Labels := by
      have ha : raw28306step3 = -raw28306step2 := by apply Matrix.ext; change ∀ i j, raw28306step3 i j = -(raw28306step2 i j); unfold raw28306step3 raw28306step2; decide +kernel
      have hl : raw28306step3Labels = raw28306step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw28307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28307step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28307step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28307step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28307step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28307 raw28307Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw28307 raw28307Labels = mixedMoment B raw28307step0 raw28307step0Labels := by
      have hz : ∀ j, raw28307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28307step0 = (fun i j => raw28307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28307step0 raw28307; decide +kernel
      have hl : raw28307step0Labels = raw28307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28307 raw28307Labels permutation434 hz
    mixedMoment B raw28307step0 raw28307step0Labels = mixedMoment B raw28307step1 raw28307step1Labels := by
      have hz : ∀ j, raw28307step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28307step1 = (fun i j => raw28307step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28307step1 raw28307step0; decide +kernel
      have hl : raw28307step1Labels = raw28307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28307step0 raw28307step0Labels permutation80 hz
    mixedMoment B raw28307step1 raw28307step1Labels = mixedMoment B raw28307step2 raw28307step2Labels := by
      have ha : raw28307step2 = (fun i j => raw28307step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28307step2 raw28307step1; decide +kernel
      have hl : raw28307step2Labels = raw28307step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28307step1 raw28307step1Labels permutation30 permutation7
    mixedMoment B raw28307step2 raw28307step2Labels = mixedMoment B raw28307step3 raw28307step3Labels := by
      have ha : raw28307step3 = raw28307step2 := by apply Matrix.ext; unfold raw28307step3 raw28307step2; decide +kernel
      have hl : raw28307step2Labels = labelEmbedding1 ∘ raw28307step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28307step2 raw28307step2Labels raw28307step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3485 node3485Labels := by rfl

def raw28308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28308step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28308 raw28308Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw28308 raw28308Labels = mixedMoment B raw28308step0 raw28308step0Labels := by
      have hz : ∀ j, raw28308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28308step0 = (fun i j => raw28308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28308step0 raw28308; decide +kernel
      have hl : raw28308step0Labels = raw28308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28308 raw28308Labels permutation434 hz
    mixedMoment B raw28308step0 raw28308step0Labels = mixedMoment B raw28308step1 raw28308step1Labels := by
      have ha : raw28308step1 = (fun i j => raw28308step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28308step1 raw28308step0; decide +kernel
      have hl : raw28308step1Labels = raw28308step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28308step0 raw28308step0Labels permutation150 permutation7
    mixedMoment B raw28308step1 raw28308step1Labels = mixedMoment B raw28308step2 raw28308step2Labels := by
      have ha : raw28308step2 = raw28308step1 := by apply Matrix.ext; unfold raw28308step2 raw28308step1; decide +kernel
      have hl : raw28308step1Labels = labelEmbedding1 ∘ raw28308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28308step1 raw28308step1Labels raw28308step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw28309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28309step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28309 raw28309Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw28309 raw28309Labels = mixedMoment B raw28309step0 raw28309step0Labels := by
      have hz : ∀ j, raw28309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28309step0 = (fun i j => raw28309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28309step0 raw28309; decide +kernel
      have hl : raw28309step0Labels = raw28309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28309 raw28309Labels permutation346 hz
    mixedMoment B raw28309step0 raw28309step0Labels = mixedMoment B raw28309step1 raw28309step1Labels := by
      have ha : raw28309step1 = (fun i j => raw28309step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28309step1 raw28309step0; decide +kernel
      have hl : raw28309step1Labels = raw28309step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28309step0 raw28309step0Labels permutation150 permutation7
    mixedMoment B raw28309step1 raw28309step1Labels = mixedMoment B raw28309step2 raw28309step2Labels := by
      have ha : raw28309step2 = raw28309step1 := by apply Matrix.ext; unfold raw28309step2 raw28309step1; decide +kernel
      have hl : raw28309step1Labels = labelEmbedding1 ∘ raw28309step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28309step1 raw28309step1Labels raw28309step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw28310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28310step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28310step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28310step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28310step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28310 raw28310Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw28310 raw28310Labels = mixedMoment B raw28310step0 raw28310step0Labels := by
      have hz : ∀ j, raw28310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28310step0 = (fun i j => raw28310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28310step0 raw28310; decide +kernel
      have hl : raw28310step0Labels = raw28310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28310 raw28310Labels permutation434 hz
    mixedMoment B raw28310step0 raw28310step0Labels = mixedMoment B raw28310step1 raw28310step1Labels := by
      have hz : ∀ j, raw28310step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28310step1 = (fun i j => raw28310step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28310step1 raw28310step0; decide +kernel
      have hl : raw28310step1Labels = raw28310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28310step0 raw28310step0Labels permutation80 hz
    mixedMoment B raw28310step1 raw28310step1Labels = mixedMoment B raw28310step2 raw28310step2Labels := by
      have ha : raw28310step2 = (fun i j => raw28310step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28310step2 raw28310step1; decide +kernel
      have hl : raw28310step2Labels = raw28310step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28310step1 raw28310step1Labels permutation30 permutation7
    mixedMoment B raw28310step2 raw28310step2Labels = mixedMoment B raw28310step3 raw28310step3Labels := by
      have ha : raw28310step3 = raw28310step2 := by apply Matrix.ext; unfold raw28310step3 raw28310step2; decide +kernel
      have hl : raw28310step2Labels = labelEmbedding1 ∘ raw28310step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28310step2 raw28310step2Labels raw28310step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw28311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28311step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28311step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28311step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28311step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28311step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28311 raw28311Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw28311 raw28311Labels = mixedMoment B raw28311step0 raw28311step0Labels := by
      have hz : ∀ j, raw28311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28311step0 = (fun i j => raw28311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28311step0 raw28311; decide +kernel
      have hl : raw28311step0Labels = raw28311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28311 raw28311Labels permutation434 hz
    mixedMoment B raw28311step0 raw28311step0Labels = mixedMoment B raw28311step1 raw28311step1Labels := by
      have hz : ∀ j, raw28311step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28311step1 = (fun i j => raw28311step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28311step1 raw28311step0; decide +kernel
      have hl : raw28311step1Labels = raw28311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28311step0 raw28311step0Labels permutation80 hz
    mixedMoment B raw28311step1 raw28311step1Labels = mixedMoment B raw28311step2 raw28311step2Labels := by
      have ha : raw28311step2 = (fun i j => raw28311step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28311step2 raw28311step1; decide +kernel
      have hl : raw28311step2Labels = raw28311step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28311step1 raw28311step1Labels permutation30 permutation7
    mixedMoment B raw28311step2 raw28311step2Labels = mixedMoment B raw28311step3 raw28311step3Labels := by
      have ha : raw28311step3 = raw28311step2 := by apply Matrix.ext; unfold raw28311step3 raw28311step2; decide +kernel
      have hl : raw28311step2Labels = labelEmbedding1 ∘ raw28311step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28311step2 raw28311step2Labels raw28311step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw28312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28312step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28312step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw28312step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28312step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28312step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28312step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28312 raw28312Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw28312 raw28312Labels = mixedMoment B raw28312step0 raw28312step0Labels := by
      have hz : ∀ j, raw28312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28312step0 = (fun i j => raw28312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28312step0 raw28312; decide +kernel
      have hl : raw28312step0Labels = raw28312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28312 raw28312Labels permutation434 hz
    mixedMoment B raw28312step0 raw28312step0Labels = mixedMoment B raw28312step1 raw28312step1Labels := by
      have hz : ∀ j, raw28312step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28312step1 = (fun i j => raw28312step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28312step1 raw28312step0; decide +kernel
      have hl : raw28312step1Labels = raw28312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28312step0 raw28312step0Labels permutation80 hz
    mixedMoment B raw28312step1 raw28312step1Labels = mixedMoment B raw28312step2 raw28312step2Labels := by
      have ha : raw28312step2 = (fun i j => raw28312step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28312step2 raw28312step1; decide +kernel
      have hl : raw28312step2Labels = raw28312step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28312step1 raw28312step1Labels permutation11 permutation5
    mixedMoment B raw28312step2 raw28312step2Labels = mixedMoment B raw28312step3 raw28312step3Labels := by
      have ha : raw28312step3 = -raw28312step2 := by apply Matrix.ext; change ∀ i j, raw28312step3 i j = -(raw28312step2 i j); unfold raw28312step3 raw28312step2; decide +kernel
      have hl : raw28312step3Labels = raw28312step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28312step3 raw28312step3Labels = mixedMoment B raw28312step4 raw28312step4Labels := by
      have ha : raw28312step4 = raw28312step3 := by apply Matrix.ext; unfold raw28312step4 raw28312step3; decide +kernel
      have hl : raw28312step3Labels = labelEmbedding1 ∘ raw28312step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28312step3 raw28312step3Labels raw28312step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw28313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw28313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28313step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28313step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28313step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28313 raw28313Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw28313 raw28313Labels = mixedMoment B raw28313step0 raw28313step0Labels := by
      have hz : ∀ j, raw28313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28313step0 = (fun i j => raw28313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28313step0 raw28313; decide +kernel
      have hl : raw28313step0Labels = raw28313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28313 raw28313Labels permutation434 hz
    mixedMoment B raw28313step0 raw28313step0Labels = mixedMoment B raw28313step1 raw28313step1Labels := by
      have ha : raw28313step1 = (fun i j => raw28313step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28313step1 raw28313step0; decide +kernel
      have hl : raw28313step1Labels = raw28313step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28313step0 raw28313step0Labels permutation41 permutation5
    mixedMoment B raw28313step1 raw28313step1Labels = mixedMoment B raw28313step2 raw28313step2Labels := by
      have ha : raw28313step2 = -raw28313step1 := by apply Matrix.ext; change ∀ i j, raw28313step2 i j = -(raw28313step1 i j); unfold raw28313step2 raw28313step1; decide +kernel
      have hl : raw28313step2Labels = raw28313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28313step2 raw28313step2Labels = mixedMoment B raw28313step3 raw28313step3Labels := by
      have ha : raw28313step3 = raw28313step2 := by apply Matrix.ext; unfold raw28313step3 raw28313step2; decide +kernel
      have hl : raw28313step2Labels = labelEmbedding1 ∘ raw28313step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28313step2 raw28313step2Labels raw28313step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

def raw28314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw28314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28314step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28314step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28314step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28314 raw28314Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw28314 raw28314Labels = mixedMoment B raw28314step0 raw28314step0Labels := by
      have hz : ∀ j, raw28314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28314step0 = (fun i j => raw28314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28314step0 raw28314; decide +kernel
      have hl : raw28314step0Labels = raw28314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28314 raw28314Labels permutation346 hz
    mixedMoment B raw28314step0 raw28314step0Labels = mixedMoment B raw28314step1 raw28314step1Labels := by
      have ha : raw28314step1 = (fun i j => raw28314step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28314step1 raw28314step0; decide +kernel
      have hl : raw28314step1Labels = raw28314step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28314step0 raw28314step0Labels permutation41 permutation5
    mixedMoment B raw28314step1 raw28314step1Labels = mixedMoment B raw28314step2 raw28314step2Labels := by
      have ha : raw28314step2 = -raw28314step1 := by apply Matrix.ext; change ∀ i j, raw28314step2 i j = -(raw28314step1 i j); unfold raw28314step2 raw28314step1; decide +kernel
      have hl : raw28314step2Labels = raw28314step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28314step2 raw28314step2Labels = mixedMoment B raw28314step3 raw28314step3Labels := by
      have ha : raw28314step3 = raw28314step2 := by apply Matrix.ext; unfold raw28314step3 raw28314step2; decide +kernel
      have hl : raw28314step2Labels = labelEmbedding1 ∘ raw28314step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28314step2 raw28314step2Labels raw28314step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

def raw28315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28315step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw28315step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28315step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw28315step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28315step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw28315step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28315 raw28315Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw28315 raw28315Labels = mixedMoment B raw28315step0 raw28315step0Labels := by
      have hz : ∀ j, raw28315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28315step0 = (fun i j => raw28315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28315step0 raw28315; decide +kernel
      have hl : raw28315step0Labels = raw28315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28315 raw28315Labels permutation434 hz
    mixedMoment B raw28315step0 raw28315step0Labels = mixedMoment B raw28315step1 raw28315step1Labels := by
      have hz : ∀ j, raw28315step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28315step1 = (fun i j => raw28315step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28315step1 raw28315step0; decide +kernel
      have hl : raw28315step1Labels = raw28315step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28315step0 raw28315step0Labels permutation80 hz
    mixedMoment B raw28315step1 raw28315step1Labels = mixedMoment B raw28315step2 raw28315step2Labels := by
      have ha : raw28315step2 = (fun i j => raw28315step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28315step2 raw28315step1; decide +kernel
      have hl : raw28315step2Labels = raw28315step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28315step1 raw28315step1Labels permutation11 permutation5
    mixedMoment B raw28315step2 raw28315step2Labels = mixedMoment B raw28315step3 raw28315step3Labels := by
      have ha : raw28315step3 = -raw28315step2 := by apply Matrix.ext; change ∀ i j, raw28315step3 i j = -(raw28315step2 i j); unfold raw28315step3 raw28315step2; decide +kernel
      have hl : raw28315step3Labels = raw28315step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28315step3 raw28315step3Labels = mixedMoment B raw28315step4 raw28315step4Labels := by
      have ha : raw28315step4 = raw28315step3 := by apply Matrix.ext; unfold raw28315step4 raw28315step3; decide +kernel
      have hl : raw28315step3Labels = labelEmbedding1 ∘ raw28315step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28315step3 raw28315step3Labels raw28315step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw28316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28316step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28316step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28316step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw28316step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28316step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw28316step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28316step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw28316step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28316 raw28316Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw28316 raw28316Labels = mixedMoment B raw28316step0 raw28316step0Labels := by
      have hz : ∀ j, raw28316 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28316step0 = (fun i j => raw28316 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28316step0 raw28316; decide +kernel
      have hl : raw28316step0Labels = raw28316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28316 raw28316Labels permutation434 hz
    mixedMoment B raw28316step0 raw28316step0Labels = mixedMoment B raw28316step1 raw28316step1Labels := by
      have hz : ∀ j, raw28316step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28316step1 = (fun i j => raw28316step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28316step1 raw28316step0; decide +kernel
      have hl : raw28316step1Labels = raw28316step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28316step0 raw28316step0Labels permutation80 hz
    mixedMoment B raw28316step1 raw28316step1Labels = mixedMoment B raw28316step2 raw28316step2Labels := by
      have ha : raw28316step2 = (fun i j => raw28316step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28316step2 raw28316step1; decide +kernel
      have hl : raw28316step2Labels = raw28316step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28316step1 raw28316step1Labels permutation11 permutation5
    mixedMoment B raw28316step2 raw28316step2Labels = mixedMoment B raw28316step3 raw28316step3Labels := by
      have ha : raw28316step3 = -raw28316step2 := by apply Matrix.ext; change ∀ i j, raw28316step3 i j = -(raw28316step2 i j); unfold raw28316step3 raw28316step2; decide +kernel
      have hl : raw28316step3Labels = raw28316step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28316step3 raw28316step3Labels = mixedMoment B raw28316step4 raw28316step4Labels := by
      have ha : raw28316step4 = raw28316step3 := by apply Matrix.ext; unfold raw28316step4 raw28316step3; decide +kernel
      have hl : raw28316step3Labels = labelEmbedding1 ∘ raw28316step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28316step3 raw28316step3Labels raw28316step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw28317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw28317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28317step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28317step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28317 raw28317Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw28317 raw28317Labels = mixedMoment B raw28317step0 raw28317step0Labels := by
      have hz : ∀ j, raw28317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28317step0 = (fun i j => raw28317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28317step0 raw28317; decide +kernel
      have hl : raw28317step0Labels = raw28317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28317 raw28317Labels permutation434 hz
    mixedMoment B raw28317step0 raw28317step0Labels = mixedMoment B raw28317step1 raw28317step1Labels := by
      have ha : raw28317step1 = (fun i j => raw28317step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28317step1 raw28317step0; decide +kernel
      have hl : raw28317step1Labels = raw28317step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28317step0 raw28317step0Labels permutation44 permutation5
    mixedMoment B raw28317step1 raw28317step1Labels = mixedMoment B raw28317step2 raw28317step2Labels := by
      have ha : raw28317step2 = -raw28317step1 := by apply Matrix.ext; change ∀ i j, raw28317step2 i j = -(raw28317step1 i j); unfold raw28317step2 raw28317step1; decide +kernel
      have hl : raw28317step2Labels = raw28317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28317step2 raw28317step2Labels = mixedMoment B raw28317step3 raw28317step3Labels := by
      have ha : raw28317step3 = raw28317step2 := by apply Matrix.ext; unfold raw28317step3 raw28317step2; decide +kernel
      have hl : raw28317step2Labels = labelEmbedding1 ∘ raw28317step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28317step2 raw28317step2Labels raw28317step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

def raw28318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28318step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28318 raw28318Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw28318 raw28318Labels = mixedMoment B raw28318step0 raw28318step0Labels := by
      have hz : ∀ j, raw28318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28318step0 = (fun i j => raw28318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28318step0 raw28318; decide +kernel
      have hl : raw28318step0Labels = raw28318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28318 raw28318Labels permutation434 hz
    mixedMoment B raw28318step0 raw28318step0Labels = mixedMoment B raw28318step1 raw28318step1Labels := by
      have ha : raw28318step1 = (fun i j => raw28318step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28318step1 raw28318step0; decide +kernel
      have hl : raw28318step1Labels = raw28318step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28318step0 raw28318step0Labels permutation150 permutation7
    mixedMoment B raw28318step1 raw28318step1Labels = mixedMoment B raw28318step2 raw28318step2Labels := by
      have ha : raw28318step2 = raw28318step1 := by apply Matrix.ext; unfold raw28318step2 raw28318step1; decide +kernel
      have hl : raw28318step1Labels = labelEmbedding1 ∘ raw28318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28318step1 raw28318step1Labels raw28318step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

def raw28319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28319 raw28319Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw28319 raw28319Labels = mixedMoment B raw28319step0 raw28319step0Labels := by
      have ha : raw28319step0 = (fun i j => raw28319 (permutation681 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28319step0 raw28319; decide +kernel
      have hl : raw28319step0Labels = raw28319Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28319 raw28319Labels permutation681 permutation7
    mixedMoment B raw28319step0 raw28319step0Labels = mixedMoment B raw28319step1 raw28319step1Labels := by
      have ha : raw28319step1 = raw28319step0 := by apply Matrix.ext; unfold raw28319step1 raw28319step0; decide +kernel
      have hl : raw28319step0Labels = labelEmbedding1 ∘ raw28319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28319step0 raw28319step0Labels raw28319step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

def raw28320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28320step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28320step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28320 raw28320Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw28320 raw28320Labels = mixedMoment B raw28320step0 raw28320step0Labels := by
      have hz : ∀ j, raw28320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28320step0 = (fun i j => raw28320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28320step0 raw28320; decide +kernel
      have hl : raw28320step0Labels = raw28320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28320 raw28320Labels permutation434 hz
    mixedMoment B raw28320step0 raw28320step0Labels = mixedMoment B raw28320step1 raw28320step1Labels := by
      have ha : raw28320step1 = (fun i j => raw28320step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28320step1 raw28320step0; decide +kernel
      have hl : raw28320step1Labels = raw28320step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28320step0 raw28320step0Labels permutation150 permutation7
    mixedMoment B raw28320step1 raw28320step1Labels = mixedMoment B raw28320step2 raw28320step2Labels := by
      have ha : raw28320step2 = raw28320step1 := by apply Matrix.ext; unfold raw28320step2 raw28320step1; decide +kernel
      have hl : raw28320step1Labels = labelEmbedding1 ∘ raw28320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28320step1 raw28320step1Labels raw28320step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw28321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28321step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw28321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw28321step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28321step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw28321step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28321 raw28321Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw28321 raw28321Labels = mixedMoment B raw28321step0 raw28321step0Labels := by
      have hz : ∀ j, raw28321 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28321step0 = (fun i j => raw28321 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28321step0 raw28321; decide +kernel
      have hl : raw28321step0Labels = raw28321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28321 raw28321Labels permutation434 hz
    mixedMoment B raw28321step0 raw28321step0Labels = mixedMoment B raw28321step1 raw28321step1Labels := by
      have ha : raw28321step1 = (fun i j => raw28321step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28321step1 raw28321step0; decide +kernel
      have hl : raw28321step1Labels = raw28321step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28321step0 raw28321step0Labels permutation48 permutation5
    mixedMoment B raw28321step1 raw28321step1Labels = mixedMoment B raw28321step2 raw28321step2Labels := by
      have ha : raw28321step2 = -raw28321step1 := by apply Matrix.ext; change ∀ i j, raw28321step2 i j = -(raw28321step1 i j); unfold raw28321step2 raw28321step1; decide +kernel
      have hl : raw28321step2Labels = raw28321step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28321step2 raw28321step2Labels = mixedMoment B raw28321step3 raw28321step3Labels := by
      have ha : raw28321step3 = raw28321step2 := by apply Matrix.ext; unfold raw28321step3 raw28321step2; decide +kernel
      have hl : raw28321step2Labels = labelEmbedding1 ∘ raw28321step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28321step2 raw28321step2Labels raw28321step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw28322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28322step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw28322step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28322step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28322step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28322step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28322step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28322 raw28322Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw28322 raw28322Labels = mixedMoment B raw28322step0 raw28322step0Labels := by
      have hz : ∀ j, raw28322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28322step0 = (fun i j => raw28322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28322step0 raw28322; decide +kernel
      have hl : raw28322step0Labels = raw28322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28322 raw28322Labels permutation346 hz
    mixedMoment B raw28322step0 raw28322step0Labels = mixedMoment B raw28322step1 raw28322step1Labels := by
      have ha : raw28322step1 = (fun i j => raw28322step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28322step1 raw28322step0; decide +kernel
      have hl : raw28322step1Labels = raw28322step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28322step0 raw28322step0Labels permutation44 permutation5
    mixedMoment B raw28322step1 raw28322step1Labels = mixedMoment B raw28322step2 raw28322step2Labels := by
      have ha : raw28322step2 = -raw28322step1 := by apply Matrix.ext; change ∀ i j, raw28322step2 i j = -(raw28322step1 i j); unfold raw28322step2 raw28322step1; decide +kernel
      have hl : raw28322step2Labels = raw28322step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28322step2 raw28322step2Labels = mixedMoment B raw28322step3 raw28322step3Labels := by
      have ha : raw28322step3 = raw28322step2 := by apply Matrix.ext; unfold raw28322step3 raw28322step2; decide +kernel
      have hl : raw28322step2Labels = labelEmbedding1 ∘ raw28322step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28322step2 raw28322step2Labels raw28322step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

def raw28323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28323step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28323step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28323 raw28323Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw28323 raw28323Labels = mixedMoment B raw28323step0 raw28323step0Labels := by
      have hz : ∀ j, raw28323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28323step0 = (fun i j => raw28323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28323step0 raw28323; decide +kernel
      have hl : raw28323step0Labels = raw28323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28323 raw28323Labels permutation346 hz
    mixedMoment B raw28323step0 raw28323step0Labels = mixedMoment B raw28323step1 raw28323step1Labels := by
      have ha : raw28323step1 = (fun i j => raw28323step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28323step1 raw28323step0; decide +kernel
      have hl : raw28323step1Labels = raw28323step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28323step0 raw28323step0Labels permutation150 permutation7
    mixedMoment B raw28323step1 raw28323step1Labels = mixedMoment B raw28323step2 raw28323step2Labels := by
      have ha : raw28323step2 = raw28323step1 := by apply Matrix.ext; unfold raw28323step2 raw28323step1; decide +kernel
      have hl : raw28323step1Labels = labelEmbedding1 ∘ raw28323step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28323step1 raw28323step1Labels raw28323step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

def raw28324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28324 raw28324Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw28324 raw28324Labels = mixedMoment B raw28324step0 raw28324step0Labels := by
      have ha : raw28324step0 = (fun i j => raw28324 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28324step0 raw28324; decide +kernel
      have hl : raw28324step0Labels = raw28324Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28324 raw28324Labels permutation687 permutation7
    mixedMoment B raw28324step0 raw28324step0Labels = mixedMoment B raw28324step1 raw28324step1Labels := by
      have ha : raw28324step1 = raw28324step0 := by apply Matrix.ext; unfold raw28324step1 raw28324step0; decide +kernel
      have hl : raw28324step0Labels = labelEmbedding1 ∘ raw28324step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28324step0 raw28324step0Labels raw28324step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

def raw28325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28325step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28325 raw28325Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw28325 raw28325Labels = mixedMoment B raw28325step0 raw28325step0Labels := by
      have hz : ∀ j, raw28325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28325step0 = (fun i j => raw28325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28325step0 raw28325; decide +kernel
      have hl : raw28325step0Labels = raw28325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28325 raw28325Labels permutation346 hz
    mixedMoment B raw28325step0 raw28325step0Labels = mixedMoment B raw28325step1 raw28325step1Labels := by
      have ha : raw28325step1 = (fun i j => raw28325step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28325step1 raw28325step0; decide +kernel
      have hl : raw28325step1Labels = raw28325step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28325step0 raw28325step0Labels permutation150 permutation7
    mixedMoment B raw28325step1 raw28325step1Labels = mixedMoment B raw28325step2 raw28325step2Labels := by
      have ha : raw28325step2 = raw28325step1 := by apply Matrix.ext; unfold raw28325step2 raw28325step1; decide +kernel
      have hl : raw28325step1Labels = labelEmbedding1 ∘ raw28325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28325step1 raw28325step1Labels raw28325step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw28326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw28326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw28326step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28326step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw28326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28326 raw28326Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw28326 raw28326Labels = mixedMoment B raw28326step0 raw28326step0Labels := by
      have hz : ∀ j, raw28326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28326step0 = (fun i j => raw28326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28326step0 raw28326; decide +kernel
      have hl : raw28326step0Labels = raw28326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28326 raw28326Labels permutation346 hz
    mixedMoment B raw28326step0 raw28326step0Labels = mixedMoment B raw28326step1 raw28326step1Labels := by
      have ha : raw28326step1 = (fun i j => raw28326step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28326step1 raw28326step0; decide +kernel
      have hl : raw28326step1Labels = raw28326step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28326step0 raw28326step0Labels permutation48 permutation5
    mixedMoment B raw28326step1 raw28326step1Labels = mixedMoment B raw28326step2 raw28326step2Labels := by
      have ha : raw28326step2 = -raw28326step1 := by apply Matrix.ext; change ∀ i j, raw28326step2 i j = -(raw28326step1 i j); unfold raw28326step2 raw28326step1; decide +kernel
      have hl : raw28326step2Labels = raw28326step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28326step2 raw28326step2Labels = mixedMoment B raw28326step3 raw28326step3Labels := by
      have ha : raw28326step3 = raw28326step2 := by apply Matrix.ext; unfold raw28326step3 raw28326step2; decide +kernel
      have hl : raw28326step2Labels = labelEmbedding1 ∘ raw28326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28326step2 raw28326step2Labels raw28326step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw28327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw28327step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw28327step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw28327step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28327step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw28327step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28327 raw28327Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw28327 raw28327Labels = mixedMoment B raw28327step0 raw28327step0Labels := by
      have hz : ∀ j, raw28327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28327step0 = (fun i j => raw28327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28327step0 raw28327; decide +kernel
      have hl : raw28327step0Labels = raw28327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28327 raw28327Labels permutation434 hz
    mixedMoment B raw28327step0 raw28327step0Labels = mixedMoment B raw28327step1 raw28327step1Labels := by
      have hz : ∀ j, raw28327step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28327step1 = (fun i j => raw28327step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28327step1 raw28327step0; decide +kernel
      have hl : raw28327step1Labels = raw28327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28327step0 raw28327step0Labels permutation80 hz
    mixedMoment B raw28327step1 raw28327step1Labels = mixedMoment B raw28327step2 raw28327step2Labels := by
      have ha : raw28327step2 = (fun i j => raw28327step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28327step2 raw28327step1; decide +kernel
      have hl : raw28327step2Labels = raw28327step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28327step1 raw28327step1Labels permutation8 permutation5
    mixedMoment B raw28327step2 raw28327step2Labels = mixedMoment B raw28327step3 raw28327step3Labels := by
      have ha : raw28327step3 = -raw28327step2 := by apply Matrix.ext; change ∀ i j, raw28327step3 i j = -(raw28327step2 i j); unfold raw28327step3 raw28327step2; decide +kernel
      have hl : raw28327step3Labels = raw28327step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28327step3 raw28327step3Labels = mixedMoment B raw28327step4 raw28327step4Labels := by
      have ha : raw28327step4 = raw28327step3 := by apply Matrix.ext; unfold raw28327step4 raw28327step3; decide +kernel
      have hl : raw28327step3Labels = labelEmbedding1 ∘ raw28327step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28327step3 raw28327step3Labels raw28327step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

def raw28328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28328step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![3, -1, -2]]
def raw28328step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28328step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw28328step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28328step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw28328step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28328 raw28328Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw28328 raw28328Labels = mixedMoment B raw28328step0 raw28328step0Labels := by
      have hz : ∀ j, raw28328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28328step0 = (fun i j => raw28328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28328step0 raw28328; decide +kernel
      have hl : raw28328step0Labels = raw28328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28328 raw28328Labels permutation434 hz
    mixedMoment B raw28328step0 raw28328step0Labels = mixedMoment B raw28328step1 raw28328step1Labels := by
      have hz : ∀ j, raw28328step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28328step1 = (fun i j => raw28328step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28328step1 raw28328step0; decide +kernel
      have hl : raw28328step1Labels = raw28328step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28328step0 raw28328step0Labels permutation80 hz
    mixedMoment B raw28328step1 raw28328step1Labels = mixedMoment B raw28328step2 raw28328step2Labels := by
      have ha : raw28328step2 = (fun i j => raw28328step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28328step2 raw28328step1; decide +kernel
      have hl : raw28328step2Labels = raw28328step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28328step1 raw28328step1Labels permutation30 permutation7
    mixedMoment B raw28328step2 raw28328step2Labels = mixedMoment B raw28328step3 raw28328step3Labels := by
      have ha : raw28328step3 = raw28328step2 := by apply Matrix.ext; unfold raw28328step3 raw28328step2; decide +kernel
      have hl : raw28328step2Labels = labelEmbedding1 ∘ raw28328step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28328step2 raw28328step2Labels raw28328step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

def raw28329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28329 raw28329Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw28329 raw28329Labels = mixedMoment B raw28329step0 raw28329step0Labels := by
      have hz : ∀ j, raw28329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28329step0 = (fun i j => raw28329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28329step0 raw28329; decide +kernel
      have hl : raw28329step0Labels = raw28329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28329 raw28329Labels permutation434 hz
    mixedMoment B raw28329step0 raw28329step0Labels = mixedMoment B raw28329step1 raw28329step1Labels := by
      have ha : raw28329step1 = (fun i j => raw28329step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28329step1 raw28329step0; decide +kernel
      have hl : raw28329step1Labels = raw28329step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28329step0 raw28329step0Labels permutation150 permutation7
    mixedMoment B raw28329step1 raw28329step1Labels = mixedMoment B raw28329step2 raw28329step2Labels := by
      have ha : raw28329step2 = raw28329step1 := by apply Matrix.ext; unfold raw28329step2 raw28329step1; decide +kernel
      have hl : raw28329step1Labels = labelEmbedding1 ∘ raw28329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28329step1 raw28329step1Labels raw28329step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw28330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28330 raw28330Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw28330 raw28330Labels = mixedMoment B raw28330step0 raw28330step0Labels := by
      have hz : ∀ j, raw28330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28330step0 = (fun i j => raw28330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28330step0 raw28330; decide +kernel
      have hl : raw28330step0Labels = raw28330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28330 raw28330Labels permutation346 hz
    mixedMoment B raw28330step0 raw28330step0Labels = mixedMoment B raw28330step1 raw28330step1Labels := by
      have ha : raw28330step1 = (fun i j => raw28330step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28330step1 raw28330step0; decide +kernel
      have hl : raw28330step1Labels = raw28330step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28330step0 raw28330step0Labels permutation150 permutation7
    mixedMoment B raw28330step1 raw28330step1Labels = mixedMoment B raw28330step2 raw28330step2Labels := by
      have ha : raw28330step2 = raw28330step1 := by apply Matrix.ext; unfold raw28330step2 raw28330step1; decide +kernel
      have hl : raw28330step1Labels = labelEmbedding1 ∘ raw28330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28330step1 raw28330step1Labels raw28330step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw28331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28331step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw28331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28331step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw28331step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28331step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw28331step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28331 raw28331Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw28331 raw28331Labels = mixedMoment B raw28331step0 raw28331step0Labels := by
      have hz : ∀ j, raw28331 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28331step0 = (fun i j => raw28331 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28331step0 raw28331; decide +kernel
      have hl : raw28331step0Labels = raw28331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28331 raw28331Labels permutation434 hz
    mixedMoment B raw28331step0 raw28331step0Labels = mixedMoment B raw28331step1 raw28331step1Labels := by
      have hz : ∀ j, raw28331step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28331step1 = (fun i j => raw28331step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28331step1 raw28331step0; decide +kernel
      have hl : raw28331step1Labels = raw28331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28331step0 raw28331step0Labels permutation80 hz
    mixedMoment B raw28331step1 raw28331step1Labels = mixedMoment B raw28331step2 raw28331step2Labels := by
      have ha : raw28331step2 = (fun i j => raw28331step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28331step2 raw28331step1; decide +kernel
      have hl : raw28331step2Labels = raw28331step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28331step1 raw28331step1Labels permutation12 permutation5
    mixedMoment B raw28331step2 raw28331step2Labels = mixedMoment B raw28331step3 raw28331step3Labels := by
      have ha : raw28331step3 = -raw28331step2 := by apply Matrix.ext; change ∀ i j, raw28331step3 i j = -(raw28331step2 i j); unfold raw28331step3 raw28331step2; decide +kernel
      have hl : raw28331step3Labels = raw28331step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28331step3 raw28331step3Labels = mixedMoment B raw28331step4 raw28331step4Labels := by
      have ha : raw28331step4 = raw28331step3 := by apply Matrix.ext; unfold raw28331step4 raw28331step3; decide +kernel
      have hl : raw28331step3Labels = labelEmbedding1 ∘ raw28331step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28331step3 raw28331step3Labels raw28331step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

def raw28332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28332step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw28332step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-2, -2, 4]]
def raw28332step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw28332step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28332step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw28332step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28332 raw28332Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw28332 raw28332Labels = mixedMoment B raw28332step0 raw28332step0Labels := by
      have hz : ∀ j, raw28332 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28332step0 = (fun i j => raw28332 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28332step0 raw28332; decide +kernel
      have hl : raw28332step0Labels = raw28332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28332 raw28332Labels permutation434 hz
    mixedMoment B raw28332step0 raw28332step0Labels = mixedMoment B raw28332step1 raw28332step1Labels := by
      have hz : ∀ j, raw28332step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28332step1 = (fun i j => raw28332step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28332step1 raw28332step0; decide +kernel
      have hl : raw28332step1Labels = raw28332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28332step0 raw28332step0Labels permutation80 hz
    mixedMoment B raw28332step1 raw28332step1Labels = mixedMoment B raw28332step2 raw28332step2Labels := by
      have ha : raw28332step2 = (fun i j => raw28332step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28332step2 raw28332step1; decide +kernel
      have hl : raw28332step2Labels = raw28332step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28332step1 raw28332step1Labels permutation10 permutation5
    mixedMoment B raw28332step2 raw28332step2Labels = mixedMoment B raw28332step3 raw28332step3Labels := by
      have ha : raw28332step3 = -raw28332step2 := by apply Matrix.ext; change ∀ i j, raw28332step3 i j = -(raw28332step2 i j); unfold raw28332step3 raw28332step2; decide +kernel
      have hl : raw28332step3Labels = raw28332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28332step3 raw28332step3Labels = mixedMoment B raw28332step4 raw28332step4Labels := by
      have ha : raw28332step4 = raw28332step3 := by apply Matrix.ext; unfold raw28332step4 raw28332step3; decide +kernel
      have hl : raw28332step3Labels = labelEmbedding1 ∘ raw28332step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28332step3 raw28332step3Labels raw28332step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

def raw28333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![4, -2, -2]]
def raw28333step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28333step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28333 raw28333Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw28333 raw28333Labels = mixedMoment B raw28333step0 raw28333step0Labels := by
      have hz : ∀ j, raw28333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28333step0 = (fun i j => raw28333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28333step0 raw28333; decide +kernel
      have hl : raw28333step0Labels = raw28333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28333 raw28333Labels permutation434 hz
    mixedMoment B raw28333step0 raw28333step0Labels = mixedMoment B raw28333step1 raw28333step1Labels := by
      have hz : ∀ j, raw28333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28333step1 = (fun i j => raw28333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28333step1 raw28333step0; decide +kernel
      have hl : raw28333step1Labels = raw28333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28333step0 raw28333step0Labels permutation80 hz
    mixedMoment B raw28333step1 raw28333step1Labels = mixedMoment B raw28333step2 raw28333step2Labels := by
      have ha : raw28333step2 = (fun i j => raw28333step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28333step2 raw28333step1; decide +kernel
      have hl : raw28333step2Labels = raw28333step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28333step1 raw28333step1Labels permutation30 permutation7
    mixedMoment B raw28333step2 raw28333step2Labels = mixedMoment B raw28333step3 raw28333step3Labels := by
      have ha : raw28333step3 = raw28333step2 := by apply Matrix.ext; unfold raw28333step3 raw28333step2; decide +kernel
      have hl : raw28333step2Labels = labelEmbedding1 ∘ raw28333step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28333step2 raw28333step2Labels raw28333step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

def raw28334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28334step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28334 raw28334Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw28334 raw28334Labels = mixedMoment B raw28334step0 raw28334step0Labels := by
      have hz : ∀ j, raw28334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28334step0 = (fun i j => raw28334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28334step0 raw28334; decide +kernel
      have hl : raw28334step0Labels = raw28334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28334 raw28334Labels permutation434 hz
    mixedMoment B raw28334step0 raw28334step0Labels = mixedMoment B raw28334step1 raw28334step1Labels := by
      have ha : raw28334step1 = (fun i j => raw28334step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28334step1 raw28334step0; decide +kernel
      have hl : raw28334step1Labels = raw28334step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28334step0 raw28334step0Labels permutation150 permutation7
    mixedMoment B raw28334step1 raw28334step1Labels = mixedMoment B raw28334step2 raw28334step2Labels := by
      have ha : raw28334step2 = raw28334step1 := by apply Matrix.ext; unfold raw28334step2 raw28334step1; decide +kernel
      have hl : raw28334step1Labels = labelEmbedding1 ∘ raw28334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28334step1 raw28334step1Labels raw28334step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

def raw28335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28335Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28335step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28335step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28335 raw28335Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw28335 raw28335Labels = mixedMoment B raw28335step0 raw28335step0Labels := by
      have hz : ∀ j, raw28335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28335step0 = (fun i j => raw28335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28335step0 raw28335; decide +kernel
      have hl : raw28335step0Labels = raw28335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28335 raw28335Labels permutation346 hz
    mixedMoment B raw28335step0 raw28335step0Labels = mixedMoment B raw28335step1 raw28335step1Labels := by
      have ha : raw28335step1 = (fun i j => raw28335step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28335step1 raw28335step0; decide +kernel
      have hl : raw28335step1Labels = raw28335step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28335step0 raw28335step0Labels permutation150 permutation7
    mixedMoment B raw28335step1 raw28335step1Labels = mixedMoment B raw28335step2 raw28335step2Labels := by
      have ha : raw28335step2 = raw28335step1 := by apply Matrix.ext; unfold raw28335step2 raw28335step1; decide +kernel
      have hl : raw28335step1Labels = labelEmbedding1 ∘ raw28335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28335step1 raw28335step1Labels raw28335step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

def raw28336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw28336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw28336step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![4, -2, -2]]
def raw28336step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw28336step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28336step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw28336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28336 raw28336Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw28336 raw28336Labels = mixedMoment B raw28336step0 raw28336step0Labels := by
      have hz : ∀ j, raw28336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28336step0 = (fun i j => raw28336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28336step0 raw28336; decide +kernel
      have hl : raw28336step0Labels = raw28336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28336 raw28336Labels permutation434 hz
    mixedMoment B raw28336step0 raw28336step0Labels = mixedMoment B raw28336step1 raw28336step1Labels := by
      have hz : ∀ j, raw28336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28336step1 = (fun i j => raw28336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28336step1 raw28336step0; decide +kernel
      have hl : raw28336step1Labels = raw28336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28336step0 raw28336step0Labels permutation80 hz
    mixedMoment B raw28336step1 raw28336step1Labels = mixedMoment B raw28336step2 raw28336step2Labels := by
      have ha : raw28336step2 = (fun i j => raw28336step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28336step2 raw28336step1; decide +kernel
      have hl : raw28336step2Labels = raw28336step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28336step1 raw28336step1Labels permutation30 permutation7
    mixedMoment B raw28336step2 raw28336step2Labels = mixedMoment B raw28336step3 raw28336step3Labels := by
      have ha : raw28336step3 = raw28336step2 := by apply Matrix.ext; unfold raw28336step3 raw28336step2; decide +kernel
      have hl : raw28336step2Labels = labelEmbedding1 ∘ raw28336step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28336step2 raw28336step2Labels raw28336step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw28337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw28337step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28337step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28337step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28337step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28337step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28337 raw28337Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw28337 raw28337Labels = mixedMoment B raw28337step0 raw28337step0Labels := by
      have hz : ∀ j, raw28337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28337step0 = (fun i j => raw28337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28337step0 raw28337; decide +kernel
      have hl : raw28337step0Labels = raw28337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28337 raw28337Labels permutation434 hz
    mixedMoment B raw28337step0 raw28337step0Labels = mixedMoment B raw28337step1 raw28337step1Labels := by
      have hz : ∀ j, raw28337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28337step1 = (fun i j => raw28337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28337step1 raw28337step0; decide +kernel
      have hl : raw28337step1Labels = raw28337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28337step0 raw28337step0Labels permutation80 hz
    mixedMoment B raw28337step1 raw28337step1Labels = mixedMoment B raw28337step2 raw28337step2Labels := by
      have ha : raw28337step2 = (fun i j => raw28337step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28337step2 raw28337step1; decide +kernel
      have hl : raw28337step2Labels = raw28337step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28337step1 raw28337step1Labels permutation30 permutation3
    mixedMoment B raw28337step2 raw28337step2Labels = mixedMoment B raw28337step3 raw28337step3Labels := by
      have ha : raw28337step3 = -raw28337step2 := by apply Matrix.ext; change ∀ i j, raw28337step3 i j = -(raw28337step2 i j); unfold raw28337step3 raw28337step2; decide +kernel
      have hl : raw28337step3Labels = raw28337step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28337step3 raw28337step3Labels = mixedMoment B raw28337step4 raw28337step4Labels := by
      have ha : raw28337step4 = raw28337step3 := by apply Matrix.ext; unfold raw28337step4 raw28337step3; decide +kernel
      have hl : raw28337step3Labels = labelEmbedding6 ∘ raw28337step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28337step3 raw28337step3Labels raw28337step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw28338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw28338step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28338step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28338step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28338step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28338 raw28338Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw28338 raw28338Labels = mixedMoment B raw28338step0 raw28338step0Labels := by
      have hz : ∀ j, raw28338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28338step0 = (fun i j => raw28338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28338step0 raw28338; decide +kernel
      have hl : raw28338step0Labels = raw28338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28338 raw28338Labels permutation434 hz
    mixedMoment B raw28338step0 raw28338step0Labels = mixedMoment B raw28338step1 raw28338step1Labels := by
      have ha : raw28338step1 = (fun i j => raw28338step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28338step1 raw28338step0; decide +kernel
      have hl : raw28338step1Labels = raw28338step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28338step0 raw28338step0Labels permutation151 permutation3
    mixedMoment B raw28338step1 raw28338step1Labels = mixedMoment B raw28338step2 raw28338step2Labels := by
      have ha : raw28338step2 = -raw28338step1 := by apply Matrix.ext; change ∀ i j, raw28338step2 i j = -(raw28338step1 i j); unfold raw28338step2 raw28338step1; decide +kernel
      have hl : raw28338step2Labels = raw28338step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28338step2 raw28338step2Labels = mixedMoment B raw28338step3 raw28338step3Labels := by
      have ha : raw28338step3 = raw28338step2 := by apply Matrix.ext; unfold raw28338step3 raw28338step2; decide +kernel
      have hl : raw28338step2Labels = labelEmbedding6 ∘ raw28338step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28338step2 raw28338step2Labels raw28338step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw28339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw28339step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28339step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28339step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28339step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28339 raw28339Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw28339 raw28339Labels = mixedMoment B raw28339step0 raw28339step0Labels := by
      have hz : ∀ j, raw28339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28339step0 = (fun i j => raw28339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28339step0 raw28339; decide +kernel
      have hl : raw28339step0Labels = raw28339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28339 raw28339Labels permutation346 hz
    mixedMoment B raw28339step0 raw28339step0Labels = mixedMoment B raw28339step1 raw28339step1Labels := by
      have ha : raw28339step1 = (fun i j => raw28339step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28339step1 raw28339step0; decide +kernel
      have hl : raw28339step1Labels = raw28339step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28339step0 raw28339step0Labels permutation151 permutation3
    mixedMoment B raw28339step1 raw28339step1Labels = mixedMoment B raw28339step2 raw28339step2Labels := by
      have ha : raw28339step2 = -raw28339step1 := by apply Matrix.ext; change ∀ i j, raw28339step2 i j = -(raw28339step1 i j); unfold raw28339step2 raw28339step1; decide +kernel
      have hl : raw28339step2Labels = raw28339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28339step2 raw28339step2Labels = mixedMoment B raw28339step3 raw28339step3Labels := by
      have ha : raw28339step3 = raw28339step2 := by apply Matrix.ext; unfold raw28339step3 raw28339step2; decide +kernel
      have hl : raw28339step2Labels = labelEmbedding6 ∘ raw28339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28339step2 raw28339step2Labels raw28339step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw28340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw28340step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28340step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28340step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28340step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28340step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28340 raw28340Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw28340 raw28340Labels = mixedMoment B raw28340step0 raw28340step0Labels := by
      have hz : ∀ j, raw28340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28340step0 = (fun i j => raw28340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28340step0 raw28340; decide +kernel
      have hl : raw28340step0Labels = raw28340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28340 raw28340Labels permutation434 hz
    mixedMoment B raw28340step0 raw28340step0Labels = mixedMoment B raw28340step1 raw28340step1Labels := by
      have hz : ∀ j, raw28340step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28340step1 = (fun i j => raw28340step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28340step1 raw28340step0; decide +kernel
      have hl : raw28340step1Labels = raw28340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28340step0 raw28340step0Labels permutation80 hz
    mixedMoment B raw28340step1 raw28340step1Labels = mixedMoment B raw28340step2 raw28340step2Labels := by
      have ha : raw28340step2 = (fun i j => raw28340step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28340step2 raw28340step1; decide +kernel
      have hl : raw28340step2Labels = raw28340step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28340step1 raw28340step1Labels permutation31 permutation3
    mixedMoment B raw28340step2 raw28340step2Labels = mixedMoment B raw28340step3 raw28340step3Labels := by
      have ha : raw28340step3 = -raw28340step2 := by apply Matrix.ext; change ∀ i j, raw28340step3 i j = -(raw28340step2 i j); unfold raw28340step3 raw28340step2; decide +kernel
      have hl : raw28340step3Labels = raw28340step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28340step3 raw28340step3Labels = mixedMoment B raw28340step4 raw28340step4Labels := by
      have ha : raw28340step4 = raw28340step3 := by apply Matrix.ext; unfold raw28340step4 raw28340step3; decide +kernel
      have hl : raw28340step3Labels = labelEmbedding6 ∘ raw28340step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28340step3 raw28340step3Labels raw28340step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw28341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28341step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28341step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28341step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28341 raw28341Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw28341 raw28341Labels = mixedMoment B raw28341step0 raw28341step0Labels := by
      have hz : ∀ j, raw28341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28341step0 = (fun i j => raw28341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28341step0 raw28341; decide +kernel
      have hl : raw28341step0Labels = raw28341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28341 raw28341Labels permutation434 hz
    mixedMoment B raw28341step0 raw28341step0Labels = mixedMoment B raw28341step1 raw28341step1Labels := by
      have hz : ∀ j, raw28341step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28341step1 = (fun i j => raw28341step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28341step1 raw28341step0; decide +kernel
      have hl : raw28341step1Labels = raw28341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28341step0 raw28341step0Labels permutation80 hz
    mixedMoment B raw28341step1 raw28341step1Labels = mixedMoment B raw28341step2 raw28341step2Labels := by
      have ha : raw28341step2 = (fun i j => raw28341step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28341step2 raw28341step1; decide +kernel
      have hl : raw28341step2Labels = raw28341step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28341step1 raw28341step1Labels permutation8 permutation3
    mixedMoment B raw28341step2 raw28341step2Labels = mixedMoment B raw28341step3 raw28341step3Labels := by
      have ha : raw28341step3 = raw28341step2 := by apply Matrix.ext; unfold raw28341step3 raw28341step2; decide +kernel
      have hl : raw28341step2Labels = labelEmbedding6 ∘ raw28341step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28341step2 raw28341step2Labels raw28341step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw28342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28342step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28342step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28342step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28342step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28342 raw28342Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw28342 raw28342Labels = mixedMoment B raw28342step0 raw28342step0Labels := by
      have hz : ∀ j, raw28342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28342step0 = (fun i j => raw28342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28342step0 raw28342; decide +kernel
      have hl : raw28342step0Labels = raw28342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28342 raw28342Labels permutation434 hz
    mixedMoment B raw28342step0 raw28342step0Labels = mixedMoment B raw28342step1 raw28342step1Labels := by
      have ha : raw28342step1 = (fun i j => raw28342step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28342step1 raw28342step0; decide +kernel
      have hl : raw28342step1Labels = raw28342step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28342step0 raw28342step0Labels permutation149 permutation3
    mixedMoment B raw28342step1 raw28342step1Labels = mixedMoment B raw28342step2 raw28342step2Labels := by
      have ha : raw28342step2 = -raw28342step1 := by apply Matrix.ext; change ∀ i j, raw28342step2 i j = -(raw28342step1 i j); unfold raw28342step2 raw28342step1; decide +kernel
      have hl : raw28342step2Labels = raw28342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28342step2 raw28342step2Labels = mixedMoment B raw28342step3 raw28342step3Labels := by
      have ha : raw28342step3 = raw28342step2 := by apply Matrix.ext; unfold raw28342step3 raw28342step2; decide +kernel
      have hl : raw28342step2Labels = labelEmbedding6 ∘ raw28342step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28342step2 raw28342step2Labels raw28342step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw28343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28343step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28343step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28343step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28343step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28343 raw28343Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw28343 raw28343Labels = mixedMoment B raw28343step0 raw28343step0Labels := by
      have hz : ∀ j, raw28343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28343step0 = (fun i j => raw28343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28343step0 raw28343; decide +kernel
      have hl : raw28343step0Labels = raw28343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28343 raw28343Labels permutation346 hz
    mixedMoment B raw28343step0 raw28343step0Labels = mixedMoment B raw28343step1 raw28343step1Labels := by
      have ha : raw28343step1 = (fun i j => raw28343step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28343step1 raw28343step0; decide +kernel
      have hl : raw28343step1Labels = raw28343step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28343step0 raw28343step0Labels permutation149 permutation3
    mixedMoment B raw28343step1 raw28343step1Labels = mixedMoment B raw28343step2 raw28343step2Labels := by
      have ha : raw28343step2 = -raw28343step1 := by apply Matrix.ext; change ∀ i j, raw28343step2 i j = -(raw28343step1 i j); unfold raw28343step2 raw28343step1; decide +kernel
      have hl : raw28343step2Labels = raw28343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28343step2 raw28343step2Labels = mixedMoment B raw28343step3 raw28343step3Labels := by
      have ha : raw28343step3 = raw28343step2 := by apply Matrix.ext; unfold raw28343step3 raw28343step2; decide +kernel
      have hl : raw28343step2Labels = labelEmbedding6 ∘ raw28343step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28343step2 raw28343step2Labels raw28343step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw28344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw28344step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28344step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw28344step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28344step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw28344step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28344 raw28344Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw28344 raw28344Labels = mixedMoment B raw28344step0 raw28344step0Labels := by
      have hz : ∀ j, raw28344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28344step0 = (fun i j => raw28344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28344step0 raw28344; decide +kernel
      have hl : raw28344step0Labels = raw28344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28344 raw28344Labels permutation434 hz
    mixedMoment B raw28344step0 raw28344step0Labels = mixedMoment B raw28344step1 raw28344step1Labels := by
      have hz : ∀ j, raw28344step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28344step1 = (fun i j => raw28344step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28344step1 raw28344step0; decide +kernel
      have hl : raw28344step1Labels = raw28344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28344step0 raw28344step0Labels permutation80 hz
    mixedMoment B raw28344step1 raw28344step1Labels = mixedMoment B raw28344step2 raw28344step2Labels := by
      have ha : raw28344step2 = (fun i j => raw28344step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28344step2 raw28344step1; decide +kernel
      have hl : raw28344step2Labels = raw28344step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28344step1 raw28344step1Labels permutation29 permutation3
    mixedMoment B raw28344step2 raw28344step2Labels = mixedMoment B raw28344step3 raw28344step3Labels := by
      have ha : raw28344step3 = -raw28344step2 := by apply Matrix.ext; change ∀ i j, raw28344step3 i j = -(raw28344step2 i j); unfold raw28344step3 raw28344step2; decide +kernel
      have hl : raw28344step3Labels = raw28344step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28344step3 raw28344step3Labels = mixedMoment B raw28344step4 raw28344step4Labels := by
      have ha : raw28344step4 = raw28344step3 := by apply Matrix.ext; unfold raw28344step4 raw28344step3; decide +kernel
      have hl : raw28344step3Labels = labelEmbedding6 ∘ raw28344step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28344step3 raw28344step3Labels raw28344step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw28345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28345step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28345 raw28345Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw28345 raw28345Labels = mixedMoment B raw28345step0 raw28345step0Labels := by
      have hz : ∀ j, raw28345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28345step0 = (fun i j => raw28345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28345step0 raw28345; decide +kernel
      have hl : raw28345step0Labels = raw28345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28345 raw28345Labels permutation434 hz
    mixedMoment B raw28345step0 raw28345step0Labels = mixedMoment B raw28345step1 raw28345step1Labels := by
      have ha : raw28345step1 = (fun i j => raw28345step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28345step1 raw28345step0; decide +kernel
      have hl : raw28345step1Labels = raw28345step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28345step0 raw28345step0Labels permutation34 permutation3
    mixedMoment B raw28345step1 raw28345step1Labels = mixedMoment B raw28345step2 raw28345step2Labels := by
      have ha : raw28345step2 = raw28345step1 := by apply Matrix.ext; unfold raw28345step2 raw28345step1; decide +kernel
      have hl : raw28345step1Labels = labelEmbedding6 ∘ raw28345step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28345step1 raw28345step1Labels raw28345step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

def raw28346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw28346step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28346step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28346step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28346step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28346 raw28346Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw28346 raw28346Labels = mixedMoment B raw28346step0 raw28346step0Labels := by
      have hz : ∀ j, raw28346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28346step0 = (fun i j => raw28346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28346step0 raw28346; decide +kernel
      have hl : raw28346step0Labels = raw28346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28346 raw28346Labels permutation434 hz
    mixedMoment B raw28346step0 raw28346step0Labels = mixedMoment B raw28346step1 raw28346step1Labels := by
      have ha : raw28346step1 = (fun i j => raw28346step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28346step1 raw28346step0; decide +kernel
      have hl : raw28346step1Labels = raw28346step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28346step0 raw28346step0Labels permutation145 permutation3
    mixedMoment B raw28346step1 raw28346step1Labels = mixedMoment B raw28346step2 raw28346step2Labels := by
      have ha : raw28346step2 = -raw28346step1 := by apply Matrix.ext; change ∀ i j, raw28346step2 i j = -(raw28346step1 i j); unfold raw28346step2 raw28346step1; decide +kernel
      have hl : raw28346step2Labels = raw28346step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28346step2 raw28346step2Labels = mixedMoment B raw28346step3 raw28346step3Labels := by
      have ha : raw28346step3 = raw28346step2 := by apply Matrix.ext; unfold raw28346step3 raw28346step2; decide +kernel
      have hl : raw28346step2Labels = labelEmbedding6 ∘ raw28346step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28346step2 raw28346step2Labels raw28346step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

def raw28347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28347step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28347step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28347step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28347 raw28347Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw28347 raw28347Labels = mixedMoment B raw28347step0 raw28347step0Labels := by
      have ha : raw28347step0 = (fun i j => raw28347 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28347step0 raw28347; decide +kernel
      have hl : raw28347step0Labels = raw28347Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28347 raw28347Labels permutation646 permutation3
    mixedMoment B raw28347step0 raw28347step0Labels = mixedMoment B raw28347step1 raw28347step1Labels := by
      have ha : raw28347step1 = -raw28347step0 := by apply Matrix.ext; change ∀ i j, raw28347step1 i j = -(raw28347step0 i j); unfold raw28347step1 raw28347step0; decide +kernel
      have hl : raw28347step1Labels = raw28347step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28347step1 raw28347step1Labels = mixedMoment B raw28347step2 raw28347step2Labels := by
      have ha : raw28347step2 = raw28347step1 := by apply Matrix.ext; unfold raw28347step2 raw28347step1; decide +kernel
      have hl : raw28347step1Labels = labelEmbedding6 ∘ raw28347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28347step1 raw28347step1Labels raw28347step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

def raw28348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28348step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28348step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28348step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28348step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28348 raw28348Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw28348 raw28348Labels = mixedMoment B raw28348step0 raw28348step0Labels := by
      have hz : ∀ j, raw28348 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28348step0 = (fun i j => raw28348 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28348step0 raw28348; decide +kernel
      have hl : raw28348step0Labels = raw28348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28348 raw28348Labels permutation434 hz
    mixedMoment B raw28348step0 raw28348step0Labels = mixedMoment B raw28348step1 raw28348step1Labels := by
      have ha : raw28348step1 = (fun i j => raw28348step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28348step1 raw28348step0; decide +kernel
      have hl : raw28348step1Labels = raw28348step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28348step0 raw28348step0Labels permutation145 permutation3
    mixedMoment B raw28348step1 raw28348step1Labels = mixedMoment B raw28348step2 raw28348step2Labels := by
      have ha : raw28348step2 = -raw28348step1 := by apply Matrix.ext; change ∀ i j, raw28348step2 i j = -(raw28348step1 i j); unfold raw28348step2 raw28348step1; decide +kernel
      have hl : raw28348step2Labels = raw28348step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28348step2 raw28348step2Labels = mixedMoment B raw28348step3 raw28348step3Labels := by
      have ha : raw28348step3 = raw28348step2 := by apply Matrix.ext; unfold raw28348step3 raw28348step2; decide +kernel
      have hl : raw28348step2Labels = labelEmbedding6 ∘ raw28348step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28348step2 raw28348step2Labels raw28348step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw28349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28349 raw28349Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw28349 raw28349Labels = mixedMoment B raw28349step0 raw28349step0Labels := by
      have hz : ∀ j, raw28349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28349step0 = (fun i j => raw28349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28349step0 raw28349; decide +kernel
      have hl : raw28349step0Labels = raw28349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28349 raw28349Labels permutation434 hz
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw28350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28350step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28350step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28350 raw28350Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw28350 raw28350Labels = mixedMoment B raw28350step0 raw28350step0Labels := by
      have hz : ∀ j, raw28350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28350step0 = (fun i j => raw28350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28350step0 raw28350; decide +kernel
      have hl : raw28350step0Labels = raw28350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28350 raw28350Labels permutation346 hz
    mixedMoment B raw28350step0 raw28350step0Labels = mixedMoment B raw28350step1 raw28350step1Labels := by
      have ha : raw28350step1 = (fun i j => raw28350step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28350step1 raw28350step0; decide +kernel
      have hl : raw28350step1Labels = raw28350step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28350step0 raw28350step0Labels permutation34 permutation3
    mixedMoment B raw28350step1 raw28350step1Labels = mixedMoment B raw28350step2 raw28350step2Labels := by
      have ha : raw28350step2 = raw28350step1 := by apply Matrix.ext; unfold raw28350step2 raw28350step1; decide +kernel
      have hl : raw28350step1Labels = labelEmbedding6 ∘ raw28350step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28350step1 raw28350step1Labels raw28350step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

def raw28351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw28351step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28351step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28351step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28351step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28351 raw28351Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw28351 raw28351Labels = mixedMoment B raw28351step0 raw28351step0Labels := by
      have hz : ∀ j, raw28351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28351step0 = (fun i j => raw28351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28351step0 raw28351; decide +kernel
      have hl : raw28351step0Labels = raw28351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28351 raw28351Labels permutation346 hz
    mixedMoment B raw28351step0 raw28351step0Labels = mixedMoment B raw28351step1 raw28351step1Labels := by
      have ha : raw28351step1 = (fun i j => raw28351step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28351step1 raw28351step0; decide +kernel
      have hl : raw28351step1Labels = raw28351step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28351step0 raw28351step0Labels permutation145 permutation3
    mixedMoment B raw28351step1 raw28351step1Labels = mixedMoment B raw28351step2 raw28351step2Labels := by
      have ha : raw28351step2 = -raw28351step1 := by apply Matrix.ext; change ∀ i j, raw28351step2 i j = -(raw28351step1 i j); unfold raw28351step2 raw28351step1; decide +kernel
      have hl : raw28351step2Labels = raw28351step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28351step2 raw28351step2Labels = mixedMoment B raw28351step3 raw28351step3Labels := by
      have ha : raw28351step3 = raw28351step2 := by apply Matrix.ext; unfold raw28351step3 raw28351step2; decide +kernel
      have hl : raw28351step2Labels = labelEmbedding6 ∘ raw28351step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28351step2 raw28351step2Labels raw28351step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

def raw28352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28352step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28352step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28352step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28352 raw28352Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw28352 raw28352Labels = mixedMoment B raw28352step0 raw28352step0Labels := by
      have ha : raw28352step0 = (fun i j => raw28352 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28352step0 raw28352; decide +kernel
      have hl : raw28352step0Labels = raw28352Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28352 raw28352Labels permutation664 permutation3
    mixedMoment B raw28352step0 raw28352step0Labels = mixedMoment B raw28352step1 raw28352step1Labels := by
      have ha : raw28352step1 = -raw28352step0 := by apply Matrix.ext; change ∀ i j, raw28352step1 i j = -(raw28352step0 i j); unfold raw28352step1 raw28352step0; decide +kernel
      have hl : raw28352step1Labels = raw28352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28352step1 raw28352step1Labels = mixedMoment B raw28352step2 raw28352step2Labels := by
      have ha : raw28352step2 = raw28352step1 := by apply Matrix.ext; unfold raw28352step2 raw28352step1; decide +kernel
      have hl : raw28352step1Labels = labelEmbedding6 ∘ raw28352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28352step1 raw28352step1Labels raw28352step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

def raw28353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28353step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28353step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28353step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28353 raw28353Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw28353 raw28353Labels = mixedMoment B raw28353step0 raw28353step0Labels := by
      have hz : ∀ j, raw28353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28353step0 = (fun i j => raw28353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28353step0 raw28353; decide +kernel
      have hl : raw28353step0Labels = raw28353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28353 raw28353Labels permutation346 hz
    mixedMoment B raw28353step0 raw28353step0Labels = mixedMoment B raw28353step1 raw28353step1Labels := by
      have ha : raw28353step1 = (fun i j => raw28353step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28353step1 raw28353step0; decide +kernel
      have hl : raw28353step1Labels = raw28353step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28353step0 raw28353step0Labels permutation145 permutation3
    mixedMoment B raw28353step1 raw28353step1Labels = mixedMoment B raw28353step2 raw28353step2Labels := by
      have ha : raw28353step2 = -raw28353step1 := by apply Matrix.ext; change ∀ i j, raw28353step2 i j = -(raw28353step1 i j); unfold raw28353step2 raw28353step1; decide +kernel
      have hl : raw28353step2Labels = raw28353step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28353step2 raw28353step2Labels = mixedMoment B raw28353step3 raw28353step3Labels := by
      have ha : raw28353step3 = raw28353step2 := by apply Matrix.ext; unfold raw28353step3 raw28353step2; decide +kernel
      have hl : raw28353step2Labels = labelEmbedding6 ∘ raw28353step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28353step2 raw28353step2Labels raw28353step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw28354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28354 raw28354Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw28354 raw28354Labels = mixedMoment B raw28354step0 raw28354step0Labels := by
      have hz : ∀ j, raw28354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28354step0 = (fun i j => raw28354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28354step0 raw28354; decide +kernel
      have hl : raw28354step0Labels = raw28354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28354 raw28354Labels permutation346 hz
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw28355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw28355step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw28355step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28355 raw28355Labels = mixedMoment B node4519 node4519Labels := by
  calc
    mixedMoment B raw28355 raw28355Labels = mixedMoment B raw28355step0 raw28355step0Labels := by
      have hz : ∀ j, raw28355 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28355step0 = (fun i j => raw28355 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28355step0 raw28355; decide +kernel
      have hl : raw28355step0Labels = raw28355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28355 raw28355Labels permutation434 hz
    mixedMoment B raw28355step0 raw28355step0Labels = mixedMoment B raw28355step1 raw28355step1Labels := by
      have hz : ∀ j, raw28355step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28355step1 = (fun i j => raw28355step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28355step1 raw28355step0; decide +kernel
      have hl : raw28355step1Labels = raw28355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28355step0 raw28355step0Labels permutation80 hz
    mixedMoment B raw28355step1 raw28355step1Labels = mixedMoment B raw28355step2 raw28355step2Labels := by
      have ha : raw28355step2 = (fun i j => raw28355step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28355step2 raw28355step1; decide +kernel
      have hl : raw28355step2Labels = raw28355step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28355step1 raw28355step1Labels permutation8 permutation3
    mixedMoment B raw28355step2 raw28355step2Labels = mixedMoment B raw28355step3 raw28355step3Labels := by
      have ha : raw28355step3 = raw28355step2 := by apply Matrix.ext; unfold raw28355step3 raw28355step2; decide +kernel
      have hl : raw28355step2Labels = labelEmbedding6 ∘ raw28355step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28355step2 raw28355step2Labels raw28355step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4519 node4519Labels := by rfl

def raw28356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28356step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw28356step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28356step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw28356step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28356step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw28356step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28356 raw28356Labels = mixedMoment B node4657 node4657Labels := by
  calc
    mixedMoment B raw28356 raw28356Labels = mixedMoment B raw28356step0 raw28356step0Labels := by
      have hz : ∀ j, raw28356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28356step0 = (fun i j => raw28356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28356step0 raw28356; decide +kernel
      have hl : raw28356step0Labels = raw28356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28356 raw28356Labels permutation434 hz
    mixedMoment B raw28356step0 raw28356step0Labels = mixedMoment B raw28356step1 raw28356step1Labels := by
      have hz : ∀ j, raw28356step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28356step1 = (fun i j => raw28356step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28356step1 raw28356step0; decide +kernel
      have hl : raw28356step1Labels = raw28356step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28356step0 raw28356step0Labels permutation80 hz
    mixedMoment B raw28356step1 raw28356step1Labels = mixedMoment B raw28356step2 raw28356step2Labels := by
      have ha : raw28356step2 = (fun i j => raw28356step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28356step2 raw28356step1; decide +kernel
      have hl : raw28356step2Labels = raw28356step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28356step1 raw28356step1Labels permutation31 permutation3
    mixedMoment B raw28356step2 raw28356step2Labels = mixedMoment B raw28356step3 raw28356step3Labels := by
      have ha : raw28356step3 = -raw28356step2 := by apply Matrix.ext; change ∀ i j, raw28356step3 i j = -(raw28356step2 i j); unfold raw28356step3 raw28356step2; decide +kernel
      have hl : raw28356step3Labels = raw28356step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28356step3 raw28356step3Labels = mixedMoment B raw28356step4 raw28356step4Labels := by
      have ha : raw28356step4 = raw28356step3 := by apply Matrix.ext; unfold raw28356step4 raw28356step3; decide +kernel
      have hl : raw28356step3Labels = labelEmbedding6 ∘ raw28356step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28356step3 raw28356step3Labels raw28356step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4657 node4657Labels := by rfl

def raw28357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28357step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28357step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28357step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28357step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28357 raw28357Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw28357 raw28357Labels = mixedMoment B raw28357step0 raw28357step0Labels := by
      have hz : ∀ j, raw28357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28357step0 = (fun i j => raw28357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28357step0 raw28357; decide +kernel
      have hl : raw28357step0Labels = raw28357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28357 raw28357Labels permutation434 hz
    mixedMoment B raw28357step0 raw28357step0Labels = mixedMoment B raw28357step1 raw28357step1Labels := by
      have ha : raw28357step1 = (fun i j => raw28357step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28357step1 raw28357step0; decide +kernel
      have hl : raw28357step1Labels = raw28357step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28357step0 raw28357step0Labels permutation151 permutation3
    mixedMoment B raw28357step1 raw28357step1Labels = mixedMoment B raw28357step2 raw28357step2Labels := by
      have ha : raw28357step2 = -raw28357step1 := by apply Matrix.ext; change ∀ i j, raw28357step2 i j = -(raw28357step1 i j); unfold raw28357step2 raw28357step1; decide +kernel
      have hl : raw28357step2Labels = raw28357step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28357step2 raw28357step2Labels = mixedMoment B raw28357step3 raw28357step3Labels := by
      have ha : raw28357step3 = raw28357step2 := by apply Matrix.ext; unfold raw28357step3 raw28357step2; decide +kernel
      have hl : raw28357step2Labels = labelEmbedding6 ∘ raw28357step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28357step2 raw28357step2Labels raw28357step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

def raw28358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28358step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28358step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28358step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28358 raw28358Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw28358 raw28358Labels = mixedMoment B raw28358step0 raw28358step0Labels := by
      have hz : ∀ j, raw28358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28358step0 = (fun i j => raw28358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28358step0 raw28358; decide +kernel
      have hl : raw28358step0Labels = raw28358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28358 raw28358Labels permutation346 hz
    mixedMoment B raw28358step0 raw28358step0Labels = mixedMoment B raw28358step1 raw28358step1Labels := by
      have ha : raw28358step1 = (fun i j => raw28358step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28358step1 raw28358step0; decide +kernel
      have hl : raw28358step1Labels = raw28358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28358step0 raw28358step0Labels permutation151 permutation3
    mixedMoment B raw28358step1 raw28358step1Labels = mixedMoment B raw28358step2 raw28358step2Labels := by
      have ha : raw28358step2 = -raw28358step1 := by apply Matrix.ext; change ∀ i j, raw28358step2 i j = -(raw28358step1 i j); unfold raw28358step2 raw28358step1; decide +kernel
      have hl : raw28358step2Labels = raw28358step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28358step2 raw28358step2Labels = mixedMoment B raw28358step3 raw28358step3Labels := by
      have ha : raw28358step3 = raw28358step2 := by apply Matrix.ext; unfold raw28358step3 raw28358step2; decide +kernel
      have hl : raw28358step2Labels = labelEmbedding6 ∘ raw28358step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28358step2 raw28358step2Labels raw28358step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

def raw28359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw28359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw28359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw28359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw28359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28359 raw28359Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw28359 raw28359Labels = mixedMoment B raw28359step0 raw28359step0Labels := by
      have hz : ∀ j, raw28359 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28359step0 = (fun i j => raw28359 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28359step0 raw28359; decide +kernel
      have hl : raw28359step0Labels = raw28359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28359 raw28359Labels permutation434 hz
    mixedMoment B raw28359step0 raw28359step0Labels = mixedMoment B raw28359step1 raw28359step1Labels := by
      have hz : ∀ j, raw28359step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28359step1 = (fun i j => raw28359step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28359step1 raw28359step0; decide +kernel
      have hl : raw28359step1Labels = raw28359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28359step0 raw28359step0Labels permutation80 hz
    mixedMoment B raw28359step1 raw28359step1Labels = mixedMoment B raw28359step2 raw28359step2Labels := by
      have ha : raw28359step2 = (fun i j => raw28359step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28359step2 raw28359step1; decide +kernel
      have hl : raw28359step2Labels = raw28359step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28359step1 raw28359step1Labels permutation9 permutation2
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw28360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw28360step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28360step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw28360step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28360step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw28360step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28360 raw28360Labels = mixedMoment B node4225 node4225Labels := by
  calc
    mixedMoment B raw28360 raw28360Labels = mixedMoment B raw28360step0 raw28360step0Labels := by
      have hz : ∀ j, raw28360 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28360step0 = (fun i j => raw28360 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28360step0 raw28360; decide +kernel
      have hl : raw28360step0Labels = raw28360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28360 raw28360Labels permutation434 hz
    mixedMoment B raw28360step0 raw28360step0Labels = mixedMoment B raw28360step1 raw28360step1Labels := by
      have hz : ∀ j, raw28360step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28360step1 = (fun i j => raw28360step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28360step1 raw28360step0; decide +kernel
      have hl : raw28360step1Labels = raw28360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28360step0 raw28360step0Labels permutation80 hz
    mixedMoment B raw28360step1 raw28360step1Labels = mixedMoment B raw28360step2 raw28360step2Labels := by
      have ha : raw28360step2 = (fun i j => raw28360step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28360step2 raw28360step1; decide +kernel
      have hl : raw28360step2Labels = raw28360step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28360step1 raw28360step1Labels permutation31 permutation3
    mixedMoment B raw28360step2 raw28360step2Labels = mixedMoment B raw28360step3 raw28360step3Labels := by
      have ha : raw28360step3 = -raw28360step2 := by apply Matrix.ext; change ∀ i j, raw28360step3 i j = -(raw28360step2 i j); unfold raw28360step3 raw28360step2; decide +kernel
      have hl : raw28360step3Labels = raw28360step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28360step3 raw28360step3Labels = mixedMoment B raw28360step4 raw28360step4Labels := by
      have ha : raw28360step4 = raw28360step3 := by apply Matrix.ext; unfold raw28360step4 raw28360step3; decide +kernel
      have hl : raw28360step3Labels = labelEmbedding6 ∘ raw28360step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28360step3 raw28360step3Labels raw28360step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4225 node4225Labels := by rfl

def raw28361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw28361step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28361step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28361step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28361step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28361step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28361 raw28361Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw28361 raw28361Labels = mixedMoment B raw28361step0 raw28361step0Labels := by
      have hz : ∀ j, raw28361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28361step0 = (fun i j => raw28361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28361step0 raw28361; decide +kernel
      have hl : raw28361step0Labels = raw28361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28361 raw28361Labels permutation434 hz
    mixedMoment B raw28361step0 raw28361step0Labels = mixedMoment B raw28361step1 raw28361step1Labels := by
      have hz : ∀ j, raw28361step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28361step1 = (fun i j => raw28361step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28361step1 raw28361step0; decide +kernel
      have hl : raw28361step1Labels = raw28361step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28361step0 raw28361step0Labels permutation80 hz
    mixedMoment B raw28361step1 raw28361step1Labels = mixedMoment B raw28361step2 raw28361step2Labels := by
      have ha : raw28361step2 = (fun i j => raw28361step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28361step2 raw28361step1; decide +kernel
      have hl : raw28361step2Labels = raw28361step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28361step1 raw28361step1Labels permutation31 permutation3
    mixedMoment B raw28361step2 raw28361step2Labels = mixedMoment B raw28361step3 raw28361step3Labels := by
      have ha : raw28361step3 = -raw28361step2 := by apply Matrix.ext; change ∀ i j, raw28361step3 i j = -(raw28361step2 i j); unfold raw28361step3 raw28361step2; decide +kernel
      have hl : raw28361step3Labels = raw28361step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28361step3 raw28361step3Labels = mixedMoment B raw28361step4 raw28361step4Labels := by
      have ha : raw28361step4 = raw28361step3 := by apply Matrix.ext; unfold raw28361step4 raw28361step3; decide +kernel
      have hl : raw28361step3Labels = labelEmbedding6 ∘ raw28361step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28361step3 raw28361step3Labels raw28361step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

def raw28362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28362step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28362step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28362step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28362step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28362 raw28362Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw28362 raw28362Labels = mixedMoment B raw28362step0 raw28362step0Labels := by
      have hz : ∀ j, raw28362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28362step0 = (fun i j => raw28362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28362step0 raw28362; decide +kernel
      have hl : raw28362step0Labels = raw28362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28362 raw28362Labels permutation434 hz
    mixedMoment B raw28362step0 raw28362step0Labels = mixedMoment B raw28362step1 raw28362step1Labels := by
      have ha : raw28362step1 = (fun i j => raw28362step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28362step1 raw28362step0; decide +kernel
      have hl : raw28362step1Labels = raw28362step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28362step0 raw28362step0Labels permutation151 permutation3
    mixedMoment B raw28362step1 raw28362step1Labels = mixedMoment B raw28362step2 raw28362step2Labels := by
      have ha : raw28362step2 = -raw28362step1 := by apply Matrix.ext; change ∀ i j, raw28362step2 i j = -(raw28362step1 i j); unfold raw28362step2 raw28362step1; decide +kernel
      have hl : raw28362step2Labels = raw28362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28362step2 raw28362step2Labels = mixedMoment B raw28362step3 raw28362step3Labels := by
      have ha : raw28362step3 = raw28362step2 := by apply Matrix.ext; unfold raw28362step3 raw28362step2; decide +kernel
      have hl : raw28362step2Labels = labelEmbedding6 ∘ raw28362step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28362step2 raw28362step2Labels raw28362step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4219 node4219Labels := by rfl

def raw28363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28363step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28363step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28363step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28363step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28363 raw28363Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw28363 raw28363Labels = mixedMoment B raw28363step0 raw28363step0Labels := by
      have hz : ∀ j, raw28363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28363step0 = (fun i j => raw28363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28363step0 raw28363; decide +kernel
      have hl : raw28363step0Labels = raw28363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28363 raw28363Labels permutation346 hz
    mixedMoment B raw28363step0 raw28363step0Labels = mixedMoment B raw28363step1 raw28363step1Labels := by
      have ha : raw28363step1 = (fun i j => raw28363step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28363step1 raw28363step0; decide +kernel
      have hl : raw28363step1Labels = raw28363step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28363step0 raw28363step0Labels permutation151 permutation3
    mixedMoment B raw28363step1 raw28363step1Labels = mixedMoment B raw28363step2 raw28363step2Labels := by
      have ha : raw28363step2 = -raw28363step1 := by apply Matrix.ext; change ∀ i j, raw28363step2 i j = -(raw28363step1 i j); unfold raw28363step2 raw28363step1; decide +kernel
      have hl : raw28363step2Labels = raw28363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28363step2 raw28363step2Labels = mixedMoment B raw28363step3 raw28363step3Labels := by
      have ha : raw28363step3 = raw28363step2 := by apply Matrix.ext; unfold raw28363step3 raw28363step2; decide +kernel
      have hl : raw28363step2Labels = labelEmbedding6 ∘ raw28363step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28363step2 raw28363step2Labels raw28363step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4219 node4219Labels := by rfl

def raw28364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -4, 0]]
def raw28364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![4, -4, 0]]
def raw28364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28364step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28364step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28364step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28364step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28364step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28364step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28364 raw28364Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw28364 raw28364Labels = mixedMoment B raw28364step0 raw28364step0Labels := by
      have hz : ∀ j, raw28364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28364step0 = (fun i j => raw28364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28364step0 raw28364; decide +kernel
      have hl : raw28364step0Labels = raw28364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28364 raw28364Labels permutation434 hz
    mixedMoment B raw28364step0 raw28364step0Labels = mixedMoment B raw28364step1 raw28364step1Labels := by
      have hz : ∀ j, raw28364step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28364step1 = (fun i j => raw28364step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28364step1 raw28364step0; decide +kernel
      have hl : raw28364step1Labels = raw28364step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28364step0 raw28364step0Labels permutation80 hz
    mixedMoment B raw28364step1 raw28364step1Labels = mixedMoment B raw28364step2 raw28364step2Labels := by
      have ha : raw28364step2 = (fun i j => raw28364step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28364step2 raw28364step1; decide +kernel
      have hl : raw28364step2Labels = raw28364step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28364step1 raw28364step1Labels permutation31 permutation3
    mixedMoment B raw28364step2 raw28364step2Labels = mixedMoment B raw28364step3 raw28364step3Labels := by
      have ha : raw28364step3 = -raw28364step2 := by apply Matrix.ext; change ∀ i j, raw28364step3 i j = -(raw28364step2 i j); unfold raw28364step3 raw28364step2; decide +kernel
      have hl : raw28364step3Labels = raw28364step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28364step3 raw28364step3Labels = mixedMoment B raw28364step4 raw28364step4Labels := by
      have ha : raw28364step4 = raw28364step3 := by apply Matrix.ext; unfold raw28364step4 raw28364step3; decide +kernel
      have hl : raw28364step3Labels = labelEmbedding6 ∘ raw28364step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28364step3 raw28364step3Labels raw28364step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw28365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw28365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28365step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28365step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28365 raw28365Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw28365 raw28365Labels = mixedMoment B raw28365step0 raw28365step0Labels := by
      have hz : ∀ j, raw28365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28365step0 = (fun i j => raw28365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28365step0 raw28365; decide +kernel
      have hl : raw28365step0Labels = raw28365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28365 raw28365Labels permutation434 hz
    mixedMoment B raw28365step0 raw28365step0Labels = mixedMoment B raw28365step1 raw28365step1Labels := by
      have hz : ∀ j, raw28365step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28365step1 = (fun i j => raw28365step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28365step1 raw28365step0; decide +kernel
      have hl : raw28365step1Labels = raw28365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28365step0 raw28365step0Labels permutation80 hz
    mixedMoment B raw28365step1 raw28365step1Labels = mixedMoment B raw28365step2 raw28365step2Labels := by
      have ha : raw28365step2 = (fun i j => raw28365step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28365step2 raw28365step1; decide +kernel
      have hl : raw28365step2Labels = raw28365step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28365step1 raw28365step1Labels permutation30 permutation3
    mixedMoment B raw28365step2 raw28365step2Labels = mixedMoment B raw28365step3 raw28365step3Labels := by
      have ha : raw28365step3 = -raw28365step2 := by apply Matrix.ext; change ∀ i j, raw28365step3 i j = -(raw28365step2 i j); unfold raw28365step3 raw28365step2; decide +kernel
      have hl : raw28365step3Labels = raw28365step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw28366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw28366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28366 raw28366Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw28366 raw28366Labels = mixedMoment B raw28366step0 raw28366step0Labels := by
      have hz : ∀ j, raw28366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28366step0 = (fun i j => raw28366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28366step0 raw28366; decide +kernel
      have hl : raw28366step0Labels = raw28366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28366 raw28366Labels permutation434 hz
    mixedMoment B raw28366step0 raw28366step0Labels = mixedMoment B raw28366step1 raw28366step1Labels := by
      have ha : raw28366step1 = (fun i j => raw28366step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28366step1 raw28366step0; decide +kernel
      have hl : raw28366step1Labels = raw28366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28366step0 raw28366step0Labels permutation151 permutation3
    mixedMoment B raw28366step1 raw28366step1Labels = mixedMoment B raw28366step2 raw28366step2Labels := by
      have ha : raw28366step2 = -raw28366step1 := by apply Matrix.ext; change ∀ i j, raw28366step2 i j = -(raw28366step1 i j); unfold raw28366step2 raw28366step1; decide +kernel
      have hl : raw28366step2Labels = raw28366step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw28367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw28367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28367step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28367 raw28367Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw28367 raw28367Labels = mixedMoment B raw28367step0 raw28367step0Labels := by
      have hz : ∀ j, raw28367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28367step0 = (fun i j => raw28367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28367step0 raw28367; decide +kernel
      have hl : raw28367step0Labels = raw28367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28367 raw28367Labels permutation346 hz
    mixedMoment B raw28367step0 raw28367step0Labels = mixedMoment B raw28367step1 raw28367step1Labels := by
      have ha : raw28367step1 = (fun i j => raw28367step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28367step1 raw28367step0; decide +kernel
      have hl : raw28367step1Labels = raw28367step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28367step0 raw28367step0Labels permutation151 permutation3
    mixedMoment B raw28367step1 raw28367step1Labels = mixedMoment B raw28367step2 raw28367step2Labels := by
      have ha : raw28367step2 = -raw28367step1 := by apply Matrix.ext; change ∀ i j, raw28367step2 i j = -(raw28367step1 i j); unfold raw28367step2 raw28367step1; decide +kernel
      have hl : raw28367step2Labels = raw28367step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw28368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28368step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28368step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw28368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28368step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28368step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28368 raw28368Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw28368 raw28368Labels = mixedMoment B raw28368step0 raw28368step0Labels := by
      have hz : ∀ j, raw28368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28368step0 = (fun i j => raw28368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28368step0 raw28368; decide +kernel
      have hl : raw28368step0Labels = raw28368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28368 raw28368Labels permutation434 hz
    mixedMoment B raw28368step0 raw28368step0Labels = mixedMoment B raw28368step1 raw28368step1Labels := by
      have hz : ∀ j, raw28368step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28368step1 = (fun i j => raw28368step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28368step1 raw28368step0; decide +kernel
      have hl : raw28368step1Labels = raw28368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28368step0 raw28368step0Labels permutation80 hz
    mixedMoment B raw28368step1 raw28368step1Labels = mixedMoment B raw28368step2 raw28368step2Labels := by
      have ha : raw28368step2 = (fun i j => raw28368step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28368step2 raw28368step1; decide +kernel
      have hl : raw28368step2Labels = raw28368step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28368step1 raw28368step1Labels permutation31 permutation3
    mixedMoment B raw28368step2 raw28368step2Labels = mixedMoment B raw28368step3 raw28368step3Labels := by
      have ha : raw28368step3 = -raw28368step2 := by apply Matrix.ext; change ∀ i j, raw28368step3 i j = -(raw28368step2 i j); unfold raw28368step3 raw28368step2; decide +kernel
      have hl : raw28368step3Labels = raw28368step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw28369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28369step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28369step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28369step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw28369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28369step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28369step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28369 raw28369Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw28369 raw28369Labels = mixedMoment B raw28369step0 raw28369step0Labels := by
      have hz : ∀ j, raw28369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28369step0 = (fun i j => raw28369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28369step0 raw28369; decide +kernel
      have hl : raw28369step0Labels = raw28369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28369 raw28369Labels permutation434 hz
    mixedMoment B raw28369step0 raw28369step0Labels = mixedMoment B raw28369step1 raw28369step1Labels := by
      have hz : ∀ j, raw28369step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28369step1 = (fun i j => raw28369step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28369step1 raw28369step0; decide +kernel
      have hl : raw28369step1Labels = raw28369step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28369step0 raw28369step0Labels permutation80 hz
    mixedMoment B raw28369step1 raw28369step1Labels = mixedMoment B raw28369step2 raw28369step2Labels := by
      have ha : raw28369step2 = (fun i j => raw28369step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28369step2 raw28369step1; decide +kernel
      have hl : raw28369step2Labels = raw28369step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28369step1 raw28369step1Labels permutation31 permutation3
    mixedMoment B raw28369step2 raw28369step2Labels = mixedMoment B raw28369step3 raw28369step3Labels := by
      have ha : raw28369step3 = -raw28369step2 := by apply Matrix.ext; change ∀ i j, raw28369step3 i j = -(raw28369step2 i j); unfold raw28369step3 raw28369step2; decide +kernel
      have hl : raw28369step3Labels = raw28369step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw28370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28370step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28370 raw28370Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw28370 raw28370Labels = mixedMoment B raw28370step0 raw28370step0Labels := by
      have hz : ∀ j, raw28370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28370step0 = (fun i j => raw28370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28370step0 raw28370; decide +kernel
      have hl : raw28370step0Labels = raw28370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28370 raw28370Labels permutation434 hz
    mixedMoment B raw28370step0 raw28370step0Labels = mixedMoment B raw28370step1 raw28370step1Labels := by
      have hz : ∀ j, raw28370step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28370step1 = (fun i j => raw28370step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28370step1 raw28370step0; decide +kernel
      have hl : raw28370step1Labels = raw28370step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28370step0 raw28370step0Labels permutation80 hz
    mixedMoment B raw28370step1 raw28370step1Labels = mixedMoment B raw28370step2 raw28370step2Labels := by
      have ha : raw28370step2 = (fun i j => raw28370step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28370step2 raw28370step1; decide +kernel
      have hl : raw28370step2Labels = raw28370step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28370step1 raw28370step1Labels permutation8 permutation3
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw28371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28371 raw28371Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw28371 raw28371Labels = mixedMoment B raw28371step0 raw28371step0Labels := by
      have hz : ∀ j, raw28371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28371step0 = (fun i j => raw28371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28371step0 raw28371; decide +kernel
      have hl : raw28371step0Labels = raw28371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28371 raw28371Labels permutation434 hz
    mixedMoment B raw28371step0 raw28371step0Labels = mixedMoment B raw28371step1 raw28371step1Labels := by
      have ha : raw28371step1 = (fun i j => raw28371step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28371step1 raw28371step0; decide +kernel
      have hl : raw28371step1Labels = raw28371step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28371step0 raw28371step0Labels permutation149 permutation3
    mixedMoment B raw28371step1 raw28371step1Labels = mixedMoment B raw28371step2 raw28371step2Labels := by
      have ha : raw28371step2 = -raw28371step1 := by apply Matrix.ext; change ∀ i j, raw28371step2 i j = -(raw28371step1 i j); unfold raw28371step2 raw28371step1; decide +kernel
      have hl : raw28371step2Labels = raw28371step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw28372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28372 raw28372Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw28372 raw28372Labels = mixedMoment B raw28372step0 raw28372step0Labels := by
      have hz : ∀ j, raw28372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28372step0 = (fun i j => raw28372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28372step0 raw28372; decide +kernel
      have hl : raw28372step0Labels = raw28372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28372 raw28372Labels permutation346 hz
    mixedMoment B raw28372step0 raw28372step0Labels = mixedMoment B raw28372step1 raw28372step1Labels := by
      have ha : raw28372step1 = (fun i j => raw28372step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28372step1 raw28372step0; decide +kernel
      have hl : raw28372step1Labels = raw28372step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28372step0 raw28372step0Labels permutation149 permutation3
    mixedMoment B raw28372step1 raw28372step1Labels = mixedMoment B raw28372step2 raw28372step2Labels := by
      have ha : raw28372step2 = -raw28372step1 := by apply Matrix.ext; change ∀ i j, raw28372step2 i j = -(raw28372step1 i j); unfold raw28372step2 raw28372step1; decide +kernel
      have hl : raw28372step2Labels = raw28372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw28373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28373step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw28373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28373step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw28373step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28373 raw28373Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw28373 raw28373Labels = mixedMoment B raw28373step0 raw28373step0Labels := by
      have hz : ∀ j, raw28373 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28373step0 = (fun i j => raw28373 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28373step0 raw28373; decide +kernel
      have hl : raw28373step0Labels = raw28373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28373 raw28373Labels permutation434 hz
    mixedMoment B raw28373step0 raw28373step0Labels = mixedMoment B raw28373step1 raw28373step1Labels := by
      have hz : ∀ j, raw28373step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28373step1 = (fun i j => raw28373step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28373step1 raw28373step0; decide +kernel
      have hl : raw28373step1Labels = raw28373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28373step0 raw28373step0Labels permutation80 hz
    mixedMoment B raw28373step1 raw28373step1Labels = mixedMoment B raw28373step2 raw28373step2Labels := by
      have ha : raw28373step2 = (fun i j => raw28373step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28373step2 raw28373step1; decide +kernel
      have hl : raw28373step2Labels = raw28373step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28373step1 raw28373step1Labels permutation29 permutation3
    mixedMoment B raw28373step2 raw28373step2Labels = mixedMoment B raw28373step3 raw28373step3Labels := by
      have ha : raw28373step3 = -raw28373step2 := by apply Matrix.ext; change ∀ i j, raw28373step3 i j = -(raw28373step2 i j); unfold raw28373step3 raw28373step2; decide +kernel
      have hl : raw28373step3Labels = raw28373step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw28374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28374 raw28374Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw28374 raw28374Labels = mixedMoment B raw28374step0 raw28374step0Labels := by
      have hz : ∀ j, raw28374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28374step0 = (fun i j => raw28374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28374step0 raw28374; decide +kernel
      have hl : raw28374step0Labels = raw28374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28374 raw28374Labels permutation434 hz
    mixedMoment B raw28374step0 raw28374step0Labels = mixedMoment B raw28374step1 raw28374step1Labels := by
      have hz : ∀ j, raw28374step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28374step1 = (fun i j => raw28374step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28374step1 raw28374step0; decide +kernel
      have hl : raw28374step1Labels = raw28374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28374step0 raw28374step0Labels permutation80 hz
    mixedMoment B raw28374step1 raw28374step1Labels = mixedMoment B raw28374step2 raw28374step2Labels := by
      have ha : raw28374step2 = (fun i j => raw28374step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28374step2 raw28374step1; decide +kernel
      have hl : raw28374step2Labels = raw28374step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28374step1 raw28374step1Labels permutation8 permutation3
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw28375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28375 raw28375Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw28375 raw28375Labels = mixedMoment B raw28375step0 raw28375step0Labels := by
      have hz : ∀ j, raw28375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28375step0 = (fun i j => raw28375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28375step0 raw28375; decide +kernel
      have hl : raw28375step0Labels = raw28375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28375 raw28375Labels permutation434 hz
    mixedMoment B raw28375step0 raw28375step0Labels = mixedMoment B raw28375step1 raw28375step1Labels := by
      have ha : raw28375step1 = (fun i j => raw28375step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28375step1 raw28375step0; decide +kernel
      have hl : raw28375step1Labels = raw28375step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28375step0 raw28375step0Labels permutation34 permutation3
    _ = mixedMoment B node1098 node1098Labels := by rfl

def raw28376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw28376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28376 raw28376Labels = mixedMoment B node1873 node1873Labels := by
  calc
    mixedMoment B raw28376 raw28376Labels = mixedMoment B raw28376step0 raw28376step0Labels := by
      have hz : ∀ j, raw28376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28376step0 = (fun i j => raw28376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28376step0 raw28376; decide +kernel
      have hl : raw28376step0Labels = raw28376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28376 raw28376Labels permutation434 hz
    mixedMoment B raw28376step0 raw28376step0Labels = mixedMoment B raw28376step1 raw28376step1Labels := by
      have ha : raw28376step1 = (fun i j => raw28376step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28376step1 raw28376step0; decide +kernel
      have hl : raw28376step1Labels = raw28376step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28376step0 raw28376step0Labels permutation145 permutation3
    mixedMoment B raw28376step1 raw28376step1Labels = mixedMoment B raw28376step2 raw28376step2Labels := by
      have ha : raw28376step2 = -raw28376step1 := by apply Matrix.ext; change ∀ i j, raw28376step2 i j = -(raw28376step1 i j); unfold raw28376step2 raw28376step1; decide +kernel
      have hl : raw28376step2Labels = raw28376step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1873 node1873Labels := by rfl

def raw28377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28377 raw28377Labels = mixedMoment B node1867 node1867Labels := by
  calc
    mixedMoment B raw28377 raw28377Labels = mixedMoment B raw28377step0 raw28377step0Labels := by
      have ha : raw28377step0 = (fun i j => raw28377 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28377step0 raw28377; decide +kernel
      have hl : raw28377step0Labels = raw28377Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28377 raw28377Labels permutation646 permutation3
    mixedMoment B raw28377step0 raw28377step0Labels = mixedMoment B raw28377step1 raw28377step1Labels := by
      have ha : raw28377step1 = -raw28377step0 := by apply Matrix.ext; change ∀ i j, raw28377step1 i j = -(raw28377step0 i j); unfold raw28377step1 raw28377step0; decide +kernel
      have hl : raw28377step1Labels = raw28377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1867 node1867Labels := by rfl

def raw28378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28378 raw28378Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw28378 raw28378Labels = mixedMoment B raw28378step0 raw28378step0Labels := by
      have hz : ∀ j, raw28378 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28378step0 = (fun i j => raw28378 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28378step0 raw28378; decide +kernel
      have hl : raw28378step0Labels = raw28378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28378 raw28378Labels permutation434 hz
    mixedMoment B raw28378step0 raw28378step0Labels = mixedMoment B raw28378step1 raw28378step1Labels := by
      have ha : raw28378step1 = (fun i j => raw28378step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28378step1 raw28378step0; decide +kernel
      have hl : raw28378step1Labels = raw28378step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28378step0 raw28378step0Labels permutation145 permutation3
    mixedMoment B raw28378step1 raw28378step1Labels = mixedMoment B raw28378step2 raw28378step2Labels := by
      have ha : raw28378step2 = -raw28378step1 := by apply Matrix.ext; change ∀ i j, raw28378step2 i j = -(raw28378step1 i j); unfold raw28378step2 raw28378step1; decide +kernel
      have hl : raw28378step2Labels = raw28378step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw28379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28379 raw28379Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw28379 raw28379Labels = mixedMoment B raw28379step0 raw28379step0Labels := by
      have hz : ∀ j, raw28379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28379step0 = (fun i j => raw28379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28379step0 raw28379; decide +kernel
      have hl : raw28379step0Labels = raw28379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28379 raw28379Labels permutation434 hz
    mixedMoment B raw28379step0 raw28379step0Labels = mixedMoment B raw28379step1 raw28379step1Labels := by
      have ha : raw28379step1 = (fun i j => raw28379step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28379step1 raw28379step0; decide +kernel
      have hl : raw28379step1Labels = raw28379step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28379step0 raw28379step0Labels permutation34 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw28380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28380 raw28380Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw28380 raw28380Labels = mixedMoment B raw28380step0 raw28380step0Labels := by
      have hz : ∀ j, raw28380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28380step0 = (fun i j => raw28380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28380step0 raw28380; decide +kernel
      have hl : raw28380step0Labels = raw28380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28380 raw28380Labels permutation346 hz
    mixedMoment B raw28380step0 raw28380step0Labels = mixedMoment B raw28380step1 raw28380step1Labels := by
      have ha : raw28380step1 = (fun i j => raw28380step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28380step1 raw28380step0; decide +kernel
      have hl : raw28380step1Labels = raw28380step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28380step0 raw28380step0Labels permutation34 permutation3
    _ = mixedMoment B node1098 node1098Labels := by rfl

def raw28381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw28381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28381step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28381 raw28381Labels = mixedMoment B node1873 node1873Labels := by
  calc
    mixedMoment B raw28381 raw28381Labels = mixedMoment B raw28381step0 raw28381step0Labels := by
      have hz : ∀ j, raw28381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28381step0 = (fun i j => raw28381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28381step0 raw28381; decide +kernel
      have hl : raw28381step0Labels = raw28381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28381 raw28381Labels permutation346 hz
    mixedMoment B raw28381step0 raw28381step0Labels = mixedMoment B raw28381step1 raw28381step1Labels := by
      have ha : raw28381step1 = (fun i j => raw28381step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28381step1 raw28381step0; decide +kernel
      have hl : raw28381step1Labels = raw28381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28381step0 raw28381step0Labels permutation145 permutation3
    mixedMoment B raw28381step1 raw28381step1Labels = mixedMoment B raw28381step2 raw28381step2Labels := by
      have ha : raw28381step2 = -raw28381step1 := by apply Matrix.ext; change ∀ i j, raw28381step2 i j = -(raw28381step1 i j); unfold raw28381step2 raw28381step1; decide +kernel
      have hl : raw28381step2Labels = raw28381step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1873 node1873Labels := by rfl

def raw28382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28382 raw28382Labels = mixedMoment B node1867 node1867Labels := by
  calc
    mixedMoment B raw28382 raw28382Labels = mixedMoment B raw28382step0 raw28382step0Labels := by
      have ha : raw28382step0 = (fun i j => raw28382 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28382step0 raw28382; decide +kernel
      have hl : raw28382step0Labels = raw28382Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28382 raw28382Labels permutation664 permutation3
    mixedMoment B raw28382step0 raw28382step0Labels = mixedMoment B raw28382step1 raw28382step1Labels := by
      have ha : raw28382step1 = -raw28382step0 := by apply Matrix.ext; change ∀ i j, raw28382step1 i j = -(raw28382step0 i j); unfold raw28382step1 raw28382step0; decide +kernel
      have hl : raw28382step1Labels = raw28382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1867 node1867Labels := by rfl

def raw28383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28383step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28383 raw28383Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw28383 raw28383Labels = mixedMoment B raw28383step0 raw28383step0Labels := by
      have hz : ∀ j, raw28383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28383step0 = (fun i j => raw28383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28383step0 raw28383; decide +kernel
      have hl : raw28383step0Labels = raw28383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28383 raw28383Labels permutation346 hz
    mixedMoment B raw28383step0 raw28383step0Labels = mixedMoment B raw28383step1 raw28383step1Labels := by
      have ha : raw28383step1 = (fun i j => raw28383step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28383step1 raw28383step0; decide +kernel
      have hl : raw28383step1Labels = raw28383step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28383step0 raw28383step0Labels permutation145 permutation3
    mixedMoment B raw28383step1 raw28383step1Labels = mixedMoment B raw28383step2 raw28383step2Labels := by
      have ha : raw28383step2 = -raw28383step1 := by apply Matrix.ext; change ∀ i j, raw28383step2 i j = -(raw28383step1 i j); unfold raw28383step2 raw28383step1; decide +kernel
      have hl : raw28383step2Labels = raw28383step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw28384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28384 raw28384Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw28384 raw28384Labels = mixedMoment B raw28384step0 raw28384step0Labels := by
      have hz : ∀ j, raw28384 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28384step0 = (fun i j => raw28384 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28384step0 raw28384; decide +kernel
      have hl : raw28384step0Labels = raw28384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28384 raw28384Labels permutation346 hz
    mixedMoment B raw28384step0 raw28384step0Labels = mixedMoment B raw28384step1 raw28384step1Labels := by
      have ha : raw28384step1 = (fun i j => raw28384step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28384step1 raw28384step0; decide +kernel
      have hl : raw28384step1Labels = raw28384step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28384step0 raw28384step0Labels permutation34 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw28385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28385step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28385step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw28385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28385 raw28385Labels = mixedMoment B node1103 node1103Labels := by
  calc
    mixedMoment B raw28385 raw28385Labels = mixedMoment B raw28385step0 raw28385step0Labels := by
      have hz : ∀ j, raw28385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28385step0 = (fun i j => raw28385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28385step0 raw28385; decide +kernel
      have hl : raw28385step0Labels = raw28385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28385 raw28385Labels permutation434 hz
    mixedMoment B raw28385step0 raw28385step0Labels = mixedMoment B raw28385step1 raw28385step1Labels := by
      have hz : ∀ j, raw28385step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28385step1 = (fun i j => raw28385step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28385step1 raw28385step0; decide +kernel
      have hl : raw28385step1Labels = raw28385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28385step0 raw28385step0Labels permutation80 hz
    mixedMoment B raw28385step1 raw28385step1Labels = mixedMoment B raw28385step2 raw28385step2Labels := by
      have ha : raw28385step2 = (fun i j => raw28385step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28385step2 raw28385step1; decide +kernel
      have hl : raw28385step2Labels = raw28385step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28385step1 raw28385step1Labels permutation8 permutation3
    _ = mixedMoment B node1103 node1103Labels := by rfl

def raw28386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28386step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw28386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28386step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw28386step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28386 raw28386Labels = mixedMoment B node1783 node1783Labels := by
  calc
    mixedMoment B raw28386 raw28386Labels = mixedMoment B raw28386step0 raw28386step0Labels := by
      have hz : ∀ j, raw28386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28386step0 = (fun i j => raw28386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28386step0 raw28386; decide +kernel
      have hl : raw28386step0Labels = raw28386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28386 raw28386Labels permutation434 hz
    mixedMoment B raw28386step0 raw28386step0Labels = mixedMoment B raw28386step1 raw28386step1Labels := by
      have hz : ∀ j, raw28386step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28386step1 = (fun i j => raw28386step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28386step1 raw28386step0; decide +kernel
      have hl : raw28386step1Labels = raw28386step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28386step0 raw28386step0Labels permutation80 hz
    mixedMoment B raw28386step1 raw28386step1Labels = mixedMoment B raw28386step2 raw28386step2Labels := by
      have ha : raw28386step2 = (fun i j => raw28386step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28386step2 raw28386step1; decide +kernel
      have hl : raw28386step2Labels = raw28386step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28386step1 raw28386step1Labels permutation31 permutation3
    mixedMoment B raw28386step2 raw28386step2Labels = mixedMoment B raw28386step3 raw28386step3Labels := by
      have ha : raw28386step3 = -raw28386step2 := by apply Matrix.ext; change ∀ i j, raw28386step3 i j = -(raw28386step2 i j); unfold raw28386step3 raw28386step2; decide +kernel
      have hl : raw28386step3Labels = raw28386step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1783 node1783Labels := by rfl

def raw28387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28387step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28387 raw28387Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw28387 raw28387Labels = mixedMoment B raw28387step0 raw28387step0Labels := by
      have hz : ∀ j, raw28387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28387step0 = (fun i j => raw28387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28387step0 raw28387; decide +kernel
      have hl : raw28387step0Labels = raw28387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28387 raw28387Labels permutation434 hz
    mixedMoment B raw28387step0 raw28387step0Labels = mixedMoment B raw28387step1 raw28387step1Labels := by
      have ha : raw28387step1 = (fun i j => raw28387step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28387step1 raw28387step0; decide +kernel
      have hl : raw28387step1Labels = raw28387step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28387step0 raw28387step0Labels permutation151 permutation3
    mixedMoment B raw28387step1 raw28387step1Labels = mixedMoment B raw28387step2 raw28387step2Labels := by
      have ha : raw28387step2 = -raw28387step1 := by apply Matrix.ext; change ∀ i j, raw28387step2 i j = -(raw28387step1 i j); unfold raw28387step2 raw28387step1; decide +kernel
      have hl : raw28387step2Labels = raw28387step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1778 node1778Labels := by rfl

def raw28388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28388 raw28388Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw28388 raw28388Labels = mixedMoment B raw28388step0 raw28388step0Labels := by
      have hz : ∀ j, raw28388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28388step0 = (fun i j => raw28388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28388step0 raw28388; decide +kernel
      have hl : raw28388step0Labels = raw28388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28388 raw28388Labels permutation346 hz
    mixedMoment B raw28388step0 raw28388step0Labels = mixedMoment B raw28388step1 raw28388step1Labels := by
      have ha : raw28388step1 = (fun i j => raw28388step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28388step1 raw28388step0; decide +kernel
      have hl : raw28388step1Labels = raw28388step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28388step0 raw28388step0Labels permutation151 permutation3
    mixedMoment B raw28388step1 raw28388step1Labels = mixedMoment B raw28388step2 raw28388step2Labels := by
      have ha : raw28388step2 = -raw28388step1 := by apply Matrix.ext; change ∀ i j, raw28388step2 i j = -(raw28388step1 i j); unfold raw28388step2 raw28388step1; decide +kernel
      have hl : raw28388step2Labels = raw28388step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1778 node1778Labels := by rfl

def raw28389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw28389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw28389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw28389step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28389step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28389 raw28389Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw28389 raw28389Labels = mixedMoment B raw28389step0 raw28389step0Labels := by
      have hz : ∀ j, raw28389 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28389step0 = (fun i j => raw28389 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28389step0 raw28389; decide +kernel
      have hl : raw28389step0Labels = raw28389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28389 raw28389Labels permutation434 hz
    mixedMoment B raw28389step0 raw28389step0Labels = mixedMoment B raw28389step1 raw28389step1Labels := by
      have hz : ∀ j, raw28389step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28389step1 = (fun i j => raw28389step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28389step1 raw28389step0; decide +kernel
      have hl : raw28389step1Labels = raw28389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28389step0 raw28389step0Labels permutation80 hz
    mixedMoment B raw28389step1 raw28389step1Labels = mixedMoment B raw28389step2 raw28389step2Labels := by
      have ha : raw28389step2 = (fun i j => raw28389step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28389step2 raw28389step1; decide +kernel
      have hl : raw28389step2Labels = raw28389step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28389step1 raw28389step1Labels permutation8 permutation3
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw28390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28390step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw28390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28390step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw28390step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28390 raw28390Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw28390 raw28390Labels = mixedMoment B raw28390step0 raw28390step0Labels := by
      have hz : ∀ j, raw28390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28390step0 = (fun i j => raw28390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28390step0 raw28390; decide +kernel
      have hl : raw28390step0Labels = raw28390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28390 raw28390Labels permutation434 hz
    mixedMoment B raw28390step0 raw28390step0Labels = mixedMoment B raw28390step1 raw28390step1Labels := by
      have hz : ∀ j, raw28390step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28390step1 = (fun i j => raw28390step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28390step1 raw28390step0; decide +kernel
      have hl : raw28390step1Labels = raw28390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28390step0 raw28390step0Labels permutation80 hz
    mixedMoment B raw28390step1 raw28390step1Labels = mixedMoment B raw28390step2 raw28390step2Labels := by
      have ha : raw28390step2 = (fun i j => raw28390step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28390step2 raw28390step1; decide +kernel
      have hl : raw28390step2Labels = raw28390step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28390step1 raw28390step1Labels permutation31 permutation3
    mixedMoment B raw28390step2 raw28390step2Labels = mixedMoment B raw28390step3 raw28390step3Labels := by
      have ha : raw28390step3 = -raw28390step2 := by apply Matrix.ext; change ∀ i j, raw28390step3 i j = -(raw28390step2 i j); unfold raw28390step3 raw28390step2; decide +kernel
      have hl : raw28390step3Labels = raw28390step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node726 node726Labels := by rfl

def raw28391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28391step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw28391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28391step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28391 raw28391Labels = mixedMoment B node729 node729Labels := by
  calc
    mixedMoment B raw28391 raw28391Labels = mixedMoment B raw28391step0 raw28391step0Labels := by
      have hz : ∀ j, raw28391 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28391step0 = (fun i j => raw28391 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28391step0 raw28391; decide +kernel
      have hl : raw28391step0Labels = raw28391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28391 raw28391Labels permutation434 hz
    mixedMoment B raw28391step0 raw28391step0Labels = mixedMoment B raw28391step1 raw28391step1Labels := by
      have hz : ∀ j, raw28391step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28391step1 = (fun i j => raw28391step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28391step1 raw28391step0; decide +kernel
      have hl : raw28391step1Labels = raw28391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28391step0 raw28391step0Labels permutation80 hz
    mixedMoment B raw28391step1 raw28391step1Labels = mixedMoment B raw28391step2 raw28391step2Labels := by
      have ha : raw28391step2 = (fun i j => raw28391step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28391step2 raw28391step1; decide +kernel
      have hl : raw28391step2Labels = raw28391step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28391step1 raw28391step1Labels permutation31 permutation3
    mixedMoment B raw28391step2 raw28391step2Labels = mixedMoment B raw28391step3 raw28391step3Labels := by
      have ha : raw28391step3 = -raw28391step2 := by apply Matrix.ext; change ∀ i j, raw28391step3 i j = -(raw28391step2 i j); unfold raw28391step3 raw28391step2; decide +kernel
      have hl : raw28391step3Labels = raw28391step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node729 node729Labels := by rfl

def raw28392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28392 raw28392Labels = mixedMoment B node720 node720Labels := by
  calc
    mixedMoment B raw28392 raw28392Labels = mixedMoment B raw28392step0 raw28392step0Labels := by
      have hz : ∀ j, raw28392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28392step0 = (fun i j => raw28392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28392step0 raw28392; decide +kernel
      have hl : raw28392step0Labels = raw28392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28392 raw28392Labels permutation434 hz
    mixedMoment B raw28392step0 raw28392step0Labels = mixedMoment B raw28392step1 raw28392step1Labels := by
      have ha : raw28392step1 = (fun i j => raw28392step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28392step1 raw28392step0; decide +kernel
      have hl : raw28392step1Labels = raw28392step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28392step0 raw28392step0Labels permutation151 permutation3
    mixedMoment B raw28392step1 raw28392step1Labels = mixedMoment B raw28392step2 raw28392step2Labels := by
      have ha : raw28392step2 = -raw28392step1 := by apply Matrix.ext; change ∀ i j, raw28392step2 i j = -(raw28392step1 i j); unfold raw28392step2 raw28392step1; decide +kernel
      have hl : raw28392step2Labels = raw28392step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node720 node720Labels := by rfl

def raw28393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28393step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28393 raw28393Labels = mixedMoment B node720 node720Labels := by
  calc
    mixedMoment B raw28393 raw28393Labels = mixedMoment B raw28393step0 raw28393step0Labels := by
      have hz : ∀ j, raw28393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28393step0 = (fun i j => raw28393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28393step0 raw28393; decide +kernel
      have hl : raw28393step0Labels = raw28393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28393 raw28393Labels permutation346 hz
    mixedMoment B raw28393step0 raw28393step0Labels = mixedMoment B raw28393step1 raw28393step1Labels := by
      have ha : raw28393step1 = (fun i j => raw28393step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28393step1 raw28393step0; decide +kernel
      have hl : raw28393step1Labels = raw28393step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28393step0 raw28393step0Labels permutation151 permutation3
    mixedMoment B raw28393step1 raw28393step1Labels = mixedMoment B raw28393step2 raw28393step2Labels := by
      have ha : raw28393step2 = -raw28393step1 := by apply Matrix.ext; change ∀ i j, raw28393step2 i j = -(raw28393step1 i j); unfold raw28393step2 raw28393step1; decide +kernel
      have hl : raw28393step2Labels = raw28393step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node720 node720Labels := by rfl

def raw28394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -4, 0]]
def raw28394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![4, -4, 0]]
def raw28394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28394step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28394step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28394step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28394 raw28394Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw28394 raw28394Labels = mixedMoment B raw28394step0 raw28394step0Labels := by
      have hz : ∀ j, raw28394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28394step0 = (fun i j => raw28394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28394step0 raw28394; decide +kernel
      have hl : raw28394step0Labels = raw28394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28394 raw28394Labels permutation434 hz
    mixedMoment B raw28394step0 raw28394step0Labels = mixedMoment B raw28394step1 raw28394step1Labels := by
      have hz : ∀ j, raw28394step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28394step1 = (fun i j => raw28394step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28394step1 raw28394step0; decide +kernel
      have hl : raw28394step1Labels = raw28394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28394step0 raw28394step0Labels permutation80 hz
    mixedMoment B raw28394step1 raw28394step1Labels = mixedMoment B raw28394step2 raw28394step2Labels := by
      have ha : raw28394step2 = (fun i j => raw28394step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28394step2 raw28394step1; decide +kernel
      have hl : raw28394step2Labels = raw28394step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28394step1 raw28394step1Labels permutation31 permutation3
    mixedMoment B raw28394step2 raw28394step2Labels = mixedMoment B raw28394step3 raw28394step3Labels := by
      have ha : raw28394step3 = -raw28394step2 := by apply Matrix.ext; change ∀ i j, raw28394step3 i j = -(raw28394step2 i j); unfold raw28394step3 raw28394step2; decide +kernel
      have hl : raw28394step3Labels = raw28394step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node813 node813Labels := by rfl

def raw28395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw28395step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28395step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28395 raw28395Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw28395 raw28395Labels = mixedMoment B raw28395step0 raw28395step0Labels := by
      have hz : ∀ j, raw28395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28395step0 = (fun i j => raw28395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28395step0 raw28395; decide +kernel
      have hl : raw28395step0Labels = raw28395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28395 raw28395Labels permutation434 hz
    mixedMoment B raw28395step0 raw28395step0Labels = mixedMoment B raw28395step1 raw28395step1Labels := by
      have hz : ∀ j, raw28395step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28395step1 = (fun i j => raw28395step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28395step1 raw28395step0; decide +kernel
      have hl : raw28395step1Labels = raw28395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28395step0 raw28395step0Labels permutation80 hz
    mixedMoment B raw28395step1 raw28395step1Labels = mixedMoment B raw28395step2 raw28395step2Labels := by
      have ha : raw28395step2 = (fun i j => raw28395step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28395step2 raw28395step1; decide +kernel
      have hl : raw28395step2Labels = raw28395step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28395step1 raw28395step1Labels permutation30 permutation2
    mixedMoment B raw28395step2 raw28395step2Labels = mixedMoment B raw28395step3 raw28395step3Labels := by
      have ha : raw28395step3 = -raw28395step2 := by apply Matrix.ext; change ∀ i j, raw28395step3 i j = -(raw28395step2 i j); unfold raw28395step3 raw28395step2; decide +kernel
      have hl : raw28395step3Labels = raw28395step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw28396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28396 raw28396Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw28396 raw28396Labels = mixedMoment B raw28396step0 raw28396step0Labels := by
      have hz : ∀ j, raw28396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28396step0 = (fun i j => raw28396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28396step0 raw28396; decide +kernel
      have hl : raw28396step0Labels = raw28396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28396 raw28396Labels permutation434 hz
    mixedMoment B raw28396step0 raw28396step0Labels = mixedMoment B raw28396step1 raw28396step1Labels := by
      have ha : raw28396step1 = (fun i j => raw28396step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28396step1 raw28396step0; decide +kernel
      have hl : raw28396step1Labels = raw28396step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28396step0 raw28396step0Labels permutation151 permutation2
    mixedMoment B raw28396step1 raw28396step1Labels = mixedMoment B raw28396step2 raw28396step2Labels := by
      have ha : raw28396step2 = -raw28396step1 := by apply Matrix.ext; change ∀ i j, raw28396step2 i j = -(raw28396step1 i j); unfold raw28396step2 raw28396step1; decide +kernel
      have hl : raw28396step2Labels = raw28396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw28397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28397step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28397 raw28397Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw28397 raw28397Labels = mixedMoment B raw28397step0 raw28397step0Labels := by
      have hz : ∀ j, raw28397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28397step0 = (fun i j => raw28397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28397step0 raw28397; decide +kernel
      have hl : raw28397step0Labels = raw28397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28397 raw28397Labels permutation346 hz
    mixedMoment B raw28397step0 raw28397step0Labels = mixedMoment B raw28397step1 raw28397step1Labels := by
      have ha : raw28397step1 = (fun i j => raw28397step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28397step1 raw28397step0; decide +kernel
      have hl : raw28397step1Labels = raw28397step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28397step0 raw28397step0Labels permutation151 permutation2
    mixedMoment B raw28397step1 raw28397step1Labels = mixedMoment B raw28397step2 raw28397step2Labels := by
      have ha : raw28397step2 = -raw28397step1 := by apply Matrix.ext; change ∀ i j, raw28397step2 i j = -(raw28397step1 i j); unfold raw28397step2 raw28397step1; decide +kernel
      have hl : raw28397step2Labels = raw28397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw28398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28398step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw28398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw28398step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw28398step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28398 raw28398Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw28398 raw28398Labels = mixedMoment B raw28398step0 raw28398step0Labels := by
      have hz : ∀ j, raw28398 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28398step0 = (fun i j => raw28398 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28398step0 raw28398; decide +kernel
      have hl : raw28398step0Labels = raw28398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28398 raw28398Labels permutation520 hz
    mixedMoment B raw28398step0 raw28398step0Labels = mixedMoment B raw28398step1 raw28398step1Labels := by
      have hz : ∀ j, raw28398step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28398step1 = (fun i j => raw28398step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28398step1 raw28398step0; decide +kernel
      have hl : raw28398step1Labels = raw28398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28398step0 raw28398step0Labels permutation104 hz
    mixedMoment B raw28398step1 raw28398step1Labels = mixedMoment B raw28398step2 raw28398step2Labels := by
      have hz : ∀ j, raw28398step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28398step2 = (fun i j => raw28398step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28398step2 raw28398step1; decide +kernel
      have hl : raw28398step2Labels = raw28398step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28398step1 raw28398step1Labels permutation20 hz
    mixedMoment B raw28398step2 raw28398step2Labels = mixedMoment B raw28398step3 raw28398step3Labels := by
      have ha : raw28398step3 = (fun i j => raw28398step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28398step3 raw28398step2; decide +kernel
      have hl : raw28398step3Labels = raw28398step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28398step2 raw28398step2Labels permutation7 permutation2
    mixedMoment B raw28398step3 raw28398step3Labels = mixedMoment B raw28398step4 raw28398step4Labels := by
      have ha : raw28398step4 = -raw28398step3 := by apply Matrix.ext; change ∀ i j, raw28398step4 i j = -(raw28398step3 i j); unfold raw28398step4 raw28398step3; decide +kernel
      have hl : raw28398step4Labels = raw28398step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4901 node4901Labels := by rfl

def raw28399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28399step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28399step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28399step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28399 raw28399Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw28399 raw28399Labels = mixedMoment B raw28399step0 raw28399step0Labels := by
      have hz : ∀ j, raw28399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28399step0 = (fun i j => raw28399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28399step0 raw28399; decide +kernel
      have hl : raw28399step0Labels = raw28399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28399 raw28399Labels permutation434 hz
    mixedMoment B raw28399step0 raw28399step0Labels = mixedMoment B raw28399step1 raw28399step1Labels := by
      have hz : ∀ j, raw28399step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28399step1 = (fun i j => raw28399step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28399step1 raw28399step0; decide +kernel
      have hl : raw28399step1Labels = raw28399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28399step0 raw28399step0Labels permutation80 hz
    mixedMoment B raw28399step1 raw28399step1Labels = mixedMoment B raw28399step2 raw28399step2Labels := by
      have ha : raw28399step2 = (fun i j => raw28399step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28399step2 raw28399step1; decide +kernel
      have hl : raw28399step2Labels = raw28399step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28399step1 raw28399step1Labels permutation30 permutation7
    mixedMoment B raw28399step2 raw28399step2Labels = mixedMoment B raw28399step3 raw28399step3Labels := by
      have ha : raw28399step3 = raw28399step2 := by apply Matrix.ext; unfold raw28399step3 raw28399step2; decide +kernel
      have hl : raw28399step2Labels = labelEmbedding10 ∘ raw28399step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28399step2 raw28399step2Labels raw28399step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw28400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28400step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28400step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28400step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28400 raw28400Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw28400 raw28400Labels = mixedMoment B raw28400step0 raw28400step0Labels := by
      have hz : ∀ j, raw28400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28400step0 = (fun i j => raw28400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28400step0 raw28400; decide +kernel
      have hl : raw28400step0Labels = raw28400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28400 raw28400Labels permutation434 hz
    mixedMoment B raw28400step0 raw28400step0Labels = mixedMoment B raw28400step1 raw28400step1Labels := by
      have hz : ∀ j, raw28400step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28400step1 = (fun i j => raw28400step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28400step1 raw28400step0; decide +kernel
      have hl : raw28400step1Labels = raw28400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28400step0 raw28400step0Labels permutation80 hz
    mixedMoment B raw28400step1 raw28400step1Labels = mixedMoment B raw28400step2 raw28400step2Labels := by
      have ha : raw28400step2 = (fun i j => raw28400step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28400step2 raw28400step1; decide +kernel
      have hl : raw28400step2Labels = raw28400step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28400step1 raw28400step1Labels permutation8 permutation3
    mixedMoment B raw28400step2 raw28400step2Labels = mixedMoment B raw28400step3 raw28400step3Labels := by
      have ha : raw28400step3 = raw28400step2 := by apply Matrix.ext; unfold raw28400step3 raw28400step2; decide +kernel
      have hl : raw28400step2Labels = labelEmbedding6 ∘ raw28400step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28400step2 raw28400step2Labels raw28400step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw28401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28401 raw28401Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw28401 raw28401Labels = mixedMoment B raw28401step0 raw28401step0Labels := by
      have hz : ∀ j, raw28401 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28401step0 = (fun i j => raw28401 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28401step0 raw28401; decide +kernel
      have hl : raw28401step0Labels = raw28401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28401 raw28401Labels permutation434 hz
    mixedMoment B raw28401step0 raw28401step0Labels = mixedMoment B raw28401step1 raw28401step1Labels := by
      have ha : raw28401step1 = (fun i j => raw28401step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28401step1 raw28401step0; decide +kernel
      have hl : raw28401step1Labels = raw28401step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28401step0 raw28401step0Labels permutation149 permutation2
    mixedMoment B raw28401step1 raw28401step1Labels = mixedMoment B raw28401step2 raw28401step2Labels := by
      have ha : raw28401step2 = -raw28401step1 := by apply Matrix.ext; change ∀ i j, raw28401step2 i j = -(raw28401step1 i j); unfold raw28401step2 raw28401step1; decide +kernel
      have hl : raw28401step2Labels = raw28401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw28402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28402 raw28402Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw28402 raw28402Labels = mixedMoment B raw28402step0 raw28402step0Labels := by
      have hz : ∀ j, raw28402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28402step0 = (fun i j => raw28402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28402step0 raw28402; decide +kernel
      have hl : raw28402step0Labels = raw28402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28402 raw28402Labels permutation346 hz
    mixedMoment B raw28402step0 raw28402step0Labels = mixedMoment B raw28402step1 raw28402step1Labels := by
      have ha : raw28402step1 = (fun i j => raw28402step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28402step1 raw28402step0; decide +kernel
      have hl : raw28402step1Labels = raw28402step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28402step0 raw28402step0Labels permutation149 permutation2
    mixedMoment B raw28402step1 raw28402step1Labels = mixedMoment B raw28402step2 raw28402step2Labels := by
      have ha : raw28402step2 = -raw28402step1 := by apply Matrix.ext; change ∀ i j, raw28402step2 i j = -(raw28402step1 i j); unfold raw28402step2 raw28402step1; decide +kernel
      have hl : raw28402step2Labels = raw28402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw28403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![3, 0, -3]]
def raw28403step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw28403step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw28403step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28403 raw28403Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw28403 raw28403Labels = mixedMoment B raw28403step0 raw28403step0Labels := by
      have hz : ∀ j, raw28403 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28403step0 = (fun i j => raw28403 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28403step0 raw28403; decide +kernel
      have hl : raw28403step0Labels = raw28403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28403 raw28403Labels permutation520 hz
    mixedMoment B raw28403step0 raw28403step0Labels = mixedMoment B raw28403step1 raw28403step1Labels := by
      have hz : ∀ j, raw28403step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28403step1 = (fun i j => raw28403step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28403step1 raw28403step0; decide +kernel
      have hl : raw28403step1Labels = raw28403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28403step0 raw28403step0Labels permutation104 hz
    mixedMoment B raw28403step1 raw28403step1Labels = mixedMoment B raw28403step2 raw28403step2Labels := by
      have hz : ∀ j, raw28403step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28403step2 = (fun i j => raw28403step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28403step2 raw28403step1; decide +kernel
      have hl : raw28403step2Labels = raw28403step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28403step1 raw28403step1Labels permutation20 hz
    mixedMoment B raw28403step2 raw28403step2Labels = mixedMoment B raw28403step3 raw28403step3Labels := by
      have ha : raw28403step3 = (fun i j => raw28403step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28403step3 raw28403step2; decide +kernel
      have hl : raw28403step3Labels = raw28403step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28403step2 raw28403step2Labels permutation7 permutation2
    mixedMoment B raw28403step3 raw28403step3Labels = mixedMoment B raw28403step4 raw28403step4Labels := by
      have ha : raw28403step4 = -raw28403step3 := by apply Matrix.ext; change ∀ i j, raw28403step4 i j = -(raw28403step3 i j); unfold raw28403step4 raw28403step3; decide +kernel
      have hl : raw28403step4Labels = raw28403step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw28404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw28404step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw28404step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28404 raw28404Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw28404 raw28404Labels = mixedMoment B raw28404step0 raw28404step0Labels := by
      have hz : ∀ j, raw28404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28404step0 = (fun i j => raw28404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28404step0 raw28404; decide +kernel
      have hl : raw28404step0Labels = raw28404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28404 raw28404Labels permutation434 hz
    mixedMoment B raw28404step0 raw28404step0Labels = mixedMoment B raw28404step1 raw28404step1Labels := by
      have hz : ∀ j, raw28404step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28404step1 = (fun i j => raw28404step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28404step1 raw28404step0; decide +kernel
      have hl : raw28404step1Labels = raw28404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28404step0 raw28404step0Labels permutation80 hz
    mixedMoment B raw28404step1 raw28404step1Labels = mixedMoment B raw28404step2 raw28404step2Labels := by
      have ha : raw28404step2 = (fun i j => raw28404step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28404step2 raw28404step1; decide +kernel
      have hl : raw28404step2Labels = raw28404step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28404step1 raw28404step1Labels permutation30 permutation7
    mixedMoment B raw28404step2 raw28404step2Labels = mixedMoment B raw28404step3 raw28404step3Labels := by
      have ha : raw28404step3 = raw28404step2 := by apply Matrix.ext; unfold raw28404step3 raw28404step2; decide +kernel
      have hl : raw28404step2Labels = labelEmbedding10 ∘ raw28404step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28404step2 raw28404step2Labels raw28404step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw28405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28405step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28405step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28405 raw28405Labels = mixedMoment B node4371 node4371Labels := by
  calc
    mixedMoment B raw28405 raw28405Labels = mixedMoment B raw28405step0 raw28405step0Labels := by
      have hz : ∀ j, raw28405 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28405step0 = (fun i j => raw28405 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28405step0 raw28405; decide +kernel
      have hl : raw28405step0Labels = raw28405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28405 raw28405Labels permutation434 hz
    mixedMoment B raw28405step0 raw28405step0Labels = mixedMoment B raw28405step1 raw28405step1Labels := by
      have ha : raw28405step1 = (fun i j => raw28405step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28405step1 raw28405step0; decide +kernel
      have hl : raw28405step1Labels = raw28405step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28405step0 raw28405step0Labels permutation32 permutation3
    mixedMoment B raw28405step1 raw28405step1Labels = mixedMoment B raw28405step2 raw28405step2Labels := by
      have ha : raw28405step2 = raw28405step1 := by apply Matrix.ext; unfold raw28405step2 raw28405step1; decide +kernel
      have hl : raw28405step1Labels = labelEmbedding6 ∘ raw28405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28405step1 raw28405step1Labels raw28405step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4371 node4371Labels := by rfl

def raw28406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28406step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28406 raw28406Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw28406 raw28406Labels = mixedMoment B raw28406step0 raw28406step0Labels := by
      have hz : ∀ j, raw28406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28406step0 = (fun i j => raw28406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28406step0 raw28406; decide +kernel
      have hl : raw28406step0Labels = raw28406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28406 raw28406Labels permutation434 hz
    mixedMoment B raw28406step0 raw28406step0Labels = mixedMoment B raw28406step1 raw28406step1Labels := by
      have ha : raw28406step1 = (fun i j => raw28406step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28406step1 raw28406step0; decide +kernel
      have hl : raw28406step1Labels = raw28406step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28406step0 raw28406step0Labels permutation145 permutation2
    mixedMoment B raw28406step1 raw28406step1Labels = mixedMoment B raw28406step2 raw28406step2Labels := by
      have ha : raw28406step2 = -raw28406step1 := by apply Matrix.ext; change ∀ i j, raw28406step2 i j = -(raw28406step1 i j); unfold raw28406step2 raw28406step1; decide +kernel
      have hl : raw28406step2Labels = raw28406step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4770 node4770Labels := by rfl

def raw28407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28407step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28407 raw28407Labels = mixedMoment B node4761 node4761Labels := by
  calc
    mixedMoment B raw28407 raw28407Labels = mixedMoment B raw28407step0 raw28407step0Labels := by
      have ha : raw28407step0 = (fun i j => raw28407 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28407step0 raw28407; decide +kernel
      have hl : raw28407step0Labels = raw28407Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28407 raw28407Labels permutation646 permutation2
    mixedMoment B raw28407step0 raw28407step0Labels = mixedMoment B raw28407step1 raw28407step1Labels := by
      have ha : raw28407step1 = -raw28407step0 := by apply Matrix.ext; change ∀ i j, raw28407step1 i j = -(raw28407step0 i j); unfold raw28407step1 raw28407step0; decide +kernel
      have hl : raw28407step1Labels = raw28407step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4761 node4761Labels := by rfl

def raw28408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28408step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28408step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28408step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28408step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28408step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28408 raw28408Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw28408 raw28408Labels = mixedMoment B raw28408step0 raw28408step0Labels := by
      have hz : ∀ j, raw28408 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28408step0 = (fun i j => raw28408 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28408step0 raw28408; decide +kernel
      have hl : raw28408step0Labels = raw28408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28408 raw28408Labels permutation520 hz
    mixedMoment B raw28408step0 raw28408step0Labels = mixedMoment B raw28408step1 raw28408step1Labels := by
      have hz : ∀ j, raw28408step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28408step1 = (fun i j => raw28408step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28408step1 raw28408step0; decide +kernel
      have hl : raw28408step1Labels = raw28408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28408step0 raw28408step0Labels permutation104 hz
    mixedMoment B raw28408step1 raw28408step1Labels = mixedMoment B raw28408step2 raw28408step2Labels := by
      have ha : raw28408step2 = (fun i j => raw28408step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28408step2 raw28408step1; decide +kernel
      have hl : raw28408step2Labels = raw28408step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28408step1 raw28408step1Labels permutation31 permutation2
    mixedMoment B raw28408step2 raw28408step2Labels = mixedMoment B raw28408step3 raw28408step3Labels := by
      have ha : raw28408step3 = -raw28408step2 := by apply Matrix.ext; change ∀ i j, raw28408step3 i j = -(raw28408step2 i j); unfold raw28408step3 raw28408step2; decide +kernel
      have hl : raw28408step3Labels = raw28408step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw28409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28409step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28409 raw28409Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw28409 raw28409Labels = mixedMoment B raw28409step0 raw28409step0Labels := by
      have hz : ∀ j, raw28409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28409step0 = (fun i j => raw28409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28409step0 raw28409; decide +kernel
      have hl : raw28409step0Labels = raw28409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28409 raw28409Labels permutation434 hz
    mixedMoment B raw28409step0 raw28409step0Labels = mixedMoment B raw28409step1 raw28409step1Labels := by
      have ha : raw28409step1 = (fun i j => raw28409step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28409step1 raw28409step0; decide +kernel
      have hl : raw28409step1Labels = raw28409step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28409step0 raw28409step0Labels permutation32 permutation3
    mixedMoment B raw28409step1 raw28409step1Labels = mixedMoment B raw28409step2 raw28409step2Labels := by
      have ha : raw28409step2 = raw28409step1 := by apply Matrix.ext; unfold raw28409step2 raw28409step1; decide +kernel
      have hl : raw28409step1Labels = labelEmbedding6 ∘ raw28409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28409step1 raw28409step1Labels raw28409step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw28410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28410step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28410step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28410 raw28410Labels = mixedMoment B node4371 node4371Labels := by
  calc
    mixedMoment B raw28410 raw28410Labels = mixedMoment B raw28410step0 raw28410step0Labels := by
      have hz : ∀ j, raw28410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28410step0 = (fun i j => raw28410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28410step0 raw28410; decide +kernel
      have hl : raw28410step0Labels = raw28410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28410 raw28410Labels permutation346 hz
    mixedMoment B raw28410step0 raw28410step0Labels = mixedMoment B raw28410step1 raw28410step1Labels := by
      have ha : raw28410step1 = (fun i j => raw28410step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28410step1 raw28410step0; decide +kernel
      have hl : raw28410step1Labels = raw28410step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28410step0 raw28410step0Labels permutation32 permutation3
    mixedMoment B raw28410step1 raw28410step1Labels = mixedMoment B raw28410step2 raw28410step2Labels := by
      have ha : raw28410step2 = raw28410step1 := by apply Matrix.ext; unfold raw28410step2 raw28410step1; decide +kernel
      have hl : raw28410step1Labels = labelEmbedding6 ∘ raw28410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28410step1 raw28410step1Labels raw28410step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4371 node4371Labels := by rfl

def raw28411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28411step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28411 raw28411Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw28411 raw28411Labels = mixedMoment B raw28411step0 raw28411step0Labels := by
      have hz : ∀ j, raw28411 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28411step0 = (fun i j => raw28411 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28411step0 raw28411; decide +kernel
      have hl : raw28411step0Labels = raw28411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28411 raw28411Labels permutation346 hz
    mixedMoment B raw28411step0 raw28411step0Labels = mixedMoment B raw28411step1 raw28411step1Labels := by
      have ha : raw28411step1 = (fun i j => raw28411step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28411step1 raw28411step0; decide +kernel
      have hl : raw28411step1Labels = raw28411step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28411step0 raw28411step0Labels permutation145 permutation2
    mixedMoment B raw28411step1 raw28411step1Labels = mixedMoment B raw28411step2 raw28411step2Labels := by
      have ha : raw28411step2 = -raw28411step1 := by apply Matrix.ext; change ∀ i j, raw28411step2 i j = -(raw28411step1 i j); unfold raw28411step2 raw28411step1; decide +kernel
      have hl : raw28411step2Labels = raw28411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4770 node4770Labels := by rfl

def raw28412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28412 raw28412Labels = mixedMoment B node4761 node4761Labels := by
  calc
    mixedMoment B raw28412 raw28412Labels = mixedMoment B raw28412step0 raw28412step0Labels := by
      have ha : raw28412step0 = (fun i j => raw28412 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28412step0 raw28412; decide +kernel
      have hl : raw28412step0Labels = raw28412Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28412 raw28412Labels permutation664 permutation2
    mixedMoment B raw28412step0 raw28412step0Labels = mixedMoment B raw28412step1 raw28412step1Labels := by
      have ha : raw28412step1 = -raw28412step0 := by apply Matrix.ext; change ∀ i j, raw28412step1 i j = -(raw28412step0 i j); unfold raw28412step1 raw28412step0; decide +kernel
      have hl : raw28412step1Labels = raw28412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4761 node4761Labels := by rfl

def raw28413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28413step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28413step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28413step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28413step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28413 raw28413Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw28413 raw28413Labels = mixedMoment B raw28413step0 raw28413step0Labels := by
      have hz : ∀ j, raw28413 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28413step0 = (fun i j => raw28413 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28413step0 raw28413; decide +kernel
      have hl : raw28413step0Labels = raw28413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28413 raw28413Labels permutation520 hz
    mixedMoment B raw28413step0 raw28413step0Labels = mixedMoment B raw28413step1 raw28413step1Labels := by
      have hz : ∀ j, raw28413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28413step1 = (fun i j => raw28413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28413step1 raw28413step0; decide +kernel
      have hl : raw28413step1Labels = raw28413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28413step0 raw28413step0Labels permutation80 hz
    mixedMoment B raw28413step1 raw28413step1Labels = mixedMoment B raw28413step2 raw28413step2Labels := by
      have ha : raw28413step2 = (fun i j => raw28413step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28413step2 raw28413step1; decide +kernel
      have hl : raw28413step2Labels = raw28413step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28413step1 raw28413step1Labels permutation31 permutation2
    mixedMoment B raw28413step2 raw28413step2Labels = mixedMoment B raw28413step3 raw28413step3Labels := by
      have ha : raw28413step3 = -raw28413step2 := by apply Matrix.ext; change ∀ i j, raw28413step3 i j = -(raw28413step2 i j); unfold raw28413step3 raw28413step2; decide +kernel
      have hl : raw28413step3Labels = raw28413step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw28414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28414step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28414step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28414 raw28414Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw28414 raw28414Labels = mixedMoment B raw28414step0 raw28414step0Labels := by
      have hz : ∀ j, raw28414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28414step0 = (fun i j => raw28414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28414step0 raw28414; decide +kernel
      have hl : raw28414step0Labels = raw28414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28414 raw28414Labels permutation346 hz
    mixedMoment B raw28414step0 raw28414step0Labels = mixedMoment B raw28414step1 raw28414step1Labels := by
      have ha : raw28414step1 = (fun i j => raw28414step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28414step1 raw28414step0; decide +kernel
      have hl : raw28414step1Labels = raw28414step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28414step0 raw28414step0Labels permutation32 permutation3
    mixedMoment B raw28414step1 raw28414step1Labels = mixedMoment B raw28414step2 raw28414step2Labels := by
      have ha : raw28414step2 = raw28414step1 := by apply Matrix.ext; unfold raw28414step2 raw28414step1; decide +kernel
      have hl : raw28414step1Labels = labelEmbedding6 ∘ raw28414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28414step1 raw28414step1Labels raw28414step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw28415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw28415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28415step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28415step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28415 raw28415Labels = mixedMoment B node4375 node4375Labels := by
  calc
    mixedMoment B raw28415 raw28415Labels = mixedMoment B raw28415step0 raw28415step0Labels := by
      have hz : ∀ j, raw28415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28415step0 = (fun i j => raw28415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28415step0 raw28415; decide +kernel
      have hl : raw28415step0Labels = raw28415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28415 raw28415Labels permutation434 hz
    mixedMoment B raw28415step0 raw28415step0Labels = mixedMoment B raw28415step1 raw28415step1Labels := by
      have hz : ∀ j, raw28415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28415step1 = (fun i j => raw28415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28415step1 raw28415step0; decide +kernel
      have hl : raw28415step1Labels = raw28415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28415step0 raw28415step0Labels permutation80 hz
    mixedMoment B raw28415step1 raw28415step1Labels = mixedMoment B raw28415step2 raw28415step2Labels := by
      have ha : raw28415step2 = (fun i j => raw28415step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28415step2 raw28415step1; decide +kernel
      have hl : raw28415step2Labels = raw28415step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28415step1 raw28415step1Labels permutation8 permutation3
    mixedMoment B raw28415step2 raw28415step2Labels = mixedMoment B raw28415step3 raw28415step3Labels := by
      have ha : raw28415step3 = raw28415step2 := by apply Matrix.ext; unfold raw28415step3 raw28415step2; decide +kernel
      have hl : raw28415step2Labels = labelEmbedding6 ∘ raw28415step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28415step2 raw28415step2Labels raw28415step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4375 node4375Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
