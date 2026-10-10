import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11392 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11392step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11392step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11392 raw11392Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw11392 raw11392Labels = mixedMoment B raw11392step0 raw11392step0Labels := by
      have ha : raw11392step0 = (fun i j => raw11392 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11392step0 raw11392; decide +kernel
      have hl : raw11392step0Labels = raw11392Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11392 raw11392Labels permutation216 permutation5
    mixedMoment B raw11392step0 raw11392step0Labels = mixedMoment B raw11392step1 raw11392step1Labels := by
      have ha : raw11392step1 = -raw11392step0 := by apply Matrix.ext; change ∀ i j, raw11392step1 i j = -(raw11392step0 i j); unfold raw11392step1 raw11392step0; decide +kernel
      have hl : raw11392step1Labels = raw11392step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11392step1 raw11392step1Labels = mixedMoment B raw11392step2 raw11392step2Labels := by
      have ha : raw11392step2 = raw11392step1 := by apply Matrix.ext; unfold raw11392step2 raw11392step1; decide +kernel
      have hl : raw11392step1Labels = labelEmbedding1 ∘ raw11392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11392step1 raw11392step1Labels raw11392step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw11393 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11393step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11393step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11393step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11393step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11393 raw11393Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw11393 raw11393Labels = mixedMoment B raw11393step0 raw11393step0Labels := by
      have hz : ∀ j, raw11393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11393step0 = (fun i j => raw11393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11393step0 raw11393; decide +kernel
      have hl : raw11393step0Labels = raw11393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11393 raw11393Labels permutation434 hz
    mixedMoment B raw11393step0 raw11393step0Labels = mixedMoment B raw11393step1 raw11393step1Labels := by
      have ha : raw11393step1 = (fun i j => raw11393step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11393step1 raw11393step0; decide +kernel
      have hl : raw11393step1Labels = raw11393step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11393step0 raw11393step0Labels permutation48 permutation5
    mixedMoment B raw11393step1 raw11393step1Labels = mixedMoment B raw11393step2 raw11393step2Labels := by
      have ha : raw11393step2 = -raw11393step1 := by apply Matrix.ext; change ∀ i j, raw11393step2 i j = -(raw11393step1 i j); unfold raw11393step2 raw11393step1; decide +kernel
      have hl : raw11393step2Labels = raw11393step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11393step2 raw11393step2Labels = mixedMoment B raw11393step3 raw11393step3Labels := by
      have ha : raw11393step3 = raw11393step2 := by apply Matrix.ext; unfold raw11393step3 raw11393step2; decide +kernel
      have hl : raw11393step2Labels = labelEmbedding1 ∘ raw11393step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11393step2 raw11393step2Labels raw11393step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw11394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11394step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11394step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11394step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11394step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11394step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11394 raw11394Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw11394 raw11394Labels = mixedMoment B raw11394step0 raw11394step0Labels := by
      have hz : ∀ j, raw11394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11394step0 = (fun i j => raw11394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11394step0 raw11394; decide +kernel
      have hl : raw11394step0Labels = raw11394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11394 raw11394Labels permutation434 hz
    mixedMoment B raw11394step0 raw11394step0Labels = mixedMoment B raw11394step1 raw11394step1Labels := by
      have ha : raw11394step1 = (fun i j => raw11394step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11394step1 raw11394step0; decide +kernel
      have hl : raw11394step1Labels = raw11394step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11394step0 raw11394step0Labels permutation44 permutation5
    mixedMoment B raw11394step1 raw11394step1Labels = mixedMoment B raw11394step2 raw11394step2Labels := by
      have ha : raw11394step2 = -raw11394step1 := by apply Matrix.ext; change ∀ i j, raw11394step2 i j = -(raw11394step1 i j); unfold raw11394step2 raw11394step1; decide +kernel
      have hl : raw11394step2Labels = raw11394step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11394step2 raw11394step2Labels = mixedMoment B raw11394step3 raw11394step3Labels := by
      have ha : raw11394step3 = raw11394step2 := by apply Matrix.ext; unfold raw11394step3 raw11394step2; decide +kernel
      have hl : raw11394step2Labels = labelEmbedding1 ∘ raw11394step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11394step2 raw11394step2Labels raw11394step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw11395 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11395step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11395step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11395step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw11395step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11395step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw11395step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11395 raw11395Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw11395 raw11395Labels = mixedMoment B raw11395step0 raw11395step0Labels := by
      have hz : ∀ j, raw11395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11395step0 = (fun i j => raw11395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11395step0 raw11395; decide +kernel
      have hl : raw11395step0Labels = raw11395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11395 raw11395Labels permutation434 hz
    mixedMoment B raw11395step0 raw11395step0Labels = mixedMoment B raw11395step1 raw11395step1Labels := by
      have hz : ∀ j, raw11395step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11395step1 = (fun i j => raw11395step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11395step1 raw11395step0; decide +kernel
      have hl : raw11395step1Labels = raw11395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11395step0 raw11395step0Labels permutation56 hz
    mixedMoment B raw11395step1 raw11395step1Labels = mixedMoment B raw11395step2 raw11395step2Labels := by
      have ha : raw11395step2 = (fun i j => raw11395step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11395step2 raw11395step1; decide +kernel
      have hl : raw11395step2Labels = raw11395step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11395step1 raw11395step1Labels permutation10 permutation5
    mixedMoment B raw11395step2 raw11395step2Labels = mixedMoment B raw11395step3 raw11395step3Labels := by
      have ha : raw11395step3 = -raw11395step2 := by apply Matrix.ext; change ∀ i j, raw11395step3 i j = -(raw11395step2 i j); unfold raw11395step3 raw11395step2; decide +kernel
      have hl : raw11395step3Labels = raw11395step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11395step3 raw11395step3Labels = mixedMoment B raw11395step4 raw11395step4Labels := by
      have ha : raw11395step4 = raw11395step3 := by apply Matrix.ext; unfold raw11395step4 raw11395step3; decide +kernel
      have hl : raw11395step3Labels = labelEmbedding1 ∘ raw11395step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11395step3 raw11395step3Labels raw11395step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw11396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw11396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11396 raw11396Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw11396 raw11396Labels = mixedMoment B raw11396step0 raw11396step0Labels := by
      have hz : ∀ j, raw11396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11396step0 = (fun i j => raw11396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11396step0 raw11396; decide +kernel
      have hl : raw11396step0Labels = raw11396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11396 raw11396Labels permutation434 hz
    mixedMoment B raw11396step0 raw11396step0Labels = mixedMoment B raw11396step1 raw11396step1Labels := by
      have ha : raw11396step1 = (fun i j => raw11396step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11396step1 raw11396step0; decide +kernel
      have hl : raw11396step1Labels = raw11396step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11396step0 raw11396step0Labels permutation45 permutation4
    mixedMoment B raw11396step1 raw11396step1Labels = mixedMoment B raw11396step2 raw11396step2Labels := by
      have ha : raw11396step2 = -raw11396step1 := by apply Matrix.ext; change ∀ i j, raw11396step2 i j = -(raw11396step1 i j); unfold raw11396step2 raw11396step1; decide +kernel
      have hl : raw11396step2Labels = raw11396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw11397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw11397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw11397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11397 raw11397Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw11397 raw11397Labels = mixedMoment B raw11397step0 raw11397step0Labels := by
      have hz : ∀ j, raw11397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11397step0 = (fun i j => raw11397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11397step0 raw11397; decide +kernel
      have hl : raw11397step0Labels = raw11397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11397 raw11397Labels permutation434 hz
    mixedMoment B raw11397step0 raw11397step0Labels = mixedMoment B raw11397step1 raw11397step1Labels := by
      have ha : raw11397step1 = (fun i j => raw11397step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11397step1 raw11397step0; decide +kernel
      have hl : raw11397step1Labels = raw11397step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11397step0 raw11397step0Labels permutation44 permutation4
    mixedMoment B raw11397step1 raw11397step1Labels = mixedMoment B raw11397step2 raw11397step2Labels := by
      have ha : raw11397step2 = -raw11397step1 := by apply Matrix.ext; change ∀ i j, raw11397step2 i j = -(raw11397step1 i j); unfold raw11397step2 raw11397step1; decide +kernel
      have hl : raw11397step2Labels = raw11397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw11398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11398step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11398step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11398step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11398step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11398step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11398step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11398step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11398 raw11398Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw11398 raw11398Labels = mixedMoment B raw11398step0 raw11398step0Labels := by
      have hz : ∀ j, raw11398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11398step0 = (fun i j => raw11398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11398step0 raw11398; decide +kernel
      have hl : raw11398step0Labels = raw11398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11398 raw11398Labels permutation434 hz
    mixedMoment B raw11398step0 raw11398step0Labels = mixedMoment B raw11398step1 raw11398step1Labels := by
      have hz : ∀ j, raw11398step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11398step1 = (fun i j => raw11398step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11398step1 raw11398step0; decide +kernel
      have hl : raw11398step1Labels = raw11398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11398step0 raw11398step0Labels permutation80 hz
    mixedMoment B raw11398step1 raw11398step1Labels = mixedMoment B raw11398step2 raw11398step2Labels := by
      have ha : raw11398step2 = (fun i j => raw11398step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11398step2 raw11398step1; decide +kernel
      have hl : raw11398step2Labels = raw11398step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11398step1 raw11398step1Labels permutation8 permutation7
    mixedMoment B raw11398step2 raw11398step2Labels = mixedMoment B raw11398step3 raw11398step3Labels := by
      have ha : raw11398step3 = -raw11398step2 := by apply Matrix.ext; change ∀ i j, raw11398step3 i j = -(raw11398step2 i j); unfold raw11398step3 raw11398step2; decide +kernel
      have hl : raw11398step3Labels = raw11398step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11398step3 raw11398step3Labels = mixedMoment B raw11398step4 raw11398step4Labels := by
      have ha : raw11398step4 = raw11398step3 := by apply Matrix.ext; unfold raw11398step4 raw11398step3; decide +kernel
      have hl : raw11398step3Labels = labelEmbedding10 ∘ raw11398step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11398step3 raw11398step3Labels raw11398step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw11399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11399step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11399step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11399step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11399step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11399 raw11399Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw11399 raw11399Labels = mixedMoment B raw11399step0 raw11399step0Labels := by
      have hz : ∀ j, raw11399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11399step0 = (fun i j => raw11399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11399step0 raw11399; decide +kernel
      have hl : raw11399step0Labels = raw11399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11399 raw11399Labels permutation434 hz
    mixedMoment B raw11399step0 raw11399step0Labels = mixedMoment B raw11399step1 raw11399step1Labels := by
      have ha : raw11399step1 = (fun i j => raw11399step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11399step1 raw11399step0; decide +kernel
      have hl : raw11399step1Labels = raw11399step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11399step0 raw11399step0Labels permutation38 permutation7
    mixedMoment B raw11399step1 raw11399step1Labels = mixedMoment B raw11399step2 raw11399step2Labels := by
      have ha : raw11399step2 = -raw11399step1 := by apply Matrix.ext; change ∀ i j, raw11399step2 i j = -(raw11399step1 i j); unfold raw11399step2 raw11399step1; decide +kernel
      have hl : raw11399step2Labels = raw11399step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11399step2 raw11399step2Labels = mixedMoment B raw11399step3 raw11399step3Labels := by
      have ha : raw11399step3 = raw11399step2 := by apply Matrix.ext; unfold raw11399step3 raw11399step2; decide +kernel
      have hl : raw11399step2Labels = labelEmbedding10 ∘ raw11399step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11399step2 raw11399step2Labels raw11399step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw11400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11400step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11400step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11400step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11400 raw11400Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw11400 raw11400Labels = mixedMoment B raw11400step0 raw11400step0Labels := by
      have hz : ∀ j, raw11400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11400step0 = (fun i j => raw11400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11400step0 raw11400; decide +kernel
      have hl : raw11400step0Labels = raw11400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11400 raw11400Labels permutation346 hz
    mixedMoment B raw11400step0 raw11400step0Labels = mixedMoment B raw11400step1 raw11400step1Labels := by
      have ha : raw11400step1 = (fun i j => raw11400step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11400step1 raw11400step0; decide +kernel
      have hl : raw11400step1Labels = raw11400step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11400step0 raw11400step0Labels permutation38 permutation7
    mixedMoment B raw11400step1 raw11400step1Labels = mixedMoment B raw11400step2 raw11400step2Labels := by
      have ha : raw11400step2 = -raw11400step1 := by apply Matrix.ext; change ∀ i j, raw11400step2 i j = -(raw11400step1 i j); unfold raw11400step2 raw11400step1; decide +kernel
      have hl : raw11400step2Labels = raw11400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11400step2 raw11400step2Labels = mixedMoment B raw11400step3 raw11400step3Labels := by
      have ha : raw11400step3 = raw11400step2 := by apply Matrix.ext; unfold raw11400step3 raw11400step2; decide +kernel
      have hl : raw11400step2Labels = labelEmbedding10 ∘ raw11400step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11400step2 raw11400step2Labels raw11400step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw11401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11401step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11401step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11401step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11401step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11401step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11401 raw11401Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw11401 raw11401Labels = mixedMoment B raw11401step0 raw11401step0Labels := by
      have hz : ∀ j, raw11401 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11401step0 = (fun i j => raw11401 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11401step0 raw11401; decide +kernel
      have hl : raw11401step0Labels = raw11401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11401 raw11401Labels permutation434 hz
    mixedMoment B raw11401step0 raw11401step0Labels = mixedMoment B raw11401step1 raw11401step1Labels := by
      have hz : ∀ j, raw11401step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11401step1 = (fun i j => raw11401step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11401step1 raw11401step0; decide +kernel
      have hl : raw11401step1Labels = raw11401step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11401step0 raw11401step0Labels permutation80 hz
    mixedMoment B raw11401step1 raw11401step1Labels = mixedMoment B raw11401step2 raw11401step2Labels := by
      have ha : raw11401step2 = (fun i j => raw11401step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11401step2 raw11401step1; decide +kernel
      have hl : raw11401step2Labels = raw11401step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11401step1 raw11401step1Labels permutation8 permutation7
    mixedMoment B raw11401step2 raw11401step2Labels = mixedMoment B raw11401step3 raw11401step3Labels := by
      have ha : raw11401step3 = -raw11401step2 := by apply Matrix.ext; change ∀ i j, raw11401step3 i j = -(raw11401step2 i j); unfold raw11401step3 raw11401step2; decide +kernel
      have hl : raw11401step3Labels = raw11401step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11401step3 raw11401step3Labels = mixedMoment B raw11401step4 raw11401step4Labels := by
      have ha : raw11401step4 = raw11401step3 := by apply Matrix.ext; unfold raw11401step4 raw11401step3; decide +kernel
      have hl : raw11401step3Labels = labelEmbedding10 ∘ raw11401step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11401step3 raw11401step3Labels raw11401step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw11402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11402step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11402step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11402step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11402step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11402step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11402step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11402 raw11402Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw11402 raw11402Labels = mixedMoment B raw11402step0 raw11402step0Labels := by
      have hz : ∀ j, raw11402 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11402step0 = (fun i j => raw11402 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11402step0 raw11402; decide +kernel
      have hl : raw11402step0Labels = raw11402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11402 raw11402Labels permutation434 hz
    mixedMoment B raw11402step0 raw11402step0Labels = mixedMoment B raw11402step1 raw11402step1Labels := by
      have hz : ∀ j, raw11402step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11402step1 = (fun i j => raw11402step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11402step1 raw11402step0; decide +kernel
      have hl : raw11402step1Labels = raw11402step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11402step0 raw11402step0Labels permutation80 hz
    mixedMoment B raw11402step1 raw11402step1Labels = mixedMoment B raw11402step2 raw11402step2Labels := by
      have ha : raw11402step2 = (fun i j => raw11402step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11402step2 raw11402step1; decide +kernel
      have hl : raw11402step2Labels = raw11402step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11402step1 raw11402step1Labels permutation8 permutation7
    mixedMoment B raw11402step2 raw11402step2Labels = mixedMoment B raw11402step3 raw11402step3Labels := by
      have ha : raw11402step3 = -raw11402step2 := by apply Matrix.ext; change ∀ i j, raw11402step3 i j = -(raw11402step2 i j); unfold raw11402step3 raw11402step2; decide +kernel
      have hl : raw11402step3Labels = raw11402step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11402step3 raw11402step3Labels = mixedMoment B raw11402step4 raw11402step4Labels := by
      have ha : raw11402step4 = raw11402step3 := by apply Matrix.ext; unfold raw11402step4 raw11402step3; decide +kernel
      have hl : raw11402step3Labels = labelEmbedding10 ∘ raw11402step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11402step3 raw11402step3Labels raw11402step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw11403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11403 raw11403Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw11403 raw11403Labels = mixedMoment B raw11403step0 raw11403step0Labels := by
      have hz : ∀ j, raw11403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11403step0 = (fun i j => raw11403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11403step0 raw11403; decide +kernel
      have hl : raw11403step0Labels = raw11403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11403 raw11403Labels permutation434 hz
    mixedMoment B raw11403step0 raw11403step0Labels = mixedMoment B raw11403step1 raw11403step1Labels := by
      have hz : ∀ j, raw11403step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11403step1 = (fun i j => raw11403step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11403step1 raw11403step0; decide +kernel
      have hl : raw11403step1Labels = raw11403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11403step0 raw11403step0Labels permutation80 hz
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw11404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11404 raw11404Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw11404 raw11404Labels = mixedMoment B raw11404step0 raw11404step0Labels := by
      have hz : ∀ j, raw11404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11404step0 = (fun i j => raw11404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11404step0 raw11404; decide +kernel
      have hl : raw11404step0Labels = raw11404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11404 raw11404Labels permutation434 hz
    mixedMoment B raw11404step0 raw11404step0Labels = mixedMoment B raw11404step1 raw11404step1Labels := by
      have ha : raw11404step1 = (fun i j => raw11404step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11404step1 raw11404step0; decide +kernel
      have hl : raw11404step1Labels = raw11404step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11404step0 raw11404step0Labels permutation38 permutation2
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw11405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11405step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11405 raw11405Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw11405 raw11405Labels = mixedMoment B raw11405step0 raw11405step0Labels := by
      have hz : ∀ j, raw11405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11405step0 = (fun i j => raw11405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11405step0 raw11405; decide +kernel
      have hl : raw11405step0Labels = raw11405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11405 raw11405Labels permutation346 hz
    mixedMoment B raw11405step0 raw11405step0Labels = mixedMoment B raw11405step1 raw11405step1Labels := by
      have ha : raw11405step1 = (fun i j => raw11405step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11405step1 raw11405step0; decide +kernel
      have hl : raw11405step1Labels = raw11405step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11405step0 raw11405step0Labels permutation38 permutation2
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw11406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11406step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11406 raw11406Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11406 raw11406Labels = mixedMoment B raw11406step0 raw11406step0Labels := by
      have hz : ∀ j, raw11406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11406step0 = (fun i j => raw11406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11406step0 raw11406; decide +kernel
      have hl : raw11406step0Labels = raw11406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11406 raw11406Labels permutation434 hz
    mixedMoment B raw11406step0 raw11406step0Labels = mixedMoment B raw11406step1 raw11406step1Labels := by
      have hz : ∀ j, raw11406step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11406step1 = (fun i j => raw11406step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11406step1 raw11406step0; decide +kernel
      have hl : raw11406step1Labels = raw11406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11406step0 raw11406step0Labels permutation80 hz
    mixedMoment B raw11406step1 raw11406step1Labels = mixedMoment B raw11406step2 raw11406step2Labels := by
      have ha : raw11406step2 = (fun i j => raw11406step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11406step2 raw11406step1; decide +kernel
      have hl : raw11406step2Labels = raw11406step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11406step1 raw11406step1Labels permutation10 permutation2
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw11407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11407step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11407step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11407step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw11407step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11407step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11407 raw11407Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11407 raw11407Labels = mixedMoment B raw11407step0 raw11407step0Labels := by
      have hz : ∀ j, raw11407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11407step0 = (fun i j => raw11407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11407step0 raw11407; decide +kernel
      have hl : raw11407step0Labels = raw11407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11407 raw11407Labels permutation434 hz
    mixedMoment B raw11407step0 raw11407step0Labels = mixedMoment B raw11407step1 raw11407step1Labels := by
      have hz : ∀ j, raw11407step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11407step1 = (fun i j => raw11407step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11407step1 raw11407step0; decide +kernel
      have hl : raw11407step1Labels = raw11407step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11407step0 raw11407step0Labels permutation80 hz
    mixedMoment B raw11407step1 raw11407step1Labels = mixedMoment B raw11407step2 raw11407step2Labels := by
      have hz : ∀ i, raw11407step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw11407step2 = (fun i j => raw11407step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw11407step2 raw11407step1; decide +kernel
      have hl : raw11407step2Labels = (fun j => raw11407step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11407step1 raw11407step1Labels permutation4 hz
    mixedMoment B raw11407step2 raw11407step2Labels = mixedMoment B raw11407step3 raw11407step3Labels := by
      have ha : raw11407step3 = raw11407step2 := by apply Matrix.ext; unfold raw11407step3 raw11407step2; decide +kernel
      have hl : raw11407step2Labels = labelEmbedding2 ∘ raw11407step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11407step2 raw11407step2Labels raw11407step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw11408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11408step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11408 raw11408Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw11408 raw11408Labels = mixedMoment B raw11408step0 raw11408step0Labels := by
      have hz : ∀ j, raw11408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11408step0 = (fun i j => raw11408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11408step0 raw11408; decide +kernel
      have hl : raw11408step0Labels = raw11408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11408 raw11408Labels permutation434 hz
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw11409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11409 raw11409Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw11409 raw11409Labels = mixedMoment B raw11409step0 raw11409step0Labels := by
      have hz : ∀ j, raw11409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11409step0 = (fun i j => raw11409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11409step0 raw11409; decide +kernel
      have hl : raw11409step0Labels = raw11409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11409 raw11409Labels permutation434 hz
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw11410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11410 raw11410Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11410 raw11410Labels = mixedMoment B raw11410step0 raw11410step0Labels := by
      have ha : raw11410step0 = (fun i j => raw11410 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11410step0 raw11410; decide +kernel
      have hl : raw11410step0Labels = raw11410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11410 raw11410Labels permutation200 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw11411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11411 raw11411Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11411 raw11411Labels = mixedMoment B raw11411step0 raw11411step0Labels := by
      have hz : ∀ j, raw11411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11411step0 = (fun i j => raw11411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11411step0 raw11411; decide +kernel
      have hl : raw11411step0Labels = raw11411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11411 raw11411Labels permutation434 hz
    mixedMoment B raw11411step0 raw11411step0Labels = mixedMoment B raw11411step1 raw11411step1Labels := by
      have ha : raw11411step1 = (fun i j => raw11411step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11411step1 raw11411step0; decide +kernel
      have hl : raw11411step1Labels = raw11411step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11411step0 raw11411step0Labels permutation34 permutation2
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw11412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11412 raw11412Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw11412 raw11412Labels = mixedMoment B raw11412step0 raw11412step0Labels := by
      have hz : ∀ j, raw11412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11412step0 = (fun i j => raw11412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11412step0 raw11412; decide +kernel
      have hl : raw11412step0Labels = raw11412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11412 raw11412Labels permutation434 hz
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw11413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11413 raw11413Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw11413 raw11413Labels = mixedMoment B raw11413step0 raw11413step0Labels := by
      have hz : ∀ j, raw11413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11413step0 = (fun i j => raw11413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11413step0 raw11413; decide +kernel
      have hl : raw11413step0Labels = raw11413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11413 raw11413Labels permutation346 hz
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw11414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11414 raw11414Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw11414 raw11414Labels = mixedMoment B raw11414step0 raw11414step0Labels := by
      have hz : ∀ j, raw11414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11414step0 = (fun i j => raw11414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11414step0 raw11414; decide +kernel
      have hl : raw11414step0Labels = raw11414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11414 raw11414Labels permutation346 hz
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw11415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11415 raw11415Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11415 raw11415Labels = mixedMoment B raw11415step0 raw11415step0Labels := by
      have ha : raw11415step0 = (fun i j => raw11415 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11415step0 raw11415; decide +kernel
      have hl : raw11415step0Labels = raw11415Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11415 raw11415Labels permutation176 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw11416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11416 raw11416Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11416 raw11416Labels = mixedMoment B raw11416step0 raw11416step0Labels := by
      have hz : ∀ j, raw11416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11416step0 = (fun i j => raw11416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11416step0 raw11416; decide +kernel
      have hl : raw11416step0Labels = raw11416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11416 raw11416Labels permutation346 hz
    mixedMoment B raw11416step0 raw11416step0Labels = mixedMoment B raw11416step1 raw11416step1Labels := by
      have ha : raw11416step1 = (fun i j => raw11416step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11416step1 raw11416step0; decide +kernel
      have hl : raw11416step1Labels = raw11416step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11416step0 raw11416step0Labels permutation34 permutation2
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw11417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11417 raw11417Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw11417 raw11417Labels = mixedMoment B raw11417step0 raw11417step0Labels := by
      have hz : ∀ j, raw11417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11417step0 = (fun i j => raw11417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11417step0 raw11417; decide +kernel
      have hl : raw11417step0Labels = raw11417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11417 raw11417Labels permutation346 hz
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw11418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11418 raw11418Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw11418 raw11418Labels = mixedMoment B raw11418step0 raw11418step0Labels := by
      have hz : ∀ j, raw11418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11418step0 = (fun i j => raw11418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11418step0 raw11418; decide +kernel
      have hl : raw11418step0Labels = raw11418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11418 raw11418Labels permutation434 hz
    mixedMoment B raw11418step0 raw11418step0Labels = mixedMoment B raw11418step1 raw11418step1Labels := by
      have hz : ∀ j, raw11418step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11418step1 = (fun i j => raw11418step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11418step1 raw11418step0; decide +kernel
      have hl : raw11418step1Labels = raw11418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11418step0 raw11418step0Labels permutation80 hz
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw11419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11419 raw11419Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw11419 raw11419Labels = mixedMoment B raw11419step0 raw11419step0Labels := by
      have hz : ∀ j, raw11419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11419step0 = (fun i j => raw11419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11419step0 raw11419; decide +kernel
      have hl : raw11419step0Labels = raw11419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11419 raw11419Labels permutation434 hz
    mixedMoment B raw11419step0 raw11419step0Labels = mixedMoment B raw11419step1 raw11419step1Labels := by
      have hz : ∀ j, raw11419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11419step1 = (fun i j => raw11419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11419step1 raw11419step0; decide +kernel
      have hl : raw11419step1Labels = raw11419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11419step0 raw11419step0Labels permutation80 hz
    _ = mixedMoment B node4875 node4875Labels := by rfl

def raw11420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11420step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11420 raw11420Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11420 raw11420Labels = mixedMoment B raw11420step0 raw11420step0Labels := by
      have hz : ∀ j, raw11420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11420step0 = (fun i j => raw11420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11420step0 raw11420; decide +kernel
      have hl : raw11420step0Labels = raw11420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11420 raw11420Labels permutation434 hz
    mixedMoment B raw11420step0 raw11420step0Labels = mixedMoment B raw11420step1 raw11420step1Labels := by
      have ha : raw11420step1 = (fun i j => raw11420step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11420step1 raw11420step0; decide +kernel
      have hl : raw11420step1Labels = raw11420step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11420step0 raw11420step0Labels permutation38 permutation2
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw11421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11421 raw11421Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11421 raw11421Labels = mixedMoment B raw11421step0 raw11421step0Labels := by
      have hz : ∀ j, raw11421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11421step0 = (fun i j => raw11421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11421step0 raw11421; decide +kernel
      have hl : raw11421step0Labels = raw11421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11421 raw11421Labels permutation346 hz
    mixedMoment B raw11421step0 raw11421step0Labels = mixedMoment B raw11421step1 raw11421step1Labels := by
      have ha : raw11421step1 = (fun i j => raw11421step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11421step1 raw11421step0; decide +kernel
      have hl : raw11421step1Labels = raw11421step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11421step0 raw11421step0Labels permutation38 permutation2
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw11422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw11422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11422step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11422 raw11422Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11422 raw11422Labels = mixedMoment B raw11422step0 raw11422step0Labels := by
      have hz : ∀ j, raw11422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11422step0 = (fun i j => raw11422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11422step0 raw11422; decide +kernel
      have hl : raw11422step0Labels = raw11422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11422 raw11422Labels permutation434 hz
    mixedMoment B raw11422step0 raw11422step0Labels = mixedMoment B raw11422step1 raw11422step1Labels := by
      have hz : ∀ j, raw11422step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11422step1 = (fun i j => raw11422step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11422step1 raw11422step0; decide +kernel
      have hl : raw11422step1Labels = raw11422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11422step0 raw11422step0Labels permutation80 hz
    mixedMoment B raw11422step1 raw11422step1Labels = mixedMoment B raw11422step2 raw11422step2Labels := by
      have ha : raw11422step2 = (fun i j => raw11422step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11422step2 raw11422step1; decide +kernel
      have hl : raw11422step2Labels = raw11422step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11422step1 raw11422step1Labels permutation9 permutation2
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw11423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11423step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11423 raw11423Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw11423 raw11423Labels = mixedMoment B raw11423step0 raw11423step0Labels := by
      have hz : ∀ j, raw11423 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11423step0 = (fun i j => raw11423 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11423step0 raw11423; decide +kernel
      have hl : raw11423step0Labels = raw11423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11423 raw11423Labels permutation434 hz
    mixedMoment B raw11423step0 raw11423step0Labels = mixedMoment B raw11423step1 raw11423step1Labels := by
      have hz : ∀ j, raw11423step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11423step1 = (fun i j => raw11423step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11423step1 raw11423step0; decide +kernel
      have hl : raw11423step1Labels = raw11423step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11423step0 raw11423step0Labels permutation80 hz
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw11424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11424 raw11424Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw11424 raw11424Labels = mixedMoment B raw11424step0 raw11424step0Labels := by
      have hz : ∀ j, raw11424 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11424step0 = (fun i j => raw11424 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11424step0 raw11424; decide +kernel
      have hl : raw11424step0Labels = raw11424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11424 raw11424Labels permutation434 hz
    mixedMoment B raw11424step0 raw11424step0Labels = mixedMoment B raw11424step1 raw11424step1Labels := by
      have hz : ∀ j, raw11424step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11424step1 = (fun i j => raw11424step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11424step1 raw11424step0; decide +kernel
      have hl : raw11424step1Labels = raw11424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11424step0 raw11424step0Labels permutation80 hz
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw11425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11425 raw11425Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw11425 raw11425Labels = mixedMoment B raw11425step0 raw11425step0Labels := by
      have hz : ∀ j, raw11425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11425step0 = (fun i j => raw11425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11425step0 raw11425; decide +kernel
      have hl : raw11425step0Labels = raw11425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11425 raw11425Labels permutation434 hz
    mixedMoment B raw11425step0 raw11425step0Labels = mixedMoment B raw11425step1 raw11425step1Labels := by
      have ha : raw11425step1 = (fun i j => raw11425step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11425step1 raw11425step0; decide +kernel
      have hl : raw11425step1Labels = raw11425step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11425step0 raw11425step0Labels permutation38 permutation2
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw11426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11426 raw11426Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw11426 raw11426Labels = mixedMoment B raw11426step0 raw11426step0Labels := by
      have hz : ∀ j, raw11426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11426step0 = (fun i j => raw11426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11426step0 raw11426; decide +kernel
      have hl : raw11426step0Labels = raw11426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11426 raw11426Labels permutation346 hz
    mixedMoment B raw11426step0 raw11426step0Labels = mixedMoment B raw11426step1 raw11426step1Labels := by
      have ha : raw11426step1 = (fun i j => raw11426step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11426step1 raw11426step0; decide +kernel
      have hl : raw11426step1Labels = raw11426step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11426step0 raw11426step0Labels permutation38 permutation2
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw11427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11427 raw11427Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw11427 raw11427Labels = mixedMoment B raw11427step0 raw11427step0Labels := by
      have hz : ∀ j, raw11427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11427step0 = (fun i j => raw11427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11427step0 raw11427; decide +kernel
      have hl : raw11427step0Labels = raw11427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11427 raw11427Labels permutation434 hz
    mixedMoment B raw11427step0 raw11427step0Labels = mixedMoment B raw11427step1 raw11427step1Labels := by
      have hz : ∀ j, raw11427step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11427step1 = (fun i j => raw11427step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11427step1 raw11427step0; decide +kernel
      have hl : raw11427step1Labels = raw11427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11427step0 raw11427step0Labels permutation80 hz
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw11428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11428step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11428step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11428step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11428step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11428step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11428step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11428step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11428 raw11428Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw11428 raw11428Labels = mixedMoment B raw11428step0 raw11428step0Labels := by
      have hz : ∀ j, raw11428 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11428step0 = (fun i j => raw11428 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11428step0 raw11428; decide +kernel
      have hl : raw11428step0Labels = raw11428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11428 raw11428Labels permutation434 hz
    mixedMoment B raw11428step0 raw11428step0Labels = mixedMoment B raw11428step1 raw11428step1Labels := by
      have hz : ∀ j, raw11428step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11428step1 = (fun i j => raw11428step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11428step1 raw11428step0; decide +kernel
      have hl : raw11428step1Labels = raw11428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11428step0 raw11428step0Labels permutation80 hz
    mixedMoment B raw11428step1 raw11428step1Labels = mixedMoment B raw11428step2 raw11428step2Labels := by
      have ha : raw11428step2 = (fun i j => raw11428step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11428step2 raw11428step1; decide +kernel
      have hl : raw11428step2Labels = raw11428step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11428step1 raw11428step1Labels permutation8 permutation7
    mixedMoment B raw11428step2 raw11428step2Labels = mixedMoment B raw11428step3 raw11428step3Labels := by
      have ha : raw11428step3 = -raw11428step2 := by apply Matrix.ext; change ∀ i j, raw11428step3 i j = -(raw11428step2 i j); unfold raw11428step3 raw11428step2; decide +kernel
      have hl : raw11428step3Labels = raw11428step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11428step3 raw11428step3Labels = mixedMoment B raw11428step4 raw11428step4Labels := by
      have ha : raw11428step4 = raw11428step3 := by apply Matrix.ext; unfold raw11428step4 raw11428step3; decide +kernel
      have hl : raw11428step3Labels = labelEmbedding1 ∘ raw11428step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11428step3 raw11428step3Labels raw11428step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw11429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11429step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11429step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11429 raw11429Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw11429 raw11429Labels = mixedMoment B raw11429step0 raw11429step0Labels := by
      have hz : ∀ j, raw11429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11429step0 = (fun i j => raw11429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11429step0 raw11429; decide +kernel
      have hl : raw11429step0Labels = raw11429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11429 raw11429Labels permutation434 hz
    mixedMoment B raw11429step0 raw11429step0Labels = mixedMoment B raw11429step1 raw11429step1Labels := by
      have ha : raw11429step1 = (fun i j => raw11429step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11429step1 raw11429step0; decide +kernel
      have hl : raw11429step1Labels = raw11429step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11429step0 raw11429step0Labels permutation38 permutation7
    mixedMoment B raw11429step1 raw11429step1Labels = mixedMoment B raw11429step2 raw11429step2Labels := by
      have ha : raw11429step2 = -raw11429step1 := by apply Matrix.ext; change ∀ i j, raw11429step2 i j = -(raw11429step1 i j); unfold raw11429step2 raw11429step1; decide +kernel
      have hl : raw11429step2Labels = raw11429step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11429step2 raw11429step2Labels = mixedMoment B raw11429step3 raw11429step3Labels := by
      have ha : raw11429step3 = raw11429step2 := by apply Matrix.ext; unfold raw11429step3 raw11429step2; decide +kernel
      have hl : raw11429step2Labels = labelEmbedding1 ∘ raw11429step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11429step2 raw11429step2Labels raw11429step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw11430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11430step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11430step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11430step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11430step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11430 raw11430Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw11430 raw11430Labels = mixedMoment B raw11430step0 raw11430step0Labels := by
      have hz : ∀ j, raw11430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11430step0 = (fun i j => raw11430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11430step0 raw11430; decide +kernel
      have hl : raw11430step0Labels = raw11430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11430 raw11430Labels permutation346 hz
    mixedMoment B raw11430step0 raw11430step0Labels = mixedMoment B raw11430step1 raw11430step1Labels := by
      have ha : raw11430step1 = (fun i j => raw11430step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11430step1 raw11430step0; decide +kernel
      have hl : raw11430step1Labels = raw11430step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11430step0 raw11430step0Labels permutation38 permutation7
    mixedMoment B raw11430step1 raw11430step1Labels = mixedMoment B raw11430step2 raw11430step2Labels := by
      have ha : raw11430step2 = -raw11430step1 := by apply Matrix.ext; change ∀ i j, raw11430step2 i j = -(raw11430step1 i j); unfold raw11430step2 raw11430step1; decide +kernel
      have hl : raw11430step2Labels = raw11430step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11430step2 raw11430step2Labels = mixedMoment B raw11430step3 raw11430step3Labels := by
      have ha : raw11430step3 = raw11430step2 := by apply Matrix.ext; unfold raw11430step3 raw11430step2; decide +kernel
      have hl : raw11430step2Labels = labelEmbedding1 ∘ raw11430step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11430step2 raw11430step2Labels raw11430step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw11431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11431step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11431step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11431step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11431step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11431step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11431step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11431step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11431 raw11431Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw11431 raw11431Labels = mixedMoment B raw11431step0 raw11431step0Labels := by
      have hz : ∀ j, raw11431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11431step0 = (fun i j => raw11431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11431step0 raw11431; decide +kernel
      have hl : raw11431step0Labels = raw11431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11431 raw11431Labels permutation434 hz
    mixedMoment B raw11431step0 raw11431step0Labels = mixedMoment B raw11431step1 raw11431step1Labels := by
      have hz : ∀ j, raw11431step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11431step1 = (fun i j => raw11431step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11431step1 raw11431step0; decide +kernel
      have hl : raw11431step1Labels = raw11431step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11431step0 raw11431step0Labels permutation80 hz
    mixedMoment B raw11431step1 raw11431step1Labels = mixedMoment B raw11431step2 raw11431step2Labels := by
      have ha : raw11431step2 = (fun i j => raw11431step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11431step2 raw11431step1; decide +kernel
      have hl : raw11431step2Labels = raw11431step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11431step1 raw11431step1Labels permutation8 permutation7
    mixedMoment B raw11431step2 raw11431step2Labels = mixedMoment B raw11431step3 raw11431step3Labels := by
      have ha : raw11431step3 = -raw11431step2 := by apply Matrix.ext; change ∀ i j, raw11431step3 i j = -(raw11431step2 i j); unfold raw11431step3 raw11431step2; decide +kernel
      have hl : raw11431step3Labels = raw11431step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11431step3 raw11431step3Labels = mixedMoment B raw11431step4 raw11431step4Labels := by
      have ha : raw11431step4 = raw11431step3 := by apply Matrix.ext; unfold raw11431step4 raw11431step3; decide +kernel
      have hl : raw11431step3Labels = labelEmbedding1 ∘ raw11431step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11431step3 raw11431step3Labels raw11431step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw11432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11432step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11432step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11432step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11432step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11432step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11432step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11432step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11432 raw11432Labels = mixedMoment B node2785 node2785Labels := by
  calc
    mixedMoment B raw11432 raw11432Labels = mixedMoment B raw11432step0 raw11432step0Labels := by
      have hz : ∀ j, raw11432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11432step0 = (fun i j => raw11432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11432step0 raw11432; decide +kernel
      have hl : raw11432step0Labels = raw11432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11432 raw11432Labels permutation434 hz
    mixedMoment B raw11432step0 raw11432step0Labels = mixedMoment B raw11432step1 raw11432step1Labels := by
      have hz : ∀ j, raw11432step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11432step1 = (fun i j => raw11432step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11432step1 raw11432step0; decide +kernel
      have hl : raw11432step1Labels = raw11432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11432step0 raw11432step0Labels permutation80 hz
    mixedMoment B raw11432step1 raw11432step1Labels = mixedMoment B raw11432step2 raw11432step2Labels := by
      have ha : raw11432step2 = (fun i j => raw11432step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11432step2 raw11432step1; decide +kernel
      have hl : raw11432step2Labels = raw11432step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11432step1 raw11432step1Labels permutation8 permutation7
    mixedMoment B raw11432step2 raw11432step2Labels = mixedMoment B raw11432step3 raw11432step3Labels := by
      have ha : raw11432step3 = -raw11432step2 := by apply Matrix.ext; change ∀ i j, raw11432step3 i j = -(raw11432step2 i j); unfold raw11432step3 raw11432step2; decide +kernel
      have hl : raw11432step3Labels = raw11432step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11432step3 raw11432step3Labels = mixedMoment B raw11432step4 raw11432step4Labels := by
      have ha : raw11432step4 = raw11432step3 := by apply Matrix.ext; unfold raw11432step4 raw11432step3; decide +kernel
      have hl : raw11432step3Labels = labelEmbedding1 ∘ raw11432step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11432step3 raw11432step3Labels raw11432step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2785 node2785Labels := by rfl

def raw11433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11433step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11433step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11433step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11433step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11433step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11433step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11433step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11433 raw11433Labels = mixedMoment B node1753 node1753Labels := by
  calc
    mixedMoment B raw11433 raw11433Labels = mixedMoment B raw11433step0 raw11433step0Labels := by
      have hz : ∀ j, raw11433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11433step0 = (fun i j => raw11433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11433step0 raw11433; decide +kernel
      have hl : raw11433step0Labels = raw11433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11433 raw11433Labels permutation434 hz
    mixedMoment B raw11433step0 raw11433step0Labels = mixedMoment B raw11433step1 raw11433step1Labels := by
      have hz : ∀ j, raw11433step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11433step1 = (fun i j => raw11433step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11433step1 raw11433step0; decide +kernel
      have hl : raw11433step1Labels = raw11433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11433step0 raw11433step0Labels permutation80 hz
    mixedMoment B raw11433step1 raw11433step1Labels = mixedMoment B raw11433step2 raw11433step2Labels := by
      have ha : raw11433step2 = (fun i j => raw11433step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11433step2 raw11433step1; decide +kernel
      have hl : raw11433step2Labels = raw11433step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11433step1 raw11433step1Labels permutation8 permutation7
    mixedMoment B raw11433step2 raw11433step2Labels = mixedMoment B raw11433step3 raw11433step3Labels := by
      have ha : raw11433step3 = -raw11433step2 := by apply Matrix.ext; change ∀ i j, raw11433step3 i j = -(raw11433step2 i j); unfold raw11433step3 raw11433step2; decide +kernel
      have hl : raw11433step3Labels = raw11433step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11433step3 raw11433step3Labels = mixedMoment B raw11433step4 raw11433step4Labels := by
      have ha : raw11433step4 = raw11433step3 := by apply Matrix.ext; unfold raw11433step4 raw11433step3; decide +kernel
      have hl : raw11433step3Labels = labelEmbedding1 ∘ raw11433step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11433step3 raw11433step3Labels raw11433step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1753 node1753Labels := by rfl

def raw11434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11434step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11434step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11434step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11434step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11434 raw11434Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw11434 raw11434Labels = mixedMoment B raw11434step0 raw11434step0Labels := by
      have hz : ∀ j, raw11434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11434step0 = (fun i j => raw11434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11434step0 raw11434; decide +kernel
      have hl : raw11434step0Labels = raw11434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11434 raw11434Labels permutation434 hz
    mixedMoment B raw11434step0 raw11434step0Labels = mixedMoment B raw11434step1 raw11434step1Labels := by
      have ha : raw11434step1 = (fun i j => raw11434step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11434step1 raw11434step0; decide +kernel
      have hl : raw11434step1Labels = raw11434step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11434step0 raw11434step0Labels permutation38 permutation7
    mixedMoment B raw11434step1 raw11434step1Labels = mixedMoment B raw11434step2 raw11434step2Labels := by
      have ha : raw11434step2 = -raw11434step1 := by apply Matrix.ext; change ∀ i j, raw11434step2 i j = -(raw11434step1 i j); unfold raw11434step2 raw11434step1; decide +kernel
      have hl : raw11434step2Labels = raw11434step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11434step2 raw11434step2Labels = mixedMoment B raw11434step3 raw11434step3Labels := by
      have ha : raw11434step3 = raw11434step2 := by apply Matrix.ext; unfold raw11434step3 raw11434step2; decide +kernel
      have hl : raw11434step2Labels = labelEmbedding1 ∘ raw11434step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11434step2 raw11434step2Labels raw11434step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

def raw11435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11435step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11435step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw11435step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11435 raw11435Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw11435 raw11435Labels = mixedMoment B raw11435step0 raw11435step0Labels := by
      have hz : ∀ j, raw11435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11435step0 = (fun i j => raw11435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11435step0 raw11435; decide +kernel
      have hl : raw11435step0Labels = raw11435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11435 raw11435Labels permutation346 hz
    mixedMoment B raw11435step0 raw11435step0Labels = mixedMoment B raw11435step1 raw11435step1Labels := by
      have ha : raw11435step1 = (fun i j => raw11435step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11435step1 raw11435step0; decide +kernel
      have hl : raw11435step1Labels = raw11435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11435step0 raw11435step0Labels permutation38 permutation7
    mixedMoment B raw11435step1 raw11435step1Labels = mixedMoment B raw11435step2 raw11435step2Labels := by
      have ha : raw11435step2 = -raw11435step1 := by apply Matrix.ext; change ∀ i j, raw11435step2 i j = -(raw11435step1 i j); unfold raw11435step2 raw11435step1; decide +kernel
      have hl : raw11435step2Labels = raw11435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11435step2 raw11435step2Labels = mixedMoment B raw11435step3 raw11435step3Labels := by
      have ha : raw11435step3 = raw11435step2 := by apply Matrix.ext; unfold raw11435step3 raw11435step2; decide +kernel
      have hl : raw11435step2Labels = labelEmbedding1 ∘ raw11435step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11435step2 raw11435step2Labels raw11435step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

def raw11436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11436step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11436step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11436step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11436step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11436step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11436step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11436step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11436 raw11436Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw11436 raw11436Labels = mixedMoment B raw11436step0 raw11436step0Labels := by
      have hz : ∀ j, raw11436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11436step0 = (fun i j => raw11436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11436step0 raw11436; decide +kernel
      have hl : raw11436step0Labels = raw11436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11436 raw11436Labels permutation434 hz
    mixedMoment B raw11436step0 raw11436step0Labels = mixedMoment B raw11436step1 raw11436step1Labels := by
      have hz : ∀ j, raw11436step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11436step1 = (fun i j => raw11436step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11436step1 raw11436step0; decide +kernel
      have hl : raw11436step1Labels = raw11436step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11436step0 raw11436step0Labels permutation80 hz
    mixedMoment B raw11436step1 raw11436step1Labels = mixedMoment B raw11436step2 raw11436step2Labels := by
      have ha : raw11436step2 = (fun i j => raw11436step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11436step2 raw11436step1; decide +kernel
      have hl : raw11436step2Labels = raw11436step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11436step1 raw11436step1Labels permutation10 permutation7
    mixedMoment B raw11436step2 raw11436step2Labels = mixedMoment B raw11436step3 raw11436step3Labels := by
      have ha : raw11436step3 = -raw11436step2 := by apply Matrix.ext; change ∀ i j, raw11436step3 i j = -(raw11436step2 i j); unfold raw11436step3 raw11436step2; decide +kernel
      have hl : raw11436step3Labels = raw11436step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11436step3 raw11436step3Labels = mixedMoment B raw11436step4 raw11436step4Labels := by
      have ha : raw11436step4 = raw11436step3 := by apply Matrix.ext; unfold raw11436step4 raw11436step3; decide +kernel
      have hl : raw11436step3Labels = labelEmbedding1 ∘ raw11436step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11436step3 raw11436step3Labels raw11436step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw11437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11437step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11437step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11437step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11437step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11437 raw11437Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11437 raw11437Labels = mixedMoment B raw11437step0 raw11437step0Labels := by
      have hz : ∀ j, raw11437 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11437step0 = (fun i j => raw11437 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11437step0 raw11437; decide +kernel
      have hl : raw11437step0Labels = raw11437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11437 raw11437Labels permutation434 hz
    mixedMoment B raw11437step0 raw11437step0Labels = mixedMoment B raw11437step1 raw11437step1Labels := by
      have hz : ∀ j, raw11437step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11437step1 = (fun i j => raw11437step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11437step1 raw11437step0; decide +kernel
      have hl : raw11437step1Labels = raw11437step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11437step0 raw11437step0Labels permutation80 hz
    mixedMoment B raw11437step1 raw11437step1Labels = mixedMoment B raw11437step2 raw11437step2Labels := by
      have hz : ∀ i, raw11437step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw11437step2 = (fun i j => raw11437step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw11437step2 raw11437step1; decide +kernel
      have hl : raw11437step2Labels = (fun j => raw11437step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11437step1 raw11437step1Labels permutation4 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw11438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11438step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11438step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11438step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11438step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11438 raw11438Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw11438 raw11438Labels = mixedMoment B raw11438step0 raw11438step0Labels := by
      have hz : ∀ j, raw11438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11438step0 = (fun i j => raw11438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11438step0 raw11438; decide +kernel
      have hl : raw11438step0Labels = raw11438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11438 raw11438Labels permutation434 hz
    mixedMoment B raw11438step0 raw11438step0Labels = mixedMoment B raw11438step1 raw11438step1Labels := by
      have ha : raw11438step1 = (fun i j => raw11438step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11438step1 raw11438step0; decide +kernel
      have hl : raw11438step1Labels = raw11438step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11438step0 raw11438step0Labels permutation38 permutation7
    mixedMoment B raw11438step1 raw11438step1Labels = mixedMoment B raw11438step2 raw11438step2Labels := by
      have ha : raw11438step2 = -raw11438step1 := by apply Matrix.ext; change ∀ i j, raw11438step2 i j = -(raw11438step1 i j); unfold raw11438step2 raw11438step1; decide +kernel
      have hl : raw11438step2Labels = raw11438step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11438step2 raw11438step2Labels = mixedMoment B raw11438step3 raw11438step3Labels := by
      have ha : raw11438step3 = raw11438step2 := by apply Matrix.ext; unfold raw11438step3 raw11438step2; decide +kernel
      have hl : raw11438step2Labels = labelEmbedding1 ∘ raw11438step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11438step2 raw11438step2Labels raw11438step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw11439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11439step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11439step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11439 raw11439Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw11439 raw11439Labels = mixedMoment B raw11439step0 raw11439step0Labels := by
      have hz : ∀ j, raw11439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11439step0 = (fun i j => raw11439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11439step0 raw11439; decide +kernel
      have hl : raw11439step0Labels = raw11439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11439 raw11439Labels permutation434 hz
    mixedMoment B raw11439step0 raw11439step0Labels = mixedMoment B raw11439step1 raw11439step1Labels := by
      have ha : raw11439step1 = (fun i j => raw11439step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11439step1 raw11439step0; decide +kernel
      have hl : raw11439step1Labels = raw11439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11439step0 raw11439step0Labels permutation38 permutation7
    mixedMoment B raw11439step1 raw11439step1Labels = mixedMoment B raw11439step2 raw11439step2Labels := by
      have ha : raw11439step2 = -raw11439step1 := by apply Matrix.ext; change ∀ i j, raw11439step2 i j = -(raw11439step1 i j); unfold raw11439step2 raw11439step1; decide +kernel
      have hl : raw11439step2Labels = raw11439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11439step2 raw11439step2Labels = mixedMoment B raw11439step3 raw11439step3Labels := by
      have ha : raw11439step3 = raw11439step2 := by apply Matrix.ext; unfold raw11439step3 raw11439step2; decide +kernel
      have hl : raw11439step2Labels = labelEmbedding1 ∘ raw11439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11439step2 raw11439step2Labels raw11439step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw11440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11440step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11440step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11440 raw11440Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw11440 raw11440Labels = mixedMoment B raw11440step0 raw11440step0Labels := by
      have ha : raw11440step0 = (fun i j => raw11440 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11440step0 raw11440; decide +kernel
      have hl : raw11440step0Labels = raw11440Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11440 raw11440Labels permutation206 permutation7
    mixedMoment B raw11440step0 raw11440step0Labels = mixedMoment B raw11440step1 raw11440step1Labels := by
      have ha : raw11440step1 = -raw11440step0 := by apply Matrix.ext; change ∀ i j, raw11440step1 i j = -(raw11440step0 i j); unfold raw11440step1 raw11440step0; decide +kernel
      have hl : raw11440step1Labels = raw11440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11440step1 raw11440step1Labels = mixedMoment B raw11440step2 raw11440step2Labels := by
      have ha : raw11440step2 = raw11440step1 := by apply Matrix.ext; unfold raw11440step2 raw11440step1; decide +kernel
      have hl : raw11440step1Labels = labelEmbedding1 ∘ raw11440step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11440step1 raw11440step1Labels raw11440step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw11441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11441step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11441step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11441step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11441step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11441 raw11441Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw11441 raw11441Labels = mixedMoment B raw11441step0 raw11441step0Labels := by
      have hz : ∀ j, raw11441 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11441step0 = (fun i j => raw11441 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11441step0 raw11441; decide +kernel
      have hl : raw11441step0Labels = raw11441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11441 raw11441Labels permutation434 hz
    mixedMoment B raw11441step0 raw11441step0Labels = mixedMoment B raw11441step1 raw11441step1Labels := by
      have ha : raw11441step1 = (fun i j => raw11441step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11441step1 raw11441step0; decide +kernel
      have hl : raw11441step1Labels = raw11441step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11441step0 raw11441step0Labels permutation38 permutation7
    mixedMoment B raw11441step1 raw11441step1Labels = mixedMoment B raw11441step2 raw11441step2Labels := by
      have ha : raw11441step2 = -raw11441step1 := by apply Matrix.ext; change ∀ i j, raw11441step2 i j = -(raw11441step1 i j); unfold raw11441step2 raw11441step1; decide +kernel
      have hl : raw11441step2Labels = raw11441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11441step2 raw11441step2Labels = mixedMoment B raw11441step3 raw11441step3Labels := by
      have ha : raw11441step3 = raw11441step2 := by apply Matrix.ext; unfold raw11441step3 raw11441step2; decide +kernel
      have hl : raw11441step2Labels = labelEmbedding1 ∘ raw11441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11441step2 raw11441step2Labels raw11441step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw11442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11442step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11442step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11442step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11442step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11442 raw11442Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11442 raw11442Labels = mixedMoment B raw11442step0 raw11442step0Labels := by
      have hz : ∀ j, raw11442 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11442step0 = (fun i j => raw11442 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11442step0 raw11442; decide +kernel
      have hl : raw11442step0Labels = raw11442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11442 raw11442Labels permutation434 hz
    mixedMoment B raw11442step0 raw11442step0Labels = mixedMoment B raw11442step1 raw11442step1Labels := by
      have ha : raw11442step1 = (fun i j => raw11442step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11442step1 raw11442step0; decide +kernel
      have hl : raw11442step1Labels = raw11442step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11442step0 raw11442step0Labels permutation38 permutation7
    mixedMoment B raw11442step1 raw11442step1Labels = mixedMoment B raw11442step2 raw11442step2Labels := by
      have ha : raw11442step2 = -raw11442step1 := by apply Matrix.ext; change ∀ i j, raw11442step2 i j = -(raw11442step1 i j); unfold raw11442step2 raw11442step1; decide +kernel
      have hl : raw11442step2Labels = raw11442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11442step2 raw11442step2Labels = mixedMoment B raw11442step3 raw11442step3Labels := by
      have ha : raw11442step3 = raw11442step2 := by apply Matrix.ext; unfold raw11442step3 raw11442step2; decide +kernel
      have hl : raw11442step2Labels = labelEmbedding1 ∘ raw11442step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11442step2 raw11442step2Labels raw11442step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw11443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11443step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11443step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11443step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11443 raw11443Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw11443 raw11443Labels = mixedMoment B raw11443step0 raw11443step0Labels := by
      have hz : ∀ j, raw11443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11443step0 = (fun i j => raw11443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11443step0 raw11443; decide +kernel
      have hl : raw11443step0Labels = raw11443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11443 raw11443Labels permutation346 hz
    mixedMoment B raw11443step0 raw11443step0Labels = mixedMoment B raw11443step1 raw11443step1Labels := by
      have ha : raw11443step1 = (fun i j => raw11443step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11443step1 raw11443step0; decide +kernel
      have hl : raw11443step1Labels = raw11443step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11443step0 raw11443step0Labels permutation38 permutation7
    mixedMoment B raw11443step1 raw11443step1Labels = mixedMoment B raw11443step2 raw11443step2Labels := by
      have ha : raw11443step2 = -raw11443step1 := by apply Matrix.ext; change ∀ i j, raw11443step2 i j = -(raw11443step1 i j); unfold raw11443step2 raw11443step1; decide +kernel
      have hl : raw11443step2Labels = raw11443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11443step2 raw11443step2Labels = mixedMoment B raw11443step3 raw11443step3Labels := by
      have ha : raw11443step3 = raw11443step2 := by apply Matrix.ext; unfold raw11443step3 raw11443step2; decide +kernel
      have hl : raw11443step2Labels = labelEmbedding1 ∘ raw11443step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11443step2 raw11443step2Labels raw11443step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw11444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11444step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11444step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11444 raw11444Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw11444 raw11444Labels = mixedMoment B raw11444step0 raw11444step0Labels := by
      have hz : ∀ j, raw11444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11444step0 = (fun i j => raw11444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11444step0 raw11444; decide +kernel
      have hl : raw11444step0Labels = raw11444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11444 raw11444Labels permutation346 hz
    mixedMoment B raw11444step0 raw11444step0Labels = mixedMoment B raw11444step1 raw11444step1Labels := by
      have ha : raw11444step1 = (fun i j => raw11444step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11444step1 raw11444step0; decide +kernel
      have hl : raw11444step1Labels = raw11444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11444step0 raw11444step0Labels permutation38 permutation7
    mixedMoment B raw11444step1 raw11444step1Labels = mixedMoment B raw11444step2 raw11444step2Labels := by
      have ha : raw11444step2 = -raw11444step1 := by apply Matrix.ext; change ∀ i j, raw11444step2 i j = -(raw11444step1 i j); unfold raw11444step2 raw11444step1; decide +kernel
      have hl : raw11444step2Labels = raw11444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11444step2 raw11444step2Labels = mixedMoment B raw11444step3 raw11444step3Labels := by
      have ha : raw11444step3 = raw11444step2 := by apply Matrix.ext; unfold raw11444step3 raw11444step2; decide +kernel
      have hl : raw11444step2Labels = labelEmbedding1 ∘ raw11444step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11444step2 raw11444step2Labels raw11444step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw11445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11445step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11445step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11445 raw11445Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw11445 raw11445Labels = mixedMoment B raw11445step0 raw11445step0Labels := by
      have ha : raw11445step0 = (fun i j => raw11445 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11445step0 raw11445; decide +kernel
      have hl : raw11445step0Labels = raw11445Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11445 raw11445Labels permutation182 permutation7
    mixedMoment B raw11445step0 raw11445step0Labels = mixedMoment B raw11445step1 raw11445step1Labels := by
      have ha : raw11445step1 = -raw11445step0 := by apply Matrix.ext; change ∀ i j, raw11445step1 i j = -(raw11445step0 i j); unfold raw11445step1 raw11445step0; decide +kernel
      have hl : raw11445step1Labels = raw11445step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11445step1 raw11445step1Labels = mixedMoment B raw11445step2 raw11445step2Labels := by
      have ha : raw11445step2 = raw11445step1 := by apply Matrix.ext; unfold raw11445step2 raw11445step1; decide +kernel
      have hl : raw11445step1Labels = labelEmbedding1 ∘ raw11445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11445step1 raw11445step1Labels raw11445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw11446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw11446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11446 raw11446Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw11446 raw11446Labels = mixedMoment B raw11446step0 raw11446step0Labels := by
      have hz : ∀ j, raw11446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11446step0 = (fun i j => raw11446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11446step0 raw11446; decide +kernel
      have hl : raw11446step0Labels = raw11446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11446 raw11446Labels permutation346 hz
    mixedMoment B raw11446step0 raw11446step0Labels = mixedMoment B raw11446step1 raw11446step1Labels := by
      have ha : raw11446step1 = (fun i j => raw11446step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11446step1 raw11446step0; decide +kernel
      have hl : raw11446step1Labels = raw11446step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11446step0 raw11446step0Labels permutation38 permutation7
    mixedMoment B raw11446step1 raw11446step1Labels = mixedMoment B raw11446step2 raw11446step2Labels := by
      have ha : raw11446step2 = -raw11446step1 := by apply Matrix.ext; change ∀ i j, raw11446step2 i j = -(raw11446step1 i j); unfold raw11446step2 raw11446step1; decide +kernel
      have hl : raw11446step2Labels = raw11446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11446step2 raw11446step2Labels = mixedMoment B raw11446step3 raw11446step3Labels := by
      have ha : raw11446step3 = raw11446step2 := by apply Matrix.ext; unfold raw11446step3 raw11446step2; decide +kernel
      have hl : raw11446step2Labels = labelEmbedding1 ∘ raw11446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11446step2 raw11446step2Labels raw11446step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw11447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11447step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11447step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11447step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11447 raw11447Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11447 raw11447Labels = mixedMoment B raw11447step0 raw11447step0Labels := by
      have hz : ∀ j, raw11447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11447step0 = (fun i j => raw11447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11447step0 raw11447; decide +kernel
      have hl : raw11447step0Labels = raw11447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11447 raw11447Labels permutation346 hz
    mixedMoment B raw11447step0 raw11447step0Labels = mixedMoment B raw11447step1 raw11447step1Labels := by
      have ha : raw11447step1 = (fun i j => raw11447step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11447step1 raw11447step0; decide +kernel
      have hl : raw11447step1Labels = raw11447step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11447step0 raw11447step0Labels permutation38 permutation7
    mixedMoment B raw11447step1 raw11447step1Labels = mixedMoment B raw11447step2 raw11447step2Labels := by
      have ha : raw11447step2 = -raw11447step1 := by apply Matrix.ext; change ∀ i j, raw11447step2 i j = -(raw11447step1 i j); unfold raw11447step2 raw11447step1; decide +kernel
      have hl : raw11447step2Labels = raw11447step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11447step2 raw11447step2Labels = mixedMoment B raw11447step3 raw11447step3Labels := by
      have ha : raw11447step3 = raw11447step2 := by apply Matrix.ext; unfold raw11447step3 raw11447step2; decide +kernel
      have hl : raw11447step2Labels = labelEmbedding1 ∘ raw11447step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11447step2 raw11447step2Labels raw11447step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw11448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11448step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11448step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11448step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw11448step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11448step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11448step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11448step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11448step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11448 raw11448Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw11448 raw11448Labels = mixedMoment B raw11448step0 raw11448step0Labels := by
      have hz : ∀ j, raw11448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11448step0 = (fun i j => raw11448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11448step0 raw11448; decide +kernel
      have hl : raw11448step0Labels = raw11448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11448 raw11448Labels permutation434 hz
    mixedMoment B raw11448step0 raw11448step0Labels = mixedMoment B raw11448step1 raw11448step1Labels := by
      have hz : ∀ j, raw11448step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11448step1 = (fun i j => raw11448step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11448step1 raw11448step0; decide +kernel
      have hl : raw11448step1Labels = raw11448step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11448step0 raw11448step0Labels permutation80 hz
    mixedMoment B raw11448step1 raw11448step1Labels = mixedMoment B raw11448step2 raw11448step2Labels := by
      have ha : raw11448step2 = (fun i j => raw11448step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11448step2 raw11448step1; decide +kernel
      have hl : raw11448step2Labels = raw11448step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11448step1 raw11448step1Labels permutation8 permutation7
    mixedMoment B raw11448step2 raw11448step2Labels = mixedMoment B raw11448step3 raw11448step3Labels := by
      have ha : raw11448step3 = -raw11448step2 := by apply Matrix.ext; change ∀ i j, raw11448step3 i j = -(raw11448step2 i j); unfold raw11448step3 raw11448step2; decide +kernel
      have hl : raw11448step3Labels = raw11448step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11448step3 raw11448step3Labels = mixedMoment B raw11448step4 raw11448step4Labels := by
      have ha : raw11448step4 = raw11448step3 := by apply Matrix.ext; unfold raw11448step4 raw11448step3; decide +kernel
      have hl : raw11448step3Labels = labelEmbedding1 ∘ raw11448step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11448step3 raw11448step3Labels raw11448step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

def raw11449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11449step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw11449step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11449step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw11449step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11449step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw11449step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11449 raw11449Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw11449 raw11449Labels = mixedMoment B raw11449step0 raw11449step0Labels := by
      have hz : ∀ j, raw11449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11449step0 = (fun i j => raw11449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11449step0 raw11449; decide +kernel
      have hl : raw11449step0Labels = raw11449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11449 raw11449Labels permutation434 hz
    mixedMoment B raw11449step0 raw11449step0Labels = mixedMoment B raw11449step1 raw11449step1Labels := by
      have hz : ∀ j, raw11449step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11449step1 = (fun i j => raw11449step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11449step1 raw11449step0; decide +kernel
      have hl : raw11449step1Labels = raw11449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11449step0 raw11449step0Labels permutation80 hz
    mixedMoment B raw11449step1 raw11449step1Labels = mixedMoment B raw11449step2 raw11449step2Labels := by
      have ha : raw11449step2 = (fun i j => raw11449step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11449step2 raw11449step1; decide +kernel
      have hl : raw11449step2Labels = raw11449step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11449step1 raw11449step1Labels permutation8 permutation7
    mixedMoment B raw11449step2 raw11449step2Labels = mixedMoment B raw11449step3 raw11449step3Labels := by
      have ha : raw11449step3 = -raw11449step2 := by apply Matrix.ext; change ∀ i j, raw11449step3 i j = -(raw11449step2 i j); unfold raw11449step3 raw11449step2; decide +kernel
      have hl : raw11449step3Labels = raw11449step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11449step3 raw11449step3Labels = mixedMoment B raw11449step4 raw11449step4Labels := by
      have ha : raw11449step4 = raw11449step3 := by apply Matrix.ext; unfold raw11449step4 raw11449step3; decide +kernel
      have hl : raw11449step3Labels = labelEmbedding1 ∘ raw11449step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11449step3 raw11449step3Labels raw11449step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw11450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw11450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11450 raw11450Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw11450 raw11450Labels = mixedMoment B raw11450step0 raw11450step0Labels := by
      have hz : ∀ j, raw11450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11450step0 = (fun i j => raw11450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11450step0 raw11450; decide +kernel
      have hl : raw11450step0Labels = raw11450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11450 raw11450Labels permutation434 hz
    mixedMoment B raw11450step0 raw11450step0Labels = mixedMoment B raw11450step1 raw11450step1Labels := by
      have ha : raw11450step1 = (fun i j => raw11450step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11450step1 raw11450step0; decide +kernel
      have hl : raw11450step1Labels = raw11450step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11450step0 raw11450step0Labels permutation38 permutation7
    mixedMoment B raw11450step1 raw11450step1Labels = mixedMoment B raw11450step2 raw11450step2Labels := by
      have ha : raw11450step2 = -raw11450step1 := by apply Matrix.ext; change ∀ i j, raw11450step2 i j = -(raw11450step1 i j); unfold raw11450step2 raw11450step1; decide +kernel
      have hl : raw11450step2Labels = raw11450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11450step2 raw11450step2Labels = mixedMoment B raw11450step3 raw11450step3Labels := by
      have ha : raw11450step3 = raw11450step2 := by apply Matrix.ext; unfold raw11450step3 raw11450step2; decide +kernel
      have hl : raw11450step2Labels = labelEmbedding1 ∘ raw11450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11450step2 raw11450step2Labels raw11450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw11451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw11451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11451step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11451step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw11451step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11451 raw11451Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw11451 raw11451Labels = mixedMoment B raw11451step0 raw11451step0Labels := by
      have hz : ∀ j, raw11451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11451step0 = (fun i j => raw11451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11451step0 raw11451; decide +kernel
      have hl : raw11451step0Labels = raw11451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11451 raw11451Labels permutation346 hz
    mixedMoment B raw11451step0 raw11451step0Labels = mixedMoment B raw11451step1 raw11451step1Labels := by
      have ha : raw11451step1 = (fun i j => raw11451step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11451step1 raw11451step0; decide +kernel
      have hl : raw11451step1Labels = raw11451step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11451step0 raw11451step0Labels permutation38 permutation7
    mixedMoment B raw11451step1 raw11451step1Labels = mixedMoment B raw11451step2 raw11451step2Labels := by
      have ha : raw11451step2 = -raw11451step1 := by apply Matrix.ext; change ∀ i j, raw11451step2 i j = -(raw11451step1 i j); unfold raw11451step2 raw11451step1; decide +kernel
      have hl : raw11451step2Labels = raw11451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11451step2 raw11451step2Labels = mixedMoment B raw11451step3 raw11451step3Labels := by
      have ha : raw11451step3 = raw11451step2 := by apply Matrix.ext; unfold raw11451step3 raw11451step2; decide +kernel
      have hl : raw11451step2Labels = labelEmbedding1 ∘ raw11451step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11451step2 raw11451step2Labels raw11451step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw11452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw11452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw11452step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11452step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11452step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11452step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11452step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11452 raw11452Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw11452 raw11452Labels = mixedMoment B raw11452step0 raw11452step0Labels := by
      have hz : ∀ j, raw11452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11452step0 = (fun i j => raw11452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11452step0 raw11452; decide +kernel
      have hl : raw11452step0Labels = raw11452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11452 raw11452Labels permutation434 hz
    mixedMoment B raw11452step0 raw11452step0Labels = mixedMoment B raw11452step1 raw11452step1Labels := by
      have hz : ∀ j, raw11452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11452step1 = (fun i j => raw11452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11452step1 raw11452step0; decide +kernel
      have hl : raw11452step1Labels = raw11452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11452step0 raw11452step0Labels permutation80 hz
    mixedMoment B raw11452step1 raw11452step1Labels = mixedMoment B raw11452step2 raw11452step2Labels := by
      have ha : raw11452step2 = (fun i j => raw11452step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11452step2 raw11452step1; decide +kernel
      have hl : raw11452step2Labels = raw11452step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11452step1 raw11452step1Labels permutation9 permutation7
    mixedMoment B raw11452step2 raw11452step2Labels = mixedMoment B raw11452step3 raw11452step3Labels := by
      have ha : raw11452step3 = -raw11452step2 := by apply Matrix.ext; change ∀ i j, raw11452step3 i j = -(raw11452step2 i j); unfold raw11452step3 raw11452step2; decide +kernel
      have hl : raw11452step3Labels = raw11452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11452step3 raw11452step3Labels = mixedMoment B raw11452step4 raw11452step4Labels := by
      have ha : raw11452step4 = raw11452step3 := by apply Matrix.ext; unfold raw11452step4 raw11452step3; decide +kernel
      have hl : raw11452step3Labels = labelEmbedding1 ∘ raw11452step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11452step3 raw11452step3Labels raw11452step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw11453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11453step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw11453step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11453step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11453step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11453step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11453step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11453 raw11453Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw11453 raw11453Labels = mixedMoment B raw11453step0 raw11453step0Labels := by
      have hz : ∀ j, raw11453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11453step0 = (fun i j => raw11453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11453step0 raw11453; decide +kernel
      have hl : raw11453step0Labels = raw11453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11453 raw11453Labels permutation434 hz
    mixedMoment B raw11453step0 raw11453step0Labels = mixedMoment B raw11453step1 raw11453step1Labels := by
      have hz : ∀ j, raw11453step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11453step1 = (fun i j => raw11453step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11453step1 raw11453step0; decide +kernel
      have hl : raw11453step1Labels = raw11453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11453step0 raw11453step0Labels permutation80 hz
    mixedMoment B raw11453step1 raw11453step1Labels = mixedMoment B raw11453step2 raw11453step2Labels := by
      have ha : raw11453step2 = (fun i j => raw11453step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11453step2 raw11453step1; decide +kernel
      have hl : raw11453step2Labels = raw11453step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11453step1 raw11453step1Labels permutation8 permutation7
    mixedMoment B raw11453step2 raw11453step2Labels = mixedMoment B raw11453step3 raw11453step3Labels := by
      have ha : raw11453step3 = -raw11453step2 := by apply Matrix.ext; change ∀ i j, raw11453step3 i j = -(raw11453step2 i j); unfold raw11453step3 raw11453step2; decide +kernel
      have hl : raw11453step3Labels = raw11453step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11453step3 raw11453step3Labels = mixedMoment B raw11453step4 raw11453step4Labels := by
      have ha : raw11453step4 = raw11453step3 := by apply Matrix.ext; unfold raw11453step4 raw11453step3; decide +kernel
      have hl : raw11453step3Labels = labelEmbedding1 ∘ raw11453step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11453step3 raw11453step3Labels raw11453step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw11454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11454step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw11454step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw11454step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11454step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw11454step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11454 raw11454Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw11454 raw11454Labels = mixedMoment B raw11454step0 raw11454step0Labels := by
      have hz : ∀ j, raw11454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11454step0 = (fun i j => raw11454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11454step0 raw11454; decide +kernel
      have hl : raw11454step0Labels = raw11454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11454 raw11454Labels permutation434 hz
    mixedMoment B raw11454step0 raw11454step0Labels = mixedMoment B raw11454step1 raw11454step1Labels := by
      have hz : ∀ j, raw11454step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11454step1 = (fun i j => raw11454step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11454step1 raw11454step0; decide +kernel
      have hl : raw11454step1Labels = raw11454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11454step0 raw11454step0Labels permutation80 hz
    mixedMoment B raw11454step1 raw11454step1Labels = mixedMoment B raw11454step2 raw11454step2Labels := by
      have ha : raw11454step2 = (fun i j => raw11454step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11454step2 raw11454step1; decide +kernel
      have hl : raw11454step2Labels = raw11454step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11454step1 raw11454step1Labels permutation8 permutation7
    mixedMoment B raw11454step2 raw11454step2Labels = mixedMoment B raw11454step3 raw11454step3Labels := by
      have ha : raw11454step3 = -raw11454step2 := by apply Matrix.ext; change ∀ i j, raw11454step3 i j = -(raw11454step2 i j); unfold raw11454step3 raw11454step2; decide +kernel
      have hl : raw11454step3Labels = raw11454step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11454step3 raw11454step3Labels = mixedMoment B raw11454step4 raw11454step4Labels := by
      have ha : raw11454step4 = raw11454step3 := by apply Matrix.ext; unfold raw11454step4 raw11454step3; decide +kernel
      have hl : raw11454step3Labels = labelEmbedding1 ∘ raw11454step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11454step3 raw11454step3Labels raw11454step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw11455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11455step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw11455step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11455step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11455step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11455 raw11455Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw11455 raw11455Labels = mixedMoment B raw11455step0 raw11455step0Labels := by
      have hz : ∀ j, raw11455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11455step0 = (fun i j => raw11455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11455step0 raw11455; decide +kernel
      have hl : raw11455step0Labels = raw11455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11455 raw11455Labels permutation434 hz
    mixedMoment B raw11455step0 raw11455step0Labels = mixedMoment B raw11455step1 raw11455step1Labels := by
      have ha : raw11455step1 = (fun i j => raw11455step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11455step1 raw11455step0; decide +kernel
      have hl : raw11455step1Labels = raw11455step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11455step0 raw11455step0Labels permutation38 permutation7
    mixedMoment B raw11455step1 raw11455step1Labels = mixedMoment B raw11455step2 raw11455step2Labels := by
      have ha : raw11455step2 = -raw11455step1 := by apply Matrix.ext; change ∀ i j, raw11455step2 i j = -(raw11455step1 i j); unfold raw11455step2 raw11455step1; decide +kernel
      have hl : raw11455step2Labels = raw11455step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11455step2 raw11455step2Labels = mixedMoment B raw11455step3 raw11455step3Labels := by
      have ha : raw11455step3 = raw11455step2 := by apply Matrix.ext; unfold raw11455step3 raw11455step2; decide +kernel
      have hl : raw11455step2Labels = labelEmbedding1 ∘ raw11455step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11455step2 raw11455step2Labels raw11455step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw11456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11456step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw11456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11456step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11456step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11456 raw11456Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw11456 raw11456Labels = mixedMoment B raw11456step0 raw11456step0Labels := by
      have hz : ∀ j, raw11456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11456step0 = (fun i j => raw11456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11456step0 raw11456; decide +kernel
      have hl : raw11456step0Labels = raw11456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11456 raw11456Labels permutation346 hz
    mixedMoment B raw11456step0 raw11456step0Labels = mixedMoment B raw11456step1 raw11456step1Labels := by
      have ha : raw11456step1 = (fun i j => raw11456step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11456step1 raw11456step0; decide +kernel
      have hl : raw11456step1Labels = raw11456step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11456step0 raw11456step0Labels permutation38 permutation7
    mixedMoment B raw11456step1 raw11456step1Labels = mixedMoment B raw11456step2 raw11456step2Labels := by
      have ha : raw11456step2 = -raw11456step1 := by apply Matrix.ext; change ∀ i j, raw11456step2 i j = -(raw11456step1 i j); unfold raw11456step2 raw11456step1; decide +kernel
      have hl : raw11456step2Labels = raw11456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11456step2 raw11456step2Labels = mixedMoment B raw11456step3 raw11456step3Labels := by
      have ha : raw11456step3 = raw11456step2 := by apply Matrix.ext; unfold raw11456step3 raw11456step2; decide +kernel
      have hl : raw11456step2Labels = labelEmbedding1 ∘ raw11456step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11456step2 raw11456step2Labels raw11456step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw11457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw11457step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11457step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw11457step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11457step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11457step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11457step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11457step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11457 raw11457Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw11457 raw11457Labels = mixedMoment B raw11457step0 raw11457step0Labels := by
      have hz : ∀ j, raw11457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11457step0 = (fun i j => raw11457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11457step0 raw11457; decide +kernel
      have hl : raw11457step0Labels = raw11457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11457 raw11457Labels permutation434 hz
    mixedMoment B raw11457step0 raw11457step0Labels = mixedMoment B raw11457step1 raw11457step1Labels := by
      have hz : ∀ j, raw11457step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11457step1 = (fun i j => raw11457step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11457step1 raw11457step0; decide +kernel
      have hl : raw11457step1Labels = raw11457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11457step0 raw11457step0Labels permutation80 hz
    mixedMoment B raw11457step1 raw11457step1Labels = mixedMoment B raw11457step2 raw11457step2Labels := by
      have ha : raw11457step2 = (fun i j => raw11457step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11457step2 raw11457step1; decide +kernel
      have hl : raw11457step2Labels = raw11457step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11457step1 raw11457step1Labels permutation8 permutation7
    mixedMoment B raw11457step2 raw11457step2Labels = mixedMoment B raw11457step3 raw11457step3Labels := by
      have ha : raw11457step3 = -raw11457step2 := by apply Matrix.ext; change ∀ i j, raw11457step3 i j = -(raw11457step2 i j); unfold raw11457step3 raw11457step2; decide +kernel
      have hl : raw11457step3Labels = raw11457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11457step3 raw11457step3Labels = mixedMoment B raw11457step4 raw11457step4Labels := by
      have ha : raw11457step4 = raw11457step3 := by apply Matrix.ext; unfold raw11457step4 raw11457step3; decide +kernel
      have hl : raw11457step3Labels = labelEmbedding1 ∘ raw11457step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11457step3 raw11457step3Labels raw11457step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw11458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11458step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11458 raw11458Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw11458 raw11458Labels = mixedMoment B raw11458step0 raw11458step0Labels := by
      have hz : ∀ j, raw11458 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11458step0 = (fun i j => raw11458 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11458step0 raw11458; decide +kernel
      have hl : raw11458step0Labels = raw11458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11458 raw11458Labels permutation434 hz
    mixedMoment B raw11458step0 raw11458step0Labels = mixedMoment B raw11458step1 raw11458step1Labels := by
      have hz : ∀ j, raw11458step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11458step1 = (fun i j => raw11458step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11458step1 raw11458step0; decide +kernel
      have hl : raw11458step1Labels = raw11458step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11458step0 raw11458step0Labels permutation80 hz
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw11459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11459 raw11459Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw11459 raw11459Labels = mixedMoment B raw11459step0 raw11459step0Labels := by
      have hz : ∀ j, raw11459 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11459step0 = (fun i j => raw11459 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11459step0 raw11459; decide +kernel
      have hl : raw11459step0Labels = raw11459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11459 raw11459Labels permutation434 hz
    mixedMoment B raw11459step0 raw11459step0Labels = mixedMoment B raw11459step1 raw11459step1Labels := by
      have hz : ∀ j, raw11459step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11459step1 = (fun i j => raw11459step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11459step1 raw11459step0; decide +kernel
      have hl : raw11459step1Labels = raw11459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11459step0 raw11459step0Labels permutation80 hz
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw11460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11460 raw11460Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw11460 raw11460Labels = mixedMoment B raw11460step0 raw11460step0Labels := by
      have hz : ∀ j, raw11460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11460step0 = (fun i j => raw11460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11460step0 raw11460; decide +kernel
      have hl : raw11460step0Labels = raw11460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11460 raw11460Labels permutation434 hz
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw11461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11461 raw11461Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw11461 raw11461Labels = mixedMoment B raw11461step0 raw11461step0Labels := by
      have hz : ∀ j, raw11461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11461step0 = (fun i j => raw11461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11461step0 raw11461; decide +kernel
      have hl : raw11461step0Labels = raw11461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11461 raw11461Labels permutation346 hz
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw11462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw11462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11462step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11462 raw11462Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw11462 raw11462Labels = mixedMoment B raw11462step0 raw11462step0Labels := by
      have hz : ∀ j, raw11462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11462step0 = (fun i j => raw11462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11462step0 raw11462; decide +kernel
      have hl : raw11462step0Labels = raw11462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11462 raw11462Labels permutation434 hz
    mixedMoment B raw11462step0 raw11462step0Labels = mixedMoment B raw11462step1 raw11462step1Labels := by
      have hz : ∀ j, raw11462step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11462step1 = (fun i j => raw11462step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11462step1 raw11462step0; decide +kernel
      have hl : raw11462step1Labels = raw11462step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11462step0 raw11462step0Labels permutation80 hz
    _ = mixedMoment B node2116 node2116Labels := by rfl

def raw11463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw11463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11463 raw11463Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw11463 raw11463Labels = mixedMoment B raw11463step0 raw11463step0Labels := by
      have hz : ∀ j, raw11463 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11463step0 = (fun i j => raw11463 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11463step0 raw11463; decide +kernel
      have hl : raw11463step0Labels = raw11463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11463 raw11463Labels permutation434 hz
    mixedMoment B raw11463step0 raw11463step0Labels = mixedMoment B raw11463step1 raw11463step1Labels := by
      have hz : ∀ j, raw11463step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11463step1 = (fun i j => raw11463step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11463step1 raw11463step0; decide +kernel
      have hl : raw11463step1Labels = raw11463step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11463step0 raw11463step0Labels permutation80 hz
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw11464 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]
def raw11464Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11464step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw11464step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11464step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11464step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11464 raw11464Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11464 raw11464Labels = mixedMoment B raw11464step0 raw11464step0Labels := by
      have hz : ∀ j, raw11464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11464step0 = (fun i j => raw11464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11464step0 raw11464; decide +kernel
      have hl : raw11464step0Labels = raw11464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11464 raw11464Labels permutation434 hz
    mixedMoment B raw11464step0 raw11464step0Labels = mixedMoment B raw11464step1 raw11464step1Labels := by
      have hz : ∀ j, raw11464step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11464step1 = (fun i j => raw11464step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11464step1 raw11464step0; decide +kernel
      have hl : raw11464step1Labels = raw11464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11464step0 raw11464step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw11465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11465step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11465step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11465step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11465step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11465 raw11465Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw11465 raw11465Labels = mixedMoment B raw11465step0 raw11465step0Labels := by
      have hz : ∀ j, raw11465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11465step0 = (fun i j => raw11465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11465step0 raw11465; decide +kernel
      have hl : raw11465step0Labels = raw11465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11465 raw11465Labels permutation346 hz
    mixedMoment B raw11465step0 raw11465step0Labels = mixedMoment B raw11465step1 raw11465step1Labels := by
      have ha : raw11465step1 = (fun i j => raw11465step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11465step1 raw11465step0; decide +kernel
      have hl : raw11465step1Labels = raw11465step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11465step0 raw11465step0Labels permutation32 permutation4
    mixedMoment B raw11465step1 raw11465step1Labels = mixedMoment B raw11465step2 raw11465step2Labels := by
      have ha : raw11465step2 = -raw11465step1 := by apply Matrix.ext; change ∀ i j, raw11465step2 i j = -(raw11465step1 i j); unfold raw11465step2 raw11465step1; decide +kernel
      have hl : raw11465step2Labels = raw11465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11465step2 raw11465step2Labels = mixedMoment B raw11465step3 raw11465step3Labels := by
      have ha : raw11465step3 = raw11465step2 := by apply Matrix.ext; unfold raw11465step3 raw11465step2; decide +kernel
      have hl : raw11465step2Labels = labelEmbedding7 ∘ raw11465step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11465step2 raw11465step2Labels raw11465step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw11466 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11466step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11466step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11466step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11466 raw11466Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw11466 raw11466Labels = mixedMoment B raw11466step0 raw11466step0Labels := by
      have ha : raw11466step0 = (fun i j => raw11466 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11466step0 raw11466; decide +kernel
      have hl : raw11466step0Labels = raw11466Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11466 raw11466Labels permutation176 permutation4
    mixedMoment B raw11466step0 raw11466step0Labels = mixedMoment B raw11466step1 raw11466step1Labels := by
      have ha : raw11466step1 = -raw11466step0 := by apply Matrix.ext; change ∀ i j, raw11466step1 i j = -(raw11466step0 i j); unfold raw11466step1 raw11466step0; decide +kernel
      have hl : raw11466step1Labels = raw11466step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11466step1 raw11466step1Labels = mixedMoment B raw11466step2 raw11466step2Labels := by
      have ha : raw11466step2 = raw11466step1 := by apply Matrix.ext; unfold raw11466step2 raw11466step1; decide +kernel
      have hl : raw11466step1Labels = labelEmbedding7 ∘ raw11466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11466step1 raw11466step1Labels raw11466step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw11467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw11467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw11467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw11467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw11467step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11467step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11467step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11467step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11467step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11467 raw11467Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw11467 raw11467Labels = mixedMoment B raw11467step0 raw11467step0Labels := by
      have hz : ∀ j, raw11467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11467step0 = (fun i j => raw11467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11467step0 raw11467; decide +kernel
      have hl : raw11467step0Labels = raw11467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11467 raw11467Labels permutation434 hz
    mixedMoment B raw11467step0 raw11467step0Labels = mixedMoment B raw11467step1 raw11467step1Labels := by
      have hz : ∀ j, raw11467step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11467step1 = (fun i j => raw11467step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11467step1 raw11467step0; decide +kernel
      have hl : raw11467step1Labels = raw11467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11467step0 raw11467step0Labels permutation80 hz
    mixedMoment B raw11467step1 raw11467step1Labels = mixedMoment B raw11467step2 raw11467step2Labels := by
      have ha : raw11467step2 = (fun i j => raw11467step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11467step2 raw11467step1; decide +kernel
      have hl : raw11467step2Labels = raw11467step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11467step1 raw11467step1Labels permutation9 permutation4
    mixedMoment B raw11467step2 raw11467step2Labels = mixedMoment B raw11467step3 raw11467step3Labels := by
      have ha : raw11467step3 = -raw11467step2 := by apply Matrix.ext; change ∀ i j, raw11467step3 i j = -(raw11467step2 i j); unfold raw11467step3 raw11467step2; decide +kernel
      have hl : raw11467step3Labels = raw11467step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11467step3 raw11467step3Labels = mixedMoment B raw11467step4 raw11467step4Labels := by
      have ha : raw11467step4 = raw11467step3 := by apply Matrix.ext; unfold raw11467step4 raw11467step3; decide +kernel
      have hl : raw11467step3Labels = labelEmbedding7 ∘ raw11467step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11467step3 raw11467step3Labels raw11467step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw11468 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw11468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw11468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw11468step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11468step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11468step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11468 raw11468Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11468 raw11468Labels = mixedMoment B raw11468step0 raw11468step0Labels := by
      have hz : ∀ j, raw11468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11468step0 = (fun i j => raw11468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11468step0 raw11468; decide +kernel
      have hl : raw11468step0Labels = raw11468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11468 raw11468Labels permutation434 hz
    mixedMoment B raw11468step0 raw11468step0Labels = mixedMoment B raw11468step1 raw11468step1Labels := by
      have ha : raw11468step1 = (fun i j => raw11468step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11468step1 raw11468step0; decide +kernel
      have hl : raw11468step1Labels = raw11468step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11468step0 raw11468step0Labels permutation39 permutation4
    mixedMoment B raw11468step1 raw11468step1Labels = mixedMoment B raw11468step2 raw11468step2Labels := by
      have ha : raw11468step2 = -raw11468step1 := by apply Matrix.ext; change ∀ i j, raw11468step2 i j = -(raw11468step1 i j); unfold raw11468step2 raw11468step1; decide +kernel
      have hl : raw11468step2Labels = raw11468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11468step2 raw11468step2Labels = mixedMoment B raw11468step3 raw11468step3Labels := by
      have ha : raw11468step3 = raw11468step2 := by apply Matrix.ext; unfold raw11468step3 raw11468step2; decide +kernel
      have hl : raw11468step2Labels = labelEmbedding7 ∘ raw11468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11468step2 raw11468step2Labels raw11468step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw11469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw11469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw11469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11469step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11469step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11469step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11469step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11469step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11469 raw11469Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw11469 raw11469Labels = mixedMoment B raw11469step0 raw11469step0Labels := by
      have hz : ∀ j, raw11469 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11469step0 = (fun i j => raw11469 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11469step0 raw11469; decide +kernel
      have hl : raw11469step0Labels = raw11469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11469 raw11469Labels permutation434 hz
    mixedMoment B raw11469step0 raw11469step0Labels = mixedMoment B raw11469step1 raw11469step1Labels := by
      have hz : ∀ j, raw11469step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11469step1 = (fun i j => raw11469step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11469step1 raw11469step0; decide +kernel
      have hl : raw11469step1Labels = raw11469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11469step0 raw11469step0Labels permutation80 hz
    mixedMoment B raw11469step1 raw11469step1Labels = mixedMoment B raw11469step2 raw11469step2Labels := by
      have ha : raw11469step2 = (fun i j => raw11469step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11469step2 raw11469step1; decide +kernel
      have hl : raw11469step2Labels = raw11469step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11469step1 raw11469step1Labels permutation8 permutation4
    mixedMoment B raw11469step2 raw11469step2Labels = mixedMoment B raw11469step3 raw11469step3Labels := by
      have ha : raw11469step3 = -raw11469step2 := by apply Matrix.ext; change ∀ i j, raw11469step3 i j = -(raw11469step2 i j); unfold raw11469step3 raw11469step2; decide +kernel
      have hl : raw11469step3Labels = raw11469step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11469step3 raw11469step3Labels = mixedMoment B raw11469step4 raw11469step4Labels := by
      have ha : raw11469step4 = raw11469step3 := by apply Matrix.ext; unfold raw11469step4 raw11469step3; decide +kernel
      have hl : raw11469step3Labels = labelEmbedding7 ∘ raw11469step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11469step3 raw11469step3Labels raw11469step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw11470 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw11470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw11470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11470step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11470step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11470step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11470step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11470 raw11470Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw11470 raw11470Labels = mixedMoment B raw11470step0 raw11470step0Labels := by
      have hz : ∀ j, raw11470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11470step0 = (fun i j => raw11470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11470step0 raw11470; decide +kernel
      have hl : raw11470step0Labels = raw11470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11470 raw11470Labels permutation434 hz
    mixedMoment B raw11470step0 raw11470step0Labels = mixedMoment B raw11470step1 raw11470step1Labels := by
      have ha : raw11470step1 = (fun i j => raw11470step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11470step1 raw11470step0; decide +kernel
      have hl : raw11470step1Labels = raw11470step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11470step0 raw11470step0Labels permutation38 permutation4
    mixedMoment B raw11470step1 raw11470step1Labels = mixedMoment B raw11470step2 raw11470step2Labels := by
      have ha : raw11470step2 = -raw11470step1 := by apply Matrix.ext; change ∀ i j, raw11470step2 i j = -(raw11470step1 i j); unfold raw11470step2 raw11470step1; decide +kernel
      have hl : raw11470step2Labels = raw11470step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11470step2 raw11470step2Labels = mixedMoment B raw11470step3 raw11470step3Labels := by
      have ha : raw11470step3 = raw11470step2 := by apply Matrix.ext; unfold raw11470step3 raw11470step2; decide +kernel
      have hl : raw11470step2Labels = labelEmbedding7 ∘ raw11470step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11470step2 raw11470step2Labels raw11470step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw11471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw11471step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11471step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11471step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11471step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11471 raw11471Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw11471 raw11471Labels = mixedMoment B raw11471step0 raw11471step0Labels := by
      have hz : ∀ j, raw11471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11471step0 = (fun i j => raw11471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11471step0 raw11471; decide +kernel
      have hl : raw11471step0Labels = raw11471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11471 raw11471Labels permutation434 hz
    mixedMoment B raw11471step0 raw11471step0Labels = mixedMoment B raw11471step1 raw11471step1Labels := by
      have hz : ∀ j, raw11471step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11471step1 = (fun i j => raw11471step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11471step1 raw11471step0; decide +kernel
      have hl : raw11471step1Labels = raw11471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11471step0 raw11471step0Labels permutation80 hz
    mixedMoment B raw11471step1 raw11471step1Labels = mixedMoment B raw11471step2 raw11471step2Labels := by
      have ha : raw11471step2 = (fun i j => raw11471step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11471step2 raw11471step1; decide +kernel
      have hl : raw11471step2Labels = raw11471step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11471step1 raw11471step1Labels permutation10 permutation7
    mixedMoment B raw11471step2 raw11471step2Labels = mixedMoment B raw11471step3 raw11471step3Labels := by
      have ha : raw11471step3 = -raw11471step2 := by apply Matrix.ext; change ∀ i j, raw11471step3 i j = -(raw11471step2 i j); unfold raw11471step3 raw11471step2; decide +kernel
      have hl : raw11471step3Labels = raw11471step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11471step3 raw11471step3Labels = mixedMoment B raw11471step4 raw11471step4Labels := by
      have ha : raw11471step4 = raw11471step3 := by apply Matrix.ext; unfold raw11471step4 raw11471step3; decide +kernel
      have hl : raw11471step3Labels = labelEmbedding10 ∘ raw11471step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11471step3 raw11471step3Labels raw11471step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw11472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11472step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11472step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11472step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11472step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11472 raw11472Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw11472 raw11472Labels = mixedMoment B raw11472step0 raw11472step0Labels := by
      have hz : ∀ j, raw11472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11472step0 = (fun i j => raw11472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11472step0 raw11472; decide +kernel
      have hl : raw11472step0Labels = raw11472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11472 raw11472Labels permutation434 hz
    mixedMoment B raw11472step0 raw11472step0Labels = mixedMoment B raw11472step1 raw11472step1Labels := by
      have ha : raw11472step1 = (fun i j => raw11472step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11472step1 raw11472step0; decide +kernel
      have hl : raw11472step1Labels = raw11472step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11472step0 raw11472step0Labels permutation40 permutation7
    mixedMoment B raw11472step1 raw11472step1Labels = mixedMoment B raw11472step2 raw11472step2Labels := by
      have ha : raw11472step2 = -raw11472step1 := by apply Matrix.ext; change ∀ i j, raw11472step2 i j = -(raw11472step1 i j); unfold raw11472step2 raw11472step1; decide +kernel
      have hl : raw11472step2Labels = raw11472step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11472step2 raw11472step2Labels = mixedMoment B raw11472step3 raw11472step3Labels := by
      have ha : raw11472step3 = raw11472step2 := by apply Matrix.ext; unfold raw11472step3 raw11472step2; decide +kernel
      have hl : raw11472step2Labels = labelEmbedding10 ∘ raw11472step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11472step2 raw11472step2Labels raw11472step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw11473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw11473step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11473step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11473step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11473step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11473 raw11473Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw11473 raw11473Labels = mixedMoment B raw11473step0 raw11473step0Labels := by
      have hz : ∀ j, raw11473 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11473step0 = (fun i j => raw11473 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11473step0 raw11473; decide +kernel
      have hl : raw11473step0Labels = raw11473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11473 raw11473Labels permutation346 hz
    mixedMoment B raw11473step0 raw11473step0Labels = mixedMoment B raw11473step1 raw11473step1Labels := by
      have ha : raw11473step1 = (fun i j => raw11473step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11473step1 raw11473step0; decide +kernel
      have hl : raw11473step1Labels = raw11473step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11473step0 raw11473step0Labels permutation40 permutation7
    mixedMoment B raw11473step1 raw11473step1Labels = mixedMoment B raw11473step2 raw11473step2Labels := by
      have ha : raw11473step2 = -raw11473step1 := by apply Matrix.ext; change ∀ i j, raw11473step2 i j = -(raw11473step1 i j); unfold raw11473step2 raw11473step1; decide +kernel
      have hl : raw11473step2Labels = raw11473step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11473step2 raw11473step2Labels = mixedMoment B raw11473step3 raw11473step3Labels := by
      have ha : raw11473step3 = raw11473step2 := by apply Matrix.ext; unfold raw11473step3 raw11473step2; decide +kernel
      have hl : raw11473step2Labels = labelEmbedding10 ∘ raw11473step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11473step2 raw11473step2Labels raw11473step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw11474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw11474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11474step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def raw11474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11474step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw11474step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11474step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11474step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11474step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11474step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11474 raw11474Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw11474 raw11474Labels = mixedMoment B raw11474step0 raw11474step0Labels := by
      have hz : ∀ j, raw11474 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11474step0 = (fun i j => raw11474 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11474step0 raw11474; decide +kernel
      have hl : raw11474step0Labels = raw11474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11474 raw11474Labels permutation520 hz
    mixedMoment B raw11474step0 raw11474step0Labels = mixedMoment B raw11474step1 raw11474step1Labels := by
      have hz : ∀ j, raw11474step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11474step1 = (fun i j => raw11474step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11474step1 raw11474step0; decide +kernel
      have hl : raw11474step1Labels = raw11474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11474step0 raw11474step0Labels permutation104 hz
    mixedMoment B raw11474step1 raw11474step1Labels = mixedMoment B raw11474step2 raw11474step2Labels := by
      have hz : ∀ j, raw11474step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw11474step2 = (fun i j => raw11474step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw11474step2 raw11474step1; decide +kernel
      have hl : raw11474step2Labels = raw11474step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11474step1 raw11474step1Labels permutation20 hz
    mixedMoment B raw11474step2 raw11474step2Labels = mixedMoment B raw11474step3 raw11474step3Labels := by
      have ha : raw11474step3 = (fun i j => raw11474step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11474step3 raw11474step2; decide +kernel
      have hl : raw11474step3Labels = raw11474step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11474step2 raw11474step2Labels permutation2 permutation7
    mixedMoment B raw11474step3 raw11474step3Labels = mixedMoment B raw11474step4 raw11474step4Labels := by
      have ha : raw11474step4 = -raw11474step3 := by apply Matrix.ext; change ∀ i j, raw11474step4 i j = -(raw11474step3 i j); unfold raw11474step4 raw11474step3; decide +kernel
      have hl : raw11474step4Labels = raw11474step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11474step4 raw11474step4Labels = mixedMoment B raw11474step5 raw11474step5Labels := by
      have ha : raw11474step5 = raw11474step4 := by apply Matrix.ext; unfold raw11474step5 raw11474step4; decide +kernel
      have hl : raw11474step4Labels = labelEmbedding10 ∘ raw11474step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11474step4 raw11474step4Labels raw11474step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw11475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11475step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11475step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11475step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11475step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11475step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11475 raw11475Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw11475 raw11475Labels = mixedMoment B raw11475step0 raw11475step0Labels := by
      have hz : ∀ j, raw11475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11475step0 = (fun i j => raw11475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11475step0 raw11475; decide +kernel
      have hl : raw11475step0Labels = raw11475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11475 raw11475Labels permutation434 hz
    mixedMoment B raw11475step0 raw11475step0Labels = mixedMoment B raw11475step1 raw11475step1Labels := by
      have hz : ∀ j, raw11475step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11475step1 = (fun i j => raw11475step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11475step1 raw11475step0; decide +kernel
      have hl : raw11475step1Labels = raw11475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11475step0 raw11475step0Labels permutation80 hz
    mixedMoment B raw11475step1 raw11475step1Labels = mixedMoment B raw11475step2 raw11475step2Labels := by
      have ha : raw11475step2 = (fun i j => raw11475step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11475step2 raw11475step1; decide +kernel
      have hl : raw11475step2Labels = raw11475step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11475step1 raw11475step1Labels permutation10 permutation7
    mixedMoment B raw11475step2 raw11475step2Labels = mixedMoment B raw11475step3 raw11475step3Labels := by
      have ha : raw11475step3 = -raw11475step2 := by apply Matrix.ext; change ∀ i j, raw11475step3 i j = -(raw11475step2 i j); unfold raw11475step3 raw11475step2; decide +kernel
      have hl : raw11475step3Labels = raw11475step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11475step3 raw11475step3Labels = mixedMoment B raw11475step4 raw11475step4Labels := by
      have ha : raw11475step4 = raw11475step3 := by apply Matrix.ext; unfold raw11475step4 raw11475step3; decide +kernel
      have hl : raw11475step3Labels = labelEmbedding10 ∘ raw11475step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11475step3 raw11475step3Labels raw11475step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw11476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11476step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11476 raw11476Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw11476 raw11476Labels = mixedMoment B raw11476step0 raw11476step0Labels := by
      have hz : ∀ j, raw11476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11476step0 = (fun i j => raw11476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11476step0 raw11476; decide +kernel
      have hl : raw11476step0Labels = raw11476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11476 raw11476Labels permutation434 hz
    mixedMoment B raw11476step0 raw11476step0Labels = mixedMoment B raw11476step1 raw11476step1Labels := by
      have hz : ∀ j, raw11476step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11476step1 = (fun i j => raw11476step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11476step1 raw11476step0; decide +kernel
      have hl : raw11476step1Labels = raw11476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11476step0 raw11476step0Labels permutation80 hz
    mixedMoment B raw11476step1 raw11476step1Labels = mixedMoment B raw11476step2 raw11476step2Labels := by
      have ha : raw11476step2 = (fun i j => raw11476step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11476step2 raw11476step1; decide +kernel
      have hl : raw11476step2Labels = raw11476step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11476step1 raw11476step1Labels permutation10 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw11477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11477 raw11477Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw11477 raw11477Labels = mixedMoment B raw11477step0 raw11477step0Labels := by
      have hz : ∀ j, raw11477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11477step0 = (fun i j => raw11477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11477step0 raw11477; decide +kernel
      have hl : raw11477step0Labels = raw11477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11477 raw11477Labels permutation434 hz
    mixedMoment B raw11477step0 raw11477step0Labels = mixedMoment B raw11477step1 raw11477step1Labels := by
      have ha : raw11477step1 = (fun i j => raw11477step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11477step1 raw11477step0; decide +kernel
      have hl : raw11477step1Labels = raw11477step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11477step0 raw11477step0Labels permutation40 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw11478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11478 raw11478Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw11478 raw11478Labels = mixedMoment B raw11478step0 raw11478step0Labels := by
      have hz : ∀ j, raw11478 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11478step0 = (fun i j => raw11478 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11478step0 raw11478; decide +kernel
      have hl : raw11478step0Labels = raw11478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11478 raw11478Labels permutation346 hz
    mixedMoment B raw11478step0 raw11478step0Labels = mixedMoment B raw11478step1 raw11478step1Labels := by
      have ha : raw11478step1 = (fun i j => raw11478step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11478step1 raw11478step0; decide +kernel
      have hl : raw11478step1Labels = raw11478step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11478step0 raw11478step0Labels permutation40 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw11479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw11479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11479step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![2, 0, -2]]
def raw11479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11479step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw11479step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw11479step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw11479step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11479 raw11479Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw11479 raw11479Labels = mixedMoment B raw11479step0 raw11479step0Labels := by
      have hz : ∀ j, raw11479 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11479step0 = (fun i j => raw11479 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11479step0 raw11479; decide +kernel
      have hl : raw11479step0Labels = raw11479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11479 raw11479Labels permutation520 hz
    mixedMoment B raw11479step0 raw11479step0Labels = mixedMoment B raw11479step1 raw11479step1Labels := by
      have hz : ∀ j, raw11479step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11479step1 = (fun i j => raw11479step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11479step1 raw11479step0; decide +kernel
      have hl : raw11479step1Labels = raw11479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11479step0 raw11479step0Labels permutation104 hz
    mixedMoment B raw11479step1 raw11479step1Labels = mixedMoment B raw11479step2 raw11479step2Labels := by
      have hz : ∀ j, raw11479step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw11479step2 = (fun i j => raw11479step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw11479step2 raw11479step1; decide +kernel
      have hl : raw11479step2Labels = raw11479step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11479step1 raw11479step1Labels permutation20 hz
    mixedMoment B raw11479step2 raw11479step2Labels = mixedMoment B raw11479step3 raw11479step3Labels := by
      have hz : ∀ i, raw11479step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw11479step3 = (fun i j => raw11479step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw11479step3 raw11479step2; decide +kernel
      have hl : raw11479step3Labels = (fun j => raw11479step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11479step2 raw11479step2Labels permutation4 hz
    mixedMoment B raw11479step3 raw11479step3Labels = mixedMoment B raw11479step4 raw11479step4Labels := by
      have ha : raw11479step4 = raw11479step3 := by apply Matrix.ext; unfold raw11479step4 raw11479step3; decide +kernel
      have hl : raw11479step3Labels = labelEmbedding2 ∘ raw11479step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11479step3 raw11479step3Labels raw11479step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw11480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11480step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11480step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11480step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11480step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11480step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11480 raw11480Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11480 raw11480Labels = mixedMoment B raw11480step0 raw11480step0Labels := by
      have hz : ∀ j, raw11480 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11480step0 = (fun i j => raw11480 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11480step0 raw11480; decide +kernel
      have hl : raw11480step0Labels = raw11480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11480 raw11480Labels permutation434 hz
    mixedMoment B raw11480step0 raw11480step0Labels = mixedMoment B raw11480step1 raw11480step1Labels := by
      have hz : ∀ j, raw11480step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11480step1 = (fun i j => raw11480step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11480step1 raw11480step0; decide +kernel
      have hl : raw11480step1Labels = raw11480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11480step0 raw11480step0Labels permutation80 hz
    mixedMoment B raw11480step1 raw11480step1Labels = mixedMoment B raw11480step2 raw11480step2Labels := by
      have ha : raw11480step2 = (fun i j => raw11480step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11480step2 raw11480step1; decide +kernel
      have hl : raw11480step2Labels = raw11480step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11480step1 raw11480step1Labels permutation10 permutation7
    mixedMoment B raw11480step2 raw11480step2Labels = mixedMoment B raw11480step3 raw11480step3Labels := by
      have ha : raw11480step3 = -raw11480step2 := by apply Matrix.ext; change ∀ i j, raw11480step3 i j = -(raw11480step2 i j); unfold raw11480step3 raw11480step2; decide +kernel
      have hl : raw11480step3Labels = raw11480step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11480step3 raw11480step3Labels = mixedMoment B raw11480step4 raw11480step4Labels := by
      have ha : raw11480step4 = raw11480step3 := by apply Matrix.ext; unfold raw11480step4 raw11480step3; decide +kernel
      have hl : raw11480step3Labels = labelEmbedding10 ∘ raw11480step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11480step3 raw11480step3Labels raw11480step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw11481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11481 raw11481Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw11481 raw11481Labels = mixedMoment B raw11481step0 raw11481step0Labels := by
      have hz : ∀ j, raw11481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11481step0 = (fun i j => raw11481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11481step0 raw11481; decide +kernel
      have hl : raw11481step0Labels = raw11481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11481 raw11481Labels permutation434 hz
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw11482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11482 raw11482Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw11482 raw11482Labels = mixedMoment B raw11482step0 raw11482step0Labels := by
      have hz : ∀ j, raw11482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11482step0 = (fun i j => raw11482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11482step0 raw11482; decide +kernel
      have hl : raw11482step0Labels = raw11482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11482 raw11482Labels permutation434 hz
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw11483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11483 raw11483Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw11483 raw11483Labels = mixedMoment B raw11483step0 raw11483step0Labels := by
      have ha : raw11483step0 = (fun i j => raw11483 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11483step0 raw11483; decide +kernel
      have hl : raw11483step0Labels = raw11483Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11483 raw11483Labels permutation200 permutation2
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw11484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11484 raw11484Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw11484 raw11484Labels = mixedMoment B raw11484step0 raw11484step0Labels := by
      have hz : ∀ j, raw11484 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11484step0 = (fun i j => raw11484 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11484step0 raw11484; decide +kernel
      have hl : raw11484step0Labels = raw11484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11484 raw11484Labels permutation520 hz
    mixedMoment B raw11484step0 raw11484step0Labels = mixedMoment B raw11484step1 raw11484step1Labels := by
      have hz : ∀ j, raw11484step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11484step1 = (fun i j => raw11484step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11484step1 raw11484step0; decide +kernel
      have hl : raw11484step1Labels = raw11484step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11484step0 raw11484step0Labels permutation104 hz
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw11485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11485step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11485step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11485step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11485step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11485 raw11485Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11485 raw11485Labels = mixedMoment B raw11485step0 raw11485step0Labels := by
      have hz : ∀ j, raw11485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11485step0 = (fun i j => raw11485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11485step0 raw11485; decide +kernel
      have hl : raw11485step0Labels = raw11485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11485 raw11485Labels permutation434 hz
    mixedMoment B raw11485step0 raw11485step0Labels = mixedMoment B raw11485step1 raw11485step1Labels := by
      have ha : raw11485step1 = (fun i j => raw11485step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11485step1 raw11485step0; decide +kernel
      have hl : raw11485step1Labels = raw11485step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11485step0 raw11485step0Labels permutation40 permutation7
    mixedMoment B raw11485step1 raw11485step1Labels = mixedMoment B raw11485step2 raw11485step2Labels := by
      have ha : raw11485step2 = -raw11485step1 := by apply Matrix.ext; change ∀ i j, raw11485step2 i j = -(raw11485step1 i j); unfold raw11485step2 raw11485step1; decide +kernel
      have hl : raw11485step2Labels = raw11485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11485step2 raw11485step2Labels = mixedMoment B raw11485step3 raw11485step3Labels := by
      have ha : raw11485step3 = raw11485step2 := by apply Matrix.ext; unfold raw11485step3 raw11485step2; decide +kernel
      have hl : raw11485step2Labels = labelEmbedding10 ∘ raw11485step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11485step2 raw11485step2Labels raw11485step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw11486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11486 raw11486Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw11486 raw11486Labels = mixedMoment B raw11486step0 raw11486step0Labels := by
      have hz : ∀ j, raw11486 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11486step0 = (fun i j => raw11486 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11486step0 raw11486; decide +kernel
      have hl : raw11486step0Labels = raw11486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11486 raw11486Labels permutation346 hz
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw11487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11487 raw11487Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw11487 raw11487Labels = mixedMoment B raw11487step0 raw11487step0Labels := by
      have hz : ∀ j, raw11487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11487step0 = (fun i j => raw11487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11487step0 raw11487; decide +kernel
      have hl : raw11487step0Labels = raw11487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11487 raw11487Labels permutation346 hz
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw11488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11488 raw11488Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw11488 raw11488Labels = mixedMoment B raw11488step0 raw11488step0Labels := by
      have ha : raw11488step0 = (fun i j => raw11488 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11488step0 raw11488; decide +kernel
      have hl : raw11488step0Labels = raw11488Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11488 raw11488Labels permutation176 permutation2
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw11489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw11489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11489 raw11489Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw11489 raw11489Labels = mixedMoment B raw11489step0 raw11489step0Labels := by
      have hz : ∀ j, raw11489 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11489step0 = (fun i j => raw11489 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11489step0 raw11489; decide +kernel
      have hl : raw11489step0Labels = raw11489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11489 raw11489Labels permutation520 hz
    mixedMoment B raw11489step0 raw11489step0Labels = mixedMoment B raw11489step1 raw11489step1Labels := by
      have hz : ∀ j, raw11489step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11489step1 = (fun i j => raw11489step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11489step1 raw11489step0; decide +kernel
      have hl : raw11489step1Labels = raw11489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11489step0 raw11489step0Labels permutation80 hz
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw11490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11490step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11490step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11490step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11490step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11490 raw11490Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11490 raw11490Labels = mixedMoment B raw11490step0 raw11490step0Labels := by
      have hz : ∀ j, raw11490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11490step0 = (fun i j => raw11490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11490step0 raw11490; decide +kernel
      have hl : raw11490step0Labels = raw11490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11490 raw11490Labels permutation346 hz
    mixedMoment B raw11490step0 raw11490step0Labels = mixedMoment B raw11490step1 raw11490step1Labels := by
      have ha : raw11490step1 = (fun i j => raw11490step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11490step1 raw11490step0; decide +kernel
      have hl : raw11490step1Labels = raw11490step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11490step0 raw11490step0Labels permutation40 permutation7
    mixedMoment B raw11490step1 raw11490step1Labels = mixedMoment B raw11490step2 raw11490step2Labels := by
      have ha : raw11490step2 = -raw11490step1 := by apply Matrix.ext; change ∀ i j, raw11490step2 i j = -(raw11490step1 i j); unfold raw11490step2 raw11490step1; decide +kernel
      have hl : raw11490step2Labels = raw11490step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11490step2 raw11490step2Labels = mixedMoment B raw11490step3 raw11490step3Labels := by
      have ha : raw11490step3 = raw11490step2 := by apply Matrix.ext; unfold raw11490step3 raw11490step2; decide +kernel
      have hl : raw11490step2Labels = labelEmbedding10 ∘ raw11490step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11490step2 raw11490step2Labels raw11490step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw11491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11491step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11491step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11491 raw11491Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw11491 raw11491Labels = mixedMoment B raw11491step0 raw11491step0Labels := by
      have hz : ∀ j, raw11491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11491step0 = (fun i j => raw11491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11491step0 raw11491; decide +kernel
      have hl : raw11491step0Labels = raw11491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11491 raw11491Labels permutation434 hz
    mixedMoment B raw11491step0 raw11491step0Labels = mixedMoment B raw11491step1 raw11491step1Labels := by
      have hz : ∀ j, raw11491step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11491step1 = (fun i j => raw11491step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11491step1 raw11491step0; decide +kernel
      have hl : raw11491step1Labels = raw11491step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11491step0 raw11491step0Labels permutation80 hz
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw11492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11492 raw11492Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw11492 raw11492Labels = mixedMoment B raw11492step0 raw11492step0Labels := by
      have hz : ∀ j, raw11492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11492step0 = (fun i j => raw11492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11492step0 raw11492; decide +kernel
      have hl : raw11492step0Labels = raw11492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11492 raw11492Labels permutation434 hz
    mixedMoment B raw11492step0 raw11492step0Labels = mixedMoment B raw11492step1 raw11492step1Labels := by
      have hz : ∀ j, raw11492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11492step1 = (fun i j => raw11492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11492step1 raw11492step0; decide +kernel
      have hl : raw11492step1Labels = raw11492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11492step0 raw11492step0Labels permutation80 hz
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw11493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11493 raw11493Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw11493 raw11493Labels = mixedMoment B raw11493step0 raw11493step0Labels := by
      have hz : ∀ j, raw11493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11493step0 = (fun i j => raw11493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11493step0 raw11493; decide +kernel
      have hl : raw11493step0Labels = raw11493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11493 raw11493Labels permutation434 hz
    mixedMoment B raw11493step0 raw11493step0Labels = mixedMoment B raw11493step1 raw11493step1Labels := by
      have ha : raw11493step1 = (fun i j => raw11493step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11493step1 raw11493step0; decide +kernel
      have hl : raw11493step1Labels = raw11493step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11493step0 raw11493step0Labels permutation38 permutation2
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw11494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11494 raw11494Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw11494 raw11494Labels = mixedMoment B raw11494step0 raw11494step0Labels := by
      have hz : ∀ j, raw11494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11494step0 = (fun i j => raw11494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11494step0 raw11494; decide +kernel
      have hl : raw11494step0Labels = raw11494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11494 raw11494Labels permutation346 hz
    mixedMoment B raw11494step0 raw11494step0Labels = mixedMoment B raw11494step1 raw11494step1Labels := by
      have ha : raw11494step1 = (fun i j => raw11494step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11494step1 raw11494step0; decide +kernel
      have hl : raw11494step1Labels = raw11494step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11494step0 raw11494step0Labels permutation38 permutation2
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw11495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw11495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11495step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11495 raw11495Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw11495 raw11495Labels = mixedMoment B raw11495step0 raw11495step0Labels := by
      have hz : ∀ j, raw11495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11495step0 = (fun i j => raw11495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11495step0 raw11495; decide +kernel
      have hl : raw11495step0Labels = raw11495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11495 raw11495Labels permutation434 hz
    mixedMoment B raw11495step0 raw11495step0Labels = mixedMoment B raw11495step1 raw11495step1Labels := by
      have hz : ∀ j, raw11495step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11495step1 = (fun i j => raw11495step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11495step1 raw11495step0; decide +kernel
      have hl : raw11495step1Labels = raw11495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11495step0 raw11495step0Labels permutation80 hz
    mixedMoment B raw11495step1 raw11495step1Labels = mixedMoment B raw11495step2 raw11495step2Labels := by
      have ha : raw11495step2 = (fun i j => raw11495step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11495step2 raw11495step1; decide +kernel
      have hl : raw11495step2Labels = raw11495step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11495step1 raw11495step1Labels permutation9 permutation2
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw11496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11496step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11496 raw11496Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw11496 raw11496Labels = mixedMoment B raw11496step0 raw11496step0Labels := by
      have hz : ∀ j, raw11496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11496step0 = (fun i j => raw11496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11496step0 raw11496; decide +kernel
      have hl : raw11496step0Labels = raw11496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11496 raw11496Labels permutation434 hz
    mixedMoment B raw11496step0 raw11496step0Labels = mixedMoment B raw11496step1 raw11496step1Labels := by
      have hz : ∀ j, raw11496step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11496step1 = (fun i j => raw11496step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11496step1 raw11496step0; decide +kernel
      have hl : raw11496step1Labels = raw11496step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11496step0 raw11496step0Labels permutation80 hz
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw11497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11497step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11497 raw11497Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw11497 raw11497Labels = mixedMoment B raw11497step0 raw11497step0Labels := by
      have hz : ∀ j, raw11497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11497step0 = (fun i j => raw11497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11497step0 raw11497; decide +kernel
      have hl : raw11497step0Labels = raw11497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11497 raw11497Labels permutation434 hz
    mixedMoment B raw11497step0 raw11497step0Labels = mixedMoment B raw11497step1 raw11497step1Labels := by
      have hz : ∀ j, raw11497step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11497step1 = (fun i j => raw11497step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11497step1 raw11497step0; decide +kernel
      have hl : raw11497step1Labels = raw11497step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11497step0 raw11497step0Labels permutation80 hz
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw11498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11498step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11498step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11498 raw11498Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw11498 raw11498Labels = mixedMoment B raw11498step0 raw11498step0Labels := by
      have hz : ∀ j, raw11498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11498step0 = (fun i j => raw11498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11498step0 raw11498; decide +kernel
      have hl : raw11498step0Labels = raw11498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11498 raw11498Labels permutation434 hz
    mixedMoment B raw11498step0 raw11498step0Labels = mixedMoment B raw11498step1 raw11498step1Labels := by
      have ha : raw11498step1 = (fun i j => raw11498step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11498step1 raw11498step0; decide +kernel
      have hl : raw11498step1Labels = raw11498step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11498step0 raw11498step0Labels permutation38 permutation2
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw11499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11499step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw11499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11499 raw11499Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw11499 raw11499Labels = mixedMoment B raw11499step0 raw11499step0Labels := by
      have hz : ∀ j, raw11499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11499step0 = (fun i j => raw11499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11499step0 raw11499; decide +kernel
      have hl : raw11499step0Labels = raw11499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11499 raw11499Labels permutation346 hz
    mixedMoment B raw11499step0 raw11499step0Labels = mixedMoment B raw11499step1 raw11499step1Labels := by
      have ha : raw11499step1 = (fun i j => raw11499step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11499step1 raw11499step0; decide +kernel
      have hl : raw11499step1Labels = raw11499step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11499step0 raw11499step0Labels permutation38 permutation2
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw11500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw11500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw11500step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw11500step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11500step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw11500step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11500 raw11500Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw11500 raw11500Labels = mixedMoment B raw11500step0 raw11500step0Labels := by
      have hz : ∀ j, raw11500 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11500step0 = (fun i j => raw11500 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11500step0 raw11500; decide +kernel
      have hl : raw11500step0Labels = raw11500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11500 raw11500Labels permutation520 hz
    mixedMoment B raw11500step0 raw11500step0Labels = mixedMoment B raw11500step1 raw11500step1Labels := by
      have hz : ∀ j, raw11500step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11500step1 = (fun i j => raw11500step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11500step1 raw11500step0; decide +kernel
      have hl : raw11500step1Labels = raw11500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11500step0 raw11500step0Labels permutation104 hz
    mixedMoment B raw11500step1 raw11500step1Labels = mixedMoment B raw11500step2 raw11500step2Labels := by
      have hz : ∀ j, raw11500step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw11500step2 = (fun i j => raw11500step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw11500step2 raw11500step1; decide +kernel
      have hl : raw11500step2Labels = raw11500step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11500step1 raw11500step1Labels permutation20 hz
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw11501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11501step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11501step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11501step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw11501step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11501step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11501step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11501step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11501step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11501 raw11501Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw11501 raw11501Labels = mixedMoment B raw11501step0 raw11501step0Labels := by
      have hz : ∀ j, raw11501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11501step0 = (fun i j => raw11501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11501step0 raw11501; decide +kernel
      have hl : raw11501step0Labels = raw11501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11501 raw11501Labels permutation434 hz
    mixedMoment B raw11501step0 raw11501step0Labels = mixedMoment B raw11501step1 raw11501step1Labels := by
      have hz : ∀ j, raw11501step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11501step1 = (fun i j => raw11501step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11501step1 raw11501step0; decide +kernel
      have hl : raw11501step1Labels = raw11501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11501step0 raw11501step0Labels permutation80 hz
    mixedMoment B raw11501step1 raw11501step1Labels = mixedMoment B raw11501step2 raw11501step2Labels := by
      have ha : raw11501step2 = (fun i j => raw11501step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11501step2 raw11501step1; decide +kernel
      have hl : raw11501step2Labels = raw11501step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11501step1 raw11501step1Labels permutation9 permutation7
    mixedMoment B raw11501step2 raw11501step2Labels = mixedMoment B raw11501step3 raw11501step3Labels := by
      have ha : raw11501step3 = -raw11501step2 := by apply Matrix.ext; change ∀ i j, raw11501step3 i j = -(raw11501step2 i j); unfold raw11501step3 raw11501step2; decide +kernel
      have hl : raw11501step3Labels = raw11501step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11501step3 raw11501step3Labels = mixedMoment B raw11501step4 raw11501step4Labels := by
      have ha : raw11501step4 = raw11501step3 := by apply Matrix.ext; unfold raw11501step4 raw11501step3; decide +kernel
      have hl : raw11501step3Labels = labelEmbedding10 ∘ raw11501step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11501step3 raw11501step3Labels raw11501step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw11502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11502step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11502step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw11502step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11502step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11502step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11502step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11502step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11502 raw11502Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw11502 raw11502Labels = mixedMoment B raw11502step0 raw11502step0Labels := by
      have hz : ∀ j, raw11502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11502step0 = (fun i j => raw11502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11502step0 raw11502; decide +kernel
      have hl : raw11502step0Labels = raw11502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11502 raw11502Labels permutation434 hz
    mixedMoment B raw11502step0 raw11502step0Labels = mixedMoment B raw11502step1 raw11502step1Labels := by
      have hz : ∀ j, raw11502step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11502step1 = (fun i j => raw11502step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11502step1 raw11502step0; decide +kernel
      have hl : raw11502step1Labels = raw11502step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11502step0 raw11502step0Labels permutation56 hz
    mixedMoment B raw11502step1 raw11502step1Labels = mixedMoment B raw11502step2 raw11502step2Labels := by
      have ha : raw11502step2 = (fun i j => raw11502step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11502step2 raw11502step1; decide +kernel
      have hl : raw11502step2Labels = raw11502step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11502step1 raw11502step1Labels permutation9 permutation7
    mixedMoment B raw11502step2 raw11502step2Labels = mixedMoment B raw11502step3 raw11502step3Labels := by
      have ha : raw11502step3 = -raw11502step2 := by apply Matrix.ext; change ∀ i j, raw11502step3 i j = -(raw11502step2 i j); unfold raw11502step3 raw11502step2; decide +kernel
      have hl : raw11502step3Labels = raw11502step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11502step3 raw11502step3Labels = mixedMoment B raw11502step4 raw11502step4Labels := by
      have ha : raw11502step4 = raw11502step3 := by apply Matrix.ext; unfold raw11502step4 raw11502step3; decide +kernel
      have hl : raw11502step3Labels = labelEmbedding10 ∘ raw11502step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11502step3 raw11502step3Labels raw11502step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw11503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11503step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11503step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw11503step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11503step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11503step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11503step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw11503step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11503 raw11503Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw11503 raw11503Labels = mixedMoment B raw11503step0 raw11503step0Labels := by
      have hz : ∀ j, raw11503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11503step0 = (fun i j => raw11503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11503step0 raw11503; decide +kernel
      have hl : raw11503step0Labels = raw11503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11503 raw11503Labels permutation346 hz
    mixedMoment B raw11503step0 raw11503step0Labels = mixedMoment B raw11503step1 raw11503step1Labels := by
      have hz : ∀ j, raw11503step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11503step1 = (fun i j => raw11503step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11503step1 raw11503step0; decide +kernel
      have hl : raw11503step1Labels = raw11503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11503step0 raw11503step0Labels permutation56 hz
    mixedMoment B raw11503step1 raw11503step1Labels = mixedMoment B raw11503step2 raw11503step2Labels := by
      have ha : raw11503step2 = (fun i j => raw11503step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11503step2 raw11503step1; decide +kernel
      have hl : raw11503step2Labels = raw11503step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11503step1 raw11503step1Labels permutation9 permutation7
    mixedMoment B raw11503step2 raw11503step2Labels = mixedMoment B raw11503step3 raw11503step3Labels := by
      have ha : raw11503step3 = -raw11503step2 := by apply Matrix.ext; change ∀ i j, raw11503step3 i j = -(raw11503step2 i j); unfold raw11503step3 raw11503step2; decide +kernel
      have hl : raw11503step3Labels = raw11503step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11503step3 raw11503step3Labels = mixedMoment B raw11503step4 raw11503step4Labels := by
      have ha : raw11503step4 = raw11503step3 := by apply Matrix.ext; unfold raw11503step4 raw11503step3; decide +kernel
      have hl : raw11503step3Labels = labelEmbedding10 ∘ raw11503step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11503step3 raw11503step3Labels raw11503step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw11504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11504step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11504step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11504step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw11504step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11504step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw11504step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11504step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw11504step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11504step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw11504step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11504 raw11504Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw11504 raw11504Labels = mixedMoment B raw11504step0 raw11504step0Labels := by
      have hz : ∀ j, raw11504 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11504step0 = (fun i j => raw11504 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11504step0 raw11504; decide +kernel
      have hl : raw11504step0Labels = raw11504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11504 raw11504Labels permutation434 hz
    mixedMoment B raw11504step0 raw11504step0Labels = mixedMoment B raw11504step1 raw11504step1Labels := by
      have hz : ∀ j, raw11504step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11504step1 = (fun i j => raw11504step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11504step1 raw11504step0; decide +kernel
      have hl : raw11504step1Labels = raw11504step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11504step0 raw11504step0Labels permutation80 hz
    mixedMoment B raw11504step1 raw11504step1Labels = mixedMoment B raw11504step2 raw11504step2Labels := by
      have hz : ∀ j, raw11504step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11504step2 = (fun i j => raw11504step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11504step2 raw11504step1; decide +kernel
      have hl : raw11504step2Labels = raw11504step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11504step1 raw11504step1Labels permutation14 hz
    mixedMoment B raw11504step2 raw11504step2Labels = mixedMoment B raw11504step3 raw11504step3Labels := by
      have ha : raw11504step3 = (fun i j => raw11504step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11504step3 raw11504step2; decide +kernel
      have hl : raw11504step3Labels = raw11504step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11504step2 raw11504step2Labels permutation3 permutation7
    mixedMoment B raw11504step3 raw11504step3Labels = mixedMoment B raw11504step4 raw11504step4Labels := by
      have ha : raw11504step4 = -raw11504step3 := by apply Matrix.ext; change ∀ i j, raw11504step4 i j = -(raw11504step3 i j); unfold raw11504step4 raw11504step3; decide +kernel
      have hl : raw11504step4Labels = raw11504step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11504step4 raw11504step4Labels = mixedMoment B raw11504step5 raw11504step5Labels := by
      have ha : raw11504step5 = raw11504step4 := by apply Matrix.ext; unfold raw11504step5 raw11504step4; decide +kernel
      have hl : raw11504step4Labels = labelEmbedding10 ∘ raw11504step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11504step4 raw11504step4Labels raw11504step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw11505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11505step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 1, -2], ![1, 0, -1]]
def raw11505step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11505step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw11505step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11505step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11505step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11505step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11505step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11505 raw11505Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw11505 raw11505Labels = mixedMoment B raw11505step0 raw11505step0Labels := by
      have hz : ∀ j, raw11505 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11505step0 = (fun i j => raw11505 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11505step0 raw11505; decide +kernel
      have hl : raw11505step0Labels = raw11505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11505 raw11505Labels permutation434 hz
    mixedMoment B raw11505step0 raw11505step0Labels = mixedMoment B raw11505step1 raw11505step1Labels := by
      have hz : ∀ j, raw11505step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11505step1 = (fun i j => raw11505step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11505step1 raw11505step0; decide +kernel
      have hl : raw11505step1Labels = raw11505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11505step0 raw11505step0Labels permutation80 hz
    mixedMoment B raw11505step1 raw11505step1Labels = mixedMoment B raw11505step2 raw11505step2Labels := by
      have hz : ∀ j, raw11505step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11505step2 = (fun i j => raw11505step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11505step2 raw11505step1; decide +kernel
      have hl : raw11505step2Labels = raw11505step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11505step1 raw11505step1Labels permutation14 hz
    mixedMoment B raw11505step2 raw11505step2Labels = mixedMoment B raw11505step3 raw11505step3Labels := by
      have ha : raw11505step3 = (fun i j => raw11505step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11505step3 raw11505step2; decide +kernel
      have hl : raw11505step3Labels = raw11505step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11505step2 raw11505step2Labels permutation3 permutation7
    mixedMoment B raw11505step3 raw11505step3Labels = mixedMoment B raw11505step4 raw11505step4Labels := by
      have ha : raw11505step4 = -raw11505step3 := by apply Matrix.ext; change ∀ i j, raw11505step4 i j = -(raw11505step3 i j); unfold raw11505step4 raw11505step3; decide +kernel
      have hl : raw11505step4Labels = raw11505step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11505step4 raw11505step4Labels = mixedMoment B raw11505step5 raw11505step5Labels := by
      have ha : raw11505step5 = raw11505step4 := by apply Matrix.ext; unfold raw11505step5 raw11505step4; decide +kernel
      have hl : raw11505step4Labels = labelEmbedding10 ∘ raw11505step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11505step4 raw11505step4Labels raw11505step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5309 node5309Labels := by rfl

def raw11506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11506step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11506 raw11506Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw11506 raw11506Labels = mixedMoment B raw11506step0 raw11506step0Labels := by
      have hz : ∀ j, raw11506 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11506step0 = (fun i j => raw11506 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11506step0 raw11506; decide +kernel
      have hl : raw11506step0Labels = raw11506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11506 raw11506Labels permutation434 hz
    mixedMoment B raw11506step0 raw11506step0Labels = mixedMoment B raw11506step1 raw11506step1Labels := by
      have hz : ∀ j, raw11506step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11506step1 = (fun i j => raw11506step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11506step1 raw11506step0; decide +kernel
      have hl : raw11506step1Labels = raw11506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11506step0 raw11506step0Labels permutation80 hz
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw11507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11507 raw11507Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11507 raw11507Labels = mixedMoment B raw11507step0 raw11507step0Labels := by
      have hz : ∀ j, raw11507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11507step0 = (fun i j => raw11507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11507step0 raw11507; decide +kernel
      have hl : raw11507step0Labels = raw11507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11507 raw11507Labels permutation434 hz
    mixedMoment B raw11507step0 raw11507step0Labels = mixedMoment B raw11507step1 raw11507step1Labels := by
      have ha : raw11507step1 = (fun i j => raw11507step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11507step1 raw11507step0; decide +kernel
      have hl : raw11507step1Labels = raw11507step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11507step0 raw11507step0Labels permutation38 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11508 raw11508Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11508 raw11508Labels = mixedMoment B raw11508step0 raw11508step0Labels := by
      have hz : ∀ j, raw11508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11508step0 = (fun i j => raw11508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11508step0 raw11508; decide +kernel
      have hl : raw11508step0Labels = raw11508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11508 raw11508Labels permutation346 hz
    mixedMoment B raw11508step0 raw11508step0Labels = mixedMoment B raw11508step1 raw11508step1Labels := by
      have ha : raw11508step1 = (fun i j => raw11508step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11508step1 raw11508step0; decide +kernel
      have hl : raw11508step1Labels = raw11508step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11508step0 raw11508step0Labels permutation38 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11509step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11509step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11509step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11509step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11509step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11509 raw11509Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw11509 raw11509Labels = mixedMoment B raw11509step0 raw11509step0Labels := by
      have hz : ∀ j, raw11509 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11509step0 = (fun i j => raw11509 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11509step0 raw11509; decide +kernel
      have hl : raw11509step0Labels = raw11509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11509 raw11509Labels permutation434 hz
    mixedMoment B raw11509step0 raw11509step0Labels = mixedMoment B raw11509step1 raw11509step1Labels := by
      have hz : ∀ j, raw11509step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11509step1 = (fun i j => raw11509step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11509step1 raw11509step0; decide +kernel
      have hl : raw11509step1Labels = raw11509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11509step0 raw11509step0Labels permutation80 hz
    mixedMoment B raw11509step1 raw11509step1Labels = mixedMoment B raw11509step2 raw11509step2Labels := by
      have ha : raw11509step2 = (fun i j => raw11509step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11509step2 raw11509step1; decide +kernel
      have hl : raw11509step2Labels = raw11509step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11509step1 raw11509step1Labels permutation9 permutation7
    mixedMoment B raw11509step2 raw11509step2Labels = mixedMoment B raw11509step3 raw11509step3Labels := by
      have ha : raw11509step3 = -raw11509step2 := by apply Matrix.ext; change ∀ i j, raw11509step3 i j = -(raw11509step2 i j); unfold raw11509step3 raw11509step2; decide +kernel
      have hl : raw11509step3Labels = raw11509step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11509step3 raw11509step3Labels = mixedMoment B raw11509step4 raw11509step4Labels := by
      have ha : raw11509step4 = raw11509step3 := by apply Matrix.ext; unfold raw11509step4 raw11509step3; decide +kernel
      have hl : raw11509step3Labels = labelEmbedding10 ∘ raw11509step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11509step3 raw11509step3Labels raw11509step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw11510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11510step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11510step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11510step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11510step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11510step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11510 raw11510Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11510 raw11510Labels = mixedMoment B raw11510step0 raw11510step0Labels := by
      have hz : ∀ j, raw11510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11510step0 = (fun i j => raw11510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11510step0 raw11510; decide +kernel
      have hl : raw11510step0Labels = raw11510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11510 raw11510Labels permutation434 hz
    mixedMoment B raw11510step0 raw11510step0Labels = mixedMoment B raw11510step1 raw11510step1Labels := by
      have hz : ∀ j, raw11510step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11510step1 = (fun i j => raw11510step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11510step1 raw11510step0; decide +kernel
      have hl : raw11510step1Labels = raw11510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11510step0 raw11510step0Labels permutation80 hz
    mixedMoment B raw11510step1 raw11510step1Labels = mixedMoment B raw11510step2 raw11510step2Labels := by
      have ha : raw11510step2 = (fun i j => raw11510step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11510step2 raw11510step1; decide +kernel
      have hl : raw11510step2Labels = raw11510step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11510step1 raw11510step1Labels permutation9 permutation7
    mixedMoment B raw11510step2 raw11510step2Labels = mixedMoment B raw11510step3 raw11510step3Labels := by
      have ha : raw11510step3 = -raw11510step2 := by apply Matrix.ext; change ∀ i j, raw11510step3 i j = -(raw11510step2 i j); unfold raw11510step3 raw11510step2; decide +kernel
      have hl : raw11510step3Labels = raw11510step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11510step3 raw11510step3Labels = mixedMoment B raw11510step4 raw11510step4Labels := by
      have ha : raw11510step4 = raw11510step3 := by apply Matrix.ext; unfold raw11510step4 raw11510step3; decide +kernel
      have hl : raw11510step3Labels = labelEmbedding10 ∘ raw11510step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11510step3 raw11510step3Labels raw11510step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw11511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11511 raw11511Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw11511 raw11511Labels = mixedMoment B raw11511step0 raw11511step0Labels := by
      have hz : ∀ j, raw11511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11511step0 = (fun i j => raw11511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11511step0 raw11511; decide +kernel
      have hl : raw11511step0Labels = raw11511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11511 raw11511Labels permutation434 hz
    mixedMoment B raw11511step0 raw11511step0Labels = mixedMoment B raw11511step1 raw11511step1Labels := by
      have hz : ∀ j, raw11511step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11511step1 = (fun i j => raw11511step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11511step1 raw11511step0; decide +kernel
      have hl : raw11511step1Labels = raw11511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11511step0 raw11511step0Labels permutation56 hz
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw11512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11512 raw11512Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11512 raw11512Labels = mixedMoment B raw11512step0 raw11512step0Labels := by
      have hz : ∀ j, raw11512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11512step0 = (fun i j => raw11512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11512step0 raw11512; decide +kernel
      have hl : raw11512step0Labels = raw11512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11512 raw11512Labels permutation434 hz
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11513step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11513 raw11513Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11513 raw11513Labels = mixedMoment B raw11513step0 raw11513step0Labels := by
      have hz : ∀ j, raw11513 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11513step0 = (fun i j => raw11513 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11513step0 raw11513; decide +kernel
      have hl : raw11513step0Labels = raw11513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11513 raw11513Labels permutation265 hz
    mixedMoment B raw11513step0 raw11513step0Labels = mixedMoment B raw11513step1 raw11513step1Labels := by
      have ha : raw11513step1 = (fun i j => raw11513step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11513step1 raw11513step0; decide +kernel
      have hl : raw11513step1Labels = raw11513step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11513step0 raw11513step0Labels permutation38 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11514step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11514step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11514step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11514step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11514 raw11514Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw11514 raw11514Labels = mixedMoment B raw11514step0 raw11514step0Labels := by
      have hz : ∀ j, raw11514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11514step0 = (fun i j => raw11514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11514step0 raw11514; decide +kernel
      have hl : raw11514step0Labels = raw11514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11514 raw11514Labels permutation434 hz
    mixedMoment B raw11514step0 raw11514step0Labels = mixedMoment B raw11514step1 raw11514step1Labels := by
      have hz : ∀ j, raw11514step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11514step1 = (fun i j => raw11514step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11514step1 raw11514step0; decide +kernel
      have hl : raw11514step1Labels = raw11514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11514step0 raw11514step0Labels permutation56 hz
    mixedMoment B raw11514step1 raw11514step1Labels = mixedMoment B raw11514step2 raw11514step2Labels := by
      have ha : raw11514step2 = (fun i j => raw11514step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11514step2 raw11514step1; decide +kernel
      have hl : raw11514step2Labels = raw11514step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11514step1 raw11514step1Labels permutation9 permutation7
    mixedMoment B raw11514step2 raw11514step2Labels = mixedMoment B raw11514step3 raw11514step3Labels := by
      have ha : raw11514step3 = -raw11514step2 := by apply Matrix.ext; change ∀ i j, raw11514step3 i j = -(raw11514step2 i j); unfold raw11514step3 raw11514step2; decide +kernel
      have hl : raw11514step3Labels = raw11514step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11514step3 raw11514step3Labels = mixedMoment B raw11514step4 raw11514step4Labels := by
      have ha : raw11514step4 = raw11514step3 := by apply Matrix.ext; unfold raw11514step4 raw11514step3; decide +kernel
      have hl : raw11514step3Labels = labelEmbedding10 ∘ raw11514step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11514step3 raw11514step3Labels raw11514step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw11515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw11515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11515step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11515step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11515step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11515step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11515step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11515 raw11515Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11515 raw11515Labels = mixedMoment B raw11515step0 raw11515step0Labels := by
      have hz : ∀ j, raw11515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11515step0 = (fun i j => raw11515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11515step0 raw11515; decide +kernel
      have hl : raw11515step0Labels = raw11515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11515 raw11515Labels permutation434 hz
    mixedMoment B raw11515step0 raw11515step0Labels = mixedMoment B raw11515step1 raw11515step1Labels := by
      have hz : ∀ j, raw11515step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11515step1 = (fun i j => raw11515step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11515step1 raw11515step0; decide +kernel
      have hl : raw11515step1Labels = raw11515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11515step0 raw11515step0Labels permutation56 hz
    mixedMoment B raw11515step1 raw11515step1Labels = mixedMoment B raw11515step2 raw11515step2Labels := by
      have ha : raw11515step2 = (fun i j => raw11515step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11515step2 raw11515step1; decide +kernel
      have hl : raw11515step2Labels = raw11515step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11515step1 raw11515step1Labels permutation9 permutation7
    mixedMoment B raw11515step2 raw11515step2Labels = mixedMoment B raw11515step3 raw11515step3Labels := by
      have ha : raw11515step3 = -raw11515step2 := by apply Matrix.ext; change ∀ i j, raw11515step3 i j = -(raw11515step2 i j); unfold raw11515step3 raw11515step2; decide +kernel
      have hl : raw11515step3Labels = raw11515step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11515step3 raw11515step3Labels = mixedMoment B raw11515step4 raw11515step4Labels := by
      have ha : raw11515step4 = raw11515step3 := by apply Matrix.ext; unfold raw11515step4 raw11515step3; decide +kernel
      have hl : raw11515step3Labels = labelEmbedding10 ∘ raw11515step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11515step3 raw11515step3Labels raw11515step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw11516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11516 raw11516Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw11516 raw11516Labels = mixedMoment B raw11516step0 raw11516step0Labels := by
      have hz : ∀ j, raw11516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11516step0 = (fun i j => raw11516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11516step0 raw11516; decide +kernel
      have hl : raw11516step0Labels = raw11516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11516 raw11516Labels permutation346 hz
    mixedMoment B raw11516step0 raw11516step0Labels = mixedMoment B raw11516step1 raw11516step1Labels := by
      have hz : ∀ j, raw11516step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11516step1 = (fun i j => raw11516step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11516step1 raw11516step0; decide +kernel
      have hl : raw11516step1Labels = raw11516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11516step0 raw11516step0Labels permutation56 hz
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw11517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11517 raw11517Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11517 raw11517Labels = mixedMoment B raw11517step0 raw11517step0Labels := by
      have hz : ∀ j, raw11517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11517step0 = (fun i j => raw11517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11517step0 raw11517; decide +kernel
      have hl : raw11517step0Labels = raw11517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11517 raw11517Labels permutation346 hz
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw11518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11518 raw11518Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11518 raw11518Labels = mixedMoment B raw11518step0 raw11518step0Labels := by
      have hz : ∀ j, raw11518 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11518step0 = (fun i j => raw11518 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11518step0 raw11518; decide +kernel
      have hl : raw11518step0Labels = raw11518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11518 raw11518Labels permutation265 hz
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw11519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw11519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11519step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11519step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11519step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11519step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11519 raw11519Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw11519 raw11519Labels = mixedMoment B raw11519step0 raw11519step0Labels := by
      have hz : ∀ j, raw11519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11519step0 = (fun i j => raw11519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11519step0 raw11519; decide +kernel
      have hl : raw11519step0Labels = raw11519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11519 raw11519Labels permutation346 hz
    mixedMoment B raw11519step0 raw11519step0Labels = mixedMoment B raw11519step1 raw11519step1Labels := by
      have hz : ∀ j, raw11519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11519step1 = (fun i j => raw11519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11519step1 raw11519step0; decide +kernel
      have hl : raw11519step1Labels = raw11519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11519step0 raw11519step0Labels permutation56 hz
    mixedMoment B raw11519step1 raw11519step1Labels = mixedMoment B raw11519step2 raw11519step2Labels := by
      have ha : raw11519step2 = (fun i j => raw11519step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11519step2 raw11519step1; decide +kernel
      have hl : raw11519step2Labels = raw11519step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11519step1 raw11519step1Labels permutation9 permutation7
    mixedMoment B raw11519step2 raw11519step2Labels = mixedMoment B raw11519step3 raw11519step3Labels := by
      have ha : raw11519step3 = -raw11519step2 := by apply Matrix.ext; change ∀ i j, raw11519step3 i j = -(raw11519step2 i j); unfold raw11519step3 raw11519step2; decide +kernel
      have hl : raw11519step3Labels = raw11519step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11519step3 raw11519step3Labels = mixedMoment B raw11519step4 raw11519step4Labels := by
      have ha : raw11519step4 = raw11519step3 := by apply Matrix.ext; unfold raw11519step4 raw11519step3; decide +kernel
      have hl : raw11519step3Labels = labelEmbedding10 ∘ raw11519step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11519step3 raw11519step3Labels raw11519step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
