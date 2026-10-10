import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw38144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38144Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38144step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw38144step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38144 raw38144Labels = mixedMoment B node486 node486Labels := by
  calc
    mixedMoment B raw38144 raw38144Labels = mixedMoment B raw38144step0 raw38144step0Labels := by
      have ha : raw38144step0 = (fun i j => raw38144 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38144step0 raw38144; decide +kernel
      have hl : raw38144step0Labels = raw38144Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38144 raw38144Labels permutation194 permutation5
    mixedMoment B raw38144step0 raw38144step0Labels = mixedMoment B raw38144step1 raw38144step1Labels := by
      have ha : raw38144step1 = -raw38144step0 := by apply Matrix.ext; change ∀ i j, raw38144step1 i j = -(raw38144step0 i j); unfold raw38144step1 raw38144step0; decide +kernel
      have hl : raw38144step1Labels = raw38144step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node486 node486Labels := by rfl

def raw38145 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38145Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw38145step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw38145step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38145 raw38145Labels = mixedMoment B node487 node487Labels := by
  calc
    mixedMoment B raw38145 raw38145Labels = mixedMoment B raw38145step0 raw38145step0Labels := by
      have ha : raw38145step0 = (fun i j => raw38145 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38145step0 raw38145; decide +kernel
      have hl : raw38145step0Labels = raw38145Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38145 raw38145Labels permutation151 permutation3
    mixedMoment B raw38145step0 raw38145step0Labels = mixedMoment B raw38145step1 raw38145step1Labels := by
      have ha : raw38145step1 = -raw38145step0 := by apply Matrix.ext; change ∀ i j, raw38145step1 i j = -(raw38145step0 i j); unfold raw38145step1 raw38145step0; decide +kernel
      have hl : raw38145step1Labels = raw38145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node487 node487Labels := by rfl

def raw38146 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw38146Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw38146step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38146 raw38146Labels = mixedMoment B node500 node500Labels := by
  calc
    mixedMoment B raw38146 raw38146Labels = mixedMoment B raw38146step0 raw38146step0Labels := by
      have ha : raw38146step0 = (fun i j => raw38146 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38146step0 raw38146; decide +kernel
      have hl : raw38146step0Labels = raw38146Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38146 raw38146Labels permutation36 permutation3
    _ = mixedMoment B node500 node500Labels := by rfl

def raw38147 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38147Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38147step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38147 raw38147Labels = mixedMoment B node502 node502Labels := by
  calc
    mixedMoment B raw38147 raw38147Labels = mixedMoment B raw38147step0 raw38147step0Labels := by
      have ha : raw38147step0 = (fun i j => raw38147 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38147step0 raw38147; decide +kernel
      have hl : raw38147step0Labels = raw38147Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38147 raw38147Labels permutation35 permutation3
    _ = mixedMoment B node502 node502Labels := by rfl

def raw38148 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw38148Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38148step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw38148step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38148 raw38148Labels = mixedMoment B node501 node501Labels := by
  calc
    mixedMoment B raw38148 raw38148Labels = mixedMoment B raw38148step0 raw38148step0Labels := by
      have ha : raw38148step0 = (fun i j => raw38148 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38148step0 raw38148; decide +kernel
      have hl : raw38148step0Labels = raw38148Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38148 raw38148Labels permutation8 permutation3
    _ = mixedMoment B node501 node501Labels := by rfl

def raw38149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38149Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38149step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38149 raw38149Labels = mixedMoment B node471 node471Labels := by
  calc
    mixedMoment B raw38149 raw38149Labels = mixedMoment B raw38149step0 raw38149step0Labels := by
      have ha : raw38149step0 = (fun i j => raw38149 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38149step0 raw38149; decide +kernel
      have hl : raw38149step0Labels = raw38149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38149 raw38149Labels permutation152 permutation3
    _ = mixedMoment B node471 node471Labels := by rfl

def raw38150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38150Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw38150step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38150 raw38150Labels = mixedMoment B node478 node478Labels := by
  calc
    mixedMoment B raw38150 raw38150Labels = mixedMoment B raw38150step0 raw38150step0Labels := by
      have ha : raw38150step0 = (fun i j => raw38150 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38150step0 raw38150; decide +kernel
      have hl : raw38150step0Labels = raw38150Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38150 raw38150Labels permutation158 permutation3
    _ = mixedMoment B node478 node478Labels := by rfl

def raw38151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38151Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38151step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38151 raw38151Labels = mixedMoment B node488 node488Labels := by
  calc
    mixedMoment B raw38151 raw38151Labels = mixedMoment B raw38151step0 raw38151step0Labels := by
      have ha : raw38151step0 = (fun i j => raw38151 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38151step0 raw38151; decide +kernel
      have hl : raw38151step0Labels = raw38151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38151 raw38151Labels permutation155 permutation3
    _ = mixedMoment B node488 node488Labels := by rfl

def raw38152 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw38152Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw38152step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38152 raw38152Labels = mixedMoment B node504 node504Labels := by
  calc
    mixedMoment B raw38152 raw38152Labels = mixedMoment B raw38152step0 raw38152step0Labels := by
      have ha : raw38152step0 = (fun i j => raw38152 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38152step0 raw38152; decide +kernel
      have hl : raw38152step0Labels = raw38152Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38152 raw38152Labels permutation32 permutation3
    _ = mixedMoment B node504 node504Labels := by rfl

def raw38153 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw38153Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw38153step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw38153step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38153 raw38153Labels = mixedMoment B node526 node526Labels := by
  calc
    mixedMoment B raw38153 raw38153Labels = mixedMoment B raw38153step0 raw38153step0Labels := by
      have ha : raw38153step0 = (fun i j => raw38153 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw38153step0 raw38153; decide +kernel
      have hl : raw38153step0Labels = raw38153Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38153 raw38153Labels permutation45 permutation6
    mixedMoment B raw38153step0 raw38153step0Labels = mixedMoment B raw38153step1 raw38153step1Labels := by
      have ha : raw38153step1 = -raw38153step0 := by apply Matrix.ext; change ∀ i j, raw38153step1 i j = -(raw38153step0 i j); unfold raw38153step1 raw38153step0; decide +kernel
      have hl : raw38153step1Labels = raw38153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node526 node526Labels := by rfl

def raw38154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw38154Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38154 raw38154Labels = mixedMoment B node531 node531Labels := by
  calc
    _ = mixedMoment B node531 node531Labels := by rfl

def raw38155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw38155Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38155 raw38155Labels = mixedMoment B node533 node533Labels := by
  calc
    _ = mixedMoment B node533 node533Labels := by rfl

def raw38156 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw38156Labels : Fin 2 → Fin 2 := ![1, 1]

def raw38156step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw38156step0Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical38156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38156 raw38156Labels = mixedMoment B node5 node5Labels := by
  calc
    mixedMoment B raw38156 raw38156Labels = mixedMoment B raw38156step0 raw38156step0Labels := by
      have ha : raw38156step0 = raw38156 := by apply Matrix.ext; unfold raw38156step0 raw38156; decide +kernel
      have hl : raw38156Labels = labelEmbedding0 ∘ raw38156step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38156 raw38156Labels raw38156step0Labels labelEmbedding0 hl
    _ = mixedMoment B node5 node5Labels := by rfl

def raw38157 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw38157Labels : Fin 2 → Fin 2 := ![1, 1]

def raw38157step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw38157step0Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical38157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38157 raw38157Labels = mixedMoment B node6 node6Labels := by
  calc
    mixedMoment B raw38157 raw38157Labels = mixedMoment B raw38157step0 raw38157step0Labels := by
      have ha : raw38157step0 = raw38157 := by apply Matrix.ext; unfold raw38157step0 raw38157; decide +kernel
      have hl : raw38157Labels = labelEmbedding0 ∘ raw38157step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38157 raw38157Labels raw38157step0Labels labelEmbedding0 hl
    _ = mixedMoment B node6 node6Labels := by rfl

def raw38158 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw38158Labels : Fin 2 → Fin 2 := ![1, 1]

def raw38158step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw38158step0Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical38158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38158 raw38158Labels = mixedMoment B node7 node7Labels := by
  calc
    mixedMoment B raw38158 raw38158Labels = mixedMoment B raw38158step0 raw38158step0Labels := by
      have ha : raw38158step0 = raw38158 := by apply Matrix.ext; unfold raw38158step0 raw38158; decide +kernel
      have hl : raw38158Labels = labelEmbedding0 ∘ raw38158step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38158 raw38158Labels raw38158step0Labels labelEmbedding0 hl
    _ = mixedMoment B node7 node7Labels := by rfl

def raw38159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38159Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38159 raw38159Labels = mixedMoment B node535 node535Labels := by
  calc
    mixedMoment B raw38159 raw38159Labels = mixedMoment B raw38159step0 raw38159step0Labels := by
      have ha : raw38159step0 = raw38159 := by apply Matrix.ext; unfold raw38159step0 raw38159; decide +kernel
      have hl : raw38159Labels = labelEmbedding2 ∘ raw38159step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38159 raw38159Labels raw38159step0Labels labelEmbedding2 hl
    _ = mixedMoment B node535 node535Labels := by rfl

def raw38160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38160Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw38160step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38160step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38160step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38160 raw38160Labels = mixedMoment B node656 node656Labels := by
  calc
    mixedMoment B raw38160 raw38160Labels = mixedMoment B raw38160step0 raw38160step0Labels := by
      have ha : raw38160step0 = (fun i j => raw38160 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38160step0 raw38160; decide +kernel
      have hl : raw38160step0Labels = raw38160Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38160 raw38160Labels permutation182 permutation7
    mixedMoment B raw38160step0 raw38160step0Labels = mixedMoment B raw38160step1 raw38160step1Labels := by
      have ha : raw38160step1 = -raw38160step0 := by apply Matrix.ext; change ∀ i j, raw38160step1 i j = -(raw38160step0 i j); unfold raw38160step1 raw38160step0; decide +kernel
      have hl : raw38160step1Labels = raw38160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38160step1 raw38160step1Labels = mixedMoment B raw38160step2 raw38160step2Labels := by
      have ha : raw38160step2 = raw38160step1 := by apply Matrix.ext; unfold raw38160step2 raw38160step1; decide +kernel
      have hl : raw38160step1Labels = labelEmbedding4 ∘ raw38160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38160step1 raw38160step1Labels raw38160step2Labels labelEmbedding4 hl
    _ = mixedMoment B node656 node656Labels := by rfl

def raw38161 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38161Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38161 raw38161Labels = mixedMoment B node536 node536Labels := by
  calc
    mixedMoment B raw38161 raw38161Labels = mixedMoment B raw38161step0 raw38161step0Labels := by
      have ha : raw38161step0 = raw38161 := by apply Matrix.ext; unfold raw38161step0 raw38161; decide +kernel
      have hl : raw38161Labels = labelEmbedding2 ∘ raw38161step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38161 raw38161Labels raw38161step0Labels labelEmbedding2 hl
    _ = mixedMoment B node536 node536Labels := by rfl

def raw38162 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38162Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw38162step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38162step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38162 raw38162Labels = mixedMoment B node657 node657Labels := by
  calc
    mixedMoment B raw38162 raw38162Labels = mixedMoment B raw38162step0 raw38162step0Labels := by
      have ha : raw38162step0 = (fun i j => raw38162 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38162step0 raw38162; decide +kernel
      have hl : raw38162step0Labels = raw38162Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38162 raw38162Labels permutation40 permutation7
    mixedMoment B raw38162step0 raw38162step0Labels = mixedMoment B raw38162step1 raw38162step1Labels := by
      have ha : raw38162step1 = -raw38162step0 := by apply Matrix.ext; change ∀ i j, raw38162step1 i j = -(raw38162step0 i j); unfold raw38162step1 raw38162step0; decide +kernel
      have hl : raw38162step1Labels = raw38162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38162step1 raw38162step1Labels = mixedMoment B raw38162step2 raw38162step2Labels := by
      have ha : raw38162step2 = raw38162step1 := by apply Matrix.ext; unfold raw38162step2 raw38162step1; decide +kernel
      have hl : raw38162step1Labels = labelEmbedding4 ∘ raw38162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38162step1 raw38162step1Labels raw38162step2Labels labelEmbedding4 hl
    _ = mixedMoment B node657 node657Labels := by rfl

def raw38163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38163Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38163 raw38163Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw38163 raw38163Labels = mixedMoment B raw38163step0 raw38163step0Labels := by
      have ha : raw38163step0 = raw38163 := by apply Matrix.ext; unfold raw38163step0 raw38163; decide +kernel
      have hl : raw38163Labels = labelEmbedding2 ∘ raw38163step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38163 raw38163Labels raw38163step0Labels labelEmbedding2 hl
    _ = mixedMoment B node537 node537Labels := by rfl

def raw38164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38164Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38164step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38164step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38164 raw38164Labels = mixedMoment B node662 node662Labels := by
  calc
    mixedMoment B raw38164 raw38164Labels = mixedMoment B raw38164step0 raw38164step0Labels := by
      have ha : raw38164step0 = (fun i j => raw38164 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38164step0 raw38164; decide +kernel
      have hl : raw38164step0Labels = raw38164Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38164 raw38164Labels permutation176 permutation7
    mixedMoment B raw38164step0 raw38164step0Labels = mixedMoment B raw38164step1 raw38164step1Labels := by
      have ha : raw38164step1 = -raw38164step0 := by apply Matrix.ext; change ∀ i j, raw38164step1 i j = -(raw38164step0 i j); unfold raw38164step1 raw38164step0; decide +kernel
      have hl : raw38164step1Labels = raw38164step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38164step1 raw38164step1Labels = mixedMoment B raw38164step2 raw38164step2Labels := by
      have ha : raw38164step2 = raw38164step1 := by apply Matrix.ext; unfold raw38164step2 raw38164step1; decide +kernel
      have hl : raw38164step1Labels = labelEmbedding4 ∘ raw38164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38164step1 raw38164step1Labels raw38164step2Labels labelEmbedding4 hl
    _ = mixedMoment B node662 node662Labels := by rfl

def raw38165 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38165Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38165 raw38165Labels = mixedMoment B node538 node538Labels := by
  calc
    mixedMoment B raw38165 raw38165Labels = mixedMoment B raw38165step0 raw38165step0Labels := by
      have ha : raw38165step0 = raw38165 := by apply Matrix.ext; unfold raw38165step0 raw38165; decide +kernel
      have hl : raw38165Labels = labelEmbedding2 ∘ raw38165step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38165 raw38165Labels raw38165step0Labels labelEmbedding2 hl
    _ = mixedMoment B node538 node538Labels := by rfl

def raw38166 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38166Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw38166step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38166step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38166step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38166 raw38166Labels = mixedMoment B node663 node663Labels := by
  calc
    mixedMoment B raw38166 raw38166Labels = mixedMoment B raw38166step0 raw38166step0Labels := by
      have ha : raw38166step0 = (fun i j => raw38166 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38166step0 raw38166; decide +kernel
      have hl : raw38166step0Labels = raw38166Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38166 raw38166Labels permutation38 permutation7
    mixedMoment B raw38166step0 raw38166step0Labels = mixedMoment B raw38166step1 raw38166step1Labels := by
      have ha : raw38166step1 = -raw38166step0 := by apply Matrix.ext; change ∀ i j, raw38166step1 i j = -(raw38166step0 i j); unfold raw38166step1 raw38166step0; decide +kernel
      have hl : raw38166step1Labels = raw38166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38166step1 raw38166step1Labels = mixedMoment B raw38166step2 raw38166step2Labels := by
      have ha : raw38166step2 = raw38166step1 := by apply Matrix.ext; unfold raw38166step2 raw38166step1; decide +kernel
      have hl : raw38166step1Labels = labelEmbedding4 ∘ raw38166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38166step1 raw38166step1Labels raw38166step2Labels labelEmbedding4 hl
    _ = mixedMoment B node663 node663Labels := by rfl

def raw38167 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38167Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38167 raw38167Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw38167 raw38167Labels = mixedMoment B raw38167step0 raw38167step0Labels := by
      have ha : raw38167step0 = raw38167 := by apply Matrix.ext; unfold raw38167step0 raw38167; decide +kernel
      have hl : raw38167Labels = labelEmbedding2 ∘ raw38167step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38167 raw38167Labels raw38167step0Labels labelEmbedding2 hl
    _ = mixedMoment B node539 node539Labels := by rfl

def raw38168 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38168Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw38168step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38168step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38168 raw38168Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw38168 raw38168Labels = mixedMoment B raw38168step0 raw38168step0Labels := by
      have ha : raw38168step0 = (fun i j => raw38168 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38168step0 raw38168; decide +kernel
      have hl : raw38168step0Labels = raw38168Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38168 raw38168Labels permutation38 permutation7
    mixedMoment B raw38168step0 raw38168step0Labels = mixedMoment B raw38168step1 raw38168step1Labels := by
      have ha : raw38168step1 = -raw38168step0 := by apply Matrix.ext; change ∀ i j, raw38168step1 i j = -(raw38168step0 i j); unfold raw38168step1 raw38168step0; decide +kernel
      have hl : raw38168step1Labels = raw38168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38168step1 raw38168step1Labels = mixedMoment B raw38168step2 raw38168step2Labels := by
      have ha : raw38168step2 = raw38168step1 := by apply Matrix.ext; unfold raw38168step2 raw38168step1; decide +kernel
      have hl : raw38168step1Labels = labelEmbedding4 ∘ raw38168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38168step1 raw38168step1Labels raw38168step2Labels labelEmbedding4 hl
    _ = mixedMoment B node664 node664Labels := by rfl

def raw38169 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38169Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38169step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38169 raw38169Labels = mixedMoment B node540 node540Labels := by
  calc
    mixedMoment B raw38169 raw38169Labels = mixedMoment B raw38169step0 raw38169step0Labels := by
      have ha : raw38169step0 = raw38169 := by apply Matrix.ext; unfold raw38169step0 raw38169; decide +kernel
      have hl : raw38169Labels = labelEmbedding2 ∘ raw38169step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38169 raw38169Labels raw38169step0Labels labelEmbedding2 hl
    _ = mixedMoment B node540 node540Labels := by rfl

def raw38170 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38170Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw38170step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw38170step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw38170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38170 raw38170Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw38170 raw38170Labels = mixedMoment B raw38170step0 raw38170step0Labels := by
      have ha : raw38170step0 = (fun i j => raw38170 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38170step0 raw38170; decide +kernel
      have hl : raw38170step0Labels = raw38170Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38170 raw38170Labels permutation10 permutation7
    mixedMoment B raw38170step0 raw38170step0Labels = mixedMoment B raw38170step1 raw38170step1Labels := by
      have ha : raw38170step1 = -raw38170step0 := by apply Matrix.ext; change ∀ i j, raw38170step1 i j = -(raw38170step0 i j); unfold raw38170step1 raw38170step0; decide +kernel
      have hl : raw38170step1Labels = raw38170step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38170step1 raw38170step1Labels = mixedMoment B raw38170step2 raw38170step2Labels := by
      have ha : raw38170step2 = raw38170step1 := by apply Matrix.ext; unfold raw38170step2 raw38170step1; decide +kernel
      have hl : raw38170step1Labels = labelEmbedding4 ∘ raw38170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38170step1 raw38170step1Labels raw38170step2Labels labelEmbedding4 hl
    _ = mixedMoment B node665 node665Labels := by rfl

def raw38171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38171Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38171 raw38171Labels = mixedMoment B node541 node541Labels := by
  calc
    mixedMoment B raw38171 raw38171Labels = mixedMoment B raw38171step0 raw38171step0Labels := by
      have ha : raw38171step0 = raw38171 := by apply Matrix.ext; unfold raw38171step0 raw38171; decide +kernel
      have hl : raw38171Labels = labelEmbedding2 ∘ raw38171step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38171 raw38171Labels raw38171step0Labels labelEmbedding2 hl
    _ = mixedMoment B node541 node541Labels := by rfl

def raw38172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38172Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38172step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38172step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38172step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38172 raw38172Labels = mixedMoment B node674 node674Labels := by
  calc
    mixedMoment B raw38172 raw38172Labels = mixedMoment B raw38172step0 raw38172step0Labels := by
      have ha : raw38172step0 = (fun i j => raw38172 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38172step0 raw38172; decide +kernel
      have hl : raw38172step0Labels = raw38172Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38172 raw38172Labels permutation246 permutation7
    mixedMoment B raw38172step0 raw38172step0Labels = mixedMoment B raw38172step1 raw38172step1Labels := by
      have ha : raw38172step1 = -raw38172step0 := by apply Matrix.ext; change ∀ i j, raw38172step1 i j = -(raw38172step0 i j); unfold raw38172step1 raw38172step0; decide +kernel
      have hl : raw38172step1Labels = raw38172step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38172step1 raw38172step1Labels = mixedMoment B raw38172step2 raw38172step2Labels := by
      have ha : raw38172step2 = raw38172step1 := by apply Matrix.ext; unfold raw38172step2 raw38172step1; decide +kernel
      have hl : raw38172step1Labels = labelEmbedding4 ∘ raw38172step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38172step1 raw38172step1Labels raw38172step2Labels labelEmbedding4 hl
    _ = mixedMoment B node674 node674Labels := by rfl

def raw38173 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38173Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38173 raw38173Labels = mixedMoment B node542 node542Labels := by
  calc
    mixedMoment B raw38173 raw38173Labels = mixedMoment B raw38173step0 raw38173step0Labels := by
      have ha : raw38173step0 = raw38173 := by apply Matrix.ext; unfold raw38173step0 raw38173; decide +kernel
      have hl : raw38173Labels = labelEmbedding2 ∘ raw38173step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38173 raw38173Labels raw38173step0Labels labelEmbedding2 hl
    _ = mixedMoment B node542 node542Labels := by rfl

def raw38174 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38174Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38174step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38174step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38174 raw38174Labels = mixedMoment B node681 node681Labels := by
  calc
    mixedMoment B raw38174 raw38174Labels = mixedMoment B raw38174step0 raw38174step0Labels := by
      have ha : raw38174step0 = (fun i j => raw38174 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38174step0 raw38174; decide +kernel
      have hl : raw38174step0Labels = raw38174Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38174 raw38174Labels permutation32 permutation7
    mixedMoment B raw38174step0 raw38174step0Labels = mixedMoment B raw38174step1 raw38174step1Labels := by
      have ha : raw38174step1 = -raw38174step0 := by apply Matrix.ext; change ∀ i j, raw38174step1 i j = -(raw38174step0 i j); unfold raw38174step1 raw38174step0; decide +kernel
      have hl : raw38174step1Labels = raw38174step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38174step1 raw38174step1Labels = mixedMoment B raw38174step2 raw38174step2Labels := by
      have ha : raw38174step2 = raw38174step1 := by apply Matrix.ext; unfold raw38174step2 raw38174step1; decide +kernel
      have hl : raw38174step1Labels = labelEmbedding4 ∘ raw38174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38174step1 raw38174step1Labels raw38174step2Labels labelEmbedding4 hl
    _ = mixedMoment B node681 node681Labels := by rfl

def raw38175 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38175Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38175 raw38175Labels = mixedMoment B node543 node543Labels := by
  calc
    mixedMoment B raw38175 raw38175Labels = mixedMoment B raw38175step0 raw38175step0Labels := by
      have ha : raw38175step0 = raw38175 := by apply Matrix.ext; unfold raw38175step0 raw38175; decide +kernel
      have hl : raw38175Labels = labelEmbedding2 ∘ raw38175step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38175 raw38175Labels raw38175step0Labels labelEmbedding2 hl
    _ = mixedMoment B node543 node543Labels := by rfl

def raw38176 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38176Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw38176step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38176step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38176 raw38176Labels = mixedMoment B node675 node675Labels := by
  calc
    mixedMoment B raw38176 raw38176Labels = mixedMoment B raw38176step0 raw38176step0Labels := by
      have ha : raw38176step0 = (fun i j => raw38176 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38176step0 raw38176; decide +kernel
      have hl : raw38176step0Labels = raw38176Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38176 raw38176Labels permutation44 permutation7
    mixedMoment B raw38176step0 raw38176step0Labels = mixedMoment B raw38176step1 raw38176step1Labels := by
      have ha : raw38176step1 = -raw38176step0 := by apply Matrix.ext; change ∀ i j, raw38176step1 i j = -(raw38176step0 i j); unfold raw38176step1 raw38176step0; decide +kernel
      have hl : raw38176step1Labels = raw38176step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38176step1 raw38176step1Labels = mixedMoment B raw38176step2 raw38176step2Labels := by
      have ha : raw38176step2 = raw38176step1 := by apply Matrix.ext; unfold raw38176step2 raw38176step1; decide +kernel
      have hl : raw38176step1Labels = labelEmbedding4 ∘ raw38176step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38176step1 raw38176step1Labels raw38176step2Labels labelEmbedding4 hl
    _ = mixedMoment B node675 node675Labels := by rfl

def raw38177 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38177Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38177 raw38177Labels = mixedMoment B node544 node544Labels := by
  calc
    mixedMoment B raw38177 raw38177Labels = mixedMoment B raw38177step0 raw38177step0Labels := by
      have ha : raw38177step0 = raw38177 := by apply Matrix.ext; unfold raw38177step0 raw38177; decide +kernel
      have hl : raw38177Labels = labelEmbedding2 ∘ raw38177step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38177 raw38177Labels raw38177step0Labels labelEmbedding2 hl
    _ = mixedMoment B node544 node544Labels := by rfl

def raw38178 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38178Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38178step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38178step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38178 raw38178Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw38178 raw38178Labels = mixedMoment B raw38178step0 raw38178step0Labels := by
      have ha : raw38178step0 = (fun i j => raw38178 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38178step0 raw38178; decide +kernel
      have hl : raw38178step0Labels = raw38178Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38178 raw38178Labels permutation32 permutation7
    mixedMoment B raw38178step0 raw38178step0Labels = mixedMoment B raw38178step1 raw38178step1Labels := by
      have ha : raw38178step1 = -raw38178step0 := by apply Matrix.ext; change ∀ i j, raw38178step1 i j = -(raw38178step0 i j); unfold raw38178step1 raw38178step0; decide +kernel
      have hl : raw38178step1Labels = raw38178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38178step1 raw38178step1Labels = mixedMoment B raw38178step2 raw38178step2Labels := by
      have ha : raw38178step2 = raw38178step1 := by apply Matrix.ext; unfold raw38178step2 raw38178step1; decide +kernel
      have hl : raw38178step1Labels = labelEmbedding4 ∘ raw38178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38178step1 raw38178step1Labels raw38178step2Labels labelEmbedding4 hl
    _ = mixedMoment B node682 node682Labels := by rfl

def raw38179 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38179Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38179step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38179 raw38179Labels = mixedMoment B node545 node545Labels := by
  calc
    mixedMoment B raw38179 raw38179Labels = mixedMoment B raw38179step0 raw38179step0Labels := by
      have ha : raw38179step0 = raw38179 := by apply Matrix.ext; unfold raw38179step0 raw38179; decide +kernel
      have hl : raw38179Labels = labelEmbedding2 ∘ raw38179step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38179 raw38179Labels raw38179step0Labels labelEmbedding2 hl
    _ = mixedMoment B node545 node545Labels := by rfl

def raw38180 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38180Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38180step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw38180step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw38180step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38180step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw38180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38180 raw38180Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw38180 raw38180Labels = mixedMoment B raw38180step0 raw38180step0Labels := by
      have ha : raw38180step0 = (fun i j => raw38180 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38180step0 raw38180; decide +kernel
      have hl : raw38180step0Labels = raw38180Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38180 raw38180Labels permutation8 permutation7
    mixedMoment B raw38180step0 raw38180step0Labels = mixedMoment B raw38180step1 raw38180step1Labels := by
      have ha : raw38180step1 = -raw38180step0 := by apply Matrix.ext; change ∀ i j, raw38180step1 i j = -(raw38180step0 i j); unfold raw38180step1 raw38180step0; decide +kernel
      have hl : raw38180step1Labels = raw38180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38180step1 raw38180step1Labels = mixedMoment B raw38180step2 raw38180step2Labels := by
      have ha : raw38180step2 = raw38180step1 := by apply Matrix.ext; unfold raw38180step2 raw38180step1; decide +kernel
      have hl : raw38180step1Labels = labelEmbedding4 ∘ raw38180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38180step1 raw38180step1Labels raw38180step2Labels labelEmbedding4 hl
    _ = mixedMoment B node683 node683Labels := by rfl

def raw38181 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38181Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38181step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38181 raw38181Labels = mixedMoment B node546 node546Labels := by
  calc
    mixedMoment B raw38181 raw38181Labels = mixedMoment B raw38181step0 raw38181step0Labels := by
      have ha : raw38181step0 = raw38181 := by apply Matrix.ext; unfold raw38181step0 raw38181; decide +kernel
      have hl : raw38181Labels = labelEmbedding2 ∘ raw38181step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38181 raw38181Labels raw38181step0Labels labelEmbedding2 hl
    _ = mixedMoment B node546 node546Labels := by rfl

def raw38182 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38182Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38182step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw38182step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw38182step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw38182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38182 raw38182Labels = mixedMoment B node676 node676Labels := by
  calc
    mixedMoment B raw38182 raw38182Labels = mixedMoment B raw38182step0 raw38182step0Labels := by
      have ha : raw38182step0 = (fun i j => raw38182 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38182step0 raw38182; decide +kernel
      have hl : raw38182step0Labels = raw38182Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38182 raw38182Labels permutation10 permutation7
    mixedMoment B raw38182step0 raw38182step0Labels = mixedMoment B raw38182step1 raw38182step1Labels := by
      have ha : raw38182step1 = -raw38182step0 := by apply Matrix.ext; change ∀ i j, raw38182step1 i j = -(raw38182step0 i j); unfold raw38182step1 raw38182step0; decide +kernel
      have hl : raw38182step1Labels = raw38182step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38182step1 raw38182step1Labels = mixedMoment B raw38182step2 raw38182step2Labels := by
      have ha : raw38182step2 = raw38182step1 := by apply Matrix.ext; unfold raw38182step2 raw38182step1; decide +kernel
      have hl : raw38182step1Labels = labelEmbedding4 ∘ raw38182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38182step1 raw38182step1Labels raw38182step2Labels labelEmbedding4 hl
    _ = mixedMoment B node676 node676Labels := by rfl

def raw38183 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38183Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38183step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38183 raw38183Labels = mixedMoment B node547 node547Labels := by
  calc
    mixedMoment B raw38183 raw38183Labels = mixedMoment B raw38183step0 raw38183step0Labels := by
      have ha : raw38183step0 = raw38183 := by apply Matrix.ext; unfold raw38183step0 raw38183; decide +kernel
      have hl : raw38183Labels = labelEmbedding2 ∘ raw38183step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38183 raw38183Labels raw38183step0Labels labelEmbedding2 hl
    _ = mixedMoment B node547 node547Labels := by rfl

def raw38184 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38184Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38184step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw38184step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38184step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38184 raw38184Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw38184 raw38184Labels = mixedMoment B raw38184step0 raw38184step0Labels := by
      have ha : raw38184step0 = (fun i j => raw38184 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38184step0 raw38184; decide +kernel
      have hl : raw38184step0Labels = raw38184Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38184 raw38184Labels permutation8 permutation7
    mixedMoment B raw38184step0 raw38184step0Labels = mixedMoment B raw38184step1 raw38184step1Labels := by
      have ha : raw38184step1 = -raw38184step0 := by apply Matrix.ext; change ∀ i j, raw38184step1 i j = -(raw38184step0 i j); unfold raw38184step1 raw38184step0; decide +kernel
      have hl : raw38184step1Labels = raw38184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38184step1 raw38184step1Labels = mixedMoment B raw38184step2 raw38184step2Labels := by
      have ha : raw38184step2 = raw38184step1 := by apply Matrix.ext; unfold raw38184step2 raw38184step1; decide +kernel
      have hl : raw38184step1Labels = labelEmbedding4 ∘ raw38184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38184step1 raw38184step1Labels raw38184step2Labels labelEmbedding4 hl
    _ = mixedMoment B node684 node684Labels := by rfl

def raw38185 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38185Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38185step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38185 raw38185Labels = mixedMoment B node548 node548Labels := by
  calc
    mixedMoment B raw38185 raw38185Labels = mixedMoment B raw38185step0 raw38185step0Labels := by
      have ha : raw38185step0 = raw38185 := by apply Matrix.ext; unfold raw38185step0 raw38185; decide +kernel
      have hl : raw38185Labels = labelEmbedding2 ∘ raw38185step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38185 raw38185Labels raw38185step0Labels labelEmbedding2 hl
    _ = mixedMoment B node548 node548Labels := by rfl

def raw38186 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38186Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38186step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw38186step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38186step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38186 raw38186Labels = mixedMoment B node685 node685Labels := by
  calc
    mixedMoment B raw38186 raw38186Labels = mixedMoment B raw38186step0 raw38186step0Labels := by
      have ha : raw38186step0 = (fun i j => raw38186 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38186step0 raw38186; decide +kernel
      have hl : raw38186step0Labels = raw38186Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38186 raw38186Labels permutation9 permutation7
    mixedMoment B raw38186step0 raw38186step0Labels = mixedMoment B raw38186step1 raw38186step1Labels := by
      have ha : raw38186step1 = -raw38186step0 := by apply Matrix.ext; change ∀ i j, raw38186step1 i j = -(raw38186step0 i j); unfold raw38186step1 raw38186step0; decide +kernel
      have hl : raw38186step1Labels = raw38186step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38186step1 raw38186step1Labels = mixedMoment B raw38186step2 raw38186step2Labels := by
      have ha : raw38186step2 = raw38186step1 := by apply Matrix.ext; unfold raw38186step2 raw38186step1; decide +kernel
      have hl : raw38186step1Labels = labelEmbedding4 ∘ raw38186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38186step1 raw38186step1Labels raw38186step2Labels labelEmbedding4 hl
    _ = mixedMoment B node685 node685Labels := by rfl

def raw38187 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw38187Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38187step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw38187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38187 raw38187Labels = mixedMoment B node549 node549Labels := by
  calc
    mixedMoment B raw38187 raw38187Labels = mixedMoment B raw38187step0 raw38187step0Labels := by
      have ha : raw38187step0 = raw38187 := by apply Matrix.ext; unfold raw38187step0 raw38187; decide +kernel
      have hl : raw38187Labels = labelEmbedding2 ∘ raw38187step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38187 raw38187Labels raw38187step0Labels labelEmbedding2 hl
    _ = mixedMoment B node549 node549Labels := by rfl

def raw38188 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw38188Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38188step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw38188step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38188step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw38188step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38188step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw38188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38188 raw38188Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw38188 raw38188Labels = mixedMoment B raw38188step0 raw38188step0Labels := by
      have ha : raw38188step0 = (fun i j => raw38188 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38188step0 raw38188; decide +kernel
      have hl : raw38188step0Labels = raw38188Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38188 raw38188Labels permutation2 permutation7
    mixedMoment B raw38188step0 raw38188step0Labels = mixedMoment B raw38188step1 raw38188step1Labels := by
      have ha : raw38188step1 = -raw38188step0 := by apply Matrix.ext; change ∀ i j, raw38188step1 i j = -(raw38188step0 i j); unfold raw38188step1 raw38188step0; decide +kernel
      have hl : raw38188step1Labels = raw38188step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38188step1 raw38188step1Labels = mixedMoment B raw38188step2 raw38188step2Labels := by
      have ha : raw38188step2 = raw38188step1 := by apply Matrix.ext; unfold raw38188step2 raw38188step1; decide +kernel
      have hl : raw38188step1Labels = labelEmbedding4 ∘ raw38188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38188step1 raw38188step1Labels raw38188step2Labels labelEmbedding4 hl
    _ = mixedMoment B node686 node686Labels := by rfl

def raw38189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38189Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38189step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38189 raw38189Labels = mixedMoment B node550 node550Labels := by
  calc
    mixedMoment B raw38189 raw38189Labels = mixedMoment B raw38189step0 raw38189step0Labels := by
      have ha : raw38189step0 = raw38189 := by apply Matrix.ext; unfold raw38189step0 raw38189; decide +kernel
      have hl : raw38189Labels = labelEmbedding2 ∘ raw38189step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38189 raw38189Labels raw38189step0Labels labelEmbedding2 hl
    _ = mixedMoment B node550 node550Labels := by rfl

def raw38190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38190Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38190step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38190step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38190step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38190 raw38190Labels = mixedMoment B node658 node658Labels := by
  calc
    mixedMoment B raw38190 raw38190Labels = mixedMoment B raw38190step0 raw38190step0Labels := by
      have ha : raw38190step0 = (fun i j => raw38190 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38190step0 raw38190; decide +kernel
      have hl : raw38190step0Labels = raw38190Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38190 raw38190Labels permutation152 permutation7
    mixedMoment B raw38190step0 raw38190step0Labels = mixedMoment B raw38190step1 raw38190step1Labels := by
      have ha : raw38190step1 = -raw38190step0 := by apply Matrix.ext; change ∀ i j, raw38190step1 i j = -(raw38190step0 i j); unfold raw38190step1 raw38190step0; decide +kernel
      have hl : raw38190step1Labels = raw38190step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38190step1 raw38190step1Labels = mixedMoment B raw38190step2 raw38190step2Labels := by
      have ha : raw38190step2 = raw38190step1 := by apply Matrix.ext; unfold raw38190step2 raw38190step1; decide +kernel
      have hl : raw38190step1Labels = labelEmbedding4 ∘ raw38190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38190step1 raw38190step1Labels raw38190step2Labels labelEmbedding4 hl
    _ = mixedMoment B node658 node658Labels := by rfl

def raw38191 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38191Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38191 raw38191Labels = mixedMoment B node551 node551Labels := by
  calc
    mixedMoment B raw38191 raw38191Labels = mixedMoment B raw38191step0 raw38191step0Labels := by
      have ha : raw38191step0 = raw38191 := by apply Matrix.ext; unfold raw38191step0 raw38191; decide +kernel
      have hl : raw38191Labels = labelEmbedding2 ∘ raw38191step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38191 raw38191Labels raw38191step0Labels labelEmbedding2 hl
    _ = mixedMoment B node551 node551Labels := by rfl

def raw38192 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38192Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw38192step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38192step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38192 raw38192Labels = mixedMoment B node659 node659Labels := by
  calc
    mixedMoment B raw38192 raw38192Labels = mixedMoment B raw38192step0 raw38192step0Labels := by
      have ha : raw38192step0 = (fun i j => raw38192 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38192step0 raw38192; decide +kernel
      have hl : raw38192step0Labels = raw38192Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38192 raw38192Labels permutation32 permutation7
    mixedMoment B raw38192step0 raw38192step0Labels = mixedMoment B raw38192step1 raw38192step1Labels := by
      have ha : raw38192step1 = -raw38192step0 := by apply Matrix.ext; change ∀ i j, raw38192step1 i j = -(raw38192step0 i j); unfold raw38192step1 raw38192step0; decide +kernel
      have hl : raw38192step1Labels = raw38192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38192step1 raw38192step1Labels = mixedMoment B raw38192step2 raw38192step2Labels := by
      have ha : raw38192step2 = raw38192step1 := by apply Matrix.ext; unfold raw38192step2 raw38192step1; decide +kernel
      have hl : raw38192step1Labels = labelEmbedding4 ∘ raw38192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38192step1 raw38192step1Labels raw38192step2Labels labelEmbedding4 hl
    _ = mixedMoment B node659 node659Labels := by rfl

def raw38193 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38193Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38193 raw38193Labels = mixedMoment B node552 node552Labels := by
  calc
    mixedMoment B raw38193 raw38193Labels = mixedMoment B raw38193step0 raw38193step0Labels := by
      have ha : raw38193step0 = raw38193 := by apply Matrix.ext; unfold raw38193step0 raw38193; decide +kernel
      have hl : raw38193Labels = labelEmbedding2 ∘ raw38193step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38193 raw38193Labels raw38193step0Labels labelEmbedding2 hl
    _ = mixedMoment B node552 node552Labels := by rfl

def raw38194 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38194Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw38194step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38194step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38194 raw38194Labels = mixedMoment B node660 node660Labels := by
  calc
    mixedMoment B raw38194 raw38194Labels = mixedMoment B raw38194step0 raw38194step0Labels := by
      have ha : raw38194step0 = (fun i j => raw38194 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38194step0 raw38194; decide +kernel
      have hl : raw38194step0Labels = raw38194Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38194 raw38194Labels permutation32 permutation7
    mixedMoment B raw38194step0 raw38194step0Labels = mixedMoment B raw38194step1 raw38194step1Labels := by
      have ha : raw38194step1 = -raw38194step0 := by apply Matrix.ext; change ∀ i j, raw38194step1 i j = -(raw38194step0 i j); unfold raw38194step1 raw38194step0; decide +kernel
      have hl : raw38194step1Labels = raw38194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38194step1 raw38194step1Labels = mixedMoment B raw38194step2 raw38194step2Labels := by
      have ha : raw38194step2 = raw38194step1 := by apply Matrix.ext; unfold raw38194step2 raw38194step1; decide +kernel
      have hl : raw38194step1Labels = labelEmbedding4 ∘ raw38194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38194step1 raw38194step1Labels raw38194step2Labels labelEmbedding4 hl
    _ = mixedMoment B node660 node660Labels := by rfl

def raw38195 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38195Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38195step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38195 raw38195Labels = mixedMoment B node553 node553Labels := by
  calc
    mixedMoment B raw38195 raw38195Labels = mixedMoment B raw38195step0 raw38195step0Labels := by
      have ha : raw38195step0 = raw38195 := by apply Matrix.ext; unfold raw38195step0 raw38195; decide +kernel
      have hl : raw38195Labels = labelEmbedding2 ∘ raw38195step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38195 raw38195Labels raw38195step0Labels labelEmbedding2 hl
    _ = mixedMoment B node553 node553Labels := by rfl

def raw38196 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38196Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38196step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-4, 1, 3]]
def raw38196step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def raw38196step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38196step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def raw38196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38196 raw38196Labels = mixedMoment B node661 node661Labels := by
  calc
    mixedMoment B raw38196 raw38196Labels = mixedMoment B raw38196step0 raw38196step0Labels := by
      have ha : raw38196step0 = (fun i j => raw38196 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38196step0 raw38196; decide +kernel
      have hl : raw38196step0Labels = raw38196Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38196 raw38196Labels permutation8 permutation7
    mixedMoment B raw38196step0 raw38196step0Labels = mixedMoment B raw38196step1 raw38196step1Labels := by
      have ha : raw38196step1 = -raw38196step0 := by apply Matrix.ext; change ∀ i j, raw38196step1 i j = -(raw38196step0 i j); unfold raw38196step1 raw38196step0; decide +kernel
      have hl : raw38196step1Labels = raw38196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38196step1 raw38196step1Labels = mixedMoment B raw38196step2 raw38196step2Labels := by
      have ha : raw38196step2 = raw38196step1 := by apply Matrix.ext; unfold raw38196step2 raw38196step1; decide +kernel
      have hl : raw38196step1Labels = labelEmbedding4 ∘ raw38196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38196step1 raw38196step1Labels raw38196step2Labels labelEmbedding4 hl
    _ = mixedMoment B node661 node661Labels := by rfl

def raw38197 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38197Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38197 raw38197Labels = mixedMoment B node554 node554Labels := by
  calc
    mixedMoment B raw38197 raw38197Labels = mixedMoment B raw38197step0 raw38197step0Labels := by
      have ha : raw38197step0 = raw38197 := by apply Matrix.ext; unfold raw38197step0 raw38197; decide +kernel
      have hl : raw38197Labels = labelEmbedding2 ∘ raw38197step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38197 raw38197Labels raw38197step0Labels labelEmbedding2 hl
    _ = mixedMoment B node554 node554Labels := by rfl

def raw38198 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38198Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw38198step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38198step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38198 raw38198Labels = mixedMoment B node668 node668Labels := by
  calc
    mixedMoment B raw38198 raw38198Labels = mixedMoment B raw38198step0 raw38198step0Labels := by
      have ha : raw38198step0 = (fun i j => raw38198 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38198step0 raw38198; decide +kernel
      have hl : raw38198step0Labels = raw38198Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38198 raw38198Labels permutation33 permutation7
    mixedMoment B raw38198step0 raw38198step0Labels = mixedMoment B raw38198step1 raw38198step1Labels := by
      have ha : raw38198step1 = -raw38198step0 := by apply Matrix.ext; change ∀ i j, raw38198step1 i j = -(raw38198step0 i j); unfold raw38198step1 raw38198step0; decide +kernel
      have hl : raw38198step1Labels = raw38198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38198step1 raw38198step1Labels = mixedMoment B raw38198step2 raw38198step2Labels := by
      have ha : raw38198step2 = raw38198step1 := by apply Matrix.ext; unfold raw38198step2 raw38198step1; decide +kernel
      have hl : raw38198step1Labels = labelEmbedding4 ∘ raw38198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38198step1 raw38198step1Labels raw38198step2Labels labelEmbedding4 hl
    _ = mixedMoment B node668 node668Labels := by rfl

def raw38199 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38199Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38199step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38199 raw38199Labels = mixedMoment B node555 node555Labels := by
  calc
    mixedMoment B raw38199 raw38199Labels = mixedMoment B raw38199step0 raw38199step0Labels := by
      have ha : raw38199step0 = raw38199 := by apply Matrix.ext; unfold raw38199step0 raw38199; decide +kernel
      have hl : raw38199Labels = labelEmbedding2 ∘ raw38199step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38199 raw38199Labels raw38199step0Labels labelEmbedding2 hl
    _ = mixedMoment B node555 node555Labels := by rfl

def raw38200 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38200Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38200step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw38200step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38200step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38200step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38200 raw38200Labels = mixedMoment B node671 node671Labels := by
  calc
    mixedMoment B raw38200 raw38200Labels = mixedMoment B raw38200step0 raw38200step0Labels := by
      have ha : raw38200step0 = (fun i j => raw38200 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38200step0 raw38200; decide +kernel
      have hl : raw38200step0Labels = raw38200Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38200 raw38200Labels permutation8 permutation7
    mixedMoment B raw38200step0 raw38200step0Labels = mixedMoment B raw38200step1 raw38200step1Labels := by
      have ha : raw38200step1 = -raw38200step0 := by apply Matrix.ext; change ∀ i j, raw38200step1 i j = -(raw38200step0 i j); unfold raw38200step1 raw38200step0; decide +kernel
      have hl : raw38200step1Labels = raw38200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38200step1 raw38200step1Labels = mixedMoment B raw38200step2 raw38200step2Labels := by
      have ha : raw38200step2 = raw38200step1 := by apply Matrix.ext; unfold raw38200step2 raw38200step1; decide +kernel
      have hl : raw38200step1Labels = labelEmbedding4 ∘ raw38200step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38200step1 raw38200step1Labels raw38200step2Labels labelEmbedding4 hl
    _ = mixedMoment B node671 node671Labels := by rfl

def raw38201 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38201Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38201step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38201 raw38201Labels = mixedMoment B node556 node556Labels := by
  calc
    mixedMoment B raw38201 raw38201Labels = mixedMoment B raw38201step0 raw38201step0Labels := by
      have ha : raw38201step0 = raw38201 := by apply Matrix.ext; unfold raw38201step0 raw38201; decide +kernel
      have hl : raw38201Labels = labelEmbedding2 ∘ raw38201step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38201 raw38201Labels raw38201step0Labels labelEmbedding2 hl
    _ = mixedMoment B node556 node556Labels := by rfl

def raw38202 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38202Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38202step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw38202step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw38202step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw38202step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38202 raw38202Labels = mixedMoment B node670 node670Labels := by
  calc
    mixedMoment B raw38202 raw38202Labels = mixedMoment B raw38202step0 raw38202step0Labels := by
      have ha : raw38202step0 = (fun i j => raw38202 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38202step0 raw38202; decide +kernel
      have hl : raw38202step0Labels = raw38202Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38202 raw38202Labels permutation8 permutation7
    mixedMoment B raw38202step0 raw38202step0Labels = mixedMoment B raw38202step1 raw38202step1Labels := by
      have ha : raw38202step1 = -raw38202step0 := by apply Matrix.ext; change ∀ i j, raw38202step1 i j = -(raw38202step0 i j); unfold raw38202step1 raw38202step0; decide +kernel
      have hl : raw38202step1Labels = raw38202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38202step1 raw38202step1Labels = mixedMoment B raw38202step2 raw38202step2Labels := by
      have ha : raw38202step2 = raw38202step1 := by apply Matrix.ext; unfold raw38202step2 raw38202step1; decide +kernel
      have hl : raw38202step1Labels = labelEmbedding4 ∘ raw38202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38202step1 raw38202step1Labels raw38202step2Labels labelEmbedding4 hl
    _ = mixedMoment B node670 node670Labels := by rfl

def raw38203 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38203Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38203 raw38203Labels = mixedMoment B node557 node557Labels := by
  calc
    mixedMoment B raw38203 raw38203Labels = mixedMoment B raw38203step0 raw38203step0Labels := by
      have ha : raw38203step0 = raw38203 := by apply Matrix.ext; unfold raw38203step0 raw38203; decide +kernel
      have hl : raw38203Labels = labelEmbedding2 ∘ raw38203step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38203 raw38203Labels raw38203step0Labels labelEmbedding2 hl
    _ = mixedMoment B node557 node557Labels := by rfl

def raw38204 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38204Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38204step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38204step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38204 raw38204Labels = mixedMoment B node677 node677Labels := by
  calc
    mixedMoment B raw38204 raw38204Labels = mixedMoment B raw38204step0 raw38204step0Labels := by
      have ha : raw38204step0 = (fun i j => raw38204 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38204step0 raw38204; decide +kernel
      have hl : raw38204step0Labels = raw38204Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38204 raw38204Labels permutation50 permutation7
    mixedMoment B raw38204step0 raw38204step0Labels = mixedMoment B raw38204step1 raw38204step1Labels := by
      have ha : raw38204step1 = -raw38204step0 := by apply Matrix.ext; change ∀ i j, raw38204step1 i j = -(raw38204step0 i j); unfold raw38204step1 raw38204step0; decide +kernel
      have hl : raw38204step1Labels = raw38204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38204step1 raw38204step1Labels = mixedMoment B raw38204step2 raw38204step2Labels := by
      have ha : raw38204step2 = raw38204step1 := by apply Matrix.ext; unfold raw38204step2 raw38204step1; decide +kernel
      have hl : raw38204step1Labels = labelEmbedding4 ∘ raw38204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38204step1 raw38204step1Labels raw38204step2Labels labelEmbedding4 hl
    _ = mixedMoment B node677 node677Labels := by rfl

def raw38205 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38205Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38205 raw38205Labels = mixedMoment B node559 node559Labels := by
  calc
    mixedMoment B raw38205 raw38205Labels = mixedMoment B raw38205step0 raw38205step0Labels := by
      have ha : raw38205step0 = raw38205 := by apply Matrix.ext; unfold raw38205step0 raw38205; decide +kernel
      have hl : raw38205Labels = labelEmbedding2 ∘ raw38205step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38205 raw38205Labels raw38205step0Labels labelEmbedding2 hl
    _ = mixedMoment B node559 node559Labels := by rfl

def raw38206 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38206Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38206step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw38206step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38206step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38206step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38206step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38206 raw38206Labels = mixedMoment B node690 node690Labels := by
  calc
    mixedMoment B raw38206 raw38206Labels = mixedMoment B raw38206step0 raw38206step0Labels := by
      have ha : raw38206step0 = (fun i j => raw38206 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38206step0 raw38206; decide +kernel
      have hl : raw38206step0Labels = raw38206Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38206 raw38206Labels permutation9 permutation7
    mixedMoment B raw38206step0 raw38206step0Labels = mixedMoment B raw38206step1 raw38206step1Labels := by
      have ha : raw38206step1 = -raw38206step0 := by apply Matrix.ext; change ∀ i j, raw38206step1 i j = -(raw38206step0 i j); unfold raw38206step1 raw38206step0; decide +kernel
      have hl : raw38206step1Labels = raw38206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38206step1 raw38206step1Labels = mixedMoment B raw38206step2 raw38206step2Labels := by
      have ha : raw38206step2 = raw38206step1 := by apply Matrix.ext; unfold raw38206step2 raw38206step1; decide +kernel
      have hl : raw38206step1Labels = labelEmbedding4 ∘ raw38206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38206step1 raw38206step1Labels raw38206step2Labels labelEmbedding4 hl
    _ = mixedMoment B node690 node690Labels := by rfl

def raw38207 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38207Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38207step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38207 raw38207Labels = mixedMoment B node560 node560Labels := by
  calc
    mixedMoment B raw38207 raw38207Labels = mixedMoment B raw38207step0 raw38207step0Labels := by
      have ha : raw38207step0 = raw38207 := by apply Matrix.ext; unfold raw38207step0 raw38207; decide +kernel
      have hl : raw38207Labels = labelEmbedding2 ∘ raw38207step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38207 raw38207Labels raw38207step0Labels labelEmbedding2 hl
    _ = mixedMoment B node560 node560Labels := by rfl

def raw38208 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38208Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38208step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw38208step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw38208step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw38208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38208 raw38208Labels = mixedMoment B node678 node678Labels := by
  calc
    mixedMoment B raw38208 raw38208Labels = mixedMoment B raw38208step0 raw38208step0Labels := by
      have ha : raw38208step0 = (fun i j => raw38208 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38208step0 raw38208; decide +kernel
      have hl : raw38208step0Labels = raw38208Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38208 raw38208Labels permutation10 permutation7
    mixedMoment B raw38208step0 raw38208step0Labels = mixedMoment B raw38208step1 raw38208step1Labels := by
      have ha : raw38208step1 = -raw38208step0 := by apply Matrix.ext; change ∀ i j, raw38208step1 i j = -(raw38208step0 i j); unfold raw38208step1 raw38208step0; decide +kernel
      have hl : raw38208step1Labels = raw38208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38208step1 raw38208step1Labels = mixedMoment B raw38208step2 raw38208step2Labels := by
      have ha : raw38208step2 = raw38208step1 := by apply Matrix.ext; unfold raw38208step2 raw38208step1; decide +kernel
      have hl : raw38208step1Labels = labelEmbedding4 ∘ raw38208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38208step1 raw38208step1Labels raw38208step2Labels labelEmbedding4 hl
    _ = mixedMoment B node678 node678Labels := by rfl

def raw38209 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38209Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38209step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38209 raw38209Labels = mixedMoment B node562 node562Labels := by
  calc
    mixedMoment B raw38209 raw38209Labels = mixedMoment B raw38209step0 raw38209step0Labels := by
      have ha : raw38209step0 = raw38209 := by apply Matrix.ext; unfold raw38209step0 raw38209; decide +kernel
      have hl : raw38209Labels = labelEmbedding2 ∘ raw38209step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38209 raw38209Labels raw38209step0Labels labelEmbedding2 hl
    _ = mixedMoment B node562 node562Labels := by rfl

def raw38210 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38210Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38210step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw38210step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38210step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38210step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38210 raw38210Labels = mixedMoment B node679 node679Labels := by
  calc
    mixedMoment B raw38210 raw38210Labels = mixedMoment B raw38210step0 raw38210step0Labels := by
      have ha : raw38210step0 = (fun i j => raw38210 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38210step0 raw38210; decide +kernel
      have hl : raw38210step0Labels = raw38210Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38210 raw38210Labels permutation10 permutation7
    mixedMoment B raw38210step0 raw38210step0Labels = mixedMoment B raw38210step1 raw38210step1Labels := by
      have ha : raw38210step1 = -raw38210step0 := by apply Matrix.ext; change ∀ i j, raw38210step1 i j = -(raw38210step0 i j); unfold raw38210step1 raw38210step0; decide +kernel
      have hl : raw38210step1Labels = raw38210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38210step1 raw38210step1Labels = mixedMoment B raw38210step2 raw38210step2Labels := by
      have ha : raw38210step2 = raw38210step1 := by apply Matrix.ext; unfold raw38210step2 raw38210step1; decide +kernel
      have hl : raw38210step1Labels = labelEmbedding4 ∘ raw38210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38210step1 raw38210step1Labels raw38210step2Labels labelEmbedding4 hl
    _ = mixedMoment B node679 node679Labels := by rfl

def raw38211 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38211Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38211step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38211 raw38211Labels = mixedMoment B node563 node563Labels := by
  calc
    mixedMoment B raw38211 raw38211Labels = mixedMoment B raw38211step0 raw38211step0Labels := by
      have ha : raw38211step0 = raw38211 := by apply Matrix.ext; unfold raw38211step0 raw38211; decide +kernel
      have hl : raw38211Labels = labelEmbedding2 ∘ raw38211step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38211 raw38211Labels raw38211step0Labels labelEmbedding2 hl
    _ = mixedMoment B node563 node563Labels := by rfl

def raw38212 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38212Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38212step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw38212step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38212step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38212 raw38212Labels = mixedMoment B node692 node692Labels := by
  calc
    mixedMoment B raw38212 raw38212Labels = mixedMoment B raw38212step0 raw38212step0Labels := by
      have ha : raw38212step0 = (fun i j => raw38212 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38212step0 raw38212; decide +kernel
      have hl : raw38212step0Labels = raw38212Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38212 raw38212Labels permutation11 permutation7
    mixedMoment B raw38212step0 raw38212step0Labels = mixedMoment B raw38212step1 raw38212step1Labels := by
      have ha : raw38212step1 = -raw38212step0 := by apply Matrix.ext; change ∀ i j, raw38212step1 i j = -(raw38212step0 i j); unfold raw38212step1 raw38212step0; decide +kernel
      have hl : raw38212step1Labels = raw38212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38212step1 raw38212step1Labels = mixedMoment B raw38212step2 raw38212step2Labels := by
      have ha : raw38212step2 = raw38212step1 := by apply Matrix.ext; unfold raw38212step2 raw38212step1; decide +kernel
      have hl : raw38212step1Labels = labelEmbedding4 ∘ raw38212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38212step1 raw38212step1Labels raw38212step2Labels labelEmbedding4 hl
    _ = mixedMoment B node692 node692Labels := by rfl

def raw38213 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw38213Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38213step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw38213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38213 raw38213Labels = mixedMoment B node564 node564Labels := by
  calc
    mixedMoment B raw38213 raw38213Labels = mixedMoment B raw38213step0 raw38213step0Labels := by
      have ha : raw38213step0 = raw38213 := by apply Matrix.ext; unfold raw38213step0 raw38213; decide +kernel
      have hl : raw38213Labels = labelEmbedding2 ∘ raw38213step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38213 raw38213Labels raw38213step0Labels labelEmbedding2 hl
    _ = mixedMoment B node564 node564Labels := by rfl

def raw38214 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw38214Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38214step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-2, 1, 1], ![-2, -2, 4]]
def raw38214step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38214step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, -1, -1], ![2, 2, -4]]
def raw38214step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38214step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, -1, -1], ![2, 2, -4]]
def raw38214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38214 raw38214Labels = mixedMoment B node695 node695Labels := by
  calc
    mixedMoment B raw38214 raw38214Labels = mixedMoment B raw38214step0 raw38214step0Labels := by
      have ha : raw38214step0 = (fun i j => raw38214 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38214step0 raw38214; decide +kernel
      have hl : raw38214step0Labels = raw38214Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38214 raw38214Labels permutation2 permutation7
    mixedMoment B raw38214step0 raw38214step0Labels = mixedMoment B raw38214step1 raw38214step1Labels := by
      have ha : raw38214step1 = -raw38214step0 := by apply Matrix.ext; change ∀ i j, raw38214step1 i j = -(raw38214step0 i j); unfold raw38214step1 raw38214step0; decide +kernel
      have hl : raw38214step1Labels = raw38214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38214step1 raw38214step1Labels = mixedMoment B raw38214step2 raw38214step2Labels := by
      have ha : raw38214step2 = raw38214step1 := by apply Matrix.ext; unfold raw38214step2 raw38214step1; decide +kernel
      have hl : raw38214step1Labels = labelEmbedding4 ∘ raw38214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38214step1 raw38214step1Labels raw38214step2Labels labelEmbedding4 hl
    _ = mixedMoment B node695 node695Labels := by rfl

def raw38215 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw38215Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38215step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw38215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38215 raw38215Labels = mixedMoment B node565 node565Labels := by
  calc
    mixedMoment B raw38215 raw38215Labels = mixedMoment B raw38215step0 raw38215step0Labels := by
      have ha : raw38215step0 = raw38215 := by apply Matrix.ext; unfold raw38215step0 raw38215; decide +kernel
      have hl : raw38215Labels = labelEmbedding2 ∘ raw38215step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38215 raw38215Labels raw38215step0Labels labelEmbedding2 hl
    _ = mixedMoment B node565 node565Labels := by rfl

def raw38216 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw38216Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38216step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-4, 1, 3]]
def raw38216step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38216step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![4, -1, -3]]
def raw38216step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38216step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![4, -1, -3]]
def raw38216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38216 raw38216Labels = mixedMoment B node680 node680Labels := by
  calc
    mixedMoment B raw38216 raw38216Labels = mixedMoment B raw38216step0 raw38216step0Labels := by
      have ha : raw38216step0 = (fun i j => raw38216 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38216step0 raw38216; decide +kernel
      have hl : raw38216step0Labels = raw38216Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38216 raw38216Labels permutation2 permutation7
    mixedMoment B raw38216step0 raw38216step0Labels = mixedMoment B raw38216step1 raw38216step1Labels := by
      have ha : raw38216step1 = -raw38216step0 := by apply Matrix.ext; change ∀ i j, raw38216step1 i j = -(raw38216step0 i j); unfold raw38216step1 raw38216step0; decide +kernel
      have hl : raw38216step1Labels = raw38216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38216step1 raw38216step1Labels = mixedMoment B raw38216step2 raw38216step2Labels := by
      have ha : raw38216step2 = raw38216step1 := by apply Matrix.ext; unfold raw38216step2 raw38216step1; decide +kernel
      have hl : raw38216step1Labels = labelEmbedding4 ∘ raw38216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38216step1 raw38216step1Labels raw38216step2Labels labelEmbedding4 hl
    _ = mixedMoment B node680 node680Labels := by rfl

def raw38217 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw38217Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38217step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw38217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38217 raw38217Labels = mixedMoment B node566 node566Labels := by
  calc
    mixedMoment B raw38217 raw38217Labels = mixedMoment B raw38217step0 raw38217step0Labels := by
      have ha : raw38217step0 = raw38217 := by apply Matrix.ext; unfold raw38217step0 raw38217; decide +kernel
      have hl : raw38217Labels = labelEmbedding2 ∘ raw38217step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38217 raw38217Labels raw38217step0Labels labelEmbedding2 hl
    _ = mixedMoment B node566 node566Labels := by rfl

def raw38218 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw38218Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38218step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, -2, 3], ![-3, 1, 2]]
def raw38218step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38218step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 2, -3], ![3, -1, -2]]
def raw38218step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38218step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 2, -3], ![3, -1, -2]]
def raw38218step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38218 raw38218Labels = mixedMoment B node694 node694Labels := by
  calc
    mixedMoment B raw38218 raw38218Labels = mixedMoment B raw38218step0 raw38218step0Labels := by
      have ha : raw38218step0 = (fun i j => raw38218 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38218step0 raw38218; decide +kernel
      have hl : raw38218step0Labels = raw38218Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38218 raw38218Labels permutation3 permutation7
    mixedMoment B raw38218step0 raw38218step0Labels = mixedMoment B raw38218step1 raw38218step1Labels := by
      have ha : raw38218step1 = -raw38218step0 := by apply Matrix.ext; change ∀ i j, raw38218step1 i j = -(raw38218step0 i j); unfold raw38218step1 raw38218step0; decide +kernel
      have hl : raw38218step1Labels = raw38218step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38218step1 raw38218step1Labels = mixedMoment B raw38218step2 raw38218step2Labels := by
      have ha : raw38218step2 = raw38218step1 := by apply Matrix.ext; unfold raw38218step2 raw38218step1; decide +kernel
      have hl : raw38218step1Labels = labelEmbedding4 ∘ raw38218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38218step1 raw38218step1Labels raw38218step2Labels labelEmbedding4 hl
    _ = mixedMoment B node694 node694Labels := by rfl

def raw38219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38219Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38219 raw38219Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw38219 raw38219Labels = mixedMoment B raw38219step0 raw38219step0Labels := by
      have ha : raw38219step0 = raw38219 := by apply Matrix.ext; unfold raw38219step0 raw38219; decide +kernel
      have hl : raw38219Labels = labelEmbedding2 ∘ raw38219step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38219 raw38219Labels raw38219step0Labels labelEmbedding2 hl
    _ = mixedMoment B node567 node567Labels := by rfl

def raw38220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38220Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38220step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38220step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38220step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38220 raw38220Labels = mixedMoment B node1488 node1488Labels := by
  calc
    mixedMoment B raw38220 raw38220Labels = mixedMoment B raw38220step0 raw38220step0Labels := by
      have ha : raw38220step0 = (fun i j => raw38220 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38220step0 raw38220; decide +kernel
      have hl : raw38220step0Labels = raw38220Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38220 raw38220Labels permutation152 permutation7
    mixedMoment B raw38220step0 raw38220step0Labels = mixedMoment B raw38220step1 raw38220step1Labels := by
      have ha : raw38220step1 = -raw38220step0 := by apply Matrix.ext; change ∀ i j, raw38220step1 i j = -(raw38220step0 i j); unfold raw38220step1 raw38220step0; decide +kernel
      have hl : raw38220step1Labels = raw38220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38220step1 raw38220step1Labels = mixedMoment B raw38220step2 raw38220step2Labels := by
      have ha : raw38220step2 = raw38220step1 := by apply Matrix.ext; unfold raw38220step2 raw38220step1; decide +kernel
      have hl : raw38220step1Labels = labelEmbedding4 ∘ raw38220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38220step1 raw38220step1Labels raw38220step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1488 node1488Labels := by rfl

def raw38221 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38221Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38221 raw38221Labels = mixedMoment B node568 node568Labels := by
  calc
    mixedMoment B raw38221 raw38221Labels = mixedMoment B raw38221step0 raw38221step0Labels := by
      have ha : raw38221step0 = raw38221 := by apply Matrix.ext; unfold raw38221step0 raw38221; decide +kernel
      have hl : raw38221Labels = labelEmbedding2 ∘ raw38221step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38221 raw38221Labels raw38221step0Labels labelEmbedding2 hl
    _ = mixedMoment B node568 node568Labels := by rfl

def raw38222 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38222Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw38222step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38222step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38222 raw38222Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw38222 raw38222Labels = mixedMoment B raw38222step0 raw38222step0Labels := by
      have ha : raw38222step0 = (fun i j => raw38222 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38222step0 raw38222; decide +kernel
      have hl : raw38222step0Labels = raw38222Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38222 raw38222Labels permutation32 permutation7
    mixedMoment B raw38222step0 raw38222step0Labels = mixedMoment B raw38222step1 raw38222step1Labels := by
      have ha : raw38222step1 = -raw38222step0 := by apply Matrix.ext; change ∀ i j, raw38222step1 i j = -(raw38222step0 i j); unfold raw38222step1 raw38222step0; decide +kernel
      have hl : raw38222step1Labels = raw38222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38222step1 raw38222step1Labels = mixedMoment B raw38222step2 raw38222step2Labels := by
      have ha : raw38222step2 = raw38222step1 := by apply Matrix.ext; unfold raw38222step2 raw38222step1; decide +kernel
      have hl : raw38222step1Labels = labelEmbedding4 ∘ raw38222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38222step1 raw38222step1Labels raw38222step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1489 node1489Labels := by rfl

def raw38223 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38223Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38223 raw38223Labels = mixedMoment B node569 node569Labels := by
  calc
    mixedMoment B raw38223 raw38223Labels = mixedMoment B raw38223step0 raw38223step0Labels := by
      have ha : raw38223step0 = raw38223 := by apply Matrix.ext; unfold raw38223step0 raw38223; decide +kernel
      have hl : raw38223Labels = labelEmbedding2 ∘ raw38223step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38223 raw38223Labels raw38223step0Labels labelEmbedding2 hl
    _ = mixedMoment B node569 node569Labels := by rfl

def raw38224 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38224Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38224step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38224step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38224 raw38224Labels = mixedMoment B node1490 node1490Labels := by
  calc
    mixedMoment B raw38224 raw38224Labels = mixedMoment B raw38224step0 raw38224step0Labels := by
      have ha : raw38224step0 = (fun i j => raw38224 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38224step0 raw38224; decide +kernel
      have hl : raw38224step0Labels = raw38224Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38224 raw38224Labels permutation32 permutation7
    mixedMoment B raw38224step0 raw38224step0Labels = mixedMoment B raw38224step1 raw38224step1Labels := by
      have ha : raw38224step1 = -raw38224step0 := by apply Matrix.ext; change ∀ i j, raw38224step1 i j = -(raw38224step0 i j); unfold raw38224step1 raw38224step0; decide +kernel
      have hl : raw38224step1Labels = raw38224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38224step1 raw38224step1Labels = mixedMoment B raw38224step2 raw38224step2Labels := by
      have ha : raw38224step2 = raw38224step1 := by apply Matrix.ext; unfold raw38224step2 raw38224step1; decide +kernel
      have hl : raw38224step1Labels = labelEmbedding4 ∘ raw38224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38224step1 raw38224step1Labels raw38224step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1490 node1490Labels := by rfl

def raw38225 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw38225Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38225step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw38225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38225 raw38225Labels = mixedMoment B node570 node570Labels := by
  calc
    mixedMoment B raw38225 raw38225Labels = mixedMoment B raw38225step0 raw38225step0Labels := by
      have ha : raw38225step0 = raw38225 := by apply Matrix.ext; unfold raw38225step0 raw38225; decide +kernel
      have hl : raw38225Labels = labelEmbedding2 ∘ raw38225step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38225 raw38225Labels raw38225step0Labels labelEmbedding2 hl
    _ = mixedMoment B node570 node570Labels := by rfl

def raw38226 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw38226Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38226step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw38226step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw38226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38226 raw38226Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw38226 raw38226Labels = mixedMoment B raw38226step0 raw38226step0Labels := by
      have ha : raw38226step0 = (fun i j => raw38226 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38226step0 raw38226; decide +kernel
      have hl : raw38226step0Labels = raw38226Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38226 raw38226Labels permutation31 permutation7
    mixedMoment B raw38226step0 raw38226step0Labels = mixedMoment B raw38226step1 raw38226step1Labels := by
      have ha : raw38226step1 = raw38226step0 := by apply Matrix.ext; unfold raw38226step1 raw38226step0; decide +kernel
      have hl : raw38226step0Labels = labelEmbedding4 ∘ raw38226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38226step0 raw38226step0Labels raw38226step1Labels labelEmbedding4 hl
    _ = mixedMoment B node765 node765Labels := by rfl

def raw38227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38227Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38227 raw38227Labels = mixedMoment B node571 node571Labels := by
  calc
    mixedMoment B raw38227 raw38227Labels = mixedMoment B raw38227step0 raw38227step0Labels := by
      have ha : raw38227step0 = raw38227 := by apply Matrix.ext; unfold raw38227step0 raw38227; decide +kernel
      have hl : raw38227Labels = labelEmbedding2 ∘ raw38227step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38227 raw38227Labels raw38227step0Labels labelEmbedding2 hl
    _ = mixedMoment B node571 node571Labels := by rfl

def raw38228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38228Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38228step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38228step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38228step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38228 raw38228Labels = mixedMoment B node1491 node1491Labels := by
  calc
    mixedMoment B raw38228 raw38228Labels = mixedMoment B raw38228step0 raw38228step0Labels := by
      have ha : raw38228step0 = (fun i j => raw38228 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38228step0 raw38228; decide +kernel
      have hl : raw38228step0Labels = raw38228Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38228 raw38228Labels permutation152 permutation7
    mixedMoment B raw38228step0 raw38228step0Labels = mixedMoment B raw38228step1 raw38228step1Labels := by
      have ha : raw38228step1 = -raw38228step0 := by apply Matrix.ext; change ∀ i j, raw38228step1 i j = -(raw38228step0 i j); unfold raw38228step1 raw38228step0; decide +kernel
      have hl : raw38228step1Labels = raw38228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38228step1 raw38228step1Labels = mixedMoment B raw38228step2 raw38228step2Labels := by
      have ha : raw38228step2 = raw38228step1 := by apply Matrix.ext; unfold raw38228step2 raw38228step1; decide +kernel
      have hl : raw38228step1Labels = labelEmbedding4 ∘ raw38228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38228step1 raw38228step1Labels raw38228step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1491 node1491Labels := by rfl

def raw38229 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38229Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38229 raw38229Labels = mixedMoment B node572 node572Labels := by
  calc
    mixedMoment B raw38229 raw38229Labels = mixedMoment B raw38229step0 raw38229step0Labels := by
      have ha : raw38229step0 = raw38229 := by apply Matrix.ext; unfold raw38229step0 raw38229; decide +kernel
      have hl : raw38229Labels = labelEmbedding2 ∘ raw38229step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38229 raw38229Labels raw38229step0Labels labelEmbedding2 hl
    _ = mixedMoment B node572 node572Labels := by rfl

def raw38230 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38230Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38230step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38230step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38230step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38230 raw38230Labels = mixedMoment B node1492 node1492Labels := by
  calc
    mixedMoment B raw38230 raw38230Labels = mixedMoment B raw38230step0 raw38230step0Labels := by
      have ha : raw38230step0 = (fun i j => raw38230 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38230step0 raw38230; decide +kernel
      have hl : raw38230step0Labels = raw38230Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38230 raw38230Labels permutation32 permutation7
    mixedMoment B raw38230step0 raw38230step0Labels = mixedMoment B raw38230step1 raw38230step1Labels := by
      have ha : raw38230step1 = -raw38230step0 := by apply Matrix.ext; change ∀ i j, raw38230step1 i j = -(raw38230step0 i j); unfold raw38230step1 raw38230step0; decide +kernel
      have hl : raw38230step1Labels = raw38230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38230step1 raw38230step1Labels = mixedMoment B raw38230step2 raw38230step2Labels := by
      have ha : raw38230step2 = raw38230step1 := by apply Matrix.ext; unfold raw38230step2 raw38230step1; decide +kernel
      have hl : raw38230step1Labels = labelEmbedding4 ∘ raw38230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38230step1 raw38230step1Labels raw38230step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1492 node1492Labels := by rfl

def raw38231 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38231Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38231 raw38231Labels = mixedMoment B node573 node573Labels := by
  calc
    mixedMoment B raw38231 raw38231Labels = mixedMoment B raw38231step0 raw38231step0Labels := by
      have ha : raw38231step0 = raw38231 := by apply Matrix.ext; unfold raw38231step0 raw38231; decide +kernel
      have hl : raw38231Labels = labelEmbedding2 ∘ raw38231step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38231 raw38231Labels raw38231step0Labels labelEmbedding2 hl
    _ = mixedMoment B node573 node573Labels := by rfl

def raw38232 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38232Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38232step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38232step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38232 raw38232Labels = mixedMoment B node1493 node1493Labels := by
  calc
    mixedMoment B raw38232 raw38232Labels = mixedMoment B raw38232step0 raw38232step0Labels := by
      have ha : raw38232step0 = (fun i j => raw38232 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38232step0 raw38232; decide +kernel
      have hl : raw38232step0Labels = raw38232Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38232 raw38232Labels permutation32 permutation7
    mixedMoment B raw38232step0 raw38232step0Labels = mixedMoment B raw38232step1 raw38232step1Labels := by
      have ha : raw38232step1 = -raw38232step0 := by apply Matrix.ext; change ∀ i j, raw38232step1 i j = -(raw38232step0 i j); unfold raw38232step1 raw38232step0; decide +kernel
      have hl : raw38232step1Labels = raw38232step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38232step1 raw38232step1Labels = mixedMoment B raw38232step2 raw38232step2Labels := by
      have ha : raw38232step2 = raw38232step1 := by apply Matrix.ext; unfold raw38232step2 raw38232step1; decide +kernel
      have hl : raw38232step1Labels = labelEmbedding4 ∘ raw38232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38232step1 raw38232step1Labels raw38232step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1493 node1493Labels := by rfl

def raw38233 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw38233Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38233step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw38233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38233 raw38233Labels = mixedMoment B node574 node574Labels := by
  calc
    mixedMoment B raw38233 raw38233Labels = mixedMoment B raw38233step0 raw38233step0Labels := by
      have ha : raw38233step0 = raw38233 := by apply Matrix.ext; unfold raw38233step0 raw38233; decide +kernel
      have hl : raw38233Labels = labelEmbedding2 ∘ raw38233step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38233 raw38233Labels raw38233step0Labels labelEmbedding2 hl
    _ = mixedMoment B node574 node574Labels := by rfl

def raw38234 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw38234Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38234step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-3, -1, 4]]
def raw38234step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw38234step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw38234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38234 raw38234Labels = mixedMoment B node1494 node1494Labels := by
  calc
    mixedMoment B raw38234 raw38234Labels = mixedMoment B raw38234step0 raw38234step0Labels := by
      have ha : raw38234step0 = (fun i j => raw38234 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38234step0 raw38234; decide +kernel
      have hl : raw38234step0Labels = raw38234Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38234 raw38234Labels permutation8 permutation7
    mixedMoment B raw38234step0 raw38234step0Labels = mixedMoment B raw38234step1 raw38234step1Labels := by
      have ha : raw38234step1 = -raw38234step0 := by apply Matrix.ext; change ∀ i j, raw38234step1 i j = -(raw38234step0 i j); unfold raw38234step1 raw38234step0; decide +kernel
      have hl : raw38234step1Labels = raw38234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38234step1 raw38234step1Labels = mixedMoment B raw38234step2 raw38234step2Labels := by
      have ha : raw38234step2 = raw38234step1 := by apply Matrix.ext; unfold raw38234step2 raw38234step1; decide +kernel
      have hl : raw38234step1Labels = labelEmbedding4 ∘ raw38234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38234step1 raw38234step1Labels raw38234step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1494 node1494Labels := by rfl

def raw38235 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw38235Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38235step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw38235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38235 raw38235Labels = mixedMoment B node575 node575Labels := by
  calc
    mixedMoment B raw38235 raw38235Labels = mixedMoment B raw38235step0 raw38235step0Labels := by
      have ha : raw38235step0 = raw38235 := by apply Matrix.ext; unfold raw38235step0 raw38235; decide +kernel
      have hl : raw38235Labels = labelEmbedding2 ∘ raw38235step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38235 raw38235Labels raw38235step0Labels labelEmbedding2 hl
    _ = mixedMoment B node575 node575Labels := by rfl

def raw38236 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw38236Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38236step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw38236step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw38236step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38236step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw38236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38236 raw38236Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw38236 raw38236Labels = mixedMoment B raw38236step0 raw38236step0Labels := by
      have ha : raw38236step0 = (fun i j => raw38236 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38236step0 raw38236; decide +kernel
      have hl : raw38236step0Labels = raw38236Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38236 raw38236Labels permutation8 permutation7
    mixedMoment B raw38236step0 raw38236step0Labels = mixedMoment B raw38236step1 raw38236step1Labels := by
      have ha : raw38236step1 = -raw38236step0 := by apply Matrix.ext; change ∀ i j, raw38236step1 i j = -(raw38236step0 i j); unfold raw38236step1 raw38236step0; decide +kernel
      have hl : raw38236step1Labels = raw38236step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38236step1 raw38236step1Labels = mixedMoment B raw38236step2 raw38236step2Labels := by
      have ha : raw38236step2 = raw38236step1 := by apply Matrix.ext; unfold raw38236step2 raw38236step1; decide +kernel
      have hl : raw38236step1Labels = labelEmbedding4 ∘ raw38236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38236step1 raw38236step1Labels raw38236step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1495 node1495Labels := by rfl

def raw38237 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38237Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38237step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38237step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38237 raw38237Labels = mixedMoment B node576 node576Labels := by
  calc
    mixedMoment B raw38237 raw38237Labels = mixedMoment B raw38237step0 raw38237step0Labels := by
      have ha : raw38237step0 = raw38237 := by apply Matrix.ext; unfold raw38237step0 raw38237; decide +kernel
      have hl : raw38237Labels = labelEmbedding2 ∘ raw38237step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38237 raw38237Labels raw38237step0Labels labelEmbedding2 hl
    _ = mixedMoment B node576 node576Labels := by rfl

def raw38238 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38238Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38238step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw38238step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw38238step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38238step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw38238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38238 raw38238Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw38238 raw38238Labels = mixedMoment B raw38238step0 raw38238step0Labels := by
      have ha : raw38238step0 = (fun i j => raw38238 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38238step0 raw38238; decide +kernel
      have hl : raw38238step0Labels = raw38238Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38238 raw38238Labels permutation8 permutation7
    mixedMoment B raw38238step0 raw38238step0Labels = mixedMoment B raw38238step1 raw38238step1Labels := by
      have ha : raw38238step1 = -raw38238step0 := by apply Matrix.ext; change ∀ i j, raw38238step1 i j = -(raw38238step0 i j); unfold raw38238step1 raw38238step0; decide +kernel
      have hl : raw38238step1Labels = raw38238step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38238step1 raw38238step1Labels = mixedMoment B raw38238step2 raw38238step2Labels := by
      have ha : raw38238step2 = raw38238step1 := by apply Matrix.ext; unfold raw38238step2 raw38238step1; decide +kernel
      have hl : raw38238step1Labels = labelEmbedding4 ∘ raw38238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38238step1 raw38238step1Labels raw38238step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1496 node1496Labels := by rfl

def raw38239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38239Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38239 raw38239Labels = mixedMoment B node592 node592Labels := by
  calc
    mixedMoment B raw38239 raw38239Labels = mixedMoment B raw38239step0 raw38239step0Labels := by
      have ha : raw38239step0 = raw38239 := by apply Matrix.ext; unfold raw38239step0 raw38239; decide +kernel
      have hl : raw38239Labels = labelEmbedding2 ∘ raw38239step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38239 raw38239Labels raw38239step0Labels labelEmbedding2 hl
    _ = mixedMoment B node592 node592Labels := by rfl

def raw38240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38240Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38240step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38240step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38240step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38240step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38240 raw38240Labels = mixedMoment B node1497 node1497Labels := by
  calc
    mixedMoment B raw38240 raw38240Labels = mixedMoment B raw38240step0 raw38240step0Labels := by
      have ha : raw38240step0 = (fun i j => raw38240 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38240step0 raw38240; decide +kernel
      have hl : raw38240step0Labels = raw38240Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38240 raw38240Labels permutation152 permutation7
    mixedMoment B raw38240step0 raw38240step0Labels = mixedMoment B raw38240step1 raw38240step1Labels := by
      have ha : raw38240step1 = -raw38240step0 := by apply Matrix.ext; change ∀ i j, raw38240step1 i j = -(raw38240step0 i j); unfold raw38240step1 raw38240step0; decide +kernel
      have hl : raw38240step1Labels = raw38240step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38240step1 raw38240step1Labels = mixedMoment B raw38240step2 raw38240step2Labels := by
      have ha : raw38240step2 = raw38240step1 := by apply Matrix.ext; unfold raw38240step2 raw38240step1; decide +kernel
      have hl : raw38240step1Labels = labelEmbedding4 ∘ raw38240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38240step1 raw38240step1Labels raw38240step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1497 node1497Labels := by rfl

def raw38241 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38241Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38241 raw38241Labels = mixedMoment B node593 node593Labels := by
  calc
    mixedMoment B raw38241 raw38241Labels = mixedMoment B raw38241step0 raw38241step0Labels := by
      have ha : raw38241step0 = raw38241 := by apply Matrix.ext; unfold raw38241step0 raw38241; decide +kernel
      have hl : raw38241Labels = labelEmbedding2 ∘ raw38241step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38241 raw38241Labels raw38241step0Labels labelEmbedding2 hl
    _ = mixedMoment B node593 node593Labels := by rfl

def raw38242 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38242Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38242step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38242step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38242 raw38242Labels = mixedMoment B node1498 node1498Labels := by
  calc
    mixedMoment B raw38242 raw38242Labels = mixedMoment B raw38242step0 raw38242step0Labels := by
      have ha : raw38242step0 = (fun i j => raw38242 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38242step0 raw38242; decide +kernel
      have hl : raw38242step0Labels = raw38242Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38242 raw38242Labels permutation32 permutation7
    mixedMoment B raw38242step0 raw38242step0Labels = mixedMoment B raw38242step1 raw38242step1Labels := by
      have ha : raw38242step1 = -raw38242step0 := by apply Matrix.ext; change ∀ i j, raw38242step1 i j = -(raw38242step0 i j); unfold raw38242step1 raw38242step0; decide +kernel
      have hl : raw38242step1Labels = raw38242step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38242step1 raw38242step1Labels = mixedMoment B raw38242step2 raw38242step2Labels := by
      have ha : raw38242step2 = raw38242step1 := by apply Matrix.ext; unfold raw38242step2 raw38242step1; decide +kernel
      have hl : raw38242step1Labels = labelEmbedding4 ∘ raw38242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38242step1 raw38242step1Labels raw38242step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1498 node1498Labels := by rfl

def raw38243 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38243Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38243step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38243step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38243 raw38243Labels = mixedMoment B node594 node594Labels := by
  calc
    mixedMoment B raw38243 raw38243Labels = mixedMoment B raw38243step0 raw38243step0Labels := by
      have ha : raw38243step0 = raw38243 := by apply Matrix.ext; unfold raw38243step0 raw38243; decide +kernel
      have hl : raw38243Labels = labelEmbedding2 ∘ raw38243step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38243 raw38243Labels raw38243step0Labels labelEmbedding2 hl
    _ = mixedMoment B node594 node594Labels := by rfl

def raw38244 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38244Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38244step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw38244step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38244step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38244step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38244 raw38244Labels = mixedMoment B node1499 node1499Labels := by
  calc
    mixedMoment B raw38244 raw38244Labels = mixedMoment B raw38244step0 raw38244step0Labels := by
      have ha : raw38244step0 = (fun i j => raw38244 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38244step0 raw38244; decide +kernel
      have hl : raw38244step0Labels = raw38244Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38244 raw38244Labels permutation8 permutation7
    mixedMoment B raw38244step0 raw38244step0Labels = mixedMoment B raw38244step1 raw38244step1Labels := by
      have ha : raw38244step1 = -raw38244step0 := by apply Matrix.ext; change ∀ i j, raw38244step1 i j = -(raw38244step0 i j); unfold raw38244step1 raw38244step0; decide +kernel
      have hl : raw38244step1Labels = raw38244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38244step1 raw38244step1Labels = mixedMoment B raw38244step2 raw38244step2Labels := by
      have ha : raw38244step2 = raw38244step1 := by apply Matrix.ext; unfold raw38244step2 raw38244step1; decide +kernel
      have hl : raw38244step1Labels = labelEmbedding4 ∘ raw38244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38244step1 raw38244step1Labels raw38244step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1499 node1499Labels := by rfl

def raw38245 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38245Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38245 raw38245Labels = mixedMoment B node595 node595Labels := by
  calc
    mixedMoment B raw38245 raw38245Labels = mixedMoment B raw38245step0 raw38245step0Labels := by
      have ha : raw38245step0 = raw38245 := by apply Matrix.ext; unfold raw38245step0 raw38245; decide +kernel
      have hl : raw38245Labels = labelEmbedding2 ∘ raw38245step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38245 raw38245Labels raw38245step0Labels labelEmbedding2 hl
    _ = mixedMoment B node595 node595Labels := by rfl

def raw38246 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38246Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38246step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38246step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38246step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38246 raw38246Labels = mixedMoment B node1500 node1500Labels := by
  calc
    mixedMoment B raw38246 raw38246Labels = mixedMoment B raw38246step0 raw38246step0Labels := by
      have ha : raw38246step0 = (fun i j => raw38246 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38246step0 raw38246; decide +kernel
      have hl : raw38246step0Labels = raw38246Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38246 raw38246Labels permutation8 permutation7
    mixedMoment B raw38246step0 raw38246step0Labels = mixedMoment B raw38246step1 raw38246step1Labels := by
      have ha : raw38246step1 = -raw38246step0 := by apply Matrix.ext; change ∀ i j, raw38246step1 i j = -(raw38246step0 i j); unfold raw38246step1 raw38246step0; decide +kernel
      have hl : raw38246step1Labels = raw38246step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38246step1 raw38246step1Labels = mixedMoment B raw38246step2 raw38246step2Labels := by
      have ha : raw38246step2 = raw38246step1 := by apply Matrix.ext; unfold raw38246step2 raw38246step1; decide +kernel
      have hl : raw38246step1Labels = labelEmbedding4 ∘ raw38246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38246step1 raw38246step1Labels raw38246step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1500 node1500Labels := by rfl

def raw38247 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw38247Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38247step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw38247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38247 raw38247Labels = mixedMoment B node596 node596Labels := by
  calc
    mixedMoment B raw38247 raw38247Labels = mixedMoment B raw38247step0 raw38247step0Labels := by
      have ha : raw38247step0 = raw38247 := by apply Matrix.ext; unfold raw38247step0 raw38247; decide +kernel
      have hl : raw38247Labels = labelEmbedding2 ∘ raw38247step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38247 raw38247Labels raw38247step0Labels labelEmbedding2 hl
    _ = mixedMoment B node596 node596Labels := by rfl

def raw38248 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw38248Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38248step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw38248step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38248step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw38248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38248 raw38248Labels = mixedMoment B node845 node845Labels := by
  calc
    mixedMoment B raw38248 raw38248Labels = mixedMoment B raw38248step0 raw38248step0Labels := by
      have ha : raw38248step0 = (fun i j => raw38248 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38248step0 raw38248; decide +kernel
      have hl : raw38248step0Labels = raw38248Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38248 raw38248Labels permutation7 permutation7
    mixedMoment B raw38248step0 raw38248step0Labels = mixedMoment B raw38248step1 raw38248step1Labels := by
      have ha : raw38248step1 = raw38248step0 := by apply Matrix.ext; unfold raw38248step1 raw38248step0; decide +kernel
      have hl : raw38248step0Labels = labelEmbedding4 ∘ raw38248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38248step0 raw38248step0Labels raw38248step1Labels labelEmbedding4 hl
    _ = mixedMoment B node845 node845Labels := by rfl

def raw38249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38249Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38249 raw38249Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw38249 raw38249Labels = mixedMoment B raw38249step0 raw38249step0Labels := by
      have ha : raw38249step0 = raw38249 := by apply Matrix.ext; unfold raw38249step0 raw38249; decide +kernel
      have hl : raw38249Labels = labelEmbedding2 ∘ raw38249step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38249 raw38249Labels raw38249step0Labels labelEmbedding2 hl
    _ = mixedMoment B node599 node599Labels := by rfl

def raw38250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38250Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38250step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38250step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38250step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38250 raw38250Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw38250 raw38250Labels = mixedMoment B raw38250step0 raw38250step0Labels := by
      have ha : raw38250step0 = (fun i j => raw38250 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38250step0 raw38250; decide +kernel
      have hl : raw38250step0Labels = raw38250Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38250 raw38250Labels permutation152 permutation7
    mixedMoment B raw38250step0 raw38250step0Labels = mixedMoment B raw38250step1 raw38250step1Labels := by
      have ha : raw38250step1 = -raw38250step0 := by apply Matrix.ext; change ∀ i j, raw38250step1 i j = -(raw38250step0 i j); unfold raw38250step1 raw38250step0; decide +kernel
      have hl : raw38250step1Labels = raw38250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38250step1 raw38250step1Labels = mixedMoment B raw38250step2 raw38250step2Labels := by
      have ha : raw38250step2 = raw38250step1 := by apply Matrix.ext; unfold raw38250step2 raw38250step1; decide +kernel
      have hl : raw38250step1Labels = labelEmbedding4 ∘ raw38250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38250step1 raw38250step1Labels raw38250step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw38251 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38251Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38251 raw38251Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw38251 raw38251Labels = mixedMoment B raw38251step0 raw38251step0Labels := by
      have ha : raw38251step0 = raw38251 := by apply Matrix.ext; unfold raw38251step0 raw38251; decide +kernel
      have hl : raw38251Labels = labelEmbedding2 ∘ raw38251step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38251 raw38251Labels raw38251step0Labels labelEmbedding2 hl
    _ = mixedMoment B node600 node600Labels := by rfl

def raw38252 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38252Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38252step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38252step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38252step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38252 raw38252Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw38252 raw38252Labels = mixedMoment B raw38252step0 raw38252step0Labels := by
      have ha : raw38252step0 = (fun i j => raw38252 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38252step0 raw38252; decide +kernel
      have hl : raw38252step0Labels = raw38252Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38252 raw38252Labels permutation32 permutation7
    mixedMoment B raw38252step0 raw38252step0Labels = mixedMoment B raw38252step1 raw38252step1Labels := by
      have ha : raw38252step1 = -raw38252step0 := by apply Matrix.ext; change ∀ i j, raw38252step1 i j = -(raw38252step0 i j); unfold raw38252step1 raw38252step0; decide +kernel
      have hl : raw38252step1Labels = raw38252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38252step1 raw38252step1Labels = mixedMoment B raw38252step2 raw38252step2Labels := by
      have ha : raw38252step2 = raw38252step1 := by apply Matrix.ext; unfold raw38252step2 raw38252step1; decide +kernel
      have hl : raw38252step1Labels = labelEmbedding4 ∘ raw38252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38252step1 raw38252step1Labels raw38252step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1507 node1507Labels := by rfl

def raw38253 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38253Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38253step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38253 raw38253Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw38253 raw38253Labels = mixedMoment B raw38253step0 raw38253step0Labels := by
      have ha : raw38253step0 = raw38253 := by apply Matrix.ext; unfold raw38253step0 raw38253; decide +kernel
      have hl : raw38253Labels = labelEmbedding2 ∘ raw38253step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38253 raw38253Labels raw38253step0Labels labelEmbedding2 hl
    _ = mixedMoment B node602 node602Labels := by rfl

def raw38254 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38254Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38254step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw38254step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw38254step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38254step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw38254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38254 raw38254Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw38254 raw38254Labels = mixedMoment B raw38254step0 raw38254step0Labels := by
      have ha : raw38254step0 = (fun i j => raw38254 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38254step0 raw38254; decide +kernel
      have hl : raw38254step0Labels = raw38254Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38254 raw38254Labels permutation8 permutation7
    mixedMoment B raw38254step0 raw38254step0Labels = mixedMoment B raw38254step1 raw38254step1Labels := by
      have ha : raw38254step1 = -raw38254step0 := by apply Matrix.ext; change ∀ i j, raw38254step1 i j = -(raw38254step0 i j); unfold raw38254step1 raw38254step0; decide +kernel
      have hl : raw38254step1Labels = raw38254step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38254step1 raw38254step1Labels = mixedMoment B raw38254step2 raw38254step2Labels := by
      have ha : raw38254step2 = raw38254step1 := by apply Matrix.ext; unfold raw38254step2 raw38254step1; decide +kernel
      have hl : raw38254step1Labels = labelEmbedding4 ∘ raw38254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38254step1 raw38254step1Labels raw38254step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

def raw38255 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38255Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38255 raw38255Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw38255 raw38255Labels = mixedMoment B raw38255step0 raw38255step0Labels := by
      have ha : raw38255step0 = raw38255 := by apply Matrix.ext; unfold raw38255step0 raw38255; decide +kernel
      have hl : raw38255Labels = labelEmbedding2 ∘ raw38255step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38255 raw38255Labels raw38255step0Labels labelEmbedding2 hl
    _ = mixedMoment B node603 node603Labels := by rfl

def raw38256 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38256Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38256step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38256step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38256 raw38256Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw38256 raw38256Labels = mixedMoment B raw38256step0 raw38256step0Labels := by
      have ha : raw38256step0 = (fun i j => raw38256 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38256step0 raw38256; decide +kernel
      have hl : raw38256step0Labels = raw38256Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38256 raw38256Labels permutation32 permutation7
    mixedMoment B raw38256step0 raw38256step0Labels = mixedMoment B raw38256step1 raw38256step1Labels := by
      have ha : raw38256step1 = -raw38256step0 := by apply Matrix.ext; change ∀ i j, raw38256step1 i j = -(raw38256step0 i j); unfold raw38256step1 raw38256step0; decide +kernel
      have hl : raw38256step1Labels = raw38256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38256step1 raw38256step1Labels = mixedMoment B raw38256step2 raw38256step2Labels := by
      have ha : raw38256step2 = raw38256step1 := by apply Matrix.ext; unfold raw38256step2 raw38256step1; decide +kernel
      have hl : raw38256step1Labels = labelEmbedding4 ∘ raw38256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38256step1 raw38256step1Labels raw38256step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1517 node1517Labels := by rfl

def raw38257 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38257Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38257step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38257 raw38257Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw38257 raw38257Labels = mixedMoment B raw38257step0 raw38257step0Labels := by
      have ha : raw38257step0 = raw38257 := by apply Matrix.ext; unfold raw38257step0 raw38257; decide +kernel
      have hl : raw38257Labels = labelEmbedding2 ∘ raw38257step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38257 raw38257Labels raw38257step0Labels labelEmbedding2 hl
    _ = mixedMoment B node605 node605Labels := by rfl

def raw38258 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38258Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38258step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38258step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38258 raw38258Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw38258 raw38258Labels = mixedMoment B raw38258step0 raw38258step0Labels := by
      have ha : raw38258step0 = (fun i j => raw38258 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38258step0 raw38258; decide +kernel
      have hl : raw38258step0Labels = raw38258Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38258 raw38258Labels permutation8 permutation7
    mixedMoment B raw38258step0 raw38258step0Labels = mixedMoment B raw38258step1 raw38258step1Labels := by
      have ha : raw38258step1 = -raw38258step0 := by apply Matrix.ext; change ∀ i j, raw38258step1 i j = -(raw38258step0 i j); unfold raw38258step1 raw38258step0; decide +kernel
      have hl : raw38258step1Labels = raw38258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38258step1 raw38258step1Labels = mixedMoment B raw38258step2 raw38258step2Labels := by
      have ha : raw38258step2 = raw38258step1 := by apply Matrix.ext; unfold raw38258step2 raw38258step1; decide +kernel
      have hl : raw38258step1Labels = labelEmbedding4 ∘ raw38258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38258step1 raw38258step1Labels raw38258step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

def raw38259 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38259Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38259step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38259 raw38259Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw38259 raw38259Labels = mixedMoment B raw38259step0 raw38259step0Labels := by
      have ha : raw38259step0 = raw38259 := by apply Matrix.ext; unfold raw38259step0 raw38259; decide +kernel
      have hl : raw38259Labels = labelEmbedding2 ∘ raw38259step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38259 raw38259Labels raw38259step0Labels labelEmbedding2 hl
    _ = mixedMoment B node608 node608Labels := by rfl

def raw38260 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38260Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38260step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38260step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38260step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38260 raw38260Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw38260 raw38260Labels = mixedMoment B raw38260step0 raw38260step0Labels := by
      have ha : raw38260step0 = (fun i j => raw38260 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38260step0 raw38260; decide +kernel
      have hl : raw38260step0Labels = raw38260Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38260 raw38260Labels permutation8 permutation7
    mixedMoment B raw38260step0 raw38260step0Labels = mixedMoment B raw38260step1 raw38260step1Labels := by
      have ha : raw38260step1 = -raw38260step0 := by apply Matrix.ext; change ∀ i j, raw38260step1 i j = -(raw38260step0 i j); unfold raw38260step1 raw38260step0; decide +kernel
      have hl : raw38260step1Labels = raw38260step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38260step1 raw38260step1Labels = mixedMoment B raw38260step2 raw38260step2Labels := by
      have ha : raw38260step2 = raw38260step1 := by apply Matrix.ext; unfold raw38260step2 raw38260step1; decide +kernel
      have hl : raw38260step1Labels = labelEmbedding4 ∘ raw38260step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38260step1 raw38260step1Labels raw38260step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

def raw38261 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw38261Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38261step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw38261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38261 raw38261Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw38261 raw38261Labels = mixedMoment B raw38261step0 raw38261step0Labels := by
      have ha : raw38261step0 = raw38261 := by apply Matrix.ext; unfold raw38261step0 raw38261; decide +kernel
      have hl : raw38261Labels = labelEmbedding2 ∘ raw38261step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38261 raw38261Labels raw38261step0Labels labelEmbedding2 hl
    _ = mixedMoment B node609 node609Labels := by rfl

def raw38262 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw38262Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38262step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw38262step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38262step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw38262step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38262step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw38262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38262 raw38262Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw38262 raw38262Labels = mixedMoment B raw38262step0 raw38262step0Labels := by
      have ha : raw38262step0 = (fun i j => raw38262 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38262step0 raw38262; decide +kernel
      have hl : raw38262step0Labels = raw38262Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38262 raw38262Labels permutation2 permutation7
    mixedMoment B raw38262step0 raw38262step0Labels = mixedMoment B raw38262step1 raw38262step1Labels := by
      have ha : raw38262step1 = -raw38262step0 := by apply Matrix.ext; change ∀ i j, raw38262step1 i j = -(raw38262step0 i j); unfold raw38262step1 raw38262step0; decide +kernel
      have hl : raw38262step1Labels = raw38262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38262step1 raw38262step1Labels = mixedMoment B raw38262step2 raw38262step2Labels := by
      have ha : raw38262step2 = raw38262step1 := by apply Matrix.ext; unfold raw38262step2 raw38262step1; decide +kernel
      have hl : raw38262step1Labels = labelEmbedding4 ∘ raw38262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38262step1 raw38262step1Labels raw38262step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw38263 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38263Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38263 raw38263Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw38263 raw38263Labels = mixedMoment B raw38263step0 raw38263step0Labels := by
      have ha : raw38263step0 = raw38263 := by apply Matrix.ext; unfold raw38263step0 raw38263; decide +kernel
      have hl : raw38263Labels = labelEmbedding2 ∘ raw38263step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38263 raw38263Labels raw38263step0Labels labelEmbedding2 hl
    _ = mixedMoment B node610 node610Labels := by rfl

def raw38264 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38264Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38264step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38264step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38264 raw38264Labels = mixedMoment B node1524 node1524Labels := by
  calc
    mixedMoment B raw38264 raw38264Labels = mixedMoment B raw38264step0 raw38264step0Labels := by
      have ha : raw38264step0 = (fun i j => raw38264 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38264step0 raw38264; decide +kernel
      have hl : raw38264step0Labels = raw38264Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38264 raw38264Labels permutation50 permutation7
    mixedMoment B raw38264step0 raw38264step0Labels = mixedMoment B raw38264step1 raw38264step1Labels := by
      have ha : raw38264step1 = -raw38264step0 := by apply Matrix.ext; change ∀ i j, raw38264step1 i j = -(raw38264step0 i j); unfold raw38264step1 raw38264step0; decide +kernel
      have hl : raw38264step1Labels = raw38264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38264step1 raw38264step1Labels = mixedMoment B raw38264step2 raw38264step2Labels := by
      have ha : raw38264step2 = raw38264step1 := by apply Matrix.ext; unfold raw38264step2 raw38264step1; decide +kernel
      have hl : raw38264step1Labels = labelEmbedding4 ∘ raw38264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38264step1 raw38264step1Labels raw38264step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1524 node1524Labels := by rfl

def raw38265 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38265Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38265step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38265 raw38265Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw38265 raw38265Labels = mixedMoment B raw38265step0 raw38265step0Labels := by
      have ha : raw38265step0 = raw38265 := by apply Matrix.ext; unfold raw38265step0 raw38265; decide +kernel
      have hl : raw38265Labels = labelEmbedding2 ∘ raw38265step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38265 raw38265Labels raw38265step0Labels labelEmbedding2 hl
    _ = mixedMoment B node611 node611Labels := by rfl

def raw38266 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38266Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38266step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38266step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38266step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38266step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38266 raw38266Labels = mixedMoment B node1535 node1535Labels := by
  calc
    mixedMoment B raw38266 raw38266Labels = mixedMoment B raw38266step0 raw38266step0Labels := by
      have ha : raw38266step0 = (fun i j => raw38266 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38266step0 raw38266; decide +kernel
      have hl : raw38266step0Labels = raw38266Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38266 raw38266Labels permutation8 permutation7
    mixedMoment B raw38266step0 raw38266step0Labels = mixedMoment B raw38266step1 raw38266step1Labels := by
      have ha : raw38266step1 = -raw38266step0 := by apply Matrix.ext; change ∀ i j, raw38266step1 i j = -(raw38266step0 i j); unfold raw38266step1 raw38266step0; decide +kernel
      have hl : raw38266step1Labels = raw38266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38266step1 raw38266step1Labels = mixedMoment B raw38266step2 raw38266step2Labels := by
      have ha : raw38266step2 = raw38266step1 := by apply Matrix.ext; unfold raw38266step2 raw38266step1; decide +kernel
      have hl : raw38266step1Labels = labelEmbedding4 ∘ raw38266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38266step1 raw38266step1Labels raw38266step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1535 node1535Labels := by rfl

def raw38267 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38267Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38267step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38267 raw38267Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw38267 raw38267Labels = mixedMoment B raw38267step0 raw38267step0Labels := by
      have ha : raw38267step0 = raw38267 := by apply Matrix.ext; unfold raw38267step0 raw38267; decide +kernel
      have hl : raw38267Labels = labelEmbedding2 ∘ raw38267step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38267 raw38267Labels raw38267step0Labels labelEmbedding2 hl
    _ = mixedMoment B node613 node613Labels := by rfl

def raw38268 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38268Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38268step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw38268step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38268step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38268 raw38268Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw38268 raw38268Labels = mixedMoment B raw38268step0 raw38268step0Labels := by
      have ha : raw38268step0 = (fun i j => raw38268 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38268step0 raw38268; decide +kernel
      have hl : raw38268step0Labels = raw38268Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38268 raw38268Labels permutation10 permutation7
    mixedMoment B raw38268step0 raw38268step0Labels = mixedMoment B raw38268step1 raw38268step1Labels := by
      have ha : raw38268step1 = -raw38268step0 := by apply Matrix.ext; change ∀ i j, raw38268step1 i j = -(raw38268step0 i j); unfold raw38268step1 raw38268step0; decide +kernel
      have hl : raw38268step1Labels = raw38268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38268step1 raw38268step1Labels = mixedMoment B raw38268step2 raw38268step2Labels := by
      have ha : raw38268step2 = raw38268step1 := by apply Matrix.ext; unfold raw38268step2 raw38268step1; decide +kernel
      have hl : raw38268step1Labels = labelEmbedding4 ∘ raw38268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38268step1 raw38268step1Labels raw38268step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1525 node1525Labels := by rfl

def raw38269 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38269Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38269step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38269 raw38269Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw38269 raw38269Labels = mixedMoment B raw38269step0 raw38269step0Labels := by
      have ha : raw38269step0 = raw38269 := by apply Matrix.ext; unfold raw38269step0 raw38269; decide +kernel
      have hl : raw38269Labels = labelEmbedding2 ∘ raw38269step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38269 raw38269Labels raw38269step0Labels labelEmbedding2 hl
    _ = mixedMoment B node614 node614Labels := by rfl

def raw38270 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38270Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38270step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38270step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38270step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38270 raw38270Labels = mixedMoment B node1536 node1536Labels := by
  calc
    mixedMoment B raw38270 raw38270Labels = mixedMoment B raw38270step0 raw38270step0Labels := by
      have ha : raw38270step0 = (fun i j => raw38270 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38270step0 raw38270; decide +kernel
      have hl : raw38270step0Labels = raw38270Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38270 raw38270Labels permutation8 permutation7
    mixedMoment B raw38270step0 raw38270step0Labels = mixedMoment B raw38270step1 raw38270step1Labels := by
      have ha : raw38270step1 = -raw38270step0 := by apply Matrix.ext; change ∀ i j, raw38270step1 i j = -(raw38270step0 i j); unfold raw38270step1 raw38270step0; decide +kernel
      have hl : raw38270step1Labels = raw38270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38270step1 raw38270step1Labels = mixedMoment B raw38270step2 raw38270step2Labels := by
      have ha : raw38270step2 = raw38270step1 := by apply Matrix.ext; unfold raw38270step2 raw38270step1; decide +kernel
      have hl : raw38270step1Labels = labelEmbedding4 ∘ raw38270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38270step1 raw38270step1Labels raw38270step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1536 node1536Labels := by rfl

def raw38271 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw38271Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38271step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw38271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38271 raw38271Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw38271 raw38271Labels = mixedMoment B raw38271step0 raw38271step0Labels := by
      have ha : raw38271step0 = raw38271 := by apply Matrix.ext; unfold raw38271step0 raw38271; decide +kernel
      have hl : raw38271Labels = labelEmbedding2 ∘ raw38271step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38271 raw38271Labels raw38271step0Labels labelEmbedding2 hl
    _ = mixedMoment B node615 node615Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
